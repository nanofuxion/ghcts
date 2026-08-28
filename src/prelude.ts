/** The minimal Prelude the dictionary-passing frontend needs, as ordinary
 * Haskell compiled through the same pipeline as user code.
 *
 * Nothing here is a builtin pretending to be a class method: `+`, `==`, `show`
 * are genuine class methods, selected from genuine dictionaries. The only
 * primitives are the `prim*` names `src/desugar.ts` maps onto JS-backend
 * primops, and they are typed over the *unboxed* types `IntPrim`/`CharPrim` -
 * never over `Int`, which is the boxed `I IntPrim` this module declares. The
 * one non-primop escape is `error`, which is a `foreign import javascript`
 * that throws: GHC's `error` bottoms out in `raise#`, and a JS `throw` is the
 * JS backend's equivalent - there is no exception closure to build here.
 *
 * Two shapes are deliberate:
 *
 *   - the comparison primops return `Bool`, not `IntPrim`. `IntLtOp` yields a
 *     0/1 machine value; wrapping it into a real constructor is GHC's
 *     `tagToEnum# (<# a b)` and it happens once, in the desugarer, so no
 *     Haskell here ever has to `case` on a raw machine word.
 *   - each class/instance member equation stays on one line. Member slices are
 *     re-parsed from their tokens (`src/dictionary.ts`), which joins them with
 *     spaces; separate equations of one method are rejoined there, but a body
 *     wanting `case`/`where` still lives in a top-level helper instead.
 *
 * `Foldable` here has no `foldMap`: it would need a `Monoid` constraint of its
 * own, which is now expressible (see `ClassMethod.ownContext`) but would leave
 * every existing instance without the method the class then requires.
 *
 * `IO` is GHC's `State# RealWorld -> (# State# RealWorld, a #)`, exactly: the
 * token is a void type the backend erases and the result is an unboxed tuple
 * returned in registers, so a bind step allocates nothing. See the comment on
 * the declaration below.
 */
/** The ghc-internal closures GHC's JS RTS names by symbol, and the Prelude
 * binding that fills each seat.
 *
 * A symbol is nothing but a unit, a module and a name (`mkJsSymbol`), so a
 * ghcts binding emitted under GHC's module *is* GHC's closure as far as the
 * RTS can tell. `src/build.ts` does the emitting and `src/elaborate.ts` keeps
 * these bindings alive through the reachability pass, since nothing in the
 * program refers to them - only the RTS does. */
export const RTS_SEATS: ReadonlyArray<{
  /** The Prelude binding that fills the seat. */
  binding: string;
  unitId: string;
  moduleName: string;
  name: string;
}> = [
  { binding: "rtsReportError", unitId: "ghc-internal", moduleName: "GHC.Internal.Conc.Sync", name: "reportError" },
  { binding: "rtsTopHandler", unitId: "ghc-internal", moduleName: "GHC.Internal.TopHandler", name: "topHandler" },
  { binding: "rtsHFlush", unitId: "ghc-internal", moduleName: "GHC.Internal.IO.Handle", name: "hFlush" },
  { binding: "rtsStdout", unitId: "ghc-internal", moduleName: "GHC.Internal.IO.Handle.FD", name: "stdout" },
];

export const PRELUDE_SOURCE = `module GHCTS.Prelude where

data Bool = False | True
data Int = I IntPrim
data Char = C CharPrim
-- \`Double\` is a one-field box for the same reason \`Int\` is \`I IntPrim\`:
-- the backend unboxes a one-constructor, one-Number-field type (Double is in
-- \`unboxableTyCons\`), so a \`DoubleBox 2.5\` IS the JS number 2.5, exactly as
-- GHC's \`D# 2.5##\` is. The name is deliberately not \`D\`: data constructors
-- live in one global namespace here, so a Prelude constructor takes its name
-- away from every program that declares one, and \`data C = A | B | D\` is a
-- thing people write.
data Double = DoubleBox DoublePrim

-- IEEE *single* precision. On this backend a \`Float\` is a JS number like a
-- \`Double\`; what makes it a different type is that every arithmetic result
-- goes back through \`Math.fround\`, which is what \`FloatAddOp\` and its
-- neighbours do. \`Float\` is in the backend's \`unboxableTyCons\` for the same
-- reason \`Double\` is, so a \`FloatBox\` IS the number.
data Float = FloatBox FloatPrim
data Ordering = LT | EQ | GT
data Maybe a = Nothing | Just a
data Either a b = Left a | Right b

-- \`IO\` in GHC's own representation. \`RealWorld\` is GHC's \`State# RealWorld\`:
-- a VOID type, zero JS values wide, declared nowhere because it has no values
-- to declare - \`src/elaborate.ts\` recognises the name and \`src/desugar.ts\`
-- gives every binder at that type \`arity = 0\`, which is what makes codegen
-- drop the argument register entirely. \`IOResult\` is GHC's unboxed tuple
-- \`(# State# RealWorld, a #)\`, wired to the backend's \`(#,#)\` in
-- \`src/desugar.ts\`; it is written as an ordinary data declaration only so the
-- type checker can see its fields.
--
-- The two together are what make an \`IO\` action a closure of arity 1 with NO
-- argument registers, which is the calling convention \`h\$ap_1_0\`, \`h\$catch\`
-- and \`h\$forkThread\` all assume - and they are why a bind step now assigns a
-- register where it used to allocate a two-field heap object.
data IOResult a = IOResult RealWorld a
data IO a = IO (RealWorld -> IOResult a)

-- --------------------------------------------------------------- classes ---

class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool
  (/=) x y = not (x == y)

class Eq a => Ord a where
  compare :: a -> a -> Ordering
  (<) :: a -> a -> Bool
  (<=) :: a -> a -> Bool
  (>) :: a -> a -> Bool
  (>=) :: a -> a -> Bool
  max :: a -> a -> a
  min :: a -> a -> a
  compare x y = if x <= y then (if y <= x then EQ else LT) else GT
  (<) x y = eqOrdering (compare x y) LT
  (<=) x y = not (eqOrdering (compare x y) GT)
  (>) x y = eqOrdering (compare x y) GT
  (>=) x y = not (eqOrdering (compare x y) LT)
  max x y = if eqOrdering (compare x y) LT then y else x
  min x y = if eqOrdering (compare x y) GT then y else x

class Num a where
  (+) :: a -> a -> a
  (-) :: a -> a -> a
  (*) :: a -> a -> a
  negate :: a -> a
  fromInteger :: Integer -> a

class Num a => Fractional a where
  (/) :: a -> a -> a
  fromRational :: DoublePrim -> a

-- The one method each of \`Real\`/\`RealFrac\`/\`Integral\` this frontend needs.
-- GHC routes \`realToFrac\` through \`Rational\`; there is no \`Ratio\` here, and
-- \`DoublePrim\` is the widest exact type a \`Fractional\` can be reached from, so
-- it stands in for the intermediate. \`Integral\` is GHC's own \`toInteger\`,
-- because \`Integer\` IS the widest exact type on the integral side: routing
-- \`fromIntegral\` through \`IntPrim\` would truncate every \`Int64\` and \`Word64\`
-- to 32 bits on the way out.
class Num a => Real a where
  toDoublePrim :: a -> DoublePrim

class Fractional a => RealFrac a where
  fracToDoublePrim :: a -> DoublePrim

class Num a => Integral a where
  toInteger :: a -> Integer

-- GHC's own three methods and their mutual defaults. \`showsPrec\` is what
-- makes nesting print right - a field is shown at precedence 11, so
-- \`Just (Just 1)\` gets the parentheses \`show\` alone could never place - and
-- \`showList\` is what makes \`show "hi"\` a quoted string rather than a list of
-- quoted characters.
class Show a where
  showsPrec :: Int -> a -> [Char] -> [Char]
  show :: a -> [Char]
  showList :: [a] -> [Char] -> [Char]
  showsPrec d x s = show x ++ s
  show x = showsPrec 0 x ""
  showList xs s = showList__ shows xs s

class Enum a where
  toEnum :: Int -> a
  fromEnum :: a -> Int
  succ :: a -> a
  pred :: a -> a
  enumFrom :: a -> [a]
  enumFromTo :: a -> a -> [a]
  enumFromThen :: a -> a -> [a]
  enumFromThenTo :: a -> a -> a -> [a]
  succ x = toEnum (fromEnum x + 1)
  pred x = toEnum (fromEnum x - 1)
  -- GHC's own defaults: the range is walked on the \`Int\` the type maps to and
  -- mapped back, so \`[x ..]\` stops at \`maxBound :: Int\` rather than wrapping.
  enumFrom x = map toEnum (enumIntFromTo (fromEnum x) maxBound)
  enumFromTo x y = map toEnum (enumIntFromTo (fromEnum x) (fromEnum y))
  enumFromThen x y = map toEnum (enumIntFromThenTo (fromEnum x) (fromEnum y - fromEnum x) (enumLimit (fromEnum y - fromEnum x)))
  enumFromThenTo x y z = map toEnum (enumIntFromThenTo (fromEnum x) (fromEnum y - fromEnum x) (fromEnum z))

class Bounded a where
  minBound :: a
  maxBound :: a

class Semigroup a where
  (<>) :: a -> a -> a

class Semigroup a => Monoid a where
  mempty :: a
  mappend :: a -> a -> a
  mconcat :: [a] -> a
  mappend x y = x <> y
  mconcat xs = foldr mappend mempty xs

class IsString a where
  fromString :: [Char] -> a

class Functor f where
  fmap :: (a -> b) -> f a -> f b
  (<$) :: a -> f b -> f a
  (<$) x m = fmap (\\y -> x) m

class Functor f => Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b
  liftA2 :: (a -> b -> c) -> f a -> f b -> f c
  (*>) :: f a -> f b -> f b
  (<*) :: f a -> f b -> f a
  liftA2 f a b = fmap f a <*> b
  (*>) a b = liftA2 (\\x y -> y) a b
  (<*) a b = liftA2 (\\x y -> x) a b

class Applicative m => Monad m where
  (>>=) :: m a -> (a -> m b) -> m b
  (>>) :: m a -> m b -> m b
  return :: a -> m a
  (>>) m k = m >>= (\\x -> k)
  return x = pure x

class Monad m => MonadFail m where
  fail :: [Char] -> m a

class Applicative f => Alternative f where
  empty :: f a
  (<|>) :: f a -> f a -> f a
  some :: f a -> f [a]
  many :: f a -> f [a]
  some v = liftA2 (\\x xs -> x : xs) v (many v)
  many v = someOrNone v

class (Alternative m, Monad m) => MonadPlus m where
  mzero :: m a
  mplus :: m a -> m a -> m a
  mzero = empty
  mplus a b = a <|> b

class Monad m => MonadIO m where
  liftIO :: IO a -> m a

-- \`foldr\` is the whole class: \`foldMap\` would need a \`Monoid\` constraint of
-- its own, which a method signature here cannot carry. Everything else that
-- folds is an ordinary function constrained by \`Foldable\`.
class Foldable t where
  foldr :: (a -> b -> b) -> b -> t a -> b
  toList :: t a -> [a]
  toList xs = foldr (\\x ys -> x : ys) [] xs

-- \`traverse\` constrains an \`f\` the class never mentions, which is exactly
-- what a method's own context is for: the dictionary field holds a function
-- of the \`Applicative\` dictionary, supplied by the call site rather than by
-- the instance.
class Foldable t => Traversable t where
  traverse :: Applicative f => (a -> f b) -> t a -> f (t b)
  sequenceA :: Applicative f => t (f a) -> f (t a)
  mapM :: Monad m => (a -> m b) -> t a -> m (t b)
  sequence :: Monad m => t (m a) -> m (t a)
  sequenceA xs = traverse (\\x -> x) xs
  mapM f xs = traverse f xs
  sequence xs = traverse (\\x -> x) xs

-- ------------------------------------------------------------- instances ---

instance Eq Int where
  (==) (I a) (I b) = primIntEq a b

instance Ord Int where
  (<) (I a) (I b) = primIntLt a b
  (<=) (I a) (I b) = primIntLe a b
  (>) (I a) (I b) = primIntGt a b
  (>=) (I a) (I b) = primIntGe a b

instance Num Int where
  (+) (I a) (I b) = I (primIntAdd a b)
  (-) (I a) (I b) = I (primIntSub a b)
  (*) (I a) (I b) = I (primIntMul a b)
  negate (I a) = I (primIntNeg a)
  -- Matching \`Integer b\` rather than calling a conversion is what keeps the
  -- machine value machine: a primitive call in an argument or a field is
  -- evaluated where it stands, but a Haskell function's result there is a
  -- THUNK - and \`I\` is an unboxed constructor, so the field would BE it.
  fromInteger (Integer b) = I (primIntegerToInt b)

instance Show Int where
  -- GHC's \`showSignedInt\`: a negative number is parenthesised at any
  -- precedence above 6, so \`show (Just (-1))\` is \`Just (-1)\`.
  showsPrec d n s = if n < 0 && d > 6 then '(' : showInt n ++ (')' : s) else showInt n ++ s

-- GHC's \`showFloat\` is \`formatRealFloat FFGeneric Nothing\` over the shortest
-- decimal digits that read back as the same value. \`toExponential()\` with no
-- argument is specified to produce exactly those digits - the same shortest
-- representation \`GHC.Float.floatToDigits\` computes - so only the placement of
-- the point around them is transcribed here, case for case: scientific below
-- 0.1 and from 10^7 up, fixed in between, and always a digit either side of
-- the point.
foreign import javascript unsafe "((x) => { if (x !== x) return 'NaN'; if (x === Infinity) return 'Infinity'; if (x === -Infinity) return '-Infinity'; var neg = x < 0 || Object.is(x, -0); var a = neg ? -x : x; var t = a.toExponential(); var i = t.indexOf('e'); var ds = t.slice(0, i).replace('.', ''); var e = parseInt(t.slice(i + 1), 10) + 1; var out; if (e < 0 || e > 7) { out = (ds.length === 1 ? ds + '.0' : ds[0] + '.' + ds.slice(1)) + 'e' + (e - 1); } else if (e <= 0) { out = '0.' + '0'.repeat(-e) + ds; } else { var w = ds.length >= e ? ds.slice(0, e) : ds + '0'.repeat(e - ds.length); var f = ds.length > e ? ds.slice(e) : ''; out = w + '.' + (f === '' ? '0' : f); } return neg ? '-' + out : out; })" primShowDouble :: DoublePrim -> JSStringPrim

-- A \`Float\`'s shortest digits are the shortest that round-trip *at single
-- precision*, which is not what \`toExponential()\` gives for a value held in a
-- double: 0.1 as a Float is 0.10000000149011612 as a double. The search is for
-- the first precision whose reading fronds back to the same float.
foreign import javascript unsafe "((x) => { if (x !== x) return 'NaN'; if (x === Infinity) return 'Infinity'; if (x === -Infinity) return '-Infinity'; var neg = x < 0 || Object.is(x, -0); var a = Math.fround(neg ? -x : x); var t = null; for (var p = 0; p < 9; p++) { var c = a.toExponential(p); if (Math.fround(Number(c)) === a) { t = c; break; } } if (t === null) t = a.toExponential(); var i = t.indexOf('e'); var ds = t.slice(0, i).replace('.', ''); var e = parseInt(t.slice(i + 1), 10) + 1; var out; if (e < 0 || e > 7) { out = (ds.length === 1 ? ds + '.0' : ds[0] + '.' + ds.slice(1)) + 'e' + (e - 1); } else if (e <= 0) { out = '0.' + '0'.repeat(-e) + ds; } else { var w = ds.length >= e ? ds.slice(0, e) : ds + '0'.repeat(e - ds.length); var f = ds.length > e ? ds.slice(e) : ''; out = w + '.' + (f === '' ? '0' : f); } return neg ? '-' + out : out; })" primShowFloat :: FloatPrim -> JSStringPrim

foreign import javascript unsafe "((s) => s.length)" primAsciiLength :: JSStringPrim -> IntPrim
foreign import javascript unsafe "((s, i) => s.charCodeAt(i))" primAsciiAt :: JSStringPrim -> IntPrim -> IntPrim
foreign import javascript unsafe "((x) => x < 0 || Object.is(x, -0))" primDoubleIsNeg :: DoublePrim -> Bool

-- These strings are digits, signs and \`e\`, so a code unit is a code point.
jsAscii :: JSStringPrim -> [Char]
jsAscii s = jsAsciiFrom s 0 (primAsciiLength s)

jsAsciiFrom :: JSStringPrim -> IntPrim -> IntPrim -> [Char]
jsAsciiFrom s i n = if primIntGe i n then [] else C (primChr (primAsciiAt s i)) : jsAsciiFrom s (primIntAdd i 1) n

showDouble :: Double -> [Char]
showDouble x = case x of
  DoubleBox p -> jsAscii (primShowDouble p)

showFloat :: Float -> [Char]
showFloat x = case x of
  FloatBox p -> jsAscii (primShowFloat p)

-- \`showSignedFloat\`: the sign is not part of the number's own spelling, so a
-- negative one is parenthesised wherever a prefix application would be.
instance Show Double where
  showsPrec d x s = case x of
    DoubleBox p -> if primDoubleIsNeg p && d > 6 then '(' : showDouble x ++ (')' : s) else showDouble x ++ s

instance Show Float where
  showsPrec d x s = case x of
    FloatBox p -> if x < 0 && d > 6 then '(' : showFloat x ++ (')' : s) else showFloat x ++ s

instance Show () where
  showsPrec d x s = showString "()" s

instance Show a => Show (Maybe a) where
  showsPrec d x s = case x of
    Nothing -> showString "Nothing" s
    Just y -> showParen (d > 10) (\\r -> showString "Just " (showsPrec 11 y r)) s

instance (Show a, Show b) => Show (Either a b) where
  showsPrec d x s = case x of
    Left y -> showParen (d > 10) (\\r -> showString "Left " (showsPrec 11 y r)) s
    Right y -> showParen (d > 10) (\\r -> showString "Right " (showsPrec 11 y r)) s

instance Show Char where
  showsPrec _ c s = if c == '\\'' then showString "'\\\\''" s else showChar '\\'' (showLitChar c (showChar '\\'' s))
  showList cs s = showChar '"' (showLitString cs (showChar '"' s))

instance Show a => Show [a] where
  showsPrec _ xs s = showList xs s

instance (Show a, Show b) => Show (a, b) where
  showsPrec _ p s = case p of
    (a, b) -> showChar '(' (shows a (showChar ',' (shows b (showChar ')' s))))

instance (Show a, Show b, Show c) => Show (a, b, c) where
  showsPrec _ p s = case p of
    (a, b, c) -> showChar '(' (shows a (showChar ',' (shows b (showChar ',' (shows c (showChar ')' s))))))

instance Real Int where
  toDoublePrim (I n) = primIntToDouble n

instance Integral Int where
  toInteger (I n) = Integer (primIntegerFromInt n)

instance Eq Double where
  (==) (DoubleBox a) (DoubleBox b) = primDoubleEq a b

instance Ord Double where
  (<) (DoubleBox a) (DoubleBox b) = primDoubleLt a b
  (<=) (DoubleBox a) (DoubleBox b) = primDoubleLe a b
  (>) (DoubleBox a) (DoubleBox b) = primDoubleGt a b
  (>=) (DoubleBox a) (DoubleBox b) = primDoubleGe a b

instance Num Double where
  (+) (DoubleBox a) (DoubleBox b) = DoubleBox (primDoubleAdd a b)
  (-) (DoubleBox a) (DoubleBox b) = DoubleBox (primDoubleSub a b)
  (*) (DoubleBox a) (DoubleBox b) = DoubleBox (primDoubleMul a b)
  negate (DoubleBox a) = DoubleBox (primDoubleNeg a)
  fromInteger (Integer b) = DoubleBox (primIntegerToDouble b)

instance Fractional Double where
  (/) (DoubleBox a) (DoubleBox b) = DoubleBox (primDoubleDiv a b)
  fromRational d = DoubleBox d

instance Real Double where
  toDoublePrim (DoubleBox d) = d

instance RealFrac Double where
  fracToDoublePrim (DoubleBox d) = d

instance Eq Float where
  (==) (FloatBox a) (FloatBox b) = primFloatEq a b

instance Ord Float where
  (<) (FloatBox a) (FloatBox b) = primFloatLt a b
  (<=) (FloatBox a) (FloatBox b) = primFloatLe a b
  (>) (FloatBox a) (FloatBox b) = primFloatGt a b
  (>=) (FloatBox a) (FloatBox b) = primFloatGe a b

instance Num Float where
  (+) (FloatBox a) (FloatBox b) = FloatBox (primFloatAdd a b)
  (-) (FloatBox a) (FloatBox b) = FloatBox (primFloatSub a b)
  (*) (FloatBox a) (FloatBox b) = FloatBox (primFloatMul a b)
  negate (FloatBox a) = FloatBox (primFloatNeg a)
  fromInteger (Integer b) = FloatBox (primDoubleToFloat (primIntegerToDouble b))

instance Fractional Float where
  (/) (FloatBox a) (FloatBox b) = FloatBox (primFloatDiv a b)
  fromRational d = FloatBox (primDoubleToFloat d)

instance Real Float where
  toDoublePrim (FloatBox a) = primFloatToDouble a

instance RealFrac Float where
  fracToDoublePrim (FloatBox a) = primFloatToDouble a

-- The JS backend's \`Int\` is 32-bit, exactly as GHC's is on that platform.
instance Bounded Int where
  minBound = negate 2147483648
  maxBound = 2147483647

-- Lazy in the tail, so \`zip [0 ..] xs\` walks only as far as \`xs\` does.
enumIntFromTo :: Int -> Int -> [Int]
enumIntFromTo x y = if x > y then [] else x : enumIntFromTo (x + 1) y

enumIntFromThenTo :: Int -> Int -> Int -> [Int]
enumIntFromThenTo x d y =
  if (if d < 0 then x < y else x > y)
    then []
    else x : enumIntFromThenTo (x + d) d y

-- \`[x, y ..]\` runs to whichever end of \`Int\` its step is heading for.
enumLimit :: Int -> Int
enumLimit d = if d < 0 then minBound else maxBound

instance Enum Int where
  toEnum n = n
  fromEnum n = n

instance Eq Char where
  (==) (C a) (C b) = primCharEq a b

instance Eq Bool where
  (==) a b = eqBool a b

instance Show Bool where
  show b = showBool b

instance Eq Ordering where
  (==) a b = eqOrdering a b

instance Show Ordering where
  show o = showOrdering o

instance Eq a => Eq [a] where
  (==) xs ys = eqList (==) xs ys

instance Ord a => Ord [a] where
  compare xs ys = compareList compare xs ys

instance Eq a => Eq (Maybe a) where
  (==) a b = eqMaybe (==) a b

instance Ord a => Ord (Maybe a) where
  compare a b = compareMaybe compare a b

instance Eq () where
  (==) a b = True

instance (Eq a, Eq b) => Eq (Either a b) where
  (==) a b = eqEither (==) (==) a b

instance (Eq a, Eq b) => Eq (a, b) where
  (==) a b = eqPair (==) (==) a b

-- base writes this \`instance a ~ Char => IsString [a]\`; the improvement that
-- makes the element \`Char\` lives in the elaborator, so the head can be exact.
instance IsString [Char] where
  fromString cs = cs

instance Semigroup [a] where
  (<>) xs ys = append xs ys

instance Monoid [a] where
  mempty = []

instance Semigroup Ordering where
  (<>) a b = thenOrdering a b

instance Monoid Ordering where
  mempty = EQ

instance Functor [] where
  fmap f xs = map f xs

instance Applicative [] where
  pure x = x : []
  (<*>) fs xs = listAp fs xs

instance Monad [] where
  (>>=) xs k = concatMap k xs

instance Alternative [] where
  (<|>) xs ys = append xs ys
  empty = []

-- base has this one, and a refutable \`do\` bind now needs it: \`[x | ...]\`
-- written as a \`do\` block drops a non-matching element rather than raising.
instance MonadFail [] where
  fail s = []

instance Traversable [] where
  traverse f xs = traverseList f xs

instance Foldable [] where
  foldr f z xs = foldrList f z xs
  toList xs = xs

instance Functor Maybe where
  fmap f m = maybeMap f m

instance Applicative Maybe where
  pure x = Just x
  (<*>) f m = maybeAp f m

instance Monad Maybe where
  (>>=) m k = maybeBind m k

instance MonadFail Maybe where
  fail s = Nothing

instance Alternative Maybe where
  empty = Nothing
  (<|>) a b = maybeOr a b

instance Foldable Maybe where
  foldr f z m = maybeFoldr f z m

instance Semigroup a => Semigroup (Maybe a) where
  (<>) a b = maybeAppend (<>) a b

-- The reader instances. \`(->) r\` is a functor in its result, so \`fmap\` is
-- composition and \`<*>\` is the S combinator; miso's lens code and
-- \`Miso.Runtime\` both go through them.
instance Functor ((->) r) where
  fmap f g = \\x -> f (g x)

instance Applicative ((->) r) where
  pure x = \\r -> x
  (<*>) f g = \\r -> f r (g r)

instance Monad ((->) r) where
  (>>=) m k = \\r -> k (m r) r

instance Functor (Either e) where
  fmap f m = eitherMap f m

instance Applicative (Either e) where
  pure x = Right x
  (<*>) f m = eitherAp f m

instance Monad (Either e) where
  (>>=) m k = eitherBind m k

instance Foldable (Either e) where
  foldr f z m = eitherFoldr f z m

instance Functor IO where
  fmap f m = ioMap f m

instance Applicative IO where
  pure x = ioPure x
  (<*>) f m = ioAp f m

instance Monad IO where
  (>>=) m k = ioBind m k
  (>>) m k = ioThen m k

instance MonadFail IO where
  fail s = error s

instance MonadIO IO where
  liftIO m = m

-- -------------------------------------------------------------------- IO ---

-- Peeling the constructor is where an \`IO\` action stops being a value and
-- becomes an application, so nothing in a \`do\` block runs until \`unIO\`
-- reaches it.
unIO :: IO a -> RealWorld -> IOResult a
unIO m s = case m of
  IO f -> f s

ioPure :: a -> IO a
ioPure x = IO (\\s -> IOResult s x)

-- GHC's \`case m s of (# s', a #) -> unIO (k a) s'\`. Matching \`IOResult\` is
-- what runs \`m\` to completion before \`k\` starts; \`a\` stays a thunk, so
-- binding a result never forces it.
ioBind :: IO a -> (a -> IO b) -> IO b
ioBind m k = IO (\\s -> ioBindStep m k s)

ioBindStep :: IO a -> (a -> IO b) -> RealWorld -> IOResult b
ioBindStep m k s = case unIO m s of
  IOResult t a -> unIO (k a) t

ioThen :: IO a -> IO b -> IO b
ioThen m k = IO (\\s -> ioThenStep m k s)

ioThenStep :: IO a -> IO b -> RealWorld -> IOResult b
ioThenStep m k s = case unIO m s of
  IOResult t a -> unIO k t

ioMap :: (a -> b) -> IO a -> IO b
ioMap f m = ioBind m (\\x -> ioPure (f x))

ioAp :: IO (a -> b) -> IO a -> IO b
ioAp f m = ioBind f (\\g -> ioMap g m)

-- GHC's \`unsafeDupablePerformIO (IO m) = case m realWorld# of (# _, a #) -> a\`.
-- An unboxed tuple cannot be passed to a function, so the match has to happen
-- here rather than in a helper - which is also why \`ioBindStep\` above takes
-- the action and the token instead of the tuple.
unsafePerformIO :: IO a -> a
unsafePerformIO m = case unIO m primRealWorld of
  IOResult s a -> a

-- GHC's real entry point is \`:Main.main = runMainIO Main.main\`;
-- \`src/elaborate.ts\` builds that wrapper and \`src/build.ts\` emits it as the
-- \`:Main\` module the RTS names.
--
-- \`h$main\` does not merely *enter* the wrapper. It enters it and then applies
-- the result with \`h$ap_1_0\` - one argument occupying no register - because
-- GHC's \`IO a\` IS the state-token function and its token is a void type. So
-- the wrapper has to leave a function of that shape behind: \`unIO\`, which
-- peels ghcts's \`IO\` constructor, and not \`unsafePerformIO\`, which would run
-- the action during entry and hand \`h$ap_1_0\` a value it cannot apply.
--
-- \`IOResult\` is an unboxed tuple whose token half is erased, so the applied
-- call returns the action's result in R1, exactly as GHC's does.
runMainIO :: IO a -> RealWorld -> IOResult a
runMainIO m s = unIO m s

-- GHC's JS RTS names four ghc-internal closures directly, as globals, and a
-- reference to an undefined global is a ReferenceError rather than
-- \`undefined\` - so a bundle that does not define them cannot even start.
-- \`h$Thread\` seats \`Conc.Sync.reportError\` under the thread's top-level
-- \`h$catch_e\` frame; outside a browser \`h$main\` replaces it with
-- \`TopHandler.topHandler\` and pushes \`h$flushStdout\`, which is
-- \`IO.Handle.hFlush\` applied to \`IO.Handle.FD.stdout\`. A ghcts program links
-- no ghc-internal, so the seats are filled from Haskell here and
-- \`src/build.ts\` emits each one under the module GHC keeps it in - a symbol
-- being nothing but a module and a name.
--
-- Both handlers are the shape \`h$catch_e\` applies: the exception and the
-- erased state token. \`topHandler\` is the one an uncaught exception reaches
-- in a real program, and GHC's exits non-zero, so this one does too - by
-- setting the exit code rather than calling \`h$exitProcess\`, which would cut
-- the RTS off mid-unwind.
foreign import javascript unsafe "((e) => { console.error('ghcts: uncaught exception:', e); return 0; })" primReportUncaught :: JSValPrim -> IntPrim
foreign import javascript unsafe "((e) => { console.error('ghcts: uncaught exception:', e); if (typeof process !== 'undefined') process.exitCode = 1; return 0; })" primDieUncaught :: JSValPrim -> IntPrim

rtsReportError :: JSValPrim -> RealWorld -> IOResult ()
rtsReportError e s = case primReportUncaught e of
  _ -> IOResult s ()

rtsTopHandler :: JSValPrim -> RealWorld -> IOResult ()
rtsTopHandler e s = case primDieUncaught e of
  _ -> IOResult s ()

-- ghcts writes through \`console.log\`, which is not buffered, so there is
-- nothing for \`hFlush\` to do; the seat still has to be the two-argument
-- closure \`h$flushStdout_e\` applies to the handle and then to the token.
rtsHFlush :: JSValPrim -> RealWorld -> IOResult ()
rtsHFlush h s = IOResult s ()

rtsStdout :: ()
rtsStdout = ()

-- ------------------------------------------------------------- functions ---

-- The wrapper is not ceremony. A *saturated* foreign call is inlined as a
-- primitive operation (see \`foreignOps\` in src/desugar.ts), and a primitive
-- operation in an argument position is evaluated there rather than thunked -
-- so \`f (errorPrim s)\` would raise before \`f\` ever ran. As an ordinary
-- Haskell function, \`error s\` is a thunk in a lazy position, exactly as GHC's
-- is, and only raises when something forces it.
foreign import javascript unsafe "((s) => { throw new Error('Prelude.error'); })" errorPrim :: [Char] -> a

error :: [Char] -> a
error s = errorPrim s

undefined :: a
undefined = error "Prelude.undefined"

otherwise :: Bool
otherwise = True

id :: a -> a
id x = x

const :: a -> b -> a
const x y = x

flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

fst :: (a, b) -> a
fst p = case p of
  (x, y) -> x

snd :: (a, b) -> b
snd p = case p of
  (x, y) -> y

curry :: ((a, b) -> c) -> a -> b -> c
curry f x y = f (x, y)

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f p = case p of
  (x, y) -> f x y

($) :: (a -> b) -> a -> b
($) f x = f x

-- \`case\` on a *var* is irrefutable and compiles to nothing, so the scrutinee
-- here is an application: that is what makes the desugarer emit a real \`Case\`,
-- and a real \`Case\` is what evaluates its scrutinee to WHNF. This is \`seq\`.
forceValue :: a -> a
forceValue x = x

seq :: a -> b -> b
seq x y = case forceValue x of
  z -> y

($!) :: (a -> b) -> a -> b
($!) f x = case forceValue x of
  y -> f y

(&) :: a -> (a -> b) -> b
(&) x f = f x

(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

(++) :: [a] -> [a] -> [a]
(++) xs ys = append xs ys

(&&) :: Bool -> Bool -> Bool
(&&) a b = if a then b else False

(||) :: Bool -> Bool -> Bool
(||) a b = if a then True else b

not :: Bool -> Bool
not b = if b then False else True

eqBool :: Bool -> Bool -> Bool
eqBool a b = if a then b else not b

showBool :: Bool -> [Char]
showBool b = if b then "True" else "False"

ordIndex :: Ordering -> IntPrim
ordIndex o = case o of
  LT -> 0
  EQ -> 1
  GT -> 2

eqOrdering :: Ordering -> Ordering -> Bool
eqOrdering a b = primIntEq (ordIndex a) (ordIndex b)

thenOrdering :: Ordering -> Ordering -> Ordering
thenOrdering a b = if eqOrdering a EQ then b else a

showOrdering :: Ordering -> [Char]
showOrdering o = case o of
  LT -> "LT"
  EQ -> "EQ"
  GT -> "GT"

shows :: Show a => a -> [Char] -> [Char]
shows x s = showsPrec 0 x s

showChar :: Char -> [Char] -> [Char]
showChar c s = c : s

showString :: [Char] -> [Char] -> [Char]
showString xs s = xs ++ s

showParen :: Bool -> ([Char] -> [Char]) -> [Char] -> [Char]
showParen b p s = if b then showChar '(' (p (showChar ')' s)) else p s

showList__ :: (a -> [Char] -> [Char]) -> [a] -> [Char] -> [Char]
showList__ showx xs s = case xs of
  [] -> "[]" ++ s
  (y : ys) -> '[' : showx y (showListTail showx ys s)

showListTail :: (a -> [Char] -> [Char]) -> [a] -> [Char] -> [Char]
showListTail showx xs s = case xs of
  [] -> ']' : s
  (y : ys) -> ',' : showx y (showListTail showx ys s)

-- GHC.Show's own table, verbatim: the mnemonic for each of the first 33 code
-- points. \`showLitChar\` never reaches the entries that have a shorter
-- spelling (\`\\n\` for LF, \`\\t\` for HT), so they are here only to keep the
-- indices right.
asciiTab :: [[Char]]
asciiTab =
  [ "NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL"
  , "BS", "HT", "LF", "VT", "FF", "CR", "SO", "SI"
  , "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB"
  , "CAN", "EM", "SUB", "ESC", "FS", "GS", "RS", "US"
  , "SP"
  ]

asciiName :: Int -> [Char]
asciiName n = case drop n asciiTab of
  (x : _) -> x
  [] -> ""

-- \`showLitChar\` and \`showLitString\` are GHC.Show's, case for case and in its
-- order: a code point above DEL is a decimal escape, DEL and the backslash are
-- named, anything printable stands for itself, seven control characters have
-- short escapes, and the rest take their mnemonic from the table.
showLitChar :: Char -> [Char] -> [Char]
showLitChar c s =
  if c > '\\DEL' then showChar '\\\\' (showString (showInt (ord c)) (escapeGuard isDecDigit s))
  else if c == '\\DEL' then showString "\\\\DEL" s
  else if c == '\\\\' then showString "\\\\\\\\" s
  else if c >= ' ' then showChar c s
  else if c == '\\a' then showString "\\\\a" s
  else if c == '\\b' then showString "\\\\b" s
  else if c == '\\f' then showString "\\\\f" s
  else if c == '\\n' then showString "\\\\n" s
  else if c == '\\r' then showString "\\\\r" s
  else if c == '\\t' then showString "\\\\t" s
  else if c == '\\v' then showString "\\\\v" s
  else if c == '\\SO' then showString "\\\\SO" (escapeGuard isH s)
  else showString ('\\\\' : asciiName (ord c)) s

showLitString :: [Char] -> [Char] -> [Char]
showLitString xs s = case xs of
  [] -> s
  (c : cs) -> if c == '"' then showString "\\\\\\"" (showLitString cs s) else showLitChar c (showLitString cs s)

-- \`\\&\` is the empty escape, and it is all that separates the two readings of
-- \`"\\1234"\`: without it a following digit would join the numeric escape, and
-- \`"\\SOH"\` would be SOH rather than SO then H.
escapeGuard :: (Char -> Bool) -> [Char] -> [Char]
escapeGuard p s = case s of
  (c : _) -> if p c then "\\\\&" ++ s else s
  [] -> s

isDecDigit :: Char -> Bool
isDecDigit c = c >= '0' && c <= '9'

isH :: Char -> Bool
isH c = c == 'H'

showInt :: Int -> [Char]
showInt (I n) = if primIntLt n 0 then C (primChr 45) : digitsOf (primIntNeg n) [] else digitsOf n []

digitsOf :: IntPrim -> [Char] -> [Char]
digitsOf n acc = if primIntLt n 10 then digitChar n : acc else digitsOf (primIntQuot n 10) (digitChar (primIntRem n 10) : acc)

digitChar :: IntPrim -> Char
digitChar n = C (primChr (primIntAdd n 48))

-- --------------------------------------------- Integer, Int64 and Word64 ---
--
-- GHC's \`Integer\` is \`ghc-bignum\`'s \`IS Int# | IP BigNat# | IN BigNat#\` over
-- the \`h$ghcbn_*\` primitives, and \`Int64\`/\`Word64\` are \`I64# Int64#\`/
-- \`W64# Word64#\` over a two-slot unboxed value. Both carriers live in the
-- backend. What is reachable from the frontend alone is a \`foreign import\`,
-- and the platform already has an exact integer of unbounded width: a JS
-- \`BigInt\`. So the box holds one, exactly as \`data ByteString = ByteString
-- JSValPrim\` holds a real \`Uint8Array\`.
--
-- That is honest by the test \`Data.ByteString\` states: a \`BigInt\` can hold
-- every value an \`Integer\` can, which is what \`Int64\` aliased to \`Int\` could
-- never have said. \`Int64\` and \`Word64\` ride the same carrier and differ only
-- in the wrap applied after every operation - \`BigInt.asIntN\` / \`asUintN\` at
-- 64 bits - which is what makes them wrap at their own width rather than grow.
--
-- They are declared here, and not in \`Data.Int\`/\`Data.Word\`, because
-- \`Fingerprint\` is two \`Word64\` halves and \`Fingerprint\` is wired in: \`static\`
-- is a keyword form that needs no import (see StaticPtr, below).
data Integer = Integer JSValPrim
data Int64 = I64 JSValPrim
data Word64 = W64 JSValPrim

foreign import javascript unsafe "((n) => BigInt(n))" primIntegerFromInt :: IntPrim -> JSValPrim
-- GHC's \`integerToInt#\` keeps the low bits of a machine word, and the machine
-- word on this backend is 32 bits wide (see \`Literal\` in src/stg.ts).
foreign import javascript unsafe "((b) => Number(BigInt.asIntN(32, b)))" primIntegerToInt :: JSValPrim -> IntPrim
-- \`Math.trunc\` first: \`BigInt\` refuses a Number with a fractional part
-- outright, where \`truncate\`/\`round\` have already decided which whole number
-- they mean.
foreign import javascript unsafe "((d) => BigInt(Math.trunc(d)))" primIntegerFromDouble :: DoublePrim -> JSValPrim
foreign import javascript unsafe "((b) => Number(b))" primIntegerToDouble :: JSValPrim -> DoublePrim
foreign import javascript unsafe "((a,b) => a + b)" primBigIntAdd :: JSValPrim -> JSValPrim -> JSValPrim
foreign import javascript unsafe "((a,b) => a - b)" primBigIntSub :: JSValPrim -> JSValPrim -> JSValPrim
foreign import javascript unsafe "((a,b) => a * b)" primBigIntMul :: JSValPrim -> JSValPrim -> JSValPrim
foreign import javascript unsafe "((b) => -b)" primBigIntNeg :: JSValPrim -> JSValPrim
foreign import javascript unsafe "((a,b) => a === b)" primBigIntEq :: JSValPrim -> JSValPrim -> Bool
foreign import javascript unsafe "((a,b) => a < b)" primBigIntLt :: JSValPrim -> JSValPrim -> Bool
foreign import javascript unsafe "((a,b) => a <= b)" primBigIntLe :: JSValPrim -> JSValPrim -> Bool
foreign import javascript unsafe "((a,b) => a > b)" primBigIntGt :: JSValPrim -> JSValPrim -> Bool
foreign import javascript unsafe "((a,b) => a >= b)" primBigIntGe :: JSValPrim -> JSValPrim -> Bool
foreign import javascript unsafe "((b) => b < 0n)" primBigIntIsNeg :: JSValPrim -> Bool
foreign import javascript unsafe "((b) => b.toString())" primBigIntShow :: JSValPrim -> JSStringPrim
foreign import javascript unsafe "((b) => BigInt.asIntN(64, b))" primNarrow64 :: JSValPrim -> JSValPrim
foreign import javascript unsafe "((b) => BigInt.asUintN(64, b))" primMask64 :: JSValPrim -> JSValPrim

-- What \`src/desugar.ts\` wraps a machine literal in when the \`fromInteger\` it
-- feeds is not one of the shapes \`overloadedLit\` short-cuts.
integerFromIntPrim :: IntPrim -> Integer
integerFromIntPrim n = Integer (primIntegerFromInt n)

integerFromDoublePrim :: DoublePrim -> Integer
integerFromDoublePrim d = Integer (primIntegerFromDouble d)

instance Eq Integer where
  (==) (Integer a) (Integer b) = primBigIntEq a b

instance Ord Integer where
  (<) (Integer a) (Integer b) = primBigIntLt a b
  (<=) (Integer a) (Integer b) = primBigIntLe a b
  (>) (Integer a) (Integer b) = primBigIntGt a b
  (>=) (Integer a) (Integer b) = primBigIntGe a b

instance Num Integer where
  (+) (Integer a) (Integer b) = Integer (primBigIntAdd a b)
  (-) (Integer a) (Integer b) = Integer (primBigIntSub a b)
  (*) (Integer a) (Integer b) = Integer (primBigIntMul a b)
  negate (Integer a) = Integer (primBigIntNeg a)
  fromInteger n = n

instance Real Integer where
  toDoublePrim (Integer b) = primIntegerToDouble b

instance Integral Integer where
  toInteger n = n

instance Show Integer where
  showsPrec d (Integer b) s = showsBigInt d b s

-- A negative number is parenthesised at any precedence above 6, exactly as
-- \`showSignedInt\` does it for \`Int\`.
showsBigInt :: Int -> JSValPrim -> [Char] -> [Char]
showsBigInt d b s =
  if primBigIntIsNeg b && d > 6 then '(' : jsAscii (primBigIntShow b) ++ (')' : s) else jsAscii (primBigIntShow b) ++ s

instance Eq Int64 where
  (==) (I64 a) (I64 b) = primBigIntEq a b

instance Ord Int64 where
  (<) (I64 a) (I64 b) = primBigIntLt a b
  (<=) (I64 a) (I64 b) = primBigIntLe a b
  (>) (I64 a) (I64 b) = primBigIntGt a b
  (>=) (I64 a) (I64 b) = primBigIntGe a b

instance Num Int64 where
  (+) (I64 a) (I64 b) = I64 (primNarrow64 (primBigIntAdd a b))
  (-) (I64 a) (I64 b) = I64 (primNarrow64 (primBigIntSub a b))
  (*) (I64 a) (I64 b) = I64 (primNarrow64 (primBigIntMul a b))
  negate (I64 a) = I64 (primNarrow64 (primBigIntNeg a))
  fromInteger (Integer b) = I64 (primNarrow64 b)

instance Real Int64 where
  toDoublePrim (I64 b) = primIntegerToDouble b

instance Integral Int64 where
  toInteger (I64 b) = Integer b

instance Show Int64 where
  showsPrec d (I64 b) s = showsBigInt d b s

instance Eq Word64 where
  (==) (W64 a) (W64 b) = primBigIntEq a b

instance Ord Word64 where
  (<) (W64 a) (W64 b) = primBigIntLt a b
  (<=) (W64 a) (W64 b) = primBigIntLe a b
  (>) (W64 a) (W64 b) = primBigIntGt a b
  (>=) (W64 a) (W64 b) = primBigIntGe a b

instance Num Word64 where
  (+) (W64 a) (W64 b) = W64 (primMask64 (primBigIntAdd a b))
  (-) (W64 a) (W64 b) = W64 (primMask64 (primBigIntSub a b))
  (*) (W64 a) (W64 b) = W64 (primMask64 (primBigIntMul a b))
  negate (W64 a) = W64 (primMask64 (primBigIntNeg a))
  fromInteger (Integer b) = W64 (primMask64 b)

instance Real Word64 where
  toDoublePrim (W64 b) = primIntegerToDouble b

instance Integral Word64 where
  toInteger (W64 b) = Integer b

-- A \`Word64\` is masked to [0, 2^64), so it never prints a sign and never needs
-- the parentheses \`Int64\` does.
instance Show Word64 where
  showsPrec d (W64 b) s = jsAscii (primBigIntShow b) ++ s

-- ---------------------------------------------------------------- numeric ---

-- GHC's own definition, method for method. The \`Integer\` in the middle is a
-- lifted box, so nothing here has to force it into place - unlike the machine
-- value this used to pass, which could not be a lazy constructor field.
fromIntegral :: (Integral a, Num b) => a -> b
fromIntegral x = fromInteger (toInteger x)

realToFrac :: (Real a, Fractional b) => a -> b
realToFrac x = case toDoublePrim x of
  d -> fromRational d

-- Every function below produces an \`Integer\`, so each one stays on
-- \`DoublePrim\` for the whole rounding decision and converts once at the end.
-- Truncating through \`IntPrim\` on the way - which is what these did while
-- \`fromInteger\` took a machine int - throws away every value a \`Double\` holds
-- exactly but a 32-bit \`Int\` cannot, and \`fromInteger . round\` at \`Int64\`,
-- \`Word64\` and \`Integer\` is exactly the code that asks for those.
foreign import javascript unsafe "((d) => Math.trunc(d))" primDoubleTrunc :: DoublePrim -> DoublePrim
foreign import javascript unsafe "((d) => Math.floor(d))" primDoubleFloor :: DoublePrim -> DoublePrim
foreign import javascript unsafe "((d) => Math.ceil(d))" primDoubleCeil :: DoublePrim -> DoublePrim
foreign import javascript unsafe "((a,b) => a % b)" primDoubleRem :: DoublePrim -> DoublePrim -> DoublePrim

-- GHC's \`round\` is round-half-to-EVEN, not round-half-up; getting that wrong
-- would be a silent one-pixel error rather than a crash, so it is spelled out.
--
-- The inner \`case\` is load-bearing: \`roundPrim\` is a Haskell function, so its
-- result in an argument position would be a THUNK, and \`integerFromDoublePrim\`
-- takes a machine double. \`floor\`/\`ceiling\`/\`truncate\` below need no such
-- \`case\` because what they pass is a primitive call, which the STG pass
-- evaluates where it stands.
round :: (RealFrac a, Num b) => a -> b
round x = case fracToDoublePrim x of
  d -> case roundPrim d of
    n -> fromInteger (integerFromDoublePrim n)

roundPrim :: DoublePrim -> DoublePrim
roundPrim d = roundHalf (primDoubleTrunc d) (primDoubleSub d (primDoubleTrunc d))

-- \`n\` is \`d\` truncated towards zero and \`r\` is the signed remainder, so
-- |r| < 1 and the only decisions left are the two halfway cases.
roundHalf :: DoublePrim -> DoublePrim -> DoublePrim
roundHalf n r = if primDoubleLt r (primDoubleNeg 0.5) then primDoubleSub n 1.0 else roundHalfUp n r

roundHalfUp :: DoublePrim -> DoublePrim -> DoublePrim
roundHalfUp n r = if primDoubleGt r 0.5 then primDoubleAdd n 1.0 else roundHalfTie n r

roundHalfTie :: DoublePrim -> DoublePrim -> DoublePrim
roundHalfTie n r = if primDoubleEq r 0.5 then evenOr n (primDoubleAdd n 1.0) else roundHalfTieDown n r

roundHalfTieDown :: DoublePrim -> DoublePrim -> DoublePrim
roundHalfTieDown n r = if primDoubleEq r (primDoubleNeg 0.5) then evenOr n (primDoubleSub n 1.0) else n

evenOr :: DoublePrim -> DoublePrim -> DoublePrim
evenOr n alternative = if primDoubleEq (primDoubleRem n 2.0) 0.0 then n else alternative

-- \\\`properFraction x\\\` is \\\`(truncate x, x - fromIntegral (truncate x))\\\`: the
-- integer part towards zero and the *signed* remainder, so the two add back to
-- \\\`x\\\` for a negative argument as well.
properFraction :: (RealFrac a, Num b) => a -> (b, a)
properFraction x = case fracToDoublePrim x of
  d -> case primDoubleTrunc d of
    n -> (fromInteger (integerFromDoublePrim n), fromRational (primDoubleSub d n))

truncate :: (RealFrac a, Num b) => a -> b
truncate x = case fracToDoublePrim x of
  d -> fromInteger (integerFromDoublePrim (primDoubleTrunc d))

floor :: (RealFrac a, Num b) => a -> b
floor x = case fracToDoublePrim x of
  d -> fromInteger (integerFromDoublePrim (primDoubleFloor d))

ceiling :: (RealFrac a, Num b) => a -> b
ceiling x = case fracToDoublePrim x of
  d -> fromInteger (integerFromDoublePrim (primDoubleCeil d))

sqrt :: Double -> Double
sqrt (DoubleBox d) = DoubleBox (primDoubleSqrt d)

abs :: Double -> Double
abs (DoubleBox d) = DoubleBox (primDoubleAbs d)

compareChar :: Char -> Char -> Ordering
compareChar (C a) (C b) = if primCharEq a b then EQ else (if primCharLt a b then LT else GT)

ord :: Char -> Int
ord (C c) = I (primCharOrd c)

chr :: Int -> Char
chr (I n) = C (primChr n)

-- \`compare\`, not just \`(<)\`: the class defaults define \`compare\` from
-- \`(<=)\` and \`(<=)\` from \`compare\`, so an instance that gives neither is an
-- infinite loop rather than a missing method.
instance Ord Char where
  compare a b = compareChar a b

-- ------------------------------------------------------- Maybe and Either --

maybe :: b -> (a -> b) -> Maybe a -> b
maybe d f m = case m of
  Nothing -> d
  Just x -> f x

fromMaybe :: a -> Maybe a -> a
fromMaybe d m = case m of
  Nothing -> d
  Just x -> x

isJust :: Maybe a -> Bool
isJust m = case m of
  Nothing -> False
  Just x -> True

isNothing :: Maybe a -> Bool
isNothing m = not (isJust m)

fromJust :: Maybe a -> a
fromJust m = case m of
  Nothing -> error "Maybe.fromJust: Nothing"
  Just x -> x

listToMaybe :: [a] -> Maybe a
listToMaybe xs = case xs of
  [] -> Nothing
  (y : ys) -> Just y

maybeToList :: Maybe a -> [a]
maybeToList m = case m of
  Nothing -> []
  Just x -> x : []

catMaybes :: [Maybe a] -> [a]
catMaybes xs = case xs of
  [] -> []
  (y : ys) -> case y of
    Nothing -> catMaybes ys
    Just v -> v : catMaybes ys

mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe f xs = catMaybes (map f xs)

either :: (a -> c) -> (b -> c) -> Either a b -> c
either f g e = case e of
  Left x -> f x
  Right y -> g y

isLeft :: Either a b -> Bool
isLeft e = case e of
  Left x -> True
  Right y -> False

isRight :: Either a b -> Bool
isRight e = not (isLeft e)

fromLeft :: a -> Either a b -> a
fromLeft d e = case e of
  Left x -> x
  Right y -> d

fromRight :: b -> Either a b -> b
fromRight d e = case e of
  Left x -> d
  Right y -> y

eqMaybe :: (a -> a -> Bool) -> Maybe a -> Maybe a -> Bool
eqMaybe eq p q = case p of
  Nothing -> case q of
    Nothing -> True
    Just y -> False
  Just x -> case q of
    Nothing -> False
    Just y -> eq x y

eqEither :: (a -> a -> Bool) -> (b -> b -> Bool) -> Either a b -> Either a b -> Bool
eqEither f g p q = case p of
  Left x -> case q of
    Left u -> f x u
    Right v -> False
  Right y -> case q of
    Left u -> False
    Right v -> g y v

-- Lexicographic, as GHC's is: the first difference decides, and a prefix is
-- less than what it is a prefix of.
compareList :: (a -> a -> Ordering) -> [a] -> [a] -> Ordering
compareList cmp xs ys = case xs of
  [] -> if nullList ys then EQ else LT
  (a : as) -> case ys of
    [] -> GT
    (b : bs) -> if eqOrdering (cmp a b) EQ then compareList cmp as bs else cmp a b

compareMaybe :: (a -> a -> Ordering) -> Maybe a -> Maybe a -> Ordering
compareMaybe cmp p q = case p of
  Nothing -> case q of
    Nothing -> EQ
    Just y -> LT
  Just x -> case q of
    Nothing -> GT
    Just y -> cmp x y

eqPair :: (a -> a -> Bool) -> (b -> b -> Bool) -> (a, b) -> (a, b) -> Bool
eqPair f g p q = case p of
  (x, y) -> case q of
    (u, v) -> if f x u then g y v else False

maybeMap :: (a -> b) -> Maybe a -> Maybe b
maybeMap f m = case m of
  Nothing -> Nothing
  Just x -> Just (f x)

maybeAp :: Maybe (a -> b) -> Maybe a -> Maybe b
maybeAp f m = case f of
  Nothing -> Nothing
  Just g -> maybeMap g m

maybeBind :: Maybe a -> (a -> Maybe b) -> Maybe b
maybeBind m k = case m of
  Nothing -> Nothing
  Just x -> k x

maybeOr :: Maybe a -> Maybe a -> Maybe a
maybeOr a b = case a of
  Nothing -> b
  Just x -> a

maybeFoldr :: (a -> b -> b) -> b -> Maybe a -> b
maybeFoldr f z m = case m of
  Nothing -> z
  Just x -> f x z

maybeAppend :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
maybeAppend op a b = case a of
  Nothing -> b
  Just x -> case b of
    Nothing -> a
    Just y -> Just (op x y)

eitherMap :: (a -> b) -> Either e a -> Either e b
eitherMap f m = case m of
  Left e -> Left e
  Right x -> Right (f x)

eitherAp :: Either e (a -> b) -> Either e a -> Either e b
eitherAp f m = case f of
  Left e -> Left e
  Right g -> eitherMap g m

eitherBind :: Either e a -> (a -> Either e b) -> Either e b
eitherBind m k = case m of
  Left e -> Left e
  Right x -> k x

eitherFoldr :: (a -> b -> b) -> b -> Either e a -> b
eitherFoldr f z m = case m of
  Left e -> z
  Right x -> f x z

-- ------------------------------------------------------------------ lists --

append :: [a] -> [a] -> [a]
append xs ys = case xs of
  [] -> ys
  (z : zs) -> z : append zs ys

nullList :: [a] -> Bool
nullList xs = case xs of
  [] -> True
  (a : as) -> False

eqList :: (a -> a -> Bool) -> [a] -> [a] -> Bool
eqList eq xs ys = case xs of
  [] -> nullList ys
  (a : as) -> case ys of
    [] -> False
    (b : bs) -> if eq a b then eqList eq as bs else False

foldrList :: (a -> b -> b) -> b -> [a] -> b
foldrList f z xs = case xs of
  [] -> z
  (y : ys) -> f y (foldrList f z ys)

map :: (a -> b) -> [a] -> [b]
map f xs = case xs of
  [] -> []
  (y : ys) -> f y : map f ys

filter :: (a -> Bool) -> [a] -> [a]
filter p xs = case xs of
  [] -> []
  (y : ys) -> if p y then y : filter p ys else filter p ys

head :: [a] -> a
head xs = case xs of
  [] -> error "Prelude.head: empty list"
  (y : ys) -> y

tail :: [a] -> [a]
tail xs = case xs of
  [] -> error "Prelude.tail: empty list"
  (y : ys) -> ys

last :: [a] -> a
last xs = case xs of
  [] -> error "Prelude.last: empty list"
  (y : ys) -> if nullList ys then y else last ys

reverse :: [a] -> [a]
reverse xs = reverseOnto xs []

reverseOnto :: [a] -> [a] -> [a]
reverseOnto xs acc = case xs of
  [] -> acc
  (y : ys) -> reverseOnto ys (y : acc)

take :: Int -> [a] -> [a]
take n xs = case xs of
  [] -> []
  (y : ys) -> if n <= 0 then [] else y : take (n - 1) ys

drop :: Int -> [a] -> [a]
drop n xs = case xs of
  [] -> []
  (y : ys) -> if n <= 0 then xs else drop (n - 1) ys

splitAt :: Int -> [a] -> ([a], [a])
splitAt n xs = (take n xs, drop n xs)

-- These are Prelude names in Haskell, not \`Data.List\` ones: a module that
-- imports neither still has them.
takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile p xs = case xs of
  [] -> []
  (y : ys) -> if p y then y : takeWhile p ys else []

dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile p xs = case xs of
  [] -> []
  (y : ys) -> if p y then dropWhile p ys else xs

span :: (a -> Bool) -> [a] -> ([a], [a])
span p xs = (takeWhile p xs, dropWhile p xs)

break :: (a -> Bool) -> [a] -> ([a], [a])
break p xs = span (\\x -> not (p x)) xs

subtract :: Num a => a -> a -> a
subtract x y = y - x

-- \`x /= x\` is true of NaN and of nothing else, and \`==\` on a \`Double\` is
-- JavaScript's \`===\`, which agrees.
isNaN :: Double -> Bool
isNaN x = not (x == x)

zip :: [a] -> [b] -> [(a, b)]
zip xs ys = zipWith (\\x y -> (x, y)) xs ys

zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith f xs ys = case xs of
  [] -> []
  (a : as) -> case ys of
    [] -> []
    (b : bs) -> f a b : zipWith f as bs

lookup :: Eq a => a -> [(a, b)] -> Maybe b
lookup k xs = case xs of
  [] -> Nothing
  (p : ps) -> case p of
    (a, b) -> if k == a then Just b else lookup k ps

replicate :: Int -> a -> [a]
replicate n x = if n <= 0 then [] else x : replicate (n - 1) x

listAp :: [a -> b] -> [a] -> [b]
listAp fs xs = concatMap (\\f -> map f xs) fs

-- ----------------------------------------------------------- folds ---------

null :: Foldable t => t a -> Bool
null xs = foldr (\\x b -> False) True xs

length :: Foldable t => t a -> Int
length xs = foldr (\\x n -> n + 1) 0 xs

elem :: (Foldable t, Eq a) => a -> t a -> Bool
elem x xs = foldr (\\y b -> if x == y then True else b) False xs

notElem :: (Foldable t, Eq a) => a -> t a -> Bool
notElem x xs = not (elem x xs)

sum :: (Foldable t, Num a) => t a -> a
sum xs = foldr (\\x acc -> x + acc) 0 xs

product :: (Foldable t, Num a) => t a -> a
product xs = foldr (\\x acc -> x * acc) 1 xs

any :: Foldable t => (a -> Bool) -> t a -> Bool
any p xs = foldr (\\x b -> if p x then True else b) False xs

all :: Foldable t => (a -> Bool) -> t a -> Bool
all p xs = foldr (\\x b -> if p x then b else False) True xs

and :: Foldable t => t Bool -> Bool
and xs = all id xs

or :: Foldable t => t Bool -> Bool
or xs = any id xs

concat :: Foldable t => t [a] -> [a]
concat xs = foldr append [] xs

concatMap :: Foldable t => (a -> [b]) -> t a -> [b]
concatMap f xs = foldr (\\x acc -> append (f x) acc) [] xs

foldl :: Foldable t => (b -> a -> b) -> b -> t a -> b
foldl f z xs = foldlList f z (toList xs)

foldlList :: (b -> a -> b) -> b -> [a] -> b
foldlList f z xs = case xs of
  [] -> z
  (y : ys) -> foldlList f (f z y) ys

fold :: (Foldable t, Monoid m) => t m -> m
fold xs = foldr mappend mempty xs

foldMapList :: Monoid m => (a -> m) -> [a] -> m
foldMapList f xs = foldr (\\x acc -> mappend (f x) acc) mempty xs

-- \`foldMap\` cannot be a \`Foldable\` method here (a method's signature carries
-- no constraint of its own), but it is the same function written outside the
-- class, which is where every other fold already lives.
foldMap :: (Foldable t, Monoid m) => (a -> m) -> t a -> m
foldMap f xs = foldr (\\x acc -> mappend (f x) acc) mempty xs

foldl' :: Foldable t => (b -> a -> b) -> b -> t a -> b
foldl' f z xs = foldlStrict f z (toList xs)

foldlStrict :: (b -> a -> b) -> b -> [a] -> b
foldlStrict f z xs = case xs of
  [] -> z
  (y : ys) -> case f z y of
    next -> seq next (foldlStrict f next ys)

-- ------------------------------------------------- Functor/Monad utilities --

(<$>) :: Functor f => (a -> b) -> f a -> f b
(<$>) f m = fmap f m

(<&>) :: Functor f => f a -> (a -> b) -> f b
(<&>) m f = fmap f m

void :: Functor f => f a -> f ()
void m = fmap (\\x -> ()) m

(=<<) :: Monad m => (a -> m b) -> m a -> m b
(=<<) k m = m >>= k

(>=>) :: Monad m => (a -> m b) -> (b -> m c) -> a -> m c
(>=>) f g x = f x >>= g

(<=<) :: Monad m => (b -> m c) -> (a -> m b) -> a -> m c
(<=<) g f x = f x >>= g

join :: Monad m => m (m a) -> m a
join m = m >>= id

when :: Applicative f => Bool -> f () -> f ()
when c m = if c then m else pure ()

unless :: Applicative f => Bool -> f () -> f ()
unless c m = if c then pure () else m

forever :: Monad m => m a -> m b
forever m = m >> forever m

guard :: Alternative f => Bool -> f ()
guard b = if b then pure () else empty

optional :: Alternative f => f a -> f (Maybe a)
optional v = fmap (\\x -> Just x) v <|> pure Nothing

someOrNone :: Alternative f => f a -> f [a]
someOrNone v = some v <|> pure []

ap :: Monad m => m (a -> b) -> m a -> m b
ap mf mx = mf >>= (\\f -> mx >>= (\\x -> pure (f x)))

liftM :: Monad m => (a -> b) -> m a -> m b
liftM f ma = ma >>= (\\a -> pure (f a))

liftM2 :: Monad m => (a -> b -> c) -> m a -> m b -> m c
liftM2 f ma mb = ma >>= (\\a -> mb >>= (\\b -> pure (f a b)))

liftM3 :: Monad m => (a -> b -> c -> d) -> m a -> m b -> m c -> m d
liftM3 f ma mb mc = ma >>= (\\a -> mb >>= (\\b -> mc >>= (\\c -> pure (f a b c))))

liftM4 :: Monad m => (a -> b -> c -> d -> e) -> m a -> m b -> m c -> m d -> m e
liftM4 f ma mb mc md = ma >>= (\\a -> mb >>= (\\b -> mc >>= (\\c -> md >>= (\\d -> pure (f a b c d)))))

msum :: (Foldable t, Alternative f) => t (f a) -> f a
msum xs = foldr (\\x rest -> x <|> rest) empty xs

asum :: (Foldable t, Alternative f) => t (f a) -> f a
asum xs = msum xs

mapM_ :: (Foldable t, Monad m) => (a -> m b) -> t a -> m ()
mapM_ f xs = foldr (\\x k -> f x >> k) (pure ()) xs

forM_ :: (Foldable t, Monad m) => t a -> (a -> m b) -> m ()
forM_ xs f = mapM_ f xs

sequence_ :: (Foldable t, Monad m) => t (m a) -> m ()
sequence_ xs = foldr (\\m k -> m >> k) (pure ()) xs

traverse_ :: (Foldable t, Monad m) => (a -> m b) -> t a -> m ()
traverse_ f xs = mapM_ f xs

traverseList :: Applicative f => (a -> f b) -> [a] -> f [b]
traverseList f xs = case xs of
  [] -> pure []
  (y : ys) -> liftA2 (\\r rs -> r : rs) (f y) (traverseList f ys)

forM :: (Traversable t, Monad m) => t a -> (a -> m b) -> m (t b)
forM xs f = mapM f xs

replicateM :: Monad m => Int -> m a -> m [a]
replicateM n m = if n <= 0 then pure [] else m >>= (\\x -> replicateM (n - 1) m >>= (\\xs -> pure (x : xs)))

replicateM_ :: Monad m => Int -> m a -> m ()
replicateM_ n m = if n <= 0 then pure () else m >> replicateM_ (n - 1) m

foldM :: Monad m => (b -> a -> m b) -> b -> [a] -> m b
foldM f z xs = case xs of
  [] -> pure z
  (y : ys) -> f z y >>= (\\acc -> foldM f acc ys)

foldM_ :: Monad m => (b -> a -> m b) -> b -> [a] -> m ()
foldM_ f z xs = void (foldM f z xs)

zipWithM :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithM f xs ys = sequence (zipWith f xs ys)

zipWithM_ :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m ()
zipWithM_ f xs ys = sequence_ (zipWith f xs ys)

-- ------------------------------------------------------------- StaticPtr ---
--
-- \`StaticPtr\` is wired in, exactly as it is in GHC: \`GHC.Tc.Gen.Expr\` and
-- \`GHC.HsToCore.Expr\` look the type constructor up by known key, because
-- \`static e\` is a *keyword form* that a module need not have imported anything
-- to write. \`GHC.StaticPtr\` (src/library.ts) is the module that re-exports
-- what is declared here. \`src/parser.ts\` floats each \`static e\` into its own
-- top-level binding and fills in the fingerprint.
--
-- GHC's key is \`Fingerprint Word64 Word64\`, and so is this one now that
-- \`Word64\` exists. The static pointer table's own interface is still four
-- 32-bit words - \`h$hs_spt_insert(k1,k2,k3,k4,ref)\` - so each half is split at
-- the call, in the order GHC's \`StgToJS.StaticPtr\` passes them: high then low.
data Fingerprint = Fingerprint Word64 Word64
type StaticKey = Fingerprint
data StaticPtr a = StaticPtr StaticKey a

-- What \`src/parser.ts\` builds each \`static\` form's key out of: the two halves
-- of one \`Word64\`, as \`md5\` hands them over.
word64FromHalves :: IntPrim -> IntPrim -> Word64
word64FromHalves hi lo = W64 (primWord64FromHalves hi lo)

foreign import javascript unsafe "((hi,lo) => (BigInt(hi >>> 0) << 32n) | BigInt(lo >>> 0))" primWord64FromHalves :: IntPrim -> IntPrim -> JSValPrim
-- Unsigned, because that is what \`h$hs_spt_insert\` was given when the key was
-- four \`Int\`s and what the table's keys are still compared as.
foreign import javascript unsafe "((b) => Number(BigInt.asUintN(32, b >> 32n)))" primWord64Hi :: JSValPrim -> IntPrim
foreign import javascript unsafe "((b) => Number(BigInt.asUintN(32, b)))" primWord64Lo :: JSValPrim -> IntPrim
foreign import javascript unsafe "((b) => b.toString(16).padStart(16, '0'))" primWord64Hex :: JSValPrim -> JSStringPrim

deRefStaticPtr :: StaticPtr a -> a
deRefStaticPtr p = case p of
  StaticPtr k v -> v

staticKey :: StaticPtr a -> StaticKey
staticKey p = case p of
  StaticPtr k v -> k

instance Eq Fingerprint where
  (==) a b = eqFingerprint a b

eqFingerprint :: Fingerprint -> Fingerprint -> Bool
eqFingerprint (Fingerprint a b) (Fingerprint w x) = a == w && b == x

-- GHC's \`Show Fingerprint\` is the two \`Word64\` halves as sixteen zero-padded
-- hex digits each.
instance Show Fingerprint where
  show k = showFingerprint k

showFingerprint :: Fingerprint -> [Char]
showFingerprint (Fingerprint a b) = hex16 a ++ hex16 b

hex16 :: Word64 -> [Char]
hex16 (W64 b) = jsAscii (primWord64Hex b)

-- The static pointer table is the RTS's (rts/js/staticpointer.js), not a
-- Haskell \`Map\`: \`unsafeLookupStaticPtr\` has to find an entry that a *different*
-- JS context registered, and the table is the only thing both contexts share.
foreign import javascript unsafe "((a,b,c,d,p) => { h$hs_spt_insert(a,b,c,d,p); return 0; })" primSptInsert :: IntPrim -> IntPrim -> IntPrim -> IntPrim -> a -> IntPrim
foreign import javascript unsafe "((a,b,c,d) => (h$hs_spt_lookup_key(a,b,c,d) === null ? 0 : 1))" primSptHas :: IntPrim -> IntPrim -> IntPrim -> IntPrim -> IntPrim
foreign import javascript unsafe "((a,b,c,d) => h$hs_spt_lookup_key(a,b,c,d))" primSptGet :: IntPrim -> IntPrim -> IntPrim -> IntPrim -> a

-- The entry itself is what goes in the table, so that \`unsafeLookupStaticPtr\`
-- returns the same \`StaticPtr\` \`static e\` denotes. Forcing it to weak head
-- normal form here allocates nothing extra and does not touch \`e\`: the payload
-- is a lazy constructor field, as GHC's is.
sptRegister :: StaticPtr a -> IO ()
sptRegister p = IO (\\s -> sptRegisterStep s p)

sptRegisterStep :: RealWorld -> StaticPtr a -> IOResult ()
sptRegisterStep s p = case p of
  StaticPtr k v -> case k of
    Fingerprint (W64 a) (W64 b) ->
      case primSptInsert (primWord64Hi a) (primWord64Lo a) (primWord64Hi b) (primWord64Lo b) p of
        _ -> IOResult s ()

-- What \`src/elaborate.ts\` puts in front of \`main\`. It is a plain function and
-- not \`sptRegister p >> m\` because it is built after elaboration, where \`>>\`
-- has no dictionary to be applied to.
sptRegisterThen :: StaticPtr a -> IO b -> IO b
sptRegisterThen p m = IO (\\s -> sptRegisterThenStep s p m)

sptRegisterThenStep :: RealWorld -> StaticPtr a -> IO b -> IOResult b
sptRegisterThenStep s p m = case sptRegisterStep s p of
  IOResult t u -> unIO m t

unsafeLookupStaticPtr :: StaticKey -> IO (Maybe (StaticPtr a))
unsafeLookupStaticPtr k = case k of
  Fingerprint (W64 x) (W64 y) ->
    sptLookup (primWord64Hi x) (primWord64Lo x) (primWord64Hi y) (primWord64Lo y)

sptLookup :: IntPrim -> IntPrim -> IntPrim -> IntPrim -> IO (Maybe (StaticPtr a))
sptLookup a b c d = if primIntEq (primSptHas a b c d) 0 then pure Nothing else sptFetch a b c d

-- Split from the test above because the miss returns \`null\`, and \`null\` in a
-- position something may enter is not a value - it is the crash one step later.
sptFetch :: IntPrim -> IntPrim -> IntPrim -> IntPrim -> IO (Maybe (StaticPtr a))
sptFetch a b c d = case primSptGet a b c d of
  p -> pure (Just p)
`;
