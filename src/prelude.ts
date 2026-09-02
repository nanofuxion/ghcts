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
-- A newtype, as GHC's is: \`src/erase-newtypes.ts\` makes the constructor a
-- coercion, so an \`IO\` action IS its state function and a bind allocates no
-- box around it.
newtype IO a = IO (RealWorld -> IOResult a)

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
  quotRem :: a -> a -> (a, a)
  divMod :: a -> a -> (a, a)
  quot :: a -> a -> a
  rem :: a -> a -> a
  div :: a -> a -> a
  mod :: a -> a -> a
  quot n d = fst (quotRem n d)
  rem n d = snd (quotRem n d)
  div n d = fst (divMod n d)
  mod n d = snd (divMod n d)
  divMod n d = divModOfQuotRem (quotRem n d) d

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
  -- \`compare\` is given directly rather than left to the class default. The
  -- default is \`if x <= y then (if y <= x then EQ else LT) else GT\`: two
  -- dictionary-dispatched \`<=\` calls, where this is two primitive comparisons
  -- and no dispatch at all. Every ordered container keyed on \`Int\` goes
  -- through here once per node, so the default costs more than the whole rest
  -- of the traversal. containers' own \`Data.Map\` relies on \`compare\` being
  -- the cheap operation for exactly this reason.
  compare (I a) (I b) = if primIntLt a b then LT else (if primIntEq a b then EQ else GT)
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
  fromInteger n = case integerToIntPrim n of m -> I m

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
  toInteger (I n) = integerFromIntPrim n
  -- \`primIntQuot\` is \`(a/b)|0\`, which is JavaScript's 0 on a zero divisor
  -- rather than an exception; GHC raises one, and so does this.
  quotRem (I a) (I b) = if primIntEq b 0 then error "divide by zero" else (I (primIntQuot a b), I (primIntRem a b))

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
  fromInteger n = case integerToDoublePrim n of d -> DoubleBox d

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
  fromInteger n = FloatBox (primDoubleToFloat (integerToDoublePrim n))

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

instance Enum Char where
  toEnum = chr
  fromEnum = ord

instance Eq Bool where
  (==) a b = eqBool a b

instance Show Bool where
  show b = showBool b

-- Declaration order, like every other stock-derived 'Ord': 'False' < 'True'.
instance Ord Bool where
  compare False False = EQ
  compare False True  = LT
  compare True  False = GT
  compare True  True  = EQ

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
-- The real message was previously discarded (\`throw new Error('Prelude.error')\`
-- unconditionally) - every \`error "..."\` call in any ghcts program showed the
-- same useless text. Walks the \`[Char]\` cons-list by hand instead of going
-- through GHC.Types.[]/(:)'s own constructor-entry symbols
-- (h\$ghczmprimZCGHCziTypesziZC_con_e / ...ZMZN) - those are never generated
-- by this pipeline for any program (a separate, deeper elaboration gap), so
-- referencing them here would just trade one ReferenceError for another.
-- \`.d1\`/\`.d2\` duck-typing is safe specifically because the argument's type is
-- \`[Char]\`: the only two shapes a value can take there are \`:\` (two fields)
-- and \`[]\` (no \`d2\`), so nothing else can be mistaken for a cons cell here.
--
-- \`errorPrim\` walks the closure's fields directly instead of entering each
-- thunk (no forcing primitive is exposed to a bare \`foreign import javascript\`
-- body here), so its argument must already be in WHNF spine-and-leaves *all
-- the way to the end* before it gets there - JS never forces anything itself,
-- it just reads whatever fields already happen to be there.
--
-- A version built as \`c \`seq\` (c : forceErrorString cs)\` does NOT give that:
-- returning a lazy \`:\` whose tail is an unforced recursive-call thunk forces
-- only the *head* eagerly, and nothing downstream ever demands the rest - the
-- foreign call reads \`$1\` as a whole unforced argument thunk (an ordinary
-- Haskell function's arguments are passed lazily), so \`errorPrim\` walks off
-- into thunk closures partway down the spine and its \`typeof cp !== 'number'\`
-- check quietly stops there (an \`error\` message longer than the first couple
-- of characters that happened to already be forced showed only those, e.g.
-- \`"GHCTS-DICT: ..."\` came out as just \`"GH"\`).
--
-- The fix walks the *entire* spine and every character's code point in one
-- strict pass (\`go\`), only returning \`s\` once that whole walk is done: \`go s
-- \`seq\` s\` forces \`go s\` to WHNF first, and \`go\`'s every recursive call is
-- itself directly \`seq\`-forced rather than lazily returned, so the walk
-- can't stop until it reaches \`[]\`. Only *then* is the (now fully-forced,
-- unchanged) original list hand to \`errorPrim\`.
forceErrorString :: [Char] -> [Char]
forceErrorString s = go s \`seq\` s
  where
    go [] = ()
    go (c:cs) = fromEnum c \`seq\` go cs

foreign import javascript unsafe "(($1) => { let msg = ''; try { let xs = $1; while (xs && xs.d2 !== undefined) { const h = xs.d1; const cp = typeof h === 'number' ? h : (h && h.d1); if (typeof cp !== 'number') break; msg += String.fromCodePoint(cp); xs = xs.d2; } } catch (e) {} throw new Error(msg || 'Prelude.error'); })" errorPrim :: [Char] -> a

-- ----------------------------------------------------------- standard IO ---
--
-- \`putStr\`, \`putStrLn\`, \`print\` and \`getLine\` are the first functions any
-- Haskell program reaches for, and until now none of them existed here: even
-- \`main = print 1\` failed to compile, so every test program had to declare a
-- \`foreign import javascript\` of its own just to show a result. These are the
-- GHC.Internal.System.IO definitions, spelled against what this backend has.
--
-- The string is packed in JavaScript rather than appended a character at a
-- time (see \`forceString\` below, and \`Data.JSString.pack\`'s own fast path):
-- one traversal, one host call. \`putStr\` buffers a partial line because
-- \`console.log\` always terminates one - the buffer is flushed by the next
-- \`putStrLn\`, by \`hFlush\`, or at exit, which is what makes
-- \`putStr "a" >> putStrLn "b"\` print \`ab\` on one line as GHC does.
foreign import javascript unsafe "(($1) => { const g = globalThis; const NL = String.fromCharCode(10); g.h$outBuf = (g.h$outBuf || '') + $1; const i = g.h$outBuf.lastIndexOf(NL); if (i >= 0) { const done = g.h$outBuf.slice(0, i); g.h$outBuf = g.h$outBuf.slice(i + 1); for (const line of done.split(NL)) console.log(line); } return 0; })" primPutStr :: JSStringPrim -> IntPrim

foreign import javascript unsafe "(() => { const g = globalThis; if (g.h$outBuf) { console.log(g.h$outBuf); g.h$outBuf = ''; } return 0; })" primFlushOut :: IntPrim



foreign import javascript unsafe "((s,c) => s + String.fromCodePoint(c))" primSnocStr :: JSStringPrim -> CharPrim -> JSStringPrim

foreign import javascript unsafe "(() => '')" primEmptyStr :: IntPrim -> JSStringPrim

-- Forces as it goes, one cons cell at a time. A JS-side walker that read
-- \`.d1\`/\`.d2\` off the cells directly would be faster, but it cannot tell a
-- forced \`C#\` box from an unevaluated thunk - both have a \`.d1\`, and a
-- thunk's is whatever its first free variable happens to be. Reading that as a
-- code point silently produces the wrong string, or throws \`RangeError:
-- invalid code point\` when the number is out of range. Only the RTS can force
-- safely, so packing stays here.
slowPackStr :: [Char] -> JSStringPrim -> JSStringPrim
slowPackStr cs acc = case cs of
  [] -> acc
  (C c : rest) -> slowPackStr rest (primSnocStr acc c)

packStr :: [Char] -> JSStringPrim
packStr cs = slowPackStr cs (primEmptyStr 0)

putStr :: [Char] -> IO ()
putStr cs = IO (\\s -> case primPutStr (packStr cs) of
  _ -> IOResult s ())

putStrLn :: [Char] -> IO ()
putStrLn cs = putStr (cs ++ [newlineChar])

newlineChar :: Char
newlineChar = chr 10

print :: Show a => a -> IO ()
print x = putStrLn (show x)

hFlush :: () -> IO ()
hFlush _ = IO (\\s -> case primFlushOut of
  _ -> IOResult s ())

stdout :: ()
stdout = ()

stderr :: ()
stderr = ()

foreign import javascript unsafe "(($1) => { console.error($1); return 0; })" primPutErr :: JSStringPrim -> IntPrim

hPutStr :: () -> [Char] -> IO ()
hPutStr _ cs = IO (\\s -> case primPutErr (packStr cs) of
  _ -> IOResult s ())

hPutStrLn :: () -> [Char] -> IO ()
hPutStrLn h cs = hPutStr h cs

error :: [Char] -> a
error s = errorPrim (forceErrorString s)

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

-- \`seq\` is a primitive now (src/desugar.ts turns a saturated use into a
-- \`case\`), so routing \`$!\` through it costs one \`case\` and no call, where
-- \`forceValue\` was an identity *function* that had to be entered.
($!) :: (a -> b) -> a -> b
($!) f x = x \`seq\` f x

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
-- 32-bit limbs, and its \`Int64\`/\`Word64\` are a pair of 32-bit halves. What GHC
-- never emits is a JS \`BigInt\`, and neither may this compiler: the target
-- engine has none. PrimJS refuses to decode a packed bundle that contains any
-- \`BigInt\` syntax at all - "RangeError: BigInt is too large to allocate", with
-- \`32n\` as the largest literal in the bundle - and miso's own JS installs
-- JSBI as \`globalThis.BigInt\`, whose objects throw the moment they meet a
-- native \`BigInt\` literal. So the carrier is a bignum in Haskell:
--
--   \`Big neg limbs\` is sign-magnitude, \`limbs\` least significant first, in
--   base 2^15, with no trailing zero limb. Zero is \`Big False []\`, so every
--   value has exactly one representation and a longer limb list is always the
--   bigger magnitude - which is what lets \`magCmp\` decide on structure alone.
--
-- Base 2^15 and not 2^31 because a limb product has to be exact and \`Int\` here
-- is the backend's 32-bit machine int: \`x * y + carry <= (2^15-1)^2 + 2^15\`
-- stays under 2^31, and \`primIntMul\` is \`Math.imul\`, which wraps a wider
-- product silently rather than rounding it loudly.
--
-- \`Int64\` and \`Word64\` ride the same carrier and differ only in the wrap
-- applied after every operation - \`bigNarrow64\`/\`bigMask64\`, which are what
-- \`BigInt.asIntN\`/\`asUintN\` at 64 bits were - so they wrap at their own width
-- rather than grow.
--
-- They are declared here, and not in \`Data.Int\`/\`Data.Word\`, because
-- \`Fingerprint\` is two \`Word64\` halves and \`Fingerprint\` is wired in: \`static\`
-- is a keyword form that needs no import (see StaticPtr, below).
data Big = Big Bool [Int]
data Integer = Integer Big
data Int64 = I64 Big
data Word64 = W64 Big

-- \`quot\`/\`rem\` on one limb. Both primops are exact on a JS number of any
-- width - \`(x/y)|0\` and \`x % y\` - which is what lets the halves of a 32-bit
-- word be split out of a value that does not fit an \`Int\`.
quotSmall :: Int -> Int -> Int
quotSmall (I a) (I b) = I (primIntQuot a b)

remSmall :: Int -> Int -> Int
remSmall (I a) (I b) = I (primIntRem a b)

lowLimb :: Int -> Int
lowLimb t = remSmall t 32768

highLimb :: Int -> Int
highLimb t = quotSmall t 32768

unInt :: Int -> IntPrim
unInt (I n) = n

-- Drop trailing zero limbs, so that magnitudes stay comparable by structure.
magNorm :: [Int] -> [Int]
magNorm ds = case ds of
  [] -> []
  (x : xs) -> magNormStep x (magNorm xs)

magNormStep :: Int -> [Int] -> [Int]
magNormStep x xs = if nullList xs && x == 0 then [] else x : xs

-- -1, 0 or 1. The recursion reaches the most significant limb first, so the
-- deepest difference is the one that decides - and an exhausted list is the
-- smaller magnitude precisely because both are normalised.
magCmp :: [Int] -> [Int] -> Int
magCmp a b = case a of
  [] -> if nullList b then 0 else negate 1
  (x : xs) -> case b of
    [] -> 1
    (y : ys) -> magCmpStep (magCmp xs ys) x y

magCmpStep :: Int -> Int -> Int -> Int
magCmpStep c x y = if c == 0 then magCmpLimb x y else c

magCmpLimb :: Int -> Int -> Int
magCmpLimb x y = if x == y then 0 else if x < y then negate 1 else 1

magAdd :: [Int] -> [Int] -> Int -> [Int]
magAdd a b c = case a of
  [] -> magCarry b c
  (x : xs) -> case b of
    [] -> magCarry a c
    (y : ys) -> magAddStep (x + y + c) xs ys

magAddStep :: Int -> [Int] -> [Int] -> [Int]
magAddStep t xs ys = lowLimb t : magAdd xs ys (highLimb t)

magCarry :: [Int] -> Int -> [Int]
magCarry ds c = if c == 0 then ds else magCarryInto ds c

magCarryInto :: [Int] -> Int -> [Int]
magCarryInto ds c = case ds of
  [] -> c : []
  (x : xs) -> magCarryStep (x + c) xs

magCarryStep :: Int -> [Int] -> [Int]
magCarryStep t xs = lowLimb t : magCarry xs (highLimb t)

-- \`a\` must be at least \`b\`; every caller compares first. A limb difference is
-- in [-2^15, 2^15), so one borrow always brings it back into range.
magSub :: [Int] -> [Int] -> Int -> [Int]
magSub a b w = case a of
  [] -> []
  (x : xs) -> case b of
    [] -> magSubStep (x - w) xs []
    (y : ys) -> magSubStep (x - y - w) xs ys

magSubStep :: Int -> [Int] -> [Int] -> [Int]
magSubStep t xs ys = if t < 0 then (t + 32768) : magSub xs ys 1 else t : magSub xs ys 0

magMul :: [Int] -> [Int] -> [Int]
magMul a b = case b of
  [] -> []
  (y : ys) -> magAdd (magMulLimb a y 0) (magShift (magMul a ys)) 0

-- Multiply by one limb. An empty magnitude stays empty, so the shift never
-- introduces the trailing zero limb the representation forbids.
magShift :: [Int] -> [Int]
magShift ds = if nullList ds then [] else 0 : ds

magMulLimb :: [Int] -> Int -> Int -> [Int]
magMulLimb ds y c = case ds of
  [] -> if c == 0 then [] else c : []
  (x : xs) -> magMulLimbStep (x * y + c) xs y

magMulLimbStep :: Int -> [Int] -> Int -> [Int]
magMulLimbStep t xs y = lowLimb t : magMulLimb xs y (highLimb t)

-- Quotient and remainder by a small positive divisor, as long division does it
-- on paper: the recursion reaches the most significant limb first and the
-- remainder flows back down. \`r * 32768 + limb\` must stay exact, which caps
-- the divisor at 2^16.
magDivSmall :: [Int] -> Int -> ([Int], Int)
magDivSmall ds n = case ds of
  [] -> ([], 0)
  (x : xs) -> magDivStep (magDivSmall xs n) x n

magDivStep :: ([Int], Int) -> Int -> Int -> ([Int], Int)
magDivStep qr x n = case qr of
  (qs, r) -> magDivJoin (r * 32768 + x) qs n

magDivJoin :: Int -> [Int] -> Int -> ([Int], Int)
magDivJoin cur qs n = (quotSmall cur n : qs, remSmall cur n)

-- Schoolbook long division by a divisor of any width, the same shape as
-- \`magDivSmall\`: the recursion reaches the most significant limb first and the
-- remainder flows back down. The remainder handed up is below the divisor, so
-- \`r * 2^15 + limb\` is below \`divisor * 2^15\` and the limb that fits is found
-- by bisecting [0, 2^15) - fifteen comparisons, and no estimate to correct.
magQuotRem :: [Int] -> [Int] -> ([Int], [Int])
magQuotRem ds b = case ds of
  [] -> ([], [])
  (x : xs) -> magQuotStep (magQuotRem xs b) x b

magQuotStep :: ([Int], [Int]) -> Int -> [Int] -> ([Int], [Int])
magQuotStep qr x b = case qr of
  -- \`r\` is little-endian, so \`r * 2^15 + x\` is \`x\` pushed on the front.
  (qs, r) -> magQuotJoin (magNorm (x : r)) qs b

magQuotJoin :: [Int] -> [Int] -> [Int] -> ([Int], [Int])
magQuotJoin cur qs b = magQuotOf cur qs b (magDigit cur b 0 32768)

magQuotOf :: [Int] -> [Int] -> [Int] -> Int -> ([Int], [Int])
magQuotOf cur qs b d = (d : qs, magNorm (magSub cur (magNorm (magMulLimb b d 0)) 0))

-- The largest \`d\` in [lo, hi) with \`b * d <= cur\`.
magDigit :: [Int] -> [Int] -> Int -> Int -> Int
magDigit cur b lo hi = if hi - lo <= 1 then lo else magDigitStep cur b lo hi (quotSmall (lo + hi) 2)

magDigitStep :: [Int] -> [Int] -> Int -> Int -> Int -> Int
magDigitStep cur b lo hi m =
  if magCmp (magNorm (magMulLimb b m 0)) cur > 0 then magDigit cur b lo m else magDigit cur b m hi

-- Truncating division, which is \`quot\`/\`rem\`: the quotient takes the product
-- of the signs and the remainder keeps the dividend's, so \`rem\` is zero or
-- has the dividend's sign, exactly as GHC's does.
bigQuotRem :: Big -> Big -> (Big, Big)
bigQuotRem x y = case y of
  Big nb b -> if nullList b then error "divide by zero" else bigQuotRemOf x nb (bigMag x) b

bigMag :: Big -> [Int]
bigMag (Big n ds) = ds

bigQuotRemOf :: Big -> Bool -> [Int] -> [Int] -> (Big, Big)
bigQuotRemOf x nb a b = bigQuotRemSign (bigIsNeg x) nb (magQuotRem a b)

bigQuotRemSign :: Bool -> Bool -> ([Int], [Int]) -> (Big, Big)
bigQuotRemSign na nb qr = case qr of
  (q, r) -> (bigOf (if na then not nb else nb) q, bigOf na r)

bigIsZero :: Big -> Bool
bigIsZero (Big n ds) = nullList ds

-- Repeated division by 10^4 - the largest power of ten for which
-- \`r * 32768 + limb\` still fits in 31 bits. Every group but the leading one
-- is zero-padded, which is what makes the concatenation the decimal number.
magDecimal :: [Int] -> [Char]
magDecimal ds = case magDivSmall ds 10000 of
  (qs, r) -> magDecimalStep (magNorm qs) r

magDecimalStep :: [Int] -> Int -> [Char]
magDecimalStep qs r = if nullList qs then showInt r else magDecimal qs ++ pad4 (showInt r)

pad4 :: [Char] -> [Char]
pad4 s = replicate (4 - length s) '0' ++ s

bigZero :: Big
bigZero = Big False []

-- The one place a \`Big\` is built: normalising here is what keeps zero
-- unsigned and magnitudes unique.
bigOf :: Bool -> [Int] -> Big
bigOf neg ds = case magNorm ds of
  m -> if nullList m then bigZero else Big neg m

bigAdd :: Big -> Big -> Big
bigAdd (Big na a) (Big nb b) = if na == nb then bigOf na (magAdd a b 0) else bigAddSub (magCmp a b) na a b

-- Opposite signs: the larger magnitude keeps its sign and the smaller is
-- subtracted from it.
bigAddSub :: Int -> Bool -> [Int] -> [Int] -> Big
bigAddSub c na a b =
  if c == 0 then bigZero else if c > 0 then bigOf na (magSub a b 0) else bigOf (not na) (magSub b a 0)

bigNeg :: Big -> Big
bigNeg (Big n ds) = if nullList ds then bigZero else Big (not n) ds

bigSub :: Big -> Big -> Big
bigSub x y = bigAdd x (bigNeg y)

bigMul :: Big -> Big -> Big
bigMul (Big na a) (Big nb b) = bigOf (if na then not nb else nb) (magMul a b)

bigCmp :: Big -> Big -> Int
bigCmp (Big na a) (Big nb b) =
  if na then (if nb then magCmp b a else negate 1) else (if nb then 1 else magCmp a b)

bigEq :: Big -> Big -> Bool
bigEq x y = bigCmp x y == 0

bigLt :: Big -> Big -> Bool
bigLt x y = bigCmp x y < 0

bigLe :: Big -> Big -> Bool
bigLe x y = bigCmp x y <= 0

bigGt :: Big -> Big -> Bool
bigGt x y = bigCmp x y > 0

bigGe :: Big -> Big -> Bool
bigGe x y = bigCmp x y >= 0

bigIsNeg :: Big -> Bool
bigIsNeg (Big n ds) = n

bigShow :: Big -> [Char]
bigShow (Big neg ds) = if neg then '-' : magDecimal ds else magDecimal ds

-- GHC's \`integerToInt#\` keeps the low bits of a machine word, and the machine
-- word on this backend is 32 bits wide (see \`Literal\` in src/stg.ts). \`Int\`
-- arithmetic IS that truncation - \`primIntAdd\` is \`(a+b)|0\` and \`primIntMul\`
-- is \`Math.imul\` - so the Horner sum below discards everything above bit 31 by
-- itself, and negating it is the two's complement of the low word.
bigToIntPrim :: Big -> IntPrim
bigToIntPrim (Big neg ds) = unInt (if neg then negate (magLow32 ds) else magLow32 ds)

magLow32 :: [Int] -> Int
magLow32 ds = case ds of
  [] -> 0
  (x : xs) -> x + 32768 * magLow32 xs

-- Most significant limb first, so each step rounds once and everything below
-- 2^53 - which is every value a \`Double\` holds exactly anyway - is exact.
bigToDoublePrim :: Big -> DoublePrim
bigToDoublePrim (Big neg ds) = if neg then primDoubleNeg (magToDouble ds) else magToDouble ds

magToDouble :: [Int] -> DoublePrim
magToDouble ds = case ds of
  [] -> 0.0
  (x : xs) -> primDoubleAdd (primDoubleMul (magToDouble xs) 32768.0) (intToDoublePrim x)

intToDoublePrim :: Int -> DoublePrim
intToDoublePrim (I n) = primIntToDouble n

-- \`d\` is whole by the time it arrives, so \`d % 32768\` and \`(d - r) / 32768\`
-- are both exact: the divisor is a power of two and the remainder is below
-- 2^15. That is what carries a \`Double\` as large as 1e308 across without
-- losing a bit it actually held.
bigFromDoublePrim :: DoublePrim -> Big
bigFromDoublePrim d =
  if primDoubleLt d 0.0 then bigOf True (magFromDouble (primDoubleNeg d)) else bigOf False (magFromDouble d)

magFromDouble :: DoublePrim -> [Int]
magFromDouble d = if primDoubleLt d 1.0 then [] else magFromDoubleStep (primDoubleRem d 32768.0) d

magFromDoubleStep :: DoublePrim -> DoublePrim -> [Int]
magFromDoubleStep r d =
  I (primDoubleToInt r) : magFromDouble (primDoubleDiv (primDoubleSub d r) 32768.0)

-- 2^64 and 2^63 as magnitudes: 64 = 4 * 15 + 4, so both are four zero limbs
-- and one small top limb.
pow64 :: [Int]
pow64 = 0 : 0 : 0 : 0 : 16 : []

pow63 :: [Int]
pow63 = 0 : 0 : 0 : 0 : 8 : []

-- The low 64 bits of a magnitude: four whole limbs and the low four bits of
-- the fifth.
magLow64 :: [Int] -> Int -> [Int]
magLow64 ds k = case ds of
  [] -> []
  (x : xs) -> if k > 0 then x : magLow64 xs (k - 1) else remSmall x 16 : []

-- What \`BigInt.asUintN(64, b)\` was: the value modulo 2^64, so a negative one
-- comes back as its two's complement.
bigMask64 :: Big -> Big
bigMask64 (Big neg ds) = bigMask64Of neg (magNorm (magLow64 ds 4))

bigMask64Of :: Bool -> [Int] -> Big
bigMask64Of neg m = if not neg then bigOf False m else if nullList m then bigZero else bigOf False (magSub pow64 m 0)

-- And \`BigInt.asIntN(64, b)\`: the same value read as signed, so everything at
-- or above 2^63 is 2^64 less than it looks.
bigNarrow64 :: Big -> Big
bigNarrow64 b = case bigMask64 b of
  Big n m -> if magCmp m pow63 < 0 then bigOf False m else bigOf True (magSub pow64 m 0)

-- What \`src/desugar.ts\` wraps a machine literal in when the \`fromInteger\` it
-- feeds is not one of the shapes \`overloadedLit\` short-cuts. The literal
-- arrives untouched (\`boxIntegerLit\`), so it is a JS number of any magnitude
-- and not a 32-bit one: going through \`DoublePrim\` is what keeps
-- \`4611686018427387904 :: Int64\` exact, where \`Int\` arithmetic would wrap it.
integerFromIntPrim :: IntPrim -> Integer
integerFromIntPrim n = Integer (bigFromDoublePrim (primIntToDouble n))

integerFromDoublePrim :: DoublePrim -> Integer
integerFromDoublePrim d = Integer (bigFromDoublePrim d)

-- What \`Data.Int\`/\`Data.Word\` narrow to their own width. Taking the boxed
-- \`Integer\` rather than its payload keeps every one of those instances
-- independent of how a \`Big\` is laid out.
integerToIntPrim :: Integer -> IntPrim
integerToIntPrim (Integer b) = bigToIntPrim b

integerToDoublePrim :: Integer -> DoublePrim
integerToDoublePrim (Integer b) = bigToDoublePrim b

integerIsNeg :: Integer -> Bool
integerIsNeg (Integer b) = bigIsNeg b

instance Eq Integer where
  (==) (Integer a) (Integer b) = bigEq a b

instance Ord Integer where
  (<) (Integer a) (Integer b) = bigLt a b
  (<=) (Integer a) (Integer b) = bigLe a b
  (>) (Integer a) (Integer b) = bigGt a b
  (>=) (Integer a) (Integer b) = bigGe a b

instance Num Integer where
  (+) (Integer a) (Integer b) = Integer (bigAdd a b)
  (-) (Integer a) (Integer b) = Integer (bigSub a b)
  (*) (Integer a) (Integer b) = Integer (bigMul a b)
  negate (Integer a) = Integer (bigNeg a)
  fromInteger n = n

instance Real Integer where
  toDoublePrim (Integer b) = bigToDoublePrim b

instance Integral Integer where
  toInteger n = n
  quotRem (Integer a) (Integer b) = integerQuotRem (bigQuotRem a b)

instance Show Integer where
  showsPrec d (Integer b) s = showsBigInt d b s

-- A negative number is parenthesised at any precedence above 6, exactly as
-- \`showSignedInt\` does it for \`Int\`.
showsBigInt :: Int -> Big -> [Char] -> [Char]
showsBigInt d b s =
  if bigIsNeg b && d > 6 then '(' : bigShow b ++ (')' : s) else bigShow b ++ s

instance Eq Int64 where
  (==) (I64 a) (I64 b) = bigEq a b

instance Ord Int64 where
  (<) (I64 a) (I64 b) = bigLt a b
  (<=) (I64 a) (I64 b) = bigLe a b
  (>) (I64 a) (I64 b) = bigGt a b
  (>=) (I64 a) (I64 b) = bigGe a b

instance Num Int64 where
  (+) (I64 a) (I64 b) = I64 (bigNarrow64 (bigAdd a b))
  (-) (I64 a) (I64 b) = I64 (bigNarrow64 (bigSub a b))
  (*) (I64 a) (I64 b) = I64 (bigNarrow64 (bigMul a b))
  negate (I64 a) = I64 (bigNarrow64 (bigNeg a))
  fromInteger (Integer b) = I64 (bigNarrow64 b)

instance Real Int64 where
  toDoublePrim (I64 b) = bigToDoublePrim b

instance Integral Int64 where
  toInteger (I64 b) = Integer b
  quotRem (I64 a) (I64 b) = int64QuotRem (bigQuotRem a b)

instance Show Int64 where
  showsPrec d (I64 b) s = showsBigInt d b s

instance Eq Word64 where
  (==) (W64 a) (W64 b) = bigEq a b

instance Ord Word64 where
  (<) (W64 a) (W64 b) = bigLt a b
  (<=) (W64 a) (W64 b) = bigLe a b
  (>) (W64 a) (W64 b) = bigGt a b
  (>=) (W64 a) (W64 b) = bigGe a b

instance Num Word64 where
  (+) (W64 a) (W64 b) = W64 (bigMask64 (bigAdd a b))
  (-) (W64 a) (W64 b) = W64 (bigMask64 (bigSub a b))
  (*) (W64 a) (W64 b) = W64 (bigMask64 (bigMul a b))
  negate (W64 a) = W64 (bigMask64 (bigNeg a))
  fromInteger (Integer b) = W64 (bigMask64 b)

instance Real Word64 where
  toDoublePrim (W64 b) = bigToDoublePrim b

instance Integral Word64 where
  toInteger (W64 b) = Integer b
  quotRem (W64 a) (W64 b) = word64QuotRem (bigQuotRem a b)

-- A \`Word64\` is masked to [0, 2^64), so it never prints a sign and never needs
-- the parentheses \`Int64\` does.
instance Show Word64 where
  showsPrec d (W64 b) s = bigShow b ++ s

-- ---------------------------------------------------------------- numeric ---

-- GHC's own definition, method for method. The \`Integer\` in the middle is a
-- lifted box, so nothing here has to force it into place - unlike the machine
-- value this used to pass, which could not be a lazy constructor field.
fromIntegral :: (Integral a, Num b) => a -> b
fromIntegral x = fromInteger (toInteger x)

-- GHC's own definitions, from \`rem\`. GHC's \`Integral\` implies \`Eq\` through
-- \`Real => Ord => Eq\`; this hierarchy keeps them separate, so it is named
-- explicitly here.
even :: (Integral a, Eq a) => a -> Bool
even n = rem n 2 == 0

odd :: (Integral a, Eq a) => a -> Bool
odd n = not (even n)

-- GHC's own default for \`divMod\`: it differs from \`quotRem\` exactly when the
-- remainder's sign disagrees with the divisor's, in which case the quotient
-- goes one lower and the remainder gains a divisor. GHC writes that test as
-- \`signum r == negate (signum d)\`; \`Num\` here has no \`signum\` and \`Integral\`
-- has no \`Ord\` superclass, so the two signs are read off \`toInteger\` instead.
divModOfQuotRem :: Integral a => (a, a) -> a -> (a, a)
divModOfQuotRem qr d = case qr of
  (q, r) -> if signsDisagree (toInteger r) (toInteger d) then (q - 1, r + d) else qr

signsDisagree :: Integer -> Integer -> Bool
signsDisagree (Integer a) (Integer b) = if bigIsZero a then False else notBool (bigIsNeg a) (bigIsNeg b)

notBool :: Bool -> Bool -> Bool
notBool a b = if a then not b else b

integerQuotRem :: (Big, Big) -> (Integer, Integer)
integerQuotRem qr = case qr of
  (q, r) -> (Integer q, Integer r)

-- \`quot\` of two 64-bit values is in range except for \`minBound \`quot\` (-1)\`,
-- which wraps back to \`minBound\` here exactly as GHC's \`quotInt64#\` does.
int64QuotRem :: (Big, Big) -> (Int64, Int64)
int64QuotRem qr = case qr of
  (q, r) -> (I64 (bigNarrow64 q), I64 (bigNarrow64 r))

word64QuotRem :: (Big, Big) -> (Word64, Word64)
word64QuotRem qr = case qr of
  (q, r) -> (W64 (bigMask64 q), W64 (bigMask64 r))

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

init :: [a] -> [a]
init xs = case xs of
  [] -> error "Prelude.init: empty list"
  (y : ys) -> if nullList ys then [] else y : init ys

(!!) :: [a] -> Int -> a
(!!) xs n = if n < 0 then error "Prelude.!!: negative index" else indexList xs n

indexList :: [a] -> Int -> a
indexList xs n = case xs of
  [] -> error "Prelude.!!: index too large"
  (y : ys) -> if n == 0 then y else indexList ys (n - 1)

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

-- GHC 9's list \`Foldable\` defines both as strict left folds
-- (\`GHC.Internal.Data.Foldable\`). The lazy \`foldr\` they had here built one
-- addition thunk per element and only collapsed the chain at the end, which
-- is both slower and a space leak on a long list.
sum :: (Foldable t, Num a) => t a -> a
sum xs = foldlStrict (\\acc x -> acc + x) 0 (toList xs)

product :: (Foldable t, Num a) => t a -> a
product xs = foldlStrict (\\acc x -> acc * x) 1 (toList xs)

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

-- ------------------------------------------------------------------ Read ---
--
-- GHC's \`Read\` is \`ReadPrec\` over a full Haskell lexer; the instances that
-- carry their weight are the numeric ones. Half a lexer would read some
-- programs' text *wrongly* rather than not at all, so what is here is exactly
-- the numeric-literal grammar - optional parentheses, an optional sign, and a
-- decimal, hexadecimal or octal numeral - and nothing derives \`Read\`.
class Read a where
  readsPrec :: Int -> [Char] -> [(a, [Char])]

reads :: Read a => [Char] -> [(a, [Char])]
reads s = readsPrec 0 s

read :: Read a => [Char] -> a
read s = readOne (reads s)

readOne :: [(a, [Char])] -> a
readOne ps = case readParsed ps of
  Just x -> x
  Nothing -> error "Prelude.read: no parse"

-- What \`read\` and \`readMaybe\` both demand: exactly one parse, with nothing
-- but whitespace left after it.
readParsed :: [(a, [Char])] -> Maybe a
readParsed ps = case ps of
  [] -> Nothing
  (p : rest) -> if nullList rest then readParsedFull p else Nothing

readParsedFull :: (a, [Char]) -> Maybe a
readParsedFull p = case p of
  (x, r) -> if nullList (dropWhile isSpaceChar r) then Just x else Nothing

-- \`readsPrec\` ignores its precedence because GHC's \`readNumber\` does: the
-- minus sign is read as a lexeme of its own, under no precedence test, so
-- \`readsPrec 11 "-5"\` is -5 there as well.
instance Read Int where
  readsPrec d s = readsSigned readsIntegral s

instance Read Integer where
  readsPrec d s = readsSigned readsIntegral s

instance Read Double where
  readsPrec d s = readsSigned readsDouble s

-- Whitespace, then either a parenthesised number or a signed numeral. The
-- parentheses nest and the sign may be separated from the digits, so
-- \`read " ( - 5 ) "\` is -5 here exactly as it is in GHC.
readsSigned :: Num a => ([Char] -> [(a, [Char])]) -> [Char] -> [(a, [Char])]
readsSigned body s = readsSignedAt body (dropWhile isSpaceChar s)

readsSignedAt :: Num a => ([Char] -> [(a, [Char])]) -> [Char] -> [(a, [Char])]
readsSignedAt body s = case s of
  [] -> []
  (c : t) ->
    if c == '(' then readsParen (readsSigned body t)
    else if c == '-' then readsNegate (body (dropWhile isSpaceChar t))
    else body s

readsParen :: [(a, [Char])] -> [(a, [Char])]
readsParen ps = case ps of
  [] -> []
  (p : rest) -> readsCloseAt p

readsCloseAt :: (a, [Char]) -> [(a, [Char])]
readsCloseAt p = case p of
  (x, r) -> readsCloseOn x (dropWhile isSpaceChar r)

readsCloseOn :: a -> [Char] -> [(a, [Char])]
readsCloseOn x s = case s of
  [] -> []
  (c : t) -> if c == ')' then (x, t) : [] else []

readsNegate :: Num a => [(a, [Char])] -> [(a, [Char])]
readsNegate ps = case ps of
  [] -> []
  (p : rest) -> readsNegateAt p

readsNegateAt :: Num a => (a, [Char]) -> [(a, [Char])]
readsNegateAt p = case p of
  (x, r) -> (negate x, r) : []

-- Every integral instance reads the same numeral and ends in \`fromInteger\`,
-- which is what GHC's \`convertInt\` does.
readsIntegral :: Num a => [Char] -> [(a, [Char])]
readsIntegral s = readsFromInteger (readsNatural s)

-- A leading \`0\` may begin \`0x\`/\`0o\`; when the base prefix is not followed by a
-- digit of that base the \`0\` is a decimal numeral on its own, and the prefix
-- letter is left behind - GHC's lexer backtracks the same way.
readsNatural :: [Char] -> [(Integer, [Char])]
readsNatural s = case s of
  [] -> []
  (c : t) -> if c == '0' then readsPrefixed t s else readsRadix 10 s

readsPrefixed :: [Char] -> [Char] -> [(Integer, [Char])]
readsPrefixed t s = case t of
  [] -> readsRadix 10 s
  (c : u) ->
    if c == 'x' || c == 'X' then readsOrDecimal (readsRadix 16 u) s
    else if c == 'o' || c == 'O' then readsOrDecimal (readsRadix 8 u) s
    else readsRadix 10 s

readsOrDecimal :: [(Integer, [Char])] -> [Char] -> [(Integer, [Char])]
readsOrDecimal ps s = if nullList ps then readsRadix 10 s else ps

readsRadix :: Int -> [Char] -> [(Integer, [Char])]
readsRadix r s = readsRadixOf r (span (isRadixDigit r) s)

readsRadixOf :: Int -> ([Char], [Char]) -> [(Integer, [Char])]
readsRadixOf r p = case p of
  (ds, rest) -> if nullList ds then [] else (digitsValue r ds 0, rest) : []

digitsValue :: Int -> [Char] -> Integer -> Integer
digitsValue r ds acc = case ds of
  [] -> acc
  (c : cs) -> digitsValue r cs (acc * toInteger r + toInteger (digitValue c))

isRadixDigit :: Int -> Char -> Bool
isRadixDigit r c = digitValue c >= 0 && digitValue c < r

isDigitChar :: Char -> Bool
isDigitChar c = isRadixDigit 10 c

-- -1 for anything that is not a digit in any base this reads.
digitValue :: Char -> Int
digitValue c = digitValueOf (ord c)

digitValueOf :: Int -> Int
digitValueOf n =
  if n >= 48 && n <= 57 then n - 48
  else if n >= 97 && n <= 102 then n - 87
  else if n >= 65 && n <= 70 then n - 55
  else negate 1

readsFromInteger :: Num a => [(Integer, [Char])] -> [(a, [Char])]
readsFromInteger ps = case ps of
  [] -> []
  (p : rest) -> readsFromIntegerAt p

readsFromIntegerAt :: Num a => (Integer, [Char]) -> [(a, [Char])]
readsFromIntegerAt p = case p of
  (n, r) -> (fromInteger n, r) : []

-- GHC's \`isSpace\` over the range \`read\` can meet: the ASCII whitespace and
-- the non-breaking space.
isSpaceChar :: Char -> Bool
isSpaceChar c = isSpaceOrd (ord c)

isSpaceOrd :: Int -> Bool
isSpaceOrd n = n == 32 || (n >= 9 && n <= 13) || n == 160

-- A \`Double\` has its shape checked here against Haskell's grammar and its
-- value computed by JavaScript's own \`Number\`, which is correctly rounded -
-- and so is GHC's \`fromRational\`, while a mantissa scaled by a power of ten
-- rounds twice and would differ in the last bit. Only text the two languages
-- read alike is ever handed over, \`0x\`/\`0o\` included.
readsDouble :: [Char] -> [(Double, [Char])]
readsDouble s = case s of
  [] -> []
  (c : t) -> if c == '0' then readsDoublePrefixed t s else readsDecimalDouble s

readsDoublePrefixed :: [Char] -> [Char] -> [(Double, [Char])]
readsDoublePrefixed t s = case t of
  [] -> readsDecimalDouble s
  (c : u) ->
    if c == 'x' || c == 'X' then readsDoubleRadix (readsRadix 16 u) s
    else if c == 'o' || c == 'O' then readsDoubleRadix (readsRadix 8 u) s
    else readsDecimalDouble s

readsDoubleRadix :: [(Integer, [Char])] -> [Char] -> [(Double, [Char])]
readsDoubleRadix ps s = if nullList ps then readsDecimalDouble s else readsFromInteger ps

readsDecimalDouble :: [Char] -> [(Double, [Char])]
readsDecimalDouble s = readsWhole (span isDigitChar s)

readsWhole :: ([Char], [Char]) -> [(Double, [Char])]
readsWhole p = case p of
  (whole, r) -> if nullList whole then [] else readsFrac whole r

-- A fraction counts only when a digit follows the point, and an exponent only
-- when a digit follows the \`e\`: \`read "1." :: Double\` leaves the \`.\` behind in
-- GHC rather than reading it, and so does \`1e\`.
readsFrac :: [Char] -> [Char] -> [(Double, [Char])]
readsFrac whole r = case r of
  [] -> readsExp whole r
  (c : t) -> if c == '.' then readsFracDigits whole (span isDigitChar t) r else readsExp whole r

readsFracDigits :: [Char] -> ([Char], [Char]) -> [Char] -> [(Double, [Char])]
readsFracDigits whole p r = case p of
  (ds, rest) -> if nullList ds then readsExp whole r else readsExp (whole ++ ('.' : ds)) rest

readsExp :: [Char] -> [Char] -> [(Double, [Char])]
readsExp mant r = case r of
  [] -> readsDoubleOf mant r
  (c : t) -> if c == 'e' || c == 'E' then readsExpSign mant t r else readsDoubleOf mant r

readsExpSign :: [Char] -> [Char] -> [Char] -> [(Double, [Char])]
readsExpSign mant t r = case t of
  [] -> readsDoubleOf mant r
  (c : u) ->
    if c == '+' then readsExpDigits mant "e+" (span isDigitChar u) r
    else if c == '-' then readsExpDigits mant "e-" (span isDigitChar u) r
    else readsExpDigits mant "e" (span isDigitChar t) r

readsExpDigits :: [Char] -> [Char] -> ([Char], [Char]) -> [Char] -> [(Double, [Char])]
readsExpDigits mant tag p r = case p of
  (ds, rest) -> if nullList ds then readsDoubleOf mant r else readsDoubleOf (mant ++ (tag ++ ds)) rest

readsDoubleOf :: [Char] -> [Char] -> [(Double, [Char])]
readsDoubleOf text rest = (DoubleBox (primReadDouble (packDigits text (primDigitsEmpty 0))), rest) : []

packDigits :: [Char] -> JSStringPrim -> JSStringPrim
packDigits cs acc = case cs of
  [] -> acc
  (c : rest) -> packDigits rest (primDigitsSnoc acc (unInt (ord c)))

foreign import javascript unsafe "((n) => '')" primDigitsEmpty :: IntPrim -> JSStringPrim
foreign import javascript unsafe "((s, c) => s + String.fromCharCode(c))" primDigitsSnoc :: JSStringPrim -> IntPrim -> JSStringPrim
foreign import javascript unsafe "((s) => Number(s))" primReadDouble :: JSStringPrim -> DoublePrim

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
word64FromHalves hi lo = W64 (bigFromHalves hi lo)

-- 2^32 is 4 * 2^30, so the high half lands two limbs up shifted left by two
-- bits: its low 13 bits finish limb 2 (3 + 8191 * 4 is 32767, exactly one
-- limb, so no carry), the next 15 are limb 3 and the top 4 are limb 4.
bigFromHalves :: IntPrim -> IntPrim -> Big
bigFromHalves hi lo = bigFromHalvesUnsigned (I (primUnsigned32 hi)) (I (primUnsigned32 lo))

bigFromHalvesUnsigned :: Int -> Int -> Big
bigFromHalvesUnsigned hi lo =
  bigOf False (remSmall lo 32768 : remSmall (quotSmall lo 32768) 32768 : quotSmall lo 1073741824 + 4 * remSmall hi 8192 : remSmall (quotSmall hi 8192) 32768 : quotSmall hi 268435456 : [])

-- Unsigned, because that is what \`h$hs_spt_insert\` was given when the key was
-- four \`Int\`s and what the table's keys are still compared as. The magnitude
-- arithmetic that produces each half is 32-bit \`Int\` arithmetic, so the value
-- arrives with bit 31 read as a sign; \`>>> 0\` is the one thing JS has that
-- reads it back as the unsigned word it is.
foreign import javascript unsafe "((n) => n >>> 0)" primUnsigned32 :: IntPrim -> IntPrim

bigLo32 :: Big -> IntPrim
bigLo32 (Big neg ds) = primUnsigned32 (unInt (magLow32 ds))

-- Bits 32 and up: drop the two whole limbs below bit 30, then divide the rest
-- by 4. A \`Word64\` is below 2^64, so what is left IS the high word.
bigHi32 :: Big -> IntPrim
bigHi32 (Big neg ds) = primUnsigned32 (unInt (magLow32 (fst (magDivSmall (drop 2 ds) 4))))

-- Sixteen hex digits, zero-padded, which is what \`b.toString(16)\` padded to
-- 16 was: the value is masked to 64 bits, so sixteen digits is exactly it.
bigHex16 :: Big -> [Char]
bigHex16 (Big neg ds) = hexDigits ds 16 []

hexDigits :: [Int] -> Int -> [Char] -> [Char]
hexDigits ds n acc = if n == 0 then acc else hexDigitsStep (magDivSmall ds 16) n acc

hexDigitsStep :: ([Int], Int) -> Int -> [Char] -> [Char]
hexDigitsStep qr n acc = case qr of
  (qs, r) -> hexDigits (magNorm qs) (n - 1) (hexDigitChar r : acc)

hexDigitChar :: Int -> Char
hexDigitChar (I n) = C (primChr (if primIntLt n 10 then primIntAdd n 48 else primIntAdd n 87))

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
hex16 (W64 b) = bigHex16 b

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
      case primSptInsert (bigHi32 a) (bigLo32 a) (bigHi32 b) (bigLo32 b) p of
        _ -> IOResult s ()

-- What \`src/elaborate.ts\` puts in front of \`main\`. It is a plain function and
-- not \`sptRegister p >> m\` because it is built after elaboration, where \`>>\`
-- has no dictionary to be applied to.
sptRegisterThen :: StaticPtr a -> IO b -> IO b
sptRegisterThen p m = IO (\\s -> sptRegisterThenStep s p m)

sptRegisterThenStep :: RealWorld -> StaticPtr a -> IO b -> IOResult b
sptRegisterThenStep s p m = case sptRegisterStep s p of
  IOResult t u -> unIO m t

-- The halves are split at the primop calls themselves, and not passed down as
-- four \`IntPrim\`s: a machine value in a *Haskell* function's argument is not a
-- strict position, so \`sptLookup (bigHi32 x) ..\` would hand over four THUNKS
-- where the table wants four numbers - and the table would key on them. A
-- primop's argument is strict, so each split below is evaluated where it
-- stands. (This is the same rule the constructor fields in \`Data.Int\` follow.)
unsafeLookupStaticPtr :: StaticKey -> IO (Maybe (StaticPtr a))
unsafeLookupStaticPtr k = case k of
  Fingerprint (W64 x) (W64 y) -> sptLookup x y

sptLookup :: Big -> Big -> IO (Maybe (StaticPtr a))
sptLookup x y =
  if primIntEq (primSptHas (bigHi32 x) (bigLo32 x) (bigHi32 y) (bigLo32 y)) 0 then pure Nothing else sptFetch x y

-- Split from the test above because the miss returns \`null\`, and \`null\` in a
-- position something may enter is not a value - it is the crash one step later.
sptFetch :: Big -> Big -> IO (Maybe (StaticPtr a))
sptFetch x y = case primSptGet (bigHi32 x) (bigLo32 x) (bigHi32 y) (bigLo32 y) of
  p -> pure (Just p)
`;
