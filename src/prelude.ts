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
 * A class method may not carry a constraint of its own: `src/elaborate.ts`
 * reads a method signature with `parseType`, which drops the context. That is
 * why `Foldable` here has no `foldMap`, and why `traverse`/`mapM` are ordinary
 * list functions rather than `Traversable` methods.
 *
 * `IO` follows GHC: an action is a *function of a state token*, so building it
 * is not running it, and running it means applying it. GHC's is
 * `State# RealWorld -> (# State# RealWorld, a #)`; the token here is a real
 * nullary constructor and the result pair is a real data type, because this
 * frontend has no void types and no unboxed tuples. What matters is preserved:
 * matching the result constructor is what sequences one action after another,
 * and it does so without forcing the value inside.
 */
export const PRELUDE_SOURCE = `module GHCTS.Prelude where

data Bool = False | True
data Int = I IntPrim
data Char = C CharPrim
data Ordering = LT | EQ | GT
data Maybe a = Nothing | Just a
data Either a b = Left a | Right b

data RealWorld = RealWorld
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
  fromInteger :: IntPrim -> a

class Show a where
  show :: a -> [Char]

class Enum a where
  toEnum :: Int -> a
  fromEnum :: a -> Int
  succ :: a -> a
  pred :: a -> a
  succ x = toEnum (fromEnum x + 1)
  pred x = toEnum (fromEnum x - 1)

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
  fromInteger n = I n

instance Show Int where
  show n = showInt n

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

instance Eq a => Eq (Maybe a) where
  (==) a b = eqMaybe (==) a b

instance (Eq a, Eq b) => Eq (Either a b) where
  (==) a b = eqEither (==) (==) a b

instance (Eq a, Eq b) => Eq (a, b) where
  (==) a b = eqPair (==) (==) a b

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
ioBind m k = IO (\\s -> ioBindStep (unIO m s) k)

ioBindStep :: IOResult a -> (a -> IO b) -> IOResult b
ioBindStep r k = case r of
  IOResult s a -> unIO (k a) s

ioThen :: IO a -> IO b -> IO b
ioThen m k = IO (\\s -> ioThenStep (unIO m s) k)

ioThenStep :: IOResult a -> IO b -> IOResult b
ioThenStep r k = case r of
  IOResult s a -> unIO k s

ioMap :: (a -> b) -> IO a -> IO b
ioMap f m = ioBind m (\\x -> ioPure (f x))

ioAp :: IO (a -> b) -> IO a -> IO b
ioAp f m = ioBind f (\\g -> ioMap g m)

ioValue :: IOResult a -> a
ioValue r = case r of
  IOResult s a -> a

unsafePerformIO :: IO a -> a
unsafePerformIO m = ioValue (unIO m RealWorld)

-- GHC's real entry point is \`:Main.main = runMainIO Main.main\`, and
-- \`src/elaborate.ts\` emits that same wrapper, so \`h$main(...Main.main)\` -
-- plain entry - is what runs the program.
runMainIO :: IO a -> a
runMainIO m = unsafePerformIO m

-- ------------------------------------------------------------- functions ---

foreign import javascript unsafe "((s) => { throw new Error('Prelude.error'); })" error :: [Char] -> a

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

showInt :: Int -> [Char]
showInt (I n) = if primIntLt n 0 then C (primChr 45) : digitsOf (primIntNeg n) [] else digitsOf n []

digitsOf :: IntPrim -> [Char] -> [Char]
digitsOf n acc = if primIntLt n 10 then digitChar n : acc else digitsOf (primIntQuot n 10) (digitChar (primIntRem n 10) : acc)

digitChar :: IntPrim -> Char
digitChar n = C (primChr (primIntAdd n 48))

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

mapM_ :: (Foldable t, Monad m) => (a -> m b) -> t a -> m ()
mapM_ f xs = foldr (\\x k -> f x >> k) (pure ()) xs

forM_ :: (Foldable t, Monad m) => t a -> (a -> m b) -> m ()
forM_ xs f = mapM_ f xs

sequence_ :: (Foldable t, Monad m) => t (m a) -> m ()
sequence_ xs = foldr (\\m k -> m >> k) (pure ()) xs

traverse_ :: (Foldable t, Monad m) => (a -> m b) -> t a -> m ()
traverse_ f xs = mapM_ f xs

-- \`Traversable\` cannot be a class here (\`traverse\` carries its own
-- \`Applicative\` constraint), so these are the list instances written out.
mapM :: Monad m => (a -> m b) -> [a] -> m [b]
mapM f xs = case xs of
  [] -> pure []
  (y : ys) -> f y >>= (\\r -> mapM f ys >>= (\\rs -> pure (r : rs)))

traverse :: Monad m => (a -> m b) -> [a] -> m [b]
traverse f xs = mapM f xs

forM :: Monad m => [a] -> (a -> m b) -> m [b]
forM xs f = mapM f xs

sequence :: Monad m => [m a] -> m [a]
sequence xs = mapM id xs

sequenceA :: Monad m => [m a] -> m [a]
sequenceA xs = mapM id xs

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
`;
