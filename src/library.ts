/** The library modules the compiler ships, as ordinary Haskell.
 *
 * These are the modules GHC gets from wired-in packages (`base`, `containers`,
 * `ghc-internal`). They are *modules*, not another flat Prelude, because that
 * is what makes `import qualified Data.Map as M` put `M.fromList` - and only
 * `M.fromList` - in scope: `src/modules.ts` resolves them exactly as it
 * resolves a project's own modules, and a name a module does not export stays
 * the honest "not in scope" it is.
 *
 * A project module of the same name wins, so a program can supply its own.
 *
 * WHERE THIS USES JAVASCRIPT, AND WHERE IT REFUSES TO
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * The rule is that a JS shortcut is allowed only when it cannot be observed:
 *
 *   - `IORef` is a mutable cell and nothing more, so it is GHC's own `MutVar#`
 *     primops - a property read and a property write (`rts/js/mem.js`).
 *   - `MVar` is not a cell: `takeMVar` on an empty one *blocks the thread*, and
 *     only the RTS can do that. It is GHC's `MVar#` primops
 *     (`rts/js/thread.js`), never a JS object with a value in it.
 *   - `Data.Map`/`Data.IntMap`/`Data.Set` are ordered, persistent and lazy.
 *     A JS `Map` is insertion-ordered, mutable and strict, and the difference
 *     is observable through `toList`, `foldr`, `elems` and `keys` - all of
 *     which miso calls. So these are written in Haskell, as real search trees.
 *   - `JSString` IS a JavaScript string, so every operation on one is FFI.
 *     Folding it into a `[Char]` first would be a different type with different
 *     performance and the same answers - but `Miso.String` is on miso's hot
 *     path, and the FFI version cannot answer differently.
 *
 * A note on shape, which the frontend forces. A value of an unlifted primitive
 * type (`IntPrim`, `DoublePrim`, `MVarPrim`, `JSValPrim`, `JSStringPrim`) is a
 * machine value, not a heap object. A variable holding one, and a primop or
 * foreign call producing one, may go anywhere - `src/core-to-stg.ts` binds a
 * primop argument with `case`. But the result of an ordinary *Haskell function*
 * in a lazy position (a constructor field, a function argument) is let-bound as
 * a THUNK, and a thunk is not a machine value: `JSString (packOnto cs ...)`
 * puts a closure where the JS string should be, and the next `.toUpperCase()`
 * fails. Every such result here is therefore named by a `case` first.
 */
import type { Module } from "./ast.js";
import { parseModule } from "./parser.js";

const sources: Record<string, string> = {
  "Data.IORef": `module Data.IORef where

-- GHC's \`data IORef a = IORef (MutVar# RealWorld a)\`, and the primops below
-- are the same ones GHC.IORef uses. Reimplementing the cell in Haskell would
-- be slower and no more correct.
data IORef a = IORef (MutVarPrim a)

newIORef :: a -> IO (IORef a)
newIORef x = IO (\\s -> newIORefStep s x)

newIORefStep :: RealWorld -> a -> IOResult (IORef a)
newIORefStep s x = case primNewMutVar x of
  v -> IOResult s (IORef v)

-- The stored closure comes back untouched, so a value written lazily is still
-- a thunk when it is read: \`readIORef\` does not force, and neither does this.
readIORef :: IORef a -> IO a
readIORef r = IO (\\s -> readIORefStep s r)

readIORefStep :: RealWorld -> IORef a -> IOResult a
readIORefStep s (IORef v) = case primReadMutVar v of
  x -> IOResult s x

writeIORef :: IORef a -> a -> IO ()
writeIORef r x = IO (\\s -> writeIORefStep s r x)

writeIORefStep :: RealWorld -> IORef a -> a -> IOResult ()
writeIORefStep s (IORef v) x = case primWriteMutVar v x of
  _ -> IOResult s ()

writeIORefStrict :: IORef a -> a -> IO ()
writeIORefStrict r x = seq x (writeIORef r x)

modifyIORef :: IORef a -> (a -> a) -> IO ()
modifyIORef r f = readIORef r >>= (\\x -> writeIORef r (f x))

modifyIORef' :: IORef a -> (a -> a) -> IO ()
modifyIORef' r f = readIORef r >>= (\\x -> writeIORefStrict r (f x))

-- On this target there is one JS thread, so a read followed by a write cannot
-- be interleaved and the "atomic" of the name is free. What is NOT free is the
-- strictness: GHC's \`atomicModifyIORef'\` forces both the new contents and the
-- returned value before it returns, and a lazy version would leak thunks into
-- the cell instead.
atomicModifyIORef' :: IORef a -> (a -> (a, b)) -> IO b
atomicModifyIORef' r f = readIORef r >>= (\\x -> atomicModifyStep r (f x))

atomicModifyStep :: IORef a -> (a, b) -> IO b
atomicModifyStep r p = case p of
  (a, b) -> writeIORefStrict r a >> seq b (pure b)

atomicModifyIORef :: IORef a -> (a -> (a, b)) -> IO b
atomicModifyIORef r f = readIORef r >>= (\\x -> atomicModifyLazyStep r (f x))

atomicModifyIORef_ :: IORef a -> (a -> a) -> IO ()
atomicModifyIORef_ r f = modifyIORef' r f

atomicModifyLazyStep :: IORef a -> (a, b) -> IO b
atomicModifyLazyStep r p = case p of
  (a, b) -> writeIORef r a >> pure b

atomicWriteIORef :: IORef a -> a -> IO ()
atomicWriteIORef r x = writeIORefStrict r x
`,
  "Control.Concurrent.MVar": `module Control.Concurrent.MVar where

-- \`MVar#\`, not a cell. \`takeMVar\` on an empty MVar enqueues the current thread
-- and returns to the scheduler (rts/js/thread.js); modelling it as a JS object
-- with a value in it would silently turn a blocking take into a non-blocking
-- read of a hole.
data MVar a = MVar (MVarPrim a)

newEmptyMVar :: IO (MVar a)
newEmptyMVar = IO newEmptyMVarStep

-- \`primNewMVar\` ignores the token; it is passed only so the allocation is a
-- call and not one shared top-level MVar.
newEmptyMVarStep :: RealWorld -> IOResult (MVar a)
newEmptyMVarStep s = case primNewMVar s of
  m -> IOResult s (MVar m)

newMVar :: a -> IO (MVar a)
newMVar x = newEmptyMVar >>= (\\v -> putMVar v x >> pure v)

takeMVar :: MVar a -> IO a
takeMVar v = IO (\\s -> takeMVarStep s v)

takeMVarStep :: RealWorld -> MVar a -> IOResult a
takeMVarStep s (MVar m) = case primTakeMVar m of
  x -> IOResult s x

putMVar :: MVar a -> a -> IO ()
putMVar v x = IO (\\s -> putMVarStep s v x)

putMVarStep :: RealWorld -> MVar a -> a -> IOResult ()
putMVarStep s (MVar m) x = case primPutMVar m x of
  _ -> IOResult s ()

readMVar :: MVar a -> IO a
readMVar v = IO (\\s -> readMVarStep s v)

readMVarStep :: RealWorld -> MVar a -> IOResult a
readMVarStep s (MVar m) = case primReadMVar m of
  x -> IOResult s x

tryPutMVar :: MVar a -> a -> IO Bool
tryPutMVar v x = IO (\\s -> tryPutMVarStep s v x)

tryPutMVarStep :: RealWorld -> MVar a -> a -> IOResult Bool
tryPutMVarStep s (MVar m) x = case primTryPutMVar m x of
  b -> IOResult s b

isEmptyMVar :: MVar a -> IO Bool
isEmptyMVar v = IO (\\s -> isEmptyMVarStep s v)

isEmptyMVarStep :: RealWorld -> MVar a -> IOResult Bool
isEmptyMVarStep s (MVar m) = case primIsEmptyMVar m of
  b -> IOResult s b

modifyMVar_ :: MVar a -> (a -> IO a) -> IO ()
modifyMVar_ v f = takeMVar v >>= (\\x -> f x >>= (\\y -> putMVar v y))

modifyMVar :: MVar a -> (a -> IO (a, b)) -> IO b
modifyMVar v f = takeMVar v >>= (\\x -> f x >>= (\\p -> modifyMVarPut v p))

modifyMVarPut :: MVar a -> (a, b) -> IO b
modifyMVarPut v p = case p of
  (a, b) -> putMVar v a >> pure b

withMVar :: MVar a -> (a -> IO b) -> IO b
withMVar v f = takeMVar v >>= (\\x -> f x >>= (\\r -> putMVar v x >> pure r))

swapMVar :: MVar a -> a -> IO a
swapMVar v x = takeMVar v >>= (\\old -> putMVar v x >> pure old)
`,
  "Control.Concurrent": `module Control.Concurrent (module Control.Concurrent.MVar, ThreadId, forkIO, threadDelay, yield) where
import Control.Concurrent.MVar

data ThreadId = ThreadId ThreadIdPrim

-- \`h$forkThread\` starts the new thread with \`h$ap_1_0\`, i.e. it applies the
-- closure to one *void* argument - which is exactly GHC's \`forkIO#\`, whose
-- argument has type \`State# RealWorld -> (# State# RealWorld, () #)\`. An \`IO\`
-- here is a data constructor and applying one is a panic, so what is handed
-- over is the state-token function inside it. The token the RTS supplies is
-- whatever happens to be in the argument register, which is safe for the same
-- reason GHC's void token is: nothing ever scrutinises a \`RealWorld\`.
forkIO :: IO () -> IO ThreadId
forkIO action = IO (\\s -> forkIOStep s (\\t -> unIO action t))

forkIOStep :: RealWorld -> (RealWorld -> IOResult ()) -> IOResult ThreadId
forkIOStep s thunk = case primFork thunk of
  t -> IOResult s (ThreadId t)

-- GHC's \`threadDelay\` suspends the thread and lets the scheduler run others;
-- \`h$delayThread\` does exactly that, so this must not be a busy wait.
threadDelay :: Int -> IO ()
threadDelay n = IO (\\s -> threadDelayStep s n)

threadDelayStep :: RealWorld -> Int -> IOResult ()
threadDelayStep s (I n) = case primDelay n of
  _ -> IOResult s ()

yield :: IO ()
yield = threadDelay 0
`,
  "Data.Map": `module Data.Map where

-- A size-balanced binary search tree: containers' own representation, with
-- containers' delta/ratio (3/2). A JS \`Map\` would have been three lines, and
-- would have been a different data structure - insertion-ordered, mutable and
-- strict - which \`toList\`, \`keys\`, \`elems\` and \`foldr\` all report on.
data Map k a = Tip | Bin Int k a (Map k a) (Map k a)

size :: Map k a -> Int
size Tip = 0
size (Bin n _ _ _ _) = n

null :: Map k a -> Bool
null Tip = True
null (Bin _ _ _ _ _) = False

empty :: Map k a
empty = Tip

singleton :: k -> a -> Map k a
singleton k x = Bin 1 k x Tip Tip

bin :: k -> a -> Map k a -> Map k a -> Map k a
bin k x l r = Bin (size l + size r + 1) k x l r

balance :: k -> a -> Map k a -> Map k a -> Map k a
balance k x l r
  | size l + size r <= 1 = bin k x l r
  | size r > 3 * size l = rotateL k x l r
  | size l > 3 * size r = rotateR k x l r
  | otherwise = bin k x l r

rotateL :: k -> a -> Map k a -> Map k a -> Map k a
rotateL k x l Tip = bin k x l Tip
rotateL k x l (Bin _ rk rx rl rr) =
  if size rl < 2 * size rr then bin rk rx (bin k x l rl) rr else doubleL k x l rk rx rl rr

doubleL :: k -> a -> Map k a -> k -> a -> Map k a -> Map k a -> Map k a
doubleL k1 x1 t1 k2 x2 (Bin _ k3 x3 t2 t3) t4 = bin k3 x3 (bin k1 x1 t1 t2) (bin k2 x2 t3 t4)
doubleL k1 x1 t1 k2 x2 Tip t4 = bin k2 x2 t1 t4

rotateR :: k -> a -> Map k a -> Map k a -> Map k a
rotateR k x Tip r = bin k x Tip r
rotateR k x (Bin _ lk lx ll lr) r =
  if size lr < 2 * size ll then bin lk lx ll (bin k x lr r) else doubleR k x lk lx ll lr r

doubleR :: k -> a -> k -> a -> Map k a -> Map k a -> Map k a -> Map k a
doubleR k1 x1 k2 x2 t1 (Bin _ k3 x3 t2 t3) t4 = bin k3 x3 (bin k2 x2 t1 t2) (bin k1 x1 t3 t4)
doubleR k1 x1 k2 x2 t1 Tip t4 = bin k2 x2 t1 t4

lookup :: Ord k => k -> Map k a -> Maybe a
lookup _ Tip = Nothing
lookup k (Bin _ ky y l r)
  | k < ky = lookup k l
  | k > ky = lookup k r
  | otherwise = Just y

(!?) :: Ord k => Map k a -> k -> Maybe a
(!?) m k = lookup k m

(!) :: Ord k => Map k a -> k -> a
(!) m k = case lookup k m of
  Nothing -> error "Map.!: given key is not an element in the map"
  Just x -> x

member :: Ord k => k -> Map k a -> Bool
member k m = isJust (lookup k m)

notMember :: Ord k => k -> Map k a -> Bool
notMember k m = not (member k m)

findWithDefault :: Ord k => a -> k -> Map k a -> a
findWithDefault d k m = fromMaybe d (lookup k m)

insert :: Ord k => k -> a -> Map k a -> Map k a
insert k x Tip = singleton k x
insert k x (Bin sz ky y l r)
  | k < ky = balance ky y (insert k x l) r
  | k > ky = balance ky y l (insert k x r)
  | otherwise = Bin sz k x l r

insertWith :: Ord k => (a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWith _ k x Tip = singleton k x
insertWith f k x (Bin sz ky y l r)
  | k < ky = balance ky y (insertWith f k x l) r
  | k > ky = balance ky y l (insertWith f k x r)
  | otherwise = Bin sz k (f x y) l r

delete :: Ord k => k -> Map k a -> Map k a
delete _ Tip = Tip
delete k (Bin _ ky y l r)
  | k < ky = balance ky y (delete k l) r
  | k > ky = balance ky y l (delete k r)
  | otherwise = glue l r

glue :: Map k a -> Map k a -> Map k a
glue Tip r = r
glue (Bin n k x l r) Tip = Bin n k x l r
glue (Bin n k x l r) (Bin n2 k2 x2 l2 r2) = glueMin (Bin n k x l r) (deleteFindMin (Bin n2 k2 x2 l2 r2))

glueMin :: Map k a -> (k, a, Map k a) -> Map k a
glueMin l t = case t of
  (k, x, r) -> balance k x l r

deleteFindMin :: Map k a -> (k, a, Map k a)
deleteFindMin Tip = error "Map.deleteFindMin: empty map"
deleteFindMin (Bin _ k x Tip r) = (k, x, r)
deleteFindMin (Bin _ k x (Bin n2 k2 x2 l2 r2) r) = rebuildMin k x r (deleteFindMin (Bin n2 k2 x2 l2 r2))

rebuildMin :: k -> a -> Map k a -> (k, a, Map k a) -> (k, a, Map k a)
rebuildMin k x r t = case t of
  (km, xm, l2) -> (km, xm, balance k x l2 r)

adjust :: Ord k => (a -> a) -> k -> Map k a -> Map k a
adjust _ _ Tip = Tip
adjust f k (Bin sz ky y l r)
  | k < ky = Bin sz ky y (adjust f k l) r
  | k > ky = Bin sz ky y l (adjust f k r)
  | otherwise = Bin sz ky (f y) l r

alter :: Ord k => (Maybe a -> Maybe a) -> k -> Map k a -> Map k a
alter f k m = alterWith f k m (lookup k m)

alterWith :: Ord k => (Maybe a -> Maybe a) -> k -> Map k a -> Maybe a -> Map k a
alterWith f k m before = case f before of
  Nothing -> delete k m
  Just x -> insert k x m

union :: Ord k => Map k a -> Map k a -> Map k a
union l r = foldlList (\\acc p -> unionStep acc p) r (toList l)

unionStep :: Ord k => Map k a -> (k, a) -> Map k a
unionStep m p = case p of
  (k, x) -> insert k x m

unionWith :: Ord k => (a -> a -> a) -> Map k a -> Map k a -> Map k a
unionWith f l r = foldlList (\\acc p -> unionWithStep f acc p) r (toList l)

unionWithStep :: Ord k => (a -> a -> a) -> Map k a -> (k, a) -> Map k a
unionWithStep f m p = case p of
  (k, x) -> insertWith f k x m

unions :: Ord k => [Map k a] -> Map k a
unions ms = foldlList union Tip ms

fromList :: Ord k => [(k, a)] -> Map k a
fromList xs = foldlList (\\m p -> unionStep m p) Tip xs

fromListWith :: Ord k => (a -> a -> a) -> [(k, a)] -> Map k a
fromListWith f xs = foldlList (\\m p -> unionWithStep f m p) Tip xs

-- In-order, so the list is ascending by key. This is the whole reason the tree
-- exists: \`Data.Map.toList\` is documented to be sorted, and miso folds it.
foldrWithKey :: (k -> a -> b -> b) -> b -> Map k a -> b
foldrWithKey _ z Tip = z
foldrWithKey f z (Bin _ k x l r) = foldrWithKey f (f k x (foldrWithKey f z r)) l

foldlWithKey :: (b -> k -> a -> b) -> b -> Map k a -> b
foldlWithKey _ z Tip = z
foldlWithKey f z (Bin _ k x l r) = foldlWithKey f (f (foldlWithKey f z l) k x) r

toList :: Map k a -> [(k, a)]
toList m = foldrWithKey (\\k x acc -> (k, x) : acc) [] m

toAscList :: Map k a -> [(k, a)]
toAscList m = toList m

toDescList :: Map k a -> [(k, a)]
toDescList m = foldlWithKey (\\acc k x -> (k, x) : acc) [] m

assocs :: Map k a -> [(k, a)]
assocs m = toList m

keys :: Map k a -> [k]
keys m = foldrWithKey (\\k _ acc -> k : acc) [] m

elems :: Map k a -> [a]
elems m = foldrWithKey (\\_ x acc -> x : acc) [] m

map :: (a -> b) -> Map k a -> Map k b
map _ Tip = Tip
map f (Bin n k x l r) = Bin n k (f x) (map f l) (map f r)

mapWithKey :: (k -> a -> b) -> Map k a -> Map k b
mapWithKey _ Tip = Tip
mapWithKey f (Bin n k x l r) = Bin n k (f k x) (mapWithKey f l) (mapWithKey f r)

filterWithKey :: Ord k => (k -> a -> Bool) -> Map k a -> Map k a
filterWithKey p m = fromList (filterEntries p (toList m))

filterEntries :: (k -> a -> Bool) -> [(k, a)] -> [(k, a)]
filterEntries _ [] = []
filterEntries p (e : es) = if keepEntry p e then e : filterEntries p es else filterEntries p es

keepEntry :: (k -> a -> Bool) -> (k, a) -> Bool
keepEntry p e = case e of
  (k, x) -> p k x

filter :: Ord k => (a -> Bool) -> Map k a -> Map k a
filter p m = filterWithKey (\\_ x -> p x) m

lookupMin :: Map k a -> Maybe (k, a)
lookupMin Tip = Nothing
lookupMin (Bin _ k x Tip _) = Just (k, x)
lookupMin (Bin _ _ _ (Bin n2 k2 x2 l2 r2) _) = lookupMin (Bin n2 k2 x2 l2 r2)

lookupMax :: Map k a -> Maybe (k, a)
lookupMax Tip = Nothing
lookupMax (Bin _ k x _ Tip) = Just (k, x)
lookupMax (Bin _ _ _ _ (Bin n2 k2 x2 l2 r2)) = lookupMax (Bin n2 k2 x2 l2 r2)

lookupGT :: Ord k => k -> Map k a -> Maybe (k, a)
lookupGT k m = listToMaybe (dropWhileKeyLE k (toList m))

dropWhileKeyLE :: Ord k => k -> [(k, a)] -> [(k, a)]
dropWhileKeyLE _ [] = []
dropWhileKeyLE k (p : ps) = if entryKeyLE k p then dropWhileKeyLE k ps else p : ps

entryKeyLE :: Ord k => k -> (k, a) -> Bool
entryKeyLE k p = case p of
  (k2, _) -> k2 <= k

instance Ord k => Semigroup (Map k a) where
  (<>) a b = union a b

instance Ord k => Monoid (Map k a) where
  mempty = Tip

instance Functor (Map k) where
  fmap f m = map f m

instance Foldable (Map k) where
  foldr f z m = foldrWithKey (\\_ x acc -> f x acc) z m

instance (Eq k, Eq a) => Eq (Map k a) where
  (==) a b = toList a == toList b
`,
  "Data.Map.Strict": `module Data.Map.Strict (module Data.Map) where
import Data.Map
`,
  "Data.IntMap": `module Data.IntMap (module Data.Map, IntMap) where
import Data.Map
type IntMap a = Map Int a
`,
  "Data.IntMap.Strict": `module Data.IntMap.Strict (module Data.Map, IntMap) where
import Data.Map
type IntMap a = Map Int a
`,
  "Data.Set": `module Data.Set where
import Data.Map (Map)
import qualified Data.Map as M

-- containers' own relationship: a \\\`Set\\\` is the same balanced tree as a \\\`Map\\\`,
-- carrying no values. The ordering guarantee that makes \\\`toList\\\` ascending is
-- therefore the same one.
type Set a = Map a ()

empty :: Set a
empty = M.empty

singleton :: a -> Set a
singleton x = M.singleton x ()

insert :: Ord a => a -> Set a -> Set a
insert x s = M.insert x () s

delete :: Ord a => a -> Set a -> Set a
delete x s = M.delete x s

member :: Ord a => a -> Set a -> Bool
member x s = M.member x s

notMember :: Ord a => a -> Set a -> Bool
notMember x s = not (member x s)

null :: Set a -> Bool
null s = M.null s

size :: Set a -> Int
size s = M.size s

toList :: Set a -> [a]
toList s = M.keys s

toAscList :: Set a -> [a]
toAscList s = M.keys s

elems :: Set a -> [a]
elems s = M.keys s

fromList :: Ord a => [a] -> Set a
fromList xs = M.fromList (withUnit xs)

withUnit :: [a] -> [(a, ())]
withUnit xs = case xs of
  [] -> []
  (y : ys) -> (y, ()) : withUnit ys

union :: Ord a => Set a -> Set a -> Set a
union a b = M.union a b

unions :: Ord a => [Set a] -> Set a
unions ss = M.unions ss

filter :: Ord a => (a -> Bool) -> Set a -> Set a
filter p s = M.filterWithKey (\\k _ -> p k) s

difference :: Ord a => Set a -> Set a -> Set a
difference a b = M.filterWithKey (\\k _ -> notMember k b) a

intersection :: Ord a => Set a -> Set a -> Set a
intersection a b = M.filterWithKey (\\k _ -> member k b) a
`,
  "Data.IntSet": `module Data.IntSet (module Data.Set, IntSet) where
import Data.Set
type IntSet = Set Int
`,
  "Data.JSString": `module Data.JSString where

-- A \`MisoString\` IS a JavaScript string, so every operation here is the
-- JavaScript one. Folding it into a \`[Char]\` first would give the same answers
-- through a different data structure, and \`Miso.String\` is on miso's hot path.
--
-- The wrapper is GHC's own shape for a JS value (\`data JSVal = JSVal JSVal#\`):
-- a raw JS string is not a heap object, so it cannot be entered, and only the
-- boxed form is safe in a lazy field or a polymorphic position. Every
-- operation unwraps, calls JavaScript, and rewraps.
data JSString = JSString JSStringPrim

foreign import javascript unsafe "((a,b) => a === b)" jsStringEq :: JSStringPrim -> JSStringPrim -> Bool
foreign import javascript unsafe "((a,b) => a < b)" jsStringLt :: JSStringPrim -> JSStringPrim -> Bool
foreign import javascript unsafe "((a,b) => a <= b)" jsStringLe :: JSStringPrim -> JSStringPrim -> Bool
foreign import javascript unsafe "((a,b) => a + b)" jsStringAppend :: JSStringPrim -> JSStringPrim -> JSStringPrim
foreign import javascript unsafe "((n) => '')" jsStringEmpty :: IntPrim -> JSStringPrim
foreign import javascript unsafe "((s) => s.length)" jsStringLength :: JSStringPrim -> IntPrim
foreign import javascript unsafe "((s,i) => s.codePointAt(i))" jsStringCodePointAt :: JSStringPrim -> IntPrim -> IntPrim
foreign import javascript unsafe "((s,c) => s + String.fromCodePoint(c))" jsStringSnoc :: JSStringPrim -> CharPrim -> JSStringPrim
foreign import javascript unsafe "((c) => String.fromCodePoint(c))" jsStringOfChar :: CharPrim -> JSStringPrim
foreign import javascript unsafe "((n,s) => s.slice(n))" jsStringDrop :: IntPrim -> JSStringPrim -> JSStringPrim
foreign import javascript unsafe "((n,s) => s.slice(0, n))" jsStringTake :: IntPrim -> JSStringPrim -> JSStringPrim
foreign import javascript unsafe "((s) => s.trim())" jsStringStrip :: JSStringPrim -> JSStringPrim
foreign import javascript unsafe "((s) => s.replace(/^\\\\s+/, ''))" jsStringStripStart :: JSStringPrim -> JSStringPrim
foreign import javascript unsafe "((s) => s.replace(/\\\\s+$/, ''))" jsStringStripEnd :: JSStringPrim -> JSStringPrim
foreign import javascript unsafe "((s) => s.toLowerCase())" jsStringToLower :: JSStringPrim -> JSStringPrim
foreign import javascript unsafe "((s) => s.toUpperCase())" jsStringToUpper :: JSStringPrim -> JSStringPrim
foreign import javascript unsafe "((s) => [...s].reverse().join(''))" jsStringReverse :: JSStringPrim -> JSStringPrim
foreign import javascript unsafe "((a,b) => b.startsWith(a))" jsStringIsPrefixOf :: JSStringPrim -> JSStringPrim -> Bool
foreign import javascript unsafe "((a,b) => b.endsWith(a))" jsStringIsSuffixOf :: JSStringPrim -> JSStringPrim -> Bool
foreign import javascript unsafe "((a,b) => b.includes(a))" jsStringIsInfixOf :: JSStringPrim -> JSStringPrim -> Bool
foreign import javascript unsafe "((n,s) => s.repeat(n < 0 ? 0 : n))" jsStringReplicate :: IntPrim -> JSStringPrim -> JSStringPrim
foreign import javascript unsafe "((sep,s) => s.split(sep).length)" jsStringSplitCount :: JSStringPrim -> JSStringPrim -> IntPrim
foreign import javascript unsafe "((sep,s,i) => s.split(sep)[i])" jsStringSplitAt :: JSStringPrim -> JSStringPrim -> IntPrim -> JSStringPrim

-- ------------------------------------------------------------------ core ---

empty :: JSString
empty = JSString (jsStringEmpty 0)

null :: JSString -> Bool
null (JSString s) = primIntEq (jsStringLength s) 0

length :: JSString -> Int
length (JSString s) = I (jsStringLength s)

append :: JSString -> JSString -> JSString
append (JSString a) (JSString b) = JSString (jsStringAppend a b)

singleton :: Char -> JSString
singleton (C c) = JSString (jsStringOfChar c)

cons :: Char -> JSString -> JSString
cons c s = append (singleton c) s

snoc :: JSString -> Char -> JSString
snoc (JSString s) (C c) = JSString (jsStringSnoc s c)

-- Code points, not UTF-16 code units: a \`Char\` is a code point in Haskell, so
-- an astral character must come out as one \`Char\` and advance the index by two.
unpack :: JSString -> [Char]
unpack (JSString s) = unpackFrom s 0 (jsStringLength s)

unpackFrom :: JSStringPrim -> IntPrim -> IntPrim -> [Char]
unpackFrom s i n = if primIntGe i n then [] else unpackStep s i n (jsStringCodePointAt s i)

unpackStep :: JSStringPrim -> IntPrim -> IntPrim -> IntPrim -> [Char]
unpackStep s i n cp =
  C (primChr cp) : unpackFrom s (primIntAdd i (if primIntGt cp 65535 then 2 else 1)) n

-- The \`case\` is not decoration: a JS string is a machine value, and a
-- *function call* in a constructor field is let-bound as a thunk. Scrutinising
-- it first is what puts the string, and not a thunk, in the field.
pack :: [Char] -> JSString
pack cs = case packOnto cs (jsStringEmpty 0) of
  s -> JSString s

packOnto :: [Char] -> JSStringPrim -> JSStringPrim
packOnto cs acc = case cs of
  [] -> acc
  (C c : rest) -> packOnto rest (jsStringSnoc acc c)

uncons :: JSString -> Maybe (Char, JSString)
uncons (JSString s) =
  if primIntEq (jsStringLength s) 0
    then Nothing
    else unconsAt s (jsStringCodePointAt s 0)

unconsAt :: JSStringPrim -> IntPrim -> Maybe (Char, JSString)
unconsAt s cp =
  Just (C (primChr cp), JSString (jsStringDrop (if primIntGt cp 65535 then 2 else 1) s))

head :: JSString -> Char
head s = case uncons s of
  Nothing -> error "Data.JSString.head: empty string"
  Just p -> fst p

tail :: JSString -> JSString
tail s = case uncons s of
  Nothing -> error "Data.JSString.tail: empty string"
  Just p -> snd p

index :: JSString -> Int -> Char
index (JSString s) (I i) = C (primChr (jsStringCodePointAt s i))

take :: Int -> JSString -> JSString
take (I n) (JSString s) = JSString (jsStringTake n s)

drop :: Int -> JSString -> JSString
drop (I n) (JSString s) = JSString (jsStringDrop n s)

splitAt :: Int -> JSString -> (JSString, JSString)
splitAt n s = (take n s, drop n s)

strip :: JSString -> JSString
strip (JSString s) = JSString (jsStringStrip s)

stripStart :: JSString -> JSString
stripStart (JSString s) = JSString (jsStringStripStart s)

stripEnd :: JSString -> JSString
stripEnd (JSString s) = JSString (jsStringStripEnd s)

toLower :: JSString -> JSString
toLower (JSString s) = JSString (jsStringToLower s)

toUpper :: JSString -> JSString
toUpper (JSString s) = JSString (jsStringToUpper s)

reverse :: JSString -> JSString
reverse (JSString s) = JSString (jsStringReverse s)

isPrefixOf :: JSString -> JSString -> Bool
isPrefixOf (JSString a) (JSString b) = jsStringIsPrefixOf a b

isSuffixOf :: JSString -> JSString -> Bool
isSuffixOf (JSString a) (JSString b) = jsStringIsSuffixOf a b

isInfixOf :: JSString -> JSString -> Bool
isInfixOf (JSString a) (JSString b) = jsStringIsInfixOf a b

stripPrefix :: JSString -> JSString -> Maybe JSString
stripPrefix a b = if isPrefixOf a b then Just (drop (length a) b) else Nothing

stripSuffix :: JSString -> JSString -> Maybe JSString
stripSuffix a b = if isSuffixOf a b then Just (take (length b - length a) b) else Nothing

replicate :: Int -> JSString -> JSString
replicate (I n) (JSString s) = JSString (jsStringReplicate n s)

concat :: [JSString] -> JSString
concat xs = foldlList append empty xs

concatMap :: (a -> JSString) -> [a] -> JSString
concatMap f xs = concat (mapList f xs)

intercalate :: JSString -> [JSString] -> JSString
intercalate sep xs = case xs of
  [] -> empty
  (y : ys) -> foldlList (\\acc z -> append (append acc sep) z) y ys

splitOn :: JSString -> JSString -> [JSString]
splitOn (JSString sep) (JSString s) = splitOnFrom sep s 0 (jsStringSplitCount sep s)

splitOnFrom :: JSStringPrim -> JSStringPrim -> IntPrim -> IntPrim -> [JSString]
splitOnFrom sep s i n =
  if primIntGe i n then [] else JSString (jsStringSplitAt sep s i) : splitOnFrom sep s (primIntAdd i 1) n

words :: JSString -> [JSString]
words s = filterList (\\w -> not (null w)) (splitOn (pack " ") (strip s))

unwords :: [JSString] -> JSString
unwords xs = intercalate (pack " ") xs

lines :: JSString -> [JSString]
lines s = splitOn (pack "\\n") s

unlines :: [JSString] -> JSString
unlines xs = concatMap (\\x -> append x (pack "\\n")) xs

foldl' :: (a -> Char -> a) -> a -> JSString -> a
foldl' f z s = foldlList f z (unpack s)

foldr :: (Char -> a -> a) -> a -> JSString -> a
foldr f z s = foldrList f z (unpack s)

map :: (Char -> Char) -> JSString -> JSString
map f s = pack (mapList f (unpack s))

mapList :: (a -> b) -> [a] -> [b]
mapList f xs = case xs of
  [] -> []
  (y : ys) -> f y : mapList f ys

filter :: (Char -> Bool) -> JSString -> JSString
filter p s = pack (filterList p (unpack s))

filterList :: (a -> Bool) -> [a] -> [a]
filterList p xs = case xs of
  [] -> []
  (y : ys) -> if p y then y : filterList p ys else filterList p ys

instance Eq JSString where
  (==) (JSString a) (JSString b) = jsStringEq a b

instance Ord JSString where
  (<) (JSString a) (JSString b) = jsStringLt a b
  (<=) (JSString a) (JSString b) = jsStringLe a b
  (>) (JSString a) (JSString b) = jsStringLt b a
  (>=) (JSString a) (JSString b) = jsStringLe b a

instance Semigroup JSString where
  (<>) a b = append a b

instance Monoid JSString where
  mempty = empty

instance IsString JSString where
  fromString cs = pack cs
`,
  "Data.Text": `module Data.Text (module Data.JSString, Text) where
import Data.JSString
type Text = JSString
`,
  "Data.JSString.Text": `module Data.JSString.Text where
import Data.JSString (JSString)
-- \\\`Text\\\` and \\\`JSString\\\` are the same type here (see Data.Text), so the two
-- conversions are the identity rather than a re-encoding.
textToJSString :: JSString -> JSString
textToJSString t = t
textFromJSString :: JSString -> JSString
textFromJSString s = s
lazyTextToJSString :: JSString -> JSString
lazyTextToJSString t = t
lazyTextFromJSString :: JSString -> JSString
lazyTextFromJSString s = s
`,
  "Data.Char": `module Data.Char where

-- Classification is JavaScript's, because JavaScript's regular expressions
-- carry the same Unicode general categories GHC's \\\`Data.Char\\\` is defined in
-- terms of. The ASCII-only predicates (\\\`isDigit\\\`, \\\`isHexDigit\\\`, \\\`isOctDigit\\\`)
-- are spelled out rather than using \\\\d, which in a Unicode regex is wider than
-- GHC's.
foreign import javascript unsafe "((c) => /\\\\p{Lu}|\\\\p{Lt}/u.test(String.fromCodePoint(c)))" jsIsUpper :: CharPrim -> Bool
foreign import javascript unsafe "((c) => /\\\\p{Ll}/u.test(String.fromCodePoint(c)))" jsIsLower :: CharPrim -> Bool
foreign import javascript unsafe "((c) => /\\\\p{L}/u.test(String.fromCodePoint(c)))" jsIsAlpha :: CharPrim -> Bool
foreign import javascript unsafe "((c) => /\\\\p{L}|\\\\p{Nd}|\\\\p{Nl}|\\\\p{No}/u.test(String.fromCodePoint(c)))" jsIsAlphaNum :: CharPrim -> Bool
foreign import javascript unsafe "((c) => /\\\\p{Cc}/u.test(String.fromCodePoint(c)))" jsIsControl :: CharPrim -> Bool
foreign import javascript unsafe "((c) => /\\\\p{P}|\\\\p{S}/u.test(String.fromCodePoint(c)))" jsIsPunctuation :: CharPrim -> Bool
foreign import javascript unsafe "((c) => /\\\\p{Zs}/u.test(String.fromCodePoint(c)))" jsIsUnicodeSpace :: CharPrim -> Bool
foreign import javascript unsafe "((c) => String.fromCodePoint(c).toLowerCase().codePointAt(0))" jsToLower :: CharPrim -> CharPrim
foreign import javascript unsafe "((c) => String.fromCodePoint(c).toUpperCase().codePointAt(0))" jsToUpper :: CharPrim -> CharPrim

isUpper :: Char -> Bool
isUpper (C c) = jsIsUpper c

isLower :: Char -> Bool
isLower (C c) = jsIsLower c

isAlpha :: Char -> Bool
isAlpha (C c) = jsIsAlpha c

isLetter :: Char -> Bool
isLetter c = isAlpha c

isAlphaNum :: Char -> Bool
isAlphaNum (C c) = jsIsAlphaNum c

isControl :: Char -> Bool
isControl (C c) = jsIsControl c

isPunctuation :: Char -> Bool
isPunctuation (C c) = jsIsPunctuation c

-- GHC: ' ', '\\t', '\\n', '\\v', '\\f', '\\r' and any Unicode space separator.
isSpace :: Char -> Bool
isSpace (C c) =
  if primCharEq c (primChr 32) then True
  else if primIntGe (primCharOrd c) 9 && primIntLe (primCharOrd c) 13 then True
  else jsIsUnicodeSpace c

isDigit :: Char -> Bool
isDigit (C c) = primIntGe (primCharOrd c) 48 && primIntLe (primCharOrd c) 57

isOctDigit :: Char -> Bool
isOctDigit (C c) = primIntGe (primCharOrd c) 48 && primIntLe (primCharOrd c) 55

isHexDigit :: Char -> Bool
isHexDigit c = isDigit c || inRangeChar c 97 102 || inRangeChar c 65 70

inRangeChar :: Char -> IntPrim -> IntPrim -> Bool
inRangeChar (C c) lo hi = primIntGe (primCharOrd c) lo && primIntLe (primCharOrd c) hi

isAscii :: Char -> Bool
isAscii (C c) = primIntLt (primCharOrd c) 128

toLower :: Char -> Char
toLower (C c) = C (jsToLower c)

toUpper :: Char -> Char
toUpper (C c) = C (jsToUpper c)

digitToInt :: Char -> Int
digitToInt c =
  if isDigit c then ord c - 48
  else if inRangeChar c 97 102 then ord c - 87
  else if inRangeChar c 65 70 then ord c - 55
  else error "Data.Char.digitToInt: not a digit"

intToDigit :: Int -> Char
intToDigit n = if n < 10 then chr (48 + n) else chr (87 + n)
`,
  "Data.List": `module Data.List where

-- Only the names the Prelude does not already provide. Everything else a
-- \\\`import Data.List\\\` brings in resolves to the Prelude, because a name this
-- module does not export is left exactly as written.

foldl' :: (b -> a -> b) -> b -> [a] -> b
foldl' f z xs = case xs of
  [] -> z
  (y : ys) -> seq (f z y) (foldl' f (f z y) ys)

nub :: Eq a => [a] -> [a]
nub xs = nubBy (==) xs

nubBy :: (a -> a -> Bool) -> [a] -> [a]
nubBy eq xs = case xs of
  [] -> []
  (y : ys) -> y : nubBy eq (filter (\\z -> not (eq y z)) ys)

-- A merge sort: stable, and O(n log n), which a repeated-insert sort is not.
sortBy :: (a -> a -> Ordering) -> [a] -> [a]
sortBy cmp xs = case xs of
  [] -> []
  (y : ys) -> case ys of
    [] -> y : []
    (z : zs) -> mergeSorted cmp (sortBy cmp (takeHalf xs)) (sortBy cmp (dropHalf xs))

takeHalf :: [a] -> [a]
takeHalf xs = take (halfLength xs) xs

dropHalf :: [a] -> [a]
dropHalf xs = drop (halfLength xs) xs

halfLength :: [a] -> Int
halfLength xs = quotInt (length xs) 2

quotInt :: Int -> Int -> Int
quotInt (I a) (I b) = I (primIntQuot a b)

mergeSorted :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
mergeSorted cmp xs ys = case xs of
  [] -> ys
  (a : as) -> case ys of
    [] -> xs
    (b : bs) -> if eqOrdering (cmp a b) GT then b : mergeSorted cmp xs bs else a : mergeSorted cmp as ys

sort :: Ord a => [a] -> [a]
sort xs = sortBy compare xs

sortOn :: Ord b => (a -> b) -> [a] -> [a]
sortOn f xs = sortBy (\\a b -> compare (f a) (f b)) xs

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

partition :: (a -> Bool) -> [a] -> ([a], [a])
partition p xs = (filter p xs, filter (\\x -> not (p x)) xs)

intersperse :: a -> [a] -> [a]
intersperse sep xs = case xs of
  [] -> []
  (y : ys) -> case ys of
    [] -> y : []
    (z : zs) -> y : sep : intersperse sep ys

intercalate :: [a] -> [[a]] -> [a]
intercalate sep xs = concat (intersperse sep xs)

isPrefixOf :: Eq a => [a] -> [a] -> Bool
isPrefixOf xs ys = case xs of
  [] -> True
  (a : as) -> case ys of
    [] -> False
    (b : bs) -> if a == b then isPrefixOf as bs else False

find :: (a -> Bool) -> [a] -> Maybe a
find p xs = listToMaybe (filter p xs)

subtract :: Num a => a -> a -> a
subtract x y = y - x
`,
  "Data.Function": `module Data.Function (id, const, flip, ($), (&), (.), on) where
on :: (b -> b -> c) -> (a -> b) -> a -> a -> c
on f g x y = f (g x) (g y)
`,
  "Data.Ord": `module Data.Ord (Ordering(LT, EQ, GT), comparing) where
comparing :: Ord b => (a -> b) -> a -> a -> Ordering
comparing f x y = compare (f x) (f y)
`,
  "GHC.JS.Prim": `module GHC.JS.Prim where

-- GHC's own shape: \\\`data JSVal = JSVal JSVal#\\\`. A raw JavaScript value is not
-- a heap object, so the box is what makes it storable and passable; every
-- operation unwraps it and calls JavaScript.
data JSVal = JSVal JSValPrim

foreign import javascript unsafe "((n) => null)" jsNullPrim :: IntPrim -> JSValPrim
foreign import javascript unsafe "((n) => undefined)" jsUndefinedPrim :: IntPrim -> JSValPrim
foreign import javascript unsafe "((x) => x === null)" jsIsNull :: JSValPrim -> Bool
foreign import javascript unsafe "((x) => x === undefined)" jsIsUndefined :: JSValPrim -> Bool
foreign import javascript unsafe "((x) => typeof x)" jsTypeOf :: JSValPrim -> JSStringPrim

jsNull :: JSVal
jsNull = JSVal (jsNullPrim 0)

jsUndefined :: JSVal
jsUndefined = JSVal (jsUndefinedPrim 0)

isNull :: JSVal -> Bool
isNull (JSVal x) = jsIsNull x

isUndefined :: JSVal -> Bool
isUndefined (JSVal x) = jsIsUndefined x
`,
  "GHC.JS.Foreign.Callback": `module GHC.JS.Foreign.Callback where
import GHC.JS.Prim

data OnBlocked = ThrowWouldBlock | ContinueAsync
data Callback a = Callback CallbackPrim

-- A callback is a JavaScript function that starts a Haskell thread, which is
-- what \`h$makeCallbackApply\` does in GHC. It is not reproduced verbatim
-- because its \`MK_JSVAL\` boxes into ghc-internal's \`JSVal\` constructor, which
-- a ghcts program does not link; the Haskell side here therefore takes the raw
-- value and boxes it itself.
--
-- What is kept is the part that matters: h$forkThread + h$startMainLoop
-- (which together are h$run) start a real thread, and the
-- callback is added to \`h$extraRoots\` so the GC cannot collect the closure it
-- holds. \`h$c2(h$ap1_e, g, x)\` is \`MK_AP1\` - the application \`g x\` as a thunk.
foreign import javascript unsafe "((g) => { const c = () => (h$forkThread(g, false), h$startMainLoop()); c._key = ++h$extraRootsN; c.root = g; h$extraRoots.add(c); return c; })" jsCallback0 :: (RealWorld -> IOResult ()) -> CallbackPrim
foreign import javascript unsafe "((g) => { const c = (x) => (h$forkThread(h$c2(h$ap1_e, g, x), false), h$startMainLoop()); c._key = ++h$extraRootsN; c.root = g; h$extraRoots.add(c); return c; })" jsCallback1 :: (JSValPrim -> RealWorld -> IOResult ()) -> CallbackPrim
foreign import javascript unsafe "((g) => { const c = (x,y) => (h$forkThread(h$c2(h$ap1_e, h$c2(h$ap1_e, g, x), y), false), h$startMainLoop()); c._key = ++h$extraRootsN; c.root = g; h$extraRoots.add(c); return c; })" jsCallback2 :: (JSValPrim -> JSValPrim -> RealWorld -> IOResult ()) -> CallbackPrim
foreign import javascript unsafe "((c) => { h$extraRoots.remove(c); c.root = null; })" jsReleaseCallback :: CallbackPrim -> IntPrim

asyncCallback :: IO () -> IO (Callback (IO ()))
asyncCallback action = IO (\\s -> callbackStep s (jsCallback0 (\\t -> unIO action t)))

asyncCallback1 :: (JSVal -> IO ()) -> IO (Callback (JSVal -> IO ()))
asyncCallback1 f = IO (\\s -> callbackStep s (jsCallback1 (\\x t -> unIO (f (JSVal x)) t)))

asyncCallback2 :: (JSVal -> JSVal -> IO ()) -> IO (Callback (JSVal -> JSVal -> IO ()))
asyncCallback2 f = IO (\\s -> callbackStep s (jsCallback2 (\\x y t -> unIO (f (JSVal x) (JSVal y)) t)))

-- A synchronous callback would have to run the action to completion before
-- returning, which needs \`h$runSync\` and its would-block handling. Until that
-- is modelled these are the asynchronous ones under the synchronous names,
-- which is a real difference: a \`syncCallback\` that returns before its action
-- has run would be a silent bug. They are therefore NOT defined here.

callbackStep :: RealWorld -> CallbackPrim -> IOResult (Callback a)
callbackStep s c = IOResult s (Callback c)

releaseCallback :: Callback a -> IO ()
releaseCallback (Callback c) = IO (\\s -> releaseStep s c)

releaseStep :: RealWorld -> CallbackPrim -> IOResult ()
releaseStep s c = case jsReleaseCallback c of
  _ -> IOResult s ()
`,
  "Control.Exception": `module Control.Exception where
import Data.JSString (JSString)

-- Only the JavaScript exception shape: this frontend has no \\\`Exception\\\` class
-- and no \\\`SomeException\\\` hierarchy, and \\\`throw\\\`/\\\`catch\\\` here are the JS
-- \\\`throw\\\` and \\\`try\\\`/\\\`catch\\\` a ghcts \\\`error\\\` already raises.
data SomeException = SomeException JSValPrim

foreign import javascript unsafe "((e) => { throw e; })" jsThrow :: JSValPrim -> IntPrim
foreign import javascript unsafe "((s) => new Error(s))" jsError :: JSStringPrim -> JSValPrim
foreign import javascript unsafe "((e) => String(e && e.message !== undefined ? e.message : e))" jsShowException :: JSValPrim -> JSStringPrim

displayException :: SomeException -> JSString
displayException (SomeException e) = case jsShowException e of
  s -> JSString s

throwIO :: SomeException -> IO a
throwIO (SomeException e) = IO (\\s -> throwStep s e)

throwStep :: RealWorld -> JSValPrim -> IOResult a
throwStep s e = case jsThrow e of
  _ -> IOResult s (error "Control.Exception.throwIO: unreachable")
`,
  "System.IO.Unsafe": `module System.IO.Unsafe (unsafePerformIO) where
`,
  // ------------------------------------------------------------------ mtl ---
  //
  // Every transformer below is ordinary Haskell, and deliberately so. A
  // transformer has no representation worth speaking of - it is a newtype over
  // a function - and its entire meaning is its \`Functor\`/\`Applicative\`/\`Monad\`
  // instances: which effect runs before which, what \`>>=\` threads, and what a
  // short circuit skips. None of that is expressible as a JavaScript shortcut,
  // and anything written in JavaScript here would have to reimplement lazy
  // evaluation to get it right.
  //
  // WHAT IS MISSING, AND WHY. mtl's \`MonadState\`/\`MonadReader\`/\`MonadWriter\`
  // are multi-parameter classes with functional dependencies (\`m -> s\`), and
  // \`src/elaborate.ts\` elaborates single-parameter classes only. So \`get\`,
  // \`ask\` and \`tell\` here are ordinary functions at their own transformer,
  // exactly as \`Control.Monad.Trans.State\` (transformers, not mtl) defines
  // them. Code that is polymorphic in the monad - miso's own \`Miso.Lens\`
  // operators, whose signatures read \`MonadState record m =>\` - therefore
  // still does not typecheck; a class faked with one parameter would have to
  // leave the state type free in the method signature, which the skolemised
  // instance-method check correctly rejects.
  //
  // \`MonadTrans\` is missing for the same shape of reason: \`lift :: Monad m =>
  // m a -> t m a\` puts a constraint on a *method*, which a class declaration
  // here cannot carry. Nothing in miso calls \`lift\`.
  "Data.Functor.Identity": `module Data.Functor.Identity (runIdentity) where

newtype Identity a = Identity a

runIdentity :: Identity a -> a
runIdentity (Identity x) = x

instance Functor Identity where
  fmap f m = Identity (f (runIdentity m))

instance Applicative Identity where
  pure x = Identity x
  (<*>) f m = Identity (runIdentity f (runIdentity m))

-- \\\`k\\\` is applied to the *unforced* contents, so \\\`runIdentity (undefined >>= f)\\\`
-- is \\\`f undefined\\\` and not bottom - which is what makes \\\`Identity\\\` the lazy
-- base monad the pure \\\`State\\\`/\\\`Writer\\\`/\\\`RWS\\\` are defined over.
instance Monad Identity where
  (>>=) m k = k (runIdentity m)

instance Eq a => Eq (Identity a) where
  (==) a b = runIdentity a == runIdentity b
`,
  "Control.Monad.Identity": `module Control.Monad.Identity (module Data.Functor.Identity) where
import Data.Functor.Identity
`,
  "Control.Monad.Reader": `module Control.Monad.Reader (runReaderT, runReader, ask, asks, reader, local, withReaderT) where
import Data.Functor.Identity

newtype ReaderT r m a = ReaderT (r -> m a)

type Reader r = ReaderT r Identity

runReaderT :: ReaderT r m a -> r -> m a
runReaderT (ReaderT f) r = f r

runReader :: Reader r a -> r -> a
runReader m r = runIdentity (runReaderT m r)

ask :: Monad m => ReaderT r m r
ask = ReaderT (\\r -> pure r)

asks :: Monad m => (r -> a) -> ReaderT r m a
asks f = ReaderT (\\r -> pure (f r))

reader :: Monad m => (r -> a) -> ReaderT r m a
reader f = asks f

local :: (r -> r) -> ReaderT r m a -> ReaderT r m a
local f m = ReaderT (\\r -> runReaderT m (f r))

withReaderT :: (r2 -> r) -> ReaderT r m a -> ReaderT r2 m a
withReaderT f m = ReaderT (\\r -> runReaderT m (f r))

instance Functor m => Functor (ReaderT r m) where
  fmap f m = ReaderT (\\r -> fmap f (runReaderT m r))

instance Applicative m => Applicative (ReaderT r m) where
  pure x = ReaderT (\\r -> pure x)
  (<*>) f m = ReaderT (\\r -> runReaderT f r <*> runReaderT m r)

instance Monad m => Monad (ReaderT r m) where
  (>>=) m k = ReaderT (\\r -> readerBind m k r)

readerBind :: Monad m => ReaderT r m a -> (a -> ReaderT r m b) -> r -> m b
readerBind m k r = runReaderT m r >>= (\\a -> runReaderT (k a) r)

-- The environment is not an effect, so lifting is just ignoring it. What this
-- instance buys is that a \\\`liftIO\\\` inside a \\\`ReaderT r IO\\\` runs at the point
-- the \\\`do\\\` block reaches it, in the base monad's own order.
instance MonadFail m => MonadFail (ReaderT r m) where
  fail msg = ReaderT (\\r -> fail msg)

instance MonadIO m => MonadIO (ReaderT r m) where
  liftIO io = ReaderT (\\r -> liftIO io)
`,
  "Control.Monad.State": `module Control.Monad.State (runStateT, runState, evalState, execState, evalStateT, execStateT, get, put, state, gets, modify, modify', withState) where
import Data.Functor.Identity

newtype StateT s m a = StateT (s -> m (a, s))

type State s = StateT s Identity

runStateT :: StateT s m a -> s -> m (a, s)
runStateT (StateT f) s = f s

runState :: State s a -> s -> (a, s)
runState m s = runIdentity (runStateT m s)

evalState :: State s a -> s -> a
evalState m s = fst (runState m s)

execState :: State s a -> s -> s
execState m s = snd (runState m s)

evalStateT :: Monad m => StateT s m a -> s -> m a
evalStateT m s = runStateT m s >>= (\\p -> pure (fst p))

execStateT :: Monad m => StateT s m a -> s -> m s
execStateT m s = runStateT m s >>= (\\p -> pure (snd p))

get :: Monad m => StateT s m s
get = StateT (\\s -> pure (s, s))

put :: Monad m => s -> StateT s m ()
put s = StateT (\\_ -> pure ((), s))

state :: Monad m => (s -> (a, s)) -> StateT s m a
state f = StateT (\\s -> pure (f s))

gets :: Monad m => (s -> a) -> StateT s m a
gets f = StateT (\\s -> pure (f s, s))

-- Lazy, as GHC's is: the new state is a thunk, so \\\`modify (+1)\\\` on a state
-- nobody looks at costs nothing and never diverges.
modify :: Monad m => (s -> s) -> StateT s m ()
modify f = StateT (\\s -> pure ((), f s))

-- \\\`modify'\\\` differs from \\\`modify\\\` only in the \\\`seq\\\`, and that is the whole
-- point of it: without forcing, a long fold leaves a chain of thunks in the
-- state instead of a value.
modify' :: Monad m => (s -> s) -> StateT s m ()
modify' f = StateT (\\s -> modifyStrictStep (f s))

modifyStrictStep :: Monad m => s -> m ((), s)
modifyStrictStep s = seq s (pure ((), s))

withState :: (s -> s) -> StateT s m a -> StateT s m a
withState f m = StateT (\\s -> runStateT m (f s))

instance Functor m => Functor (StateT s m) where
  fmap f m = StateT (\\s -> fmap (\\p -> stateMapStep f p) (runStateT m s))

stateMapStep :: (a -> b) -> (a, s) -> (b, s)
stateMapStep f p = case p of
  (a, s) -> (f a, s)

-- Written through the base monad's \\\`>>=\\\` rather than as \\\`ap\\\`, so the
-- \\\`Applicative\\\` dictionary does not have to reach back through the \\\`Monad\\\`
-- one that names it as a superclass.
instance Monad m => Applicative (StateT s m) where
  pure x = StateT (\\s -> pure (x, s))
  (<*>) f m = StateT (\\s -> stateAp f m s)

stateAp :: Monad m => StateT s m (a -> b) -> StateT s m a -> s -> m (b, s)
stateAp f m s = runStateT f s >>= (\\p -> stateApStep m p)

stateApStep :: Monad m => StateT s m a -> (a -> b, s) -> m (b, s)
stateApStep m p = case p of
  (g, s) -> runStateT m s >>= (\\q -> stateApFinish g q)

stateApFinish :: Monad m => (a -> b) -> (a, s) -> m (b, s)
stateApFinish g q = case q of
  (a, s) -> pure (g a, s)

-- The state threads left to right: \\\`m\\\` runs on the incoming state and \\\`k\\\`
-- runs on what \\\`m\\\` left. Matching the pair is what orders them.
instance Monad m => Monad (StateT s m) where
  (>>=) m k = StateT (\\s -> stateBind m k s)

stateBind :: Monad m => StateT s m a -> (a -> StateT s m b) -> s -> m (b, s)
stateBind m k s = runStateT m s >>= (\\p -> stateBindStep k p)

stateBindStep :: Monad m => (a -> StateT s m b) -> (a, s) -> m (b, s)
stateBindStep k p = case p of
  (a, s) -> runStateT (k a) s

instance MonadFail m => MonadFail (StateT s m) where
  fail msg = StateT (\\s -> fail msg)

instance MonadIO m => MonadIO (StateT s m) where
  liftIO io = StateT (\\s -> stateLiftIO io s)

stateLiftIO :: MonadIO m => IO a -> s -> m (a, s)
stateLiftIO io s = liftIO io >>= (\\a -> pure (a, s))
`,
  "Control.Monad.Writer": `module Control.Monad.Writer (runWriterT, runWriter, execWriter, execWriterT, writer, tell, listen, censor) where
import Data.Functor.Identity

newtype WriterT w m a = WriterT (m (a, w))

type Writer w = WriterT w Identity

runWriterT :: WriterT w m a -> m (a, w)
runWriterT (WriterT m) = m

runWriter :: Writer w a -> (a, w)
runWriter m = runIdentity (runWriterT m)

execWriter :: Writer w a -> w
execWriter m = snd (runWriter m)

execWriterT :: Monad m => WriterT w m a -> m w
execWriterT m = runWriterT m >>= (\\p -> pure (snd p))

writer :: Applicative m => (a, w) -> WriterT w m a
writer p = WriterT (pure p)

tell :: Applicative m => w -> WriterT w m ()
tell w = WriterT (pure ((), w))

listen :: Monad m => WriterT w m a -> WriterT w m (a, w)
listen m = WriterT (runWriterT m >>= (\\p -> listenStep p))

listenStep :: Monad m => (a, w) -> m ((a, w), w)
listenStep p = case p of
  (a, w) -> pure ((a, w), w)

censor :: Monad m => (w -> w) -> WriterT w m a -> WriterT w m a
censor f m = WriterT (runWriterT m >>= (\\p -> censorStep f p))

censorStep :: Monad m => (w -> w) -> (a, w) -> m (a, w)
censorStep f p = case p of
  (a, w) -> pure (a, f w)

instance Functor m => Functor (WriterT w m) where
  fmap f m = WriterT (fmap (\\p -> writerMapStep f p) (runWriterT m))

writerMapStep :: (a -> b) -> (a, w) -> (b, w)
writerMapStep f p = case p of
  (a, w) -> (f a, w)

instance (Monoid w, Monad m) => Applicative (WriterT w m) where
  pure x = WriterT (pure (x, mempty))
  (<*>) f m = WriterT (writerAp f m)

writerAp :: (Monoid w, Monad m) => WriterT w m (a -> b) -> WriterT w m a -> m (b, w)
writerAp f m = runWriterT f >>= (\\p -> writerApStep m p)

writerApStep :: (Monoid w, Monad m) => WriterT w m a -> (a -> b, w) -> m (b, w)
writerApStep m p = case p of
  (g, w) -> runWriterT m >>= (\\q -> writerApFinish g w q)

writerApFinish :: (Monoid w, Monad m) => (a -> b) -> w -> (a, w) -> m (b, w)
writerApFinish g w q = case q of
  (a, w2) -> pure (g a, w <> w2)

-- The output is appended in the order the actions ran, which is the only thing
-- a \\\`Writer\\\` promises and the only thing that makes \\\`tell\\\` useful: miso reads
-- back the \\\`[Schedule]\\\` an \\\`Effect\\\` accumulated and runs it in that order.
instance (Monoid w, Monad m) => Monad (WriterT w m) where
  (>>=) m k = WriterT (writerBind m k)

writerBind :: (Monoid w, Monad m) => WriterT w m a -> (a -> WriterT w m b) -> m (b, w)
writerBind m k = runWriterT m >>= (\\p -> writerBindStep k p)

writerBindStep :: (Monoid w, Monad m) => (a -> WriterT w m b) -> (a, w) -> m (b, w)
writerBindStep k p = case p of
  (a, w) -> runWriterT (k a) >>= (\\q -> writerBindFinish w q)

writerBindFinish :: (Monoid w, Monad m) => w -> (b, w) -> m (b, w)
writerBindFinish w q = case q of
  (b, w2) -> pure (b, w <> w2)

instance (Monoid w, MonadFail m) => MonadFail (WriterT w m) where
  fail msg = WriterT (fail msg)

instance (Monoid w, MonadIO m) => MonadIO (WriterT w m) where
  liftIO io = WriterT (writerLiftIO io)

writerLiftIO :: (Monoid w, MonadIO m) => IO a -> m (a, w)
writerLiftIO io = liftIO io >>= (\\a -> pure (a, mempty))
`,
  "Control.Monad.RWS": `module Control.Monad.RWS (runRWST, runRWS, evalRWS, execRWS, evalRWST, execRWST, rws, ask, asks, local, get, put, state, gets, modify, modify', tell, listen, censor) where
import Data.Functor.Identity

-- One pass, not \\\`ReaderT r (WriterT w (StateT s m))\\\`: miso's \\\`Effect\\\` is an
-- \\\`RWS\\\`, and the fused form is what \\\`execRWS\\\` can take apart in one \\\`case\\\`.
newtype RWST r w s m a = RWST (r -> s -> m (a, s, w))

type RWS r w s = RWST r w s Identity

runRWST :: RWST r w s m a -> r -> s -> m (a, s, w)
runRWST (RWST f) r s = f r s

runRWS :: RWS r w s a -> r -> s -> (a, s, w)
runRWS m r s = runIdentity (runRWST m r s)

evalRWS :: RWS r w s a -> r -> s -> (a, w)
evalRWS m r s = evalRWSStep (runRWS m r s)

evalRWSStep :: (a, s, w) -> (a, w)
evalRWSStep t = case t of
  (a, s, w) -> (a, w)

execRWS :: RWS r w s a -> r -> s -> (s, w)
execRWS m r s = execRWSStep (runRWS m r s)

execRWSStep :: (a, s, w) -> (s, w)
execRWSStep t = case t of
  (a, s, w) -> (s, w)

evalRWST :: Monad m => RWST r w s m a -> r -> s -> m (a, w)
evalRWST m r s = runRWST m r s >>= (\\t -> pure (evalRWSStep t))

execRWST :: Monad m => RWST r w s m a -> r -> s -> m (s, w)
execRWST m r s = runRWST m r s >>= (\\t -> pure (execRWSStep t))

rws :: Monad m => (r -> s -> (a, s, w)) -> RWST r w s m a
rws f = RWST (\\r s -> pure (f r s))

ask :: (Monoid w, Monad m) => RWST r w s m r
ask = RWST (\\r s -> pure (r, s, mempty))

asks :: (Monoid w, Monad m) => (r -> a) -> RWST r w s m a
asks f = RWST (\\r s -> pure (f r, s, mempty))

local :: (r -> r) -> RWST r w s m a -> RWST r w s m a
local f m = RWST (\\r s -> runRWST m (f r) s)

get :: (Monoid w, Monad m) => RWST r w s m s
get = RWST (\\r s -> pure (s, s, mempty))

put :: (Monoid w, Monad m) => s -> RWST r w s m ()
put s = RWST (\\r _ -> pure ((), s, mempty))

state :: (Monoid w, Monad m) => (s -> (a, s)) -> RWST r w s m a
state f = RWST (\\r s -> rwsStateStep (f s))

rwsStateStep :: (Monoid w, Monad m) => (a, s) -> m (a, s, w)
rwsStateStep p = case p of
  (a, s) -> pure (a, s, mempty)

gets :: (Monoid w, Monad m) => (s -> a) -> RWST r w s m a
gets f = RWST (\\r s -> pure (f s, s, mempty))

modify :: (Monoid w, Monad m) => (s -> s) -> RWST r w s m ()
modify f = RWST (\\r s -> pure ((), f s, mempty))

modify' :: (Monoid w, Monad m) => (s -> s) -> RWST r w s m ()
modify' f = RWST (\\r s -> rwsModifyStrict (f s))

rwsModifyStrict :: (Monoid w, Monad m) => s -> m ((), s, w)
rwsModifyStrict s = seq s (pure ((), s, mempty))

tell :: Monad m => w -> RWST r w s m ()
tell w = RWST (\\r s -> pure ((), s, w))

listen :: (Monoid w, Monad m) => RWST r w s m a -> RWST r w s m (a, w)
listen m = RWST (\\r s -> runRWST m r s >>= (\\t -> rwsListenStep t))

rwsListenStep :: (Monoid w, Monad m) => (a, s, w) -> m ((a, w), s, w)
rwsListenStep t = case t of
  (a, s, w) -> pure ((a, w), s, w)

censor :: (Monoid w, Monad m) => (w -> w) -> RWST r w s m a -> RWST r w s m a
censor f m = RWST (\\r s -> runRWST m r s >>= (\\t -> rwsCensorStep f t))

rwsCensorStep :: (Monoid w, Monad m) => (w -> w) -> (a, s, w) -> m (a, s, w)
rwsCensorStep f t = case t of
  (a, s, w) -> pure (a, s, f w)

instance Functor m => Functor (RWST r w s m) where
  fmap f m = RWST (\\r s -> fmap (\\t -> rwsMapStep f t) (runRWST m r s))

rwsMapStep :: (a -> b) -> (a, s, w) -> (b, s, w)
rwsMapStep f t = case t of
  (a, s, w) -> (f a, s, w)

instance (Monoid w, Monad m) => Applicative (RWST r w s m) where
  pure x = RWST (\\r s -> pure (x, s, mempty))
  (<*>) f m = RWST (\\r s -> rwsAp f m r s)

rwsAp :: (Monoid w, Monad m) => RWST r w s m (a -> b) -> RWST r w s m a -> r -> s -> m (b, s, w)
rwsAp f m r s = runRWST f r s >>= (\\t -> rwsApStep m r t)

rwsApStep :: (Monoid w, Monad m) => RWST r w s m a -> r -> (a -> b, s, w) -> m (b, s, w)
rwsApStep m r t = case t of
  (g, s, w) -> runRWST m r s >>= (\\u -> rwsApFinish g w u)

rwsApFinish :: (Monoid w, Monad m) => (a -> b) -> w -> (a, s, w) -> m (b, s, w)
rwsApFinish g w u = case u of
  (a, s, w2) -> pure (g a, s, w <> w2)

-- State threads forward and output appends, both in the order the actions run.
-- \\\`Effect\\\` is this monad, so \\\`value += 1\\\` followed by \\\`io_ act\\\` has to leave
-- the new model *and* the scheduled action, in that order.
instance (Monoid w, Monad m) => Monad (RWST r w s m) where
  (>>=) m k = RWST (\\r s -> rwsBind m k r s)

rwsBind :: (Monoid w, Monad m) => RWST r w s m a -> (a -> RWST r w s m b) -> r -> s -> m (b, s, w)
rwsBind m k r s = runRWST m r s >>= (\\t -> rwsBindStep k r t)

rwsBindStep :: (Monoid w, Monad m) => (a -> RWST r w s m b) -> r -> (a, s, w) -> m (b, s, w)
rwsBindStep k r t = case t of
  (a, s, w) -> runRWST (k a) r s >>= (\\u -> rwsBindFinish w u)

rwsBindFinish :: (Monoid w, Monad m) => w -> (b, s, w) -> m (b, s, w)
rwsBindFinish w u = case u of
  (b, s, w2) -> pure (b, s, w <> w2)

-- The base monad decides what failure means, exactly as transformers has it.
-- A pure \`RWS\` is \`RWST ... Identity\`, and \`Identity\` has no \`MonadFail\`, so
-- a refutable bind in a pure \`RWS\` is rejected here as GHC rejects it.
instance (Monoid w, MonadFail m) => MonadFail (RWST r w s m) where
  fail msg = RWST (\\r s -> fail msg)

instance (Monoid w, MonadIO m) => MonadIO (RWST r w s m) where
  liftIO io = RWST (\\r s -> rwsLiftIO io s)

rwsLiftIO :: (Monoid w, MonadIO m) => IO a -> s -> m (a, s, w)
rwsLiftIO io s = liftIO io >>= (\\a -> pure (a, s, mempty))
`,
  "Control.Monad.Trans.Maybe": `module Control.Monad.Trans.Maybe (runMaybeT, hoistMaybe) where

newtype MaybeT m a = MaybeT (m (Maybe a))

runMaybeT :: MaybeT m a -> m (Maybe a)
runMaybeT (MaybeT m) = m

hoistMaybe :: Applicative m => Maybe a -> MaybeT m a
hoistMaybe x = MaybeT (pure x)

instance Functor m => Functor (MaybeT m) where
  fmap f m = MaybeT (fmap (\\r -> maybeMap f r) (runMaybeT m))

instance Monad m => Applicative (MaybeT m) where
  pure x = MaybeT (pure (Just x))
  (<*>) f m = MaybeT (maybeTAp f m)

maybeTAp :: Monad m => MaybeT m (a -> b) -> MaybeT m a -> m (Maybe b)
maybeTAp f m = runMaybeT f >>= (\\r -> maybeTApStep m r)

maybeTApStep :: Monad m => MaybeT m a -> Maybe (a -> b) -> m (Maybe b)
maybeTApStep m r = case r of
  Nothing -> pure Nothing
  Just g -> runMaybeT (fmap g m)

-- The short circuit is the point: once the base action has produced
-- \\\`Nothing\\\`, \\\`k\\\` is never applied, so nothing after a failed step runs. A
-- version that ran \\\`k\\\` anyway would typecheck and be silently wrong.
instance Monad m => Monad (MaybeT m) where
  (>>=) m k = MaybeT (maybeTBind m k)

maybeTBind :: Monad m => MaybeT m a -> (a -> MaybeT m b) -> m (Maybe b)
maybeTBind m k = runMaybeT m >>= (\\r -> maybeTBindStep k r)

maybeTBindStep :: Monad m => (a -> MaybeT m b) -> Maybe a -> m (Maybe b)
maybeTBindStep k r = case r of
  Nothing -> pure Nothing
  Just a -> runMaybeT (k a)

-- A failed pattern bind in a \\\`do\\\` block calls \\\`fail\\\`, and in \\\`MaybeT\\\` that
-- has to be the same short circuit rather than an error: \\\`Just x <- act\\\` is
-- how miso's JSON decoder gives up on a field.
instance Monad m => MonadFail (MaybeT m) where
  fail s = MaybeT (pure Nothing)

instance Monad m => Alternative (MaybeT m) where
  empty = MaybeT (pure Nothing)
  (<|>) a b = MaybeT (maybeTOr a b)

maybeTOr :: Monad m => MaybeT m a -> MaybeT m a -> m (Maybe a)
maybeTOr a b = runMaybeT a >>= (\\r -> maybeTOrStep b r)

maybeTOrStep :: Monad m => MaybeT m a -> Maybe a -> m (Maybe a)
maybeTOrStep b r = case r of
  Nothing -> runMaybeT b
  Just x -> pure (Just x)

instance MonadIO m => MonadIO (MaybeT m) where
  liftIO io = MaybeT (maybeTLiftIO io)

maybeTLiftIO :: MonadIO m => IO a -> m (Maybe a)
maybeTLiftIO io = liftIO io >>= (\\a -> pure (Just a))
`,
  // ----------------------------------------------------------- marshalling ---
  "GHCJS.Types": `module GHCJS.Types (jsval) where
import GHC.JS.Prim (JSVal)
import Data.JSString (JSString)

-- ghcjs-base's \\\`class IsJSVal a where jsval :: a -> JSVal\\\`. Every instance is
-- a *representational* identity - the wrapped thing already IS the JavaScript
-- value - so the conversion is JavaScript's identity function and not any
-- Haskell work. The \\\`case\\\` is what keeps the unwrapped machine value out of a
-- lazy constructor field.
class IsJSVal a where
  jsval :: a -> JSVal

foreign import javascript unsafe "((x) => x)" jsIdentity :: JSStringPrim -> JSValPrim

instance IsJSVal JSVal where
  jsval x = x

instance IsJSVal JSString where
  jsval (JSString s) = case jsIdentity s of
    v -> JSVal v
`,
  "GHCJS.Marshal": `module GHCJS.Marshal (toJSVal, fromJSVal, fromJSValUnchecked) where
import GHC.JS.Prim
import Data.JSString (JSString)

-- THE JAVASCRIPT BOUNDARY, and therefore FFI rather than Haskell. Converting
-- an \\\`Int\\\` to a JS number is not a computation with a Haskell meaning to
-- preserve - it is the identity on the machine value - and a \\\`fromJSVal\\\` that
-- inspected a Haskell mirror of the JS value would answer differently from one
-- that asked JavaScript.
--
-- The class is named \\\`ToJSValue\\\`, not \\\`ToJSVal\\\`, on purpose: classes live in
-- one global namespace in this frontend, and miso declares its own
-- \\\`ToJSVal\\\`/\\\`FromJSVal\\\` in \\\`Miso.DSL\\\` (with a \\\`Generic\\\` default). Two
-- declarations of one class name would merge into whichever came last, and
-- miso's instances would lose their default method. The exported names are the
-- ghcjs-base ones, which is what \\\`Marshal.toJSVal\\\` resolves to.
class ToJSValue a where
  toJSValue :: a -> IO JSVal

class FromJSValue a where
  fromJSValue :: JSVal -> IO (Maybe a)
  fromJSValueUnchecked :: JSVal -> IO a
  fromJSValueUnchecked x = fromJSValue x >>= forceJSValue

forceJSValue :: Maybe a -> IO a
forceJSValue m = case m of
  Nothing -> error "GHCJS.Marshal.fromJSValUnchecked: type mismatch"
  Just x -> pure x

toJSVal :: ToJSValue a => a -> IO JSVal
toJSVal x = toJSValue x

fromJSVal :: FromJSValue a => JSVal -> IO (Maybe a)
fromJSVal x = fromJSValue x

fromJSValUnchecked :: FromJSValue a => JSVal -> IO a
fromJSValUnchecked x = fromJSValueUnchecked x

foreign import javascript unsafe "((b) => b)" boolToVal :: Bool -> JSValPrim
foreign import javascript unsafe "((n) => n)" intToVal :: IntPrim -> JSValPrim
foreign import javascript unsafe "((d) => d)" doubleToVal :: DoublePrim -> JSValPrim
foreign import javascript unsafe "((s) => s)" stringToVal :: JSStringPrim -> JSValPrim
foreign import javascript unsafe "((c) => String.fromCodePoint(c))" charToVal :: CharPrim -> JSValPrim
foreign import javascript unsafe "((n) => [])" newArrayVal :: IntPrim -> JSValPrim
foreign import javascript unsafe "((a,x) => { a.push(x); return 0; })" pushArrayVal :: JSValPrim -> JSValPrim -> IntPrim
foreign import javascript unsafe "((x) => typeof x === 'boolean')" isBoolVal :: JSValPrim -> Bool
foreign import javascript unsafe "((x) => typeof x === 'number')" isNumberVal :: JSValPrim -> Bool
foreign import javascript unsafe "((x) => typeof x === 'string')" isStringVal :: JSValPrim -> Bool
foreign import javascript unsafe "((x) => Array.isArray(x))" isArrayVal :: JSValPrim -> Bool
foreign import javascript unsafe "((x) => x === null || x === undefined)" isNullishVal :: JSValPrim -> Bool
foreign import javascript unsafe "((x) => x)" valToBool :: JSValPrim -> Bool
foreign import javascript unsafe "((x) => x)" valToDouble :: JSValPrim -> DoublePrim
foreign import javascript unsafe "((x) => x | 0)" valToInt :: JSValPrim -> IntPrim
foreign import javascript unsafe "((x) => x)" valToString :: JSValPrim -> JSStringPrim
foreign import javascript unsafe "((x) => x.codePointAt(0))" valToChar :: JSValPrim -> CharPrim
foreign import javascript unsafe "((x) => x.length)" arrayLengthVal :: JSValPrim -> IntPrim
foreign import javascript unsafe "((x,i) => x[i])" arrayIndexVal :: JSValPrim -> IntPrim -> JSValPrim

-- Every one of these names its foreign result with a \\\`case\\\` before boxing it:
-- a machine value in a lazy \\\`JSVal\\\` field would be a thunk, and the next
-- JavaScript call on it would see a closure.
pureVal :: JSValPrim -> IO JSVal
pureVal v = IO (\\s -> IOResult s (JSVal v))

instance ToJSValue JSVal where
  toJSValue x = pure x

instance ToJSValue Bool where
  toJSValue b = case boolToVal b of
    v -> pureVal v

instance ToJSValue Int where
  toJSValue (I n) = case intToVal n of
    v -> pureVal v

instance ToJSValue Double where
  toJSValue (DoubleBox d) = case doubleToVal d of
    v -> pureVal v

instance ToJSValue Char where
  toJSValue (C c) = case charToVal c of
    v -> pureVal v

instance ToJSValue JSString where
  toJSValue (JSString s) = case stringToVal s of
    v -> pureVal v

instance ToJSValue () where
  toJSValue x = pure jsNull

-- \\\`Nothing\\\` is \\\`null\\\`, which is what makes the \\\`FromJSValue (Maybe a)\\\`
-- instance below its inverse.
instance ToJSValue a => ToJSValue (Maybe a) where
  toJSValue m = case m of
    Nothing -> pure jsNull
    Just x -> toJSValue x

instance ToJSValue a => ToJSValue [a] where
  toJSValue xs = newArray >>= (\\a -> pushAll a xs)

newArray :: IO JSVal
newArray = case newArrayVal 0 of
  v -> pureVal v

pushAll :: ToJSValue a => JSVal -> [a] -> IO JSVal
pushAll a xs = case xs of
  [] -> pure a
  (y : ys) -> toJSValue y >>= (\\v -> pushOne a v >> pushAll a ys)

pushOne :: JSVal -> JSVal -> IO ()
pushOne (JSVal a) (JSVal v) = IO (\\s -> pushStep s a v)

pushStep :: RealWorld -> JSValPrim -> JSValPrim -> IOResult ()
pushStep s a v = case pushArrayVal a v of
  _ -> IOResult s ()

instance FromJSValue JSVal where
  fromJSValue x = pure (Just x)
  fromJSValueUnchecked x = pure x

instance FromJSValue Bool where
  fromJSValue (JSVal x) = if isBoolVal x then fromBoolStep x else pure Nothing

fromBoolStep :: JSValPrim -> IO (Maybe Bool)
fromBoolStep x = case valToBool x of
  b -> pure (Just b)

instance FromJSValue Int where
  fromJSValue (JSVal x) = if isNumberVal x then fromIntStep x else pure Nothing

fromIntStep :: JSValPrim -> IO (Maybe Int)
fromIntStep x = case valToInt x of
  n -> pure (Just (I n))

instance FromJSValue Double where
  fromJSValue (JSVal x) = if isNumberVal x then fromDoubleStep x else pure Nothing

fromDoubleStep :: JSValPrim -> IO (Maybe Double)
fromDoubleStep x = case valToDouble x of
  d -> pure (Just (DoubleBox d))

instance FromJSValue JSString where
  fromJSValue (JSVal x) = if isStringVal x then fromStringStep x else pure Nothing

fromStringStep :: JSValPrim -> IO (Maybe JSString)
fromStringStep x = case valToString x of
  s -> pure (Just (JSString s))

instance FromJSValue Char where
  fromJSValue (JSVal x) = if isStringVal x then fromCharStep x else pure Nothing

fromCharStep :: JSValPrim -> IO (Maybe Char)
fromCharStep x = case valToChar x of
  c -> pure (Just (C c))

-- \\\`null\\\` and \\\`undefined\\\` both decode as \\\`Just Nothing\\\` - the conversion
-- succeeded and produced an absence - which is what distinguishes this from
-- the \\\`Nothing\\\` that means "not this type at all".
instance FromJSValue a => FromJSValue (Maybe a) where
  fromJSValue (JSVal x) = if isNullishVal x then pure (Just Nothing) else fromJustStep (JSVal x)

fromJustStep :: FromJSValue a => JSVal -> IO (Maybe (Maybe a))
fromJustStep x = fromJSValue x >>= (\\r -> pure (maybeMap Just r))

instance FromJSValue a => FromJSValue [a] where
  fromJSValue (JSVal x) = if isArrayVal x then fromArrayStep x 0 (arrayLengthVal x) else pure Nothing

fromArrayStep :: FromJSValue a => JSValPrim -> IntPrim -> IntPrim -> IO (Maybe [a])
fromArrayStep x i n =
  if primIntGe i n then pure (Just []) else fromArrayAt x i n (arrayIndexVal x i)

fromArrayAt :: FromJSValue a => JSValPrim -> IntPrim -> IntPrim -> JSValPrim -> IO (Maybe [a])
fromArrayAt x i n e = fromJSValue (JSVal e) >>= (\\r -> fromArrayCons x i n r)

fromArrayCons :: FromJSValue a => JSValPrim -> IntPrim -> IntPrim -> Maybe a -> IO (Maybe [a])
fromArrayCons x i n r = case r of
  Nothing -> pure Nothing
  Just y -> fromArrayStep x (primIntAdd i 1) n >>= (\\rest -> pure (maybeMap (\\ys -> y : ys) rest))
`,
};

/** Modules already provided by the project win; everything a library module
 * itself imports is pulled in the same way, transitively. */
export function withLibraryModules(modules: ReadonlyMap<string, Module>): ReadonlyMap<string, Module> {
  const out = new Map(modules);
  const queue = [...modules.values()].flatMap((m) => m.imports.map((i) => i.module));
  while (queue.length) {
    const name = queue.pop()!;
    if (out.has(name)) continue;
    const source = sources[name];
    if (source === undefined) continue;
    const parsed = parseModule(source, `${name.replace(/\./g, "/")}.hs`);
    if (!parsed.module?.ast || parsed.diagnostics.some((d) => d.severity === "error")) {
      throw new Error(
        `ghcts library module ${name} does not parse: ${parsed.diagnostics.map((d) => d.message).join("; ")}`,
      );
    }
    out.set(name, parsed.module.ast);
    for (const imported of parsed.module.ast.imports) queue.push(imported.module);
  }
  return out;
}
