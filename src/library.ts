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
  "Control.Concurrent": `module Control.Concurrent (module Control.Concurrent.MVar, ThreadId, ThreadStatus(..), forkIO, killThread, threadStatus, threadDelay, yield) where
import Control.Concurrent.MVar

data ThreadId = ThreadId ThreadIdPrim

-- GHC's constructors and GHC's order. \`ThreadBlocked\` carries a
-- \`BlockReason\` in GHC; \`h\$threadStatus\` reports one blocked state and no
-- reason, so there is nothing to carry.
data ThreadStatus = ThreadRunning | ThreadFinished | ThreadBlocked | ThreadDied

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

foreign import javascript unsafe "((t) => new Error('thread killed'))" jsThreadKilled :: ThreadIdPrim -> JSValPrim
foreign import javascript unsafe "((t) => h\$threadStatus(t))" jsThreadStatus :: ThreadIdPrim -> IntPrim
-- \`killThread#\`, not a foreign call: killing the *current* thread means
-- never returning to the caller, and \`h\$killThread\` says so by handing back
-- the continuation to jump to instead. Only a primop can be compiled that way
-- (\`PRPrimCall\` in the backend); a \`foreign import javascript unsafe\` is a
-- plain call whose value is assigned to a register.
killThread :: ThreadId -> IO ()
killThread t = IO (\\s -> killThreadStep s t)

killThreadStep :: RealWorld -> ThreadId -> IOResult ()
killThreadStep s (ThreadId t) = case primKillThread t (jsThreadKilled t) s of
  _ -> IOResult s ()

-- GHC's \`threadStatus#\` returns \`(# status, capability, locked #)\`, and only
-- the first of the three is ever asked for here. The status numbers are the
-- RTS's own (\`src/stg-js/rts-static.ts\`): running 0, blocked 1, finished 16,
-- died 17.
threadStatus :: ThreadId -> IO ThreadStatus
threadStatus t = IO (\\s -> threadStatusStep s t)

threadStatusStep :: RealWorld -> ThreadId -> IOResult ThreadStatus
threadStatusStep s (ThreadId t) = case jsThreadStatus t of
  n -> IOResult s (toThreadStatus n)

toThreadStatus :: IntPrim -> ThreadStatus
toThreadStatus n = if primIntEq n 0 then ThreadRunning else (if primIntEq n 1 then ThreadBlocked else (if primIntEq n 16 then ThreadFinished else ThreadDied))
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

-- containers shows a map as the call that rebuilds it, at precedence 10 so a
-- nested one is parenthesised.
instance (Show k, Show a) => Show (Map k a) where
  showsPrec d m r = showParen (d > 10) (\\rest -> showString "fromList " (showsPrec 11 (toList m) rest)) r

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
  // containers' \`Seq\` is a finger tree, and its two *pattern synonyms* -
  // \`Empty\` and \`(:<|)\` - are how every consumer takes it apart. This parser
  // has no pattern synonyms, so the sequence is declared with those two
  // spellings as its real constructors: a cons list, matched exactly the way
  // miso's \`Miso.Runtime\` matches a \`Seq\`.
  //
  // What that costs and what it does not. Every answer is the same - the
  // element order, the folds, the equality, the \`Semigroup\`. What changes is
  // asymptotics: \`|>\` and \`<>\` are O(n) here where a finger tree gives O(1)
  // and O(log n). The queues miso puts in a \`Seq\` hold the actions pending for
  // one component between two frames, so the difference is a constant factor
  // on a short list, not a change of behaviour.
  "Data.Sequence": `module Data.Sequence where

data Seq a = Empty | (:<|) a (Seq a)

instance Show a => Show (Seq a) where
  showsPrec d s r = showParen (d > 10) (\\rest -> showString "fromList " (showsPrec 11 (seqToList s) rest)) r

seqToList :: Seq a -> [a]
seqToList s = case s of
  Empty -> []
  (x :<| xs) -> x : seqToList xs

empty :: Seq a
empty = Empty

singleton :: a -> Seq a
singleton x = x :<| Empty

-- Append at the right, which is the whole reason miso reaches for a \\\`Seq\\\`.
(|>) :: Seq a -> a -> Seq a
(|>) s x = case s of
  Empty -> x :<| Empty
  (y :<| ys) -> y :<| (ys |> x)

(<|) :: a -> Seq a -> Seq a
(<|) x s = x :<| s

fromList :: [a] -> Seq a
fromList xs = case xs of
  [] -> Empty
  (y : ys) -> y :<| fromList ys

filter :: (a -> Bool) -> Seq a -> Seq a
filter p s = case s of
  Empty -> Empty
  (y :<| ys) -> if p y then y :<| filter p ys else filter p ys

-- The longest prefix whose elements satisfy the predicate, and the rest.
spanl :: (a -> Bool) -> Seq a -> (Seq a, Seq a)
spanl p s = case s of
  Empty -> (Empty, Empty)
  (y :<| ys) ->
    if p y
      then case spanl p ys of
        (before, after) -> (y :<| before, after)
      else (Empty, s)

splitAt :: Int -> Seq a -> (Seq a, Seq a)
splitAt n s =
  if n <= 0
    then (Empty, s)
    else case s of
      Empty -> (Empty, Empty)
      (y :<| ys) -> case splitAt (n - 1) ys of
        (before, after) -> (y :<| before, after)

reverseSeq :: Seq a -> Seq a
reverseSeq s = fromList (reverse (seqToList s))

seqToList :: Seq a -> [a]
seqToList s = case s of
  Empty -> []
  (y :<| ys) -> y : seqToList ys

instance Functor Seq where
  fmap f s = case s of
    Empty -> Empty
    (y :<| ys) -> f y :<| fmap f ys

instance Foldable Seq where
  foldr f z s = case s of
    Empty -> z
    (y :<| ys) -> f y (foldr f z ys)

instance Eq a => Eq (Seq a) where
  (==) a b = case a of
    Empty -> case b of
      Empty -> True
      _ -> False
    (x :<| xs) -> case b of
      Empty -> False
      (y :<| ys) -> if x == y then xs == ys else False

instance Semigroup (Seq a) where
  (<>) a b = case a of
    Empty -> b
    (x :<| xs) -> x :<| (xs <> b)

instance Monoid (Seq a) where
  mempty = Empty
`,
  // \`readHex\`/\`showHex\` are what miso's \`Fingerprint\` marshalling is written
  // in; the rest of \`Numeric\` is not used and not here.
  "Numeric": `module Numeric where

-- GHC's \\\`readHex\\\` is a \\\`ReadS\\\`: it returns the value and the unconsumed
-- input, and the empty list when the first character is not a hex digit.
readHex :: [Char] -> [(Int, [Char])]
readHex cs = case hexDigit cs of
  Nothing -> []
  Just _ -> readHexGo 0 cs

readHexGo :: Int -> [Char] -> [(Int, [Char])]
readHexGo acc cs = case cs of
  [] -> (acc, []) : []
  (c : rest) -> case hexDigit (c : rest) of
    Nothing -> (acc, c : rest) : []
    Just d -> readHexGo (acc * 16 + d) rest

hexDigit :: [Char] -> Maybe Int
hexDigit cs = case cs of
  [] -> Nothing
  (c : _) ->
    let n = ord c
    in if n >= 48 && n <= 57
         then Just (n - 48)
         else if n >= 97 && n <= 102
           then Just (n - 87)
           else if n >= 65 && n <= 70 then Just (n - 55) else Nothing

showHex :: Int -> [Char] -> [Char]
showHex n rest = if n < 0 then rest else showHexGo n rest

showHexGo :: Int -> [Char] -> [Char]
showHexGo n rest =
  let d = hexChar (remInt n 16)
      q = quotInt n 16
  in if q == 0 then d : rest else showHexGo q (d : rest)

hexChar :: Int -> Char
hexChar n = chr (if n < 10 then 48 + n else 87 + n)

quotInt :: Int -> Int -> Int
quotInt (I a) (I b) = I (primIntQuot a b)

remInt :: Int -> Int -> Int
remInt (I a) (I b) = I (primIntRem a b)
`,
  // \`Ix\` is a class in GHC; every use miso makes of it is \`inRange\` on a pair
  // of \`Char\`s or \`Int\`s, so the class is the one method those two need.
  "Data.Ix": `module Data.Ix where

class Ord a => Ix a where
  inRange :: (a, a) -> a -> Bool
  inRange bounds x = case bounds of
    (lo, hi) -> lo <= x && x <= hi

instance Ix Int
instance Ix Char
`,
  "Data.Bifunctor": `module Data.Bifunctor where

class Bifunctor p where
  bimap :: (a -> b) -> (c -> d) -> p a c -> p b d
  first :: (a -> b) -> p a c -> p b c
  second :: (c -> d) -> p a c -> p a d
  first f x = bimap f (\\y -> y) x
  second g x = bimap (\\y -> y) g x

instance Bifunctor Either where
  bimap f g e = case e of
    Left a -> Left (f a)
    Right c -> Right (g c)

instance Bifunctor (,) where
  bimap f g p = case p of
    (a, c) -> (f a, g c)
`,
  // \`Const\` is the applicative \`Miso.Lens\` reads a van Laarhoven lens with;
  // \`Identity\` is the one it writes with.
  "Data.Functor.Const": `module Data.Functor.Const where

newtype Const a b = Const { getConst :: a }

instance Functor (Const a) where
  fmap f c = case c of
    Const x -> Const x
`,
  "Control.Category": `module Control.Category (Category(..), (>>>), (<<<)) where

-- GHC's \`Category\` is over \`k -> k -> Type\`; this frontend has no kinds, and
-- the class means the same without one. \`id\` and \`(.)\` are methods, not the
-- Prelude's functions, which is the whole point: miso writes
-- \`import Prelude hiding ((.))\` next to \`import Control.Category ((.))\` so
-- that \`.\` composes lenses. Both names stay scoped to this module, so a
-- program that does not import it keeps the Prelude's \`.\` unchanged.
class Category cat where
  id :: cat a a
  (.) :: cat b c -> cat a b -> cat a c

instance Category (->) where
  id = Prelude.id
  (.) f g = \\x -> f (g x)

(>>>) :: Category cat => cat a b -> cat b c -> cat a c
(>>>) f g = g . f

(<<<) :: Category cat => cat b c -> cat a b -> cat a c
(<<<) f g = f . g
`,
  "Control.Arrow": `module Control.Arrow (module Control.Category) where
import Control.Category
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

-- GHC's \`Show Text\`/\`Show JSString\`: a text value prints as the \`String\` it
-- denotes, quotes, escapes and all.
instance Show JSString where
  showsPrec d s r = showList (unpack s) r

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

-- The qualified spelling Data.List.foldl' is common; the Prelude's is the
-- Foldable one, over the same list.
foldl' :: (b -> a -> b) -> b -> [a] -> b
foldl' f z xs = foldlStrict f z xs

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

`,
  "Data.Function": `module Data.Function (id, const, flip, ($), (&), (.), on) where
on :: (b -> b -> c) -> (a -> b) -> a -> a -> c
on f g x y = f (g x) (g y)
`,
  "Data.Ord": `module Data.Ord (Ordering(LT, EQ, GT), comparing) where
comparing :: Ord b => (a -> b) -> a -> a -> Ordering
comparing f x y = compare (f x) (f y)
`,
  // \`Proxy\` carries nothing; it exists so that a type can be passed where a
  // value is expected. That is all it is in GHC too.
  "Data.Proxy": `module Data.Proxy where

data Proxy t = Proxy

instance Eq (Proxy t) where
  (==) a b = True

instance Show (Proxy t) where
  show p = "Proxy"

instance Functor Proxy where
  fmap f p = Proxy

instance Semigroup (Proxy t) where
  (<>) a b = Proxy

instance Monoid (Proxy t) where
  mempty = Proxy

asProxyTypeOf :: a -> proxy a -> a
asProxyTypeOf x p = x
`,
  // GHC.Generics, as far as a compiler with no type families can express it.
  //
  // The representation types are ordinary Haskell and nothing else would do:
  // `M1`, `K1`, `U1`, `(:*:)` and `(:+:)` exist to be *pattern matched* by
  // generic code, so they have to be real data constructors with real fields.
  //
  // WHAT THE `Rep` TYPE FAMILY BECAME, AND WHY. GHC declares
  //
  //   class Generic a where { type Rep a; from :: a -> Rep a x; ... }
  //
  // and `Rep` is an associated *type family*. This elaborator has none. It
  // does have multi-parameter classes with functional dependencies, and an
  // associated type of one class parameter is exactly a second parameter the
  // first determines, so `Generic` is declared as
  //
  //   class Generic a rep | a -> rep
  //
  // and `src/elaborate.ts` reads a written `Rep a` back as "the `rep` that
  // `Generic a rep` improves to". That is a faithful reading of what the
  // family means, and it is where the faithfulness stops: `Rep a` cannot be
  // *computed* here, only solved for, so it may only appear where a
  // constraint can be added - a signature's context - and never as, say, the
  // right-hand side of a type synonym.
  //
  // WHAT IS MISSING. There is no `deriving Generic`: nothing here synthesises
  // an instance from a data declaration, so every `Generic` instance is one
  // somebody wrote. `Meta`/`MetaData`/`MetaCons`/`MetaSel` are absent for the
  // same reason they would be useless - they are built from type-level
  // strings, and this frontend has no `Symbol` kind - so the metadata classes
  // below take whatever nullary type a hand-written instance names.
  "GHC.Generics": `module GHC.Generics where

-- \\\`V1\\\` is GHC's empty representation - the one a type with no constructors
-- has. It is declared with a constructor here only because a data declaration
-- with no right-hand side is not syntax this parser accepts; nothing may build
-- one, and the name is deliberately unusable.
data V1 p = V1Impossible
data U1 p = U1
data K1 i c p = K1 c
data M1 i c f p = M1 (f p)
data (:+:) f g p = L1 (f p) | R1 (g p)
data (:*:) f g p = (:*:) (f p) (g p)
data Par1 p = Par1 p
data Rec1 f p = Rec1 (f p)

-- The four tags that index \\\`M1\\\` and \\\`K1\\\`. They are phantom, so they need no
-- constructors of their own beyond something to declare.
data D = DTag
data C = CTag
data S = STag
data R = RTag

type D1 c f = M1 D c f
type C1 c f = M1 C c f
type S1 c f = M1 S c f
type Rec0 c = K1 R c
type Par0 c = K1 R c

unM1 :: M1 i c f p -> f p
unM1 (M1 x) = x

unK1 :: K1 i c p -> c
unK1 (K1 x) = x

data Associativity = LeftAssociative | RightAssociative | NotAssociative
data Fixity = Prefix | Infix Associativity Int

instance Eq Associativity where
  (==) a b = eqAssociativity a b

eqAssociativity :: Associativity -> Associativity -> Bool
eqAssociativity a b = case a of
  LeftAssociative -> case b of
    LeftAssociative -> True
    _ -> False
  RightAssociative -> case b of
    RightAssociative -> True
    _ -> False
  NotAssociative -> case b of
    NotAssociative -> True
    _ -> False

-- The metadata classes. GHC's argument is \\\`t d f a\\\`, a proxy shaped like the
-- \\\`M1\\\` whose tag is being asked about, so that a call site can pick the
-- instance by writing the type it wants rather than by having a value.
class Datatype d where
  datatypeName :: t d f a -> [Char]
  moduleName :: t d f a -> [Char]
  packageName :: t d f a -> [Char]
  isNewtype :: t d f a -> Bool
  moduleName x = "Main"
  packageName x = "main"
  isNewtype x = False

class Constructor c where
  conName :: t c f a -> [Char]
  conFixity :: t c f a -> Fixity
  conIsRecord :: t c f a -> Bool
  conFixity x = Prefix
  conIsRecord x = False

class Selector s where
  selName :: t s f a -> [Char]

-- \\\`rep\\\` is what GHC writes \\\`Rep a\\\`; the fundep is the whole content of the
-- family, and without it \\\`to (from x)\\\` would have nothing to fix the
-- intermediate type to.
class Generic a rep | a -> rep where
  from :: a -> rep x
  to :: rep x -> a
`,
  // \`StaticPtr\`, \`staticKey\` and \`deRefStaticPtr\` are declared in
  // \`src/prelude.ts\`, because \`static e\` is a keyword form that needs no
  // import - GHC wires the same names in for the same reason. This module is
  // the one that names them.
  //
  // WHAT IS MISSING. \`staticPtrInfo\`/\`StaticPtrInfo\` (the unit, module and
  // source location of the form) and \`staticPtrKeys\` are not here: nothing in
  // miso reads either, and \`StaticPtrInfo\` would put three strings in every
  // entry to be shown by nothing.
  "GHC.StaticPtr": `module GHC.StaticPtr (StaticPtr, StaticKey, StaticKey(StaticKey), deRefStaticPtr, staticKey, unsafeLookupStaticPtr, IsStatic) where

-- GHC's \\\`IsStatic\\\` is what \\\`static\\\` elaborates through when
-- \\\`-XExtendedLiterals\\\`-style overloading is in play; the identity instance is
-- the only one \\\`base\\\` ships.
class IsStatic p where
  fromStaticPtr :: StaticPtr a -> p a

instance IsStatic StaticPtr where
  fromStaticPtr p = p
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
import GHCJS.Types (jsval)

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
foreign import javascript unsafe "((g) => { const c = (x,y,z) => (h$forkThread(h$c2(h$ap1_e, h$c2(h$ap1_e, h$c2(h$ap1_e, g, x), y), z), false), h$startMainLoop()); c._key = ++h$extraRootsN; c.root = g; h$extraRoots.add(c); return c; })" jsCallback3 :: (JSValPrim -> JSValPrim -> JSValPrim -> RealWorld -> IOResult ()) -> CallbackPrim
foreign import javascript unsafe "((c) => { h$extraRoots.remove(c); c.root = null; })" jsReleaseCallback :: CallbackPrim -> IntPrim
foreign import javascript unsafe "((c) => c)" jsCallbackVal :: CallbackPrim -> JSValPrim

asyncCallback :: IO () -> IO (Callback (IO ()))
asyncCallback action = IO (\\s -> callbackStep s (jsCallback0 (\\t -> unIO action t)))

asyncCallback1 :: (JSVal -> IO ()) -> IO (Callback (JSVal -> IO ()))
asyncCallback1 f = IO (\\s -> callbackStep s (jsCallback1 (\\x t -> unIO (f (JSVal x)) t)))

asyncCallback2 :: (JSVal -> JSVal -> IO ()) -> IO (Callback (JSVal -> JSVal -> IO ()))
asyncCallback2 f = IO (\\s -> callbackStep s (jsCallback2 (\\x y t -> unIO (f (JSVal x) (JSVal y)) t)))

asyncCallback3 :: (JSVal -> JSVal -> JSVal -> IO ()) -> IO (Callback (JSVal -> JSVal -> JSVal -> IO ()))
asyncCallback3 f = IO (\\s -> callbackStep s (jsCallback3 (\\x y z t -> unIO (f (JSVal x) (JSVal y) (JSVal z)) t)))

-- The callback IS the JavaScript function, so handing it out as a \`JSVal\` is
-- JavaScript's identity and no Haskell work - the same representational
-- identity every other \`IsJSVal\` instance is.
instance IsJSVal (Callback a) where
  jsval (Callback c) = case jsCallbackVal c of
    v -> JSVal v

-- A synchronous callback runs its action to completion before the JavaScript
-- function returns, which is what \`h$runSync\` does - GHC's own
-- \`js_syncCallback\` is \`h$makeCallback(h$runSync, [onBlocked], action)\`.
-- \`ContinueAsync\` lets a block fall back to the asynchronous scheduler;
-- \`ThrowWouldBlock\` makes it throw instead.
--
-- These could not be written until now. \`h$runSync\` enters the action with
-- \`h$ap_1_0\` - one argument occupying no register - and only an \`IO\` whose
-- state token is a void type compiles to a closure of that shape.
--
-- The \`'\` variants hand the action's \`JSVal\` back to JavaScript. GHC uses
-- \`h$runSyncReturn\`, which reads the value through a ghc-internal symbol a
-- ghcts program does not link, so the value travels the same way the
-- arguments do: the action stores it and the wrapper reads it out. The slot is
-- saved and restored around the call, so a callback that runs another callback
-- cannot lose its own result.
foreign import javascript unsafe "((b, g) => { const run = globalThis['h$' + 'runSync']; const c = () => run(g, b); c._key = ++h$extraRootsN; c.root = g; h$extraRoots.add(c); return c; })" jsSyncCallback0 :: Bool -> (RealWorld -> IOResult ()) -> CallbackPrim
foreign import javascript unsafe "((b, g) => { const run = globalThis['h$' + 'runSync']; const c = (x) => run(h$c2(h$ap1_e, g, x), b); c._key = ++h$extraRootsN; c.root = g; h$extraRoots.add(c); return c; })" jsSyncCallback1 :: Bool -> (JSValPrim -> RealWorld -> IOResult ()) -> CallbackPrim
foreign import javascript unsafe "((b, g) => { const run = globalThis['h$' + 'runSync']; const c = (x,y) => run(h$c2(h$ap1_e, h$c2(h$ap1_e, g, x), y), b); c._key = ++h$extraRootsN; c.root = g; h$extraRoots.add(c); return c; })" jsSyncCallback2 :: Bool -> (JSValPrim -> JSValPrim -> RealWorld -> IOResult ()) -> CallbackPrim
foreign import javascript unsafe "((b, g) => { const run = globalThis['h$' + 'runSync']; const c = (x,y,z) => run(h$c2(h$ap1_e, h$c2(h$ap1_e, h$c2(h$ap1_e, g, x), y), z), b); c._key = ++h$extraRootsN; c.root = g; h$extraRoots.add(c); return c; })" jsSyncCallback3 :: Bool -> (JSValPrim -> JSValPrim -> JSValPrim -> RealWorld -> IOResult ()) -> CallbackPrim

foreign import javascript unsafe "((v) => { globalThis.h$ghctsSyncResult = v; return 0; })" jsPutSyncResult :: JSValPrim -> IntPrim
foreign import javascript unsafe "((g) => { const run = globalThis['h$' + 'runSync']; const c = () => { const p = globalThis.h$ghctsSyncResult; run(g, false); const r = globalThis.h$ghctsSyncResult; globalThis.h$ghctsSyncResult = p; return r; }; c._key = ++h$extraRootsN; c.root = g; h$extraRoots.add(c); return c; })" jsSyncCallbackReturn0 :: (RealWorld -> IOResult ()) -> CallbackPrim
foreign import javascript unsafe "((g) => { const run = globalThis['h$' + 'runSync']; const c = (x) => { const p = globalThis.h$ghctsSyncResult; run(h$c2(h$ap1_e, g, x), false); const r = globalThis.h$ghctsSyncResult; globalThis.h$ghctsSyncResult = p; return r; }; c._key = ++h$extraRootsN; c.root = g; h$extraRoots.add(c); return c; })" jsSyncCallbackReturn1 :: (JSValPrim -> RealWorld -> IOResult ()) -> CallbackPrim
foreign import javascript unsafe "((g) => { const run = globalThis['h$' + 'runSync']; const c = (x,y) => { const p = globalThis.h$ghctsSyncResult; run(h$c2(h$ap1_e, h$c2(h$ap1_e, g, x), y), false); const r = globalThis.h$ghctsSyncResult; globalThis.h$ghctsSyncResult = p; return r; }; c._key = ++h$extraRootsN; c.root = g; h$extraRoots.add(c); return c; })" jsSyncCallbackReturn2 :: (JSValPrim -> JSValPrim -> RealWorld -> IOResult ()) -> CallbackPrim
foreign import javascript unsafe "((g) => { const run = globalThis['h$' + 'runSync']; const c = (x,y,z) => { const p = globalThis.h$ghctsSyncResult; run(h$c2(h$ap1_e, h$c2(h$ap1_e, h$c2(h$ap1_e, g, x), y), z), false); const r = globalThis.h$ghctsSyncResult; globalThis.h$ghctsSyncResult = p; return r; }; c._key = ++h$extraRootsN; c.root = g; h$extraRoots.add(c); return c; })" jsSyncCallbackReturn3 :: (JSValPrim -> JSValPrim -> JSValPrim -> RealWorld -> IOResult ()) -> CallbackPrim

-- \`h$runSyncAction\` seats a top-level exception handler on the thread it
-- creates, and names ghc-internal's \`setCurrentThreadResultException\` for the
-- job. A ghcts program does not link ghc-internal, and a bare reference to an
-- undefined global is a ReferenceError rather than \`undefined\`, so the slot is
-- filled here instead - with a handler of exactly the shape \`h$catch_e\`
-- applies: two arguments in one register, the exception and the erased token.
-- Recording the exception is what makes \`h$runSync\` re-throw it to the
-- JavaScript caller instead of reporting a thread that merely did not finish.
foreign import javascript unsafe "((h) => { globalThis.h$ghczminternalZCGHCziInternalziJSziPrimziInternalzisetCurrentThreadResultException = h; return 0; })" jsInstallSyncHandler :: (JSValPrim -> RealWorld -> IOResult ()) -> IntPrim
foreign import javascript unsafe "((e) => { h$setCurrentThreadResultJSException(e); return 0; })" jsSyncFailed :: JSValPrim -> IntPrim

syncFailed :: JSValPrim -> RealWorld -> IOResult ()
syncFailed e t = case jsSyncFailed e of
  _ -> IOResult t ()

syncCallbackStep :: RealWorld -> CallbackPrim -> IOResult (Callback a)
syncCallbackStep s c = case jsInstallSyncHandler syncFailed of
  _ -> IOResult s (Callback c)

blocksAsync :: OnBlocked -> Bool
blocksAsync b = case b of
  ContinueAsync -> True
  ThrowWouldBlock -> False

syncCallback :: OnBlocked -> IO () -> IO (Callback (IO ()))
syncCallback b action = IO (\\s -> syncCallbackStep s (jsSyncCallback0 (blocksAsync b) (\\t -> unIO action t)))

syncCallback1 :: OnBlocked -> (JSVal -> IO ()) -> IO (Callback (JSVal -> IO ()))
syncCallback1 b f = IO (\\s -> syncCallbackStep s (jsSyncCallback1 (blocksAsync b) (\\x t -> unIO (f (JSVal x)) t)))

syncCallback2 :: OnBlocked -> (JSVal -> JSVal -> IO ()) -> IO (Callback (JSVal -> JSVal -> IO ()))
syncCallback2 b f = IO (\\s -> syncCallbackStep s (jsSyncCallback2 (blocksAsync b) (\\x y t -> unIO (f (JSVal x) (JSVal y)) t)))

syncCallback3 :: OnBlocked -> (JSVal -> JSVal -> JSVal -> IO ()) -> IO (Callback (JSVal -> JSVal -> JSVal -> IO ()))
syncCallback3 b f = IO (\\s -> syncCallbackStep s (jsSyncCallback3 (blocksAsync b) (\\x y z t -> unIO (f (JSVal x) (JSVal y) (JSVal z)) t)))

putSyncResult :: IO JSVal -> IO ()
putSyncResult m = m >>= putSyncResultStep

putSyncResultStep :: JSVal -> IO ()
putSyncResultStep (JSVal v) = IO (\\s -> putSyncResultDone s v)

putSyncResultDone :: RealWorld -> JSValPrim -> IOResult ()
putSyncResultDone s v = case jsPutSyncResult v of
  _ -> IOResult s ()

syncCallback' :: IO JSVal -> IO (Callback (IO JSVal))
syncCallback' m = IO (\\s -> syncCallbackStep s (jsSyncCallbackReturn0 (\\t -> unIO (putSyncResult m) t)))

syncCallback1' :: (JSVal -> IO JSVal) -> IO (Callback (JSVal -> IO JSVal))
syncCallback1' f = IO (\\s -> syncCallbackStep s (jsSyncCallbackReturn1 (\\x t -> unIO (putSyncResult (f (JSVal x))) t)))

syncCallback2' :: (JSVal -> JSVal -> IO JSVal) -> IO (Callback (JSVal -> JSVal -> IO JSVal))
syncCallback2' f = IO (\\s -> syncCallbackStep s (jsSyncCallbackReturn2 (\\x y t -> unIO (putSyncResult (f (JSVal x) (JSVal y))) t)))

syncCallback3' :: (JSVal -> JSVal -> JSVal -> IO JSVal) -> IO (Callback (JSVal -> JSVal -> JSVal -> IO JSVal))
syncCallback3' f = IO (\\s -> syncCallbackStep s (jsSyncCallbackReturn3 (\\x y z t -> unIO (putSyncResult (f (JSVal x) (JSVal y) (JSVal z))) t)))

callbackStep :: RealWorld -> CallbackPrim -> IOResult (Callback a)
callbackStep s c = IOResult s (Callback c)

releaseCallback :: Callback a -> IO ()
releaseCallback (Callback c) = IO (\\s -> releaseStep s c)

releaseStep :: RealWorld -> CallbackPrim -> IOResult ()
releaseStep s c = case jsReleaseCallback c of
  _ -> IOResult s ()
`,
  "Control.Exception": `module Control.Exception where
import Data.JSString (JSString, unpack)

-- Only the JavaScript exception shape: this frontend has no \\\`Exception\\\` class
-- and no \\\`SomeException\\\` hierarchy, so an exception is whatever JavaScript
-- value was thrown.
--
-- What IS GHC's is the mechanism. \\\`throwIO\\\` is \\\`raiseIO#\\\` and \\\`catch\\\` is
-- \\\`catch#\\\`, so the RTS unwinds the Haskell stack to the nearest handler frame
-- exactly as it does under GHC - a JS \\\`throw\\\` would instead escape past every
-- handler and kill the thread, which is what \\\`Prelude.error\\\` still does.
data SomeException = SomeException JSValPrim

foreign import javascript unsafe "((s) => new Error(s))" jsError :: JSStringPrim -> JSValPrim
foreign import javascript unsafe "((e) => String(e && e.message !== undefined ? e.message : e))" jsShowException :: JSValPrim -> JSStringPrim

displayException :: SomeException -> JSString
displayException (SomeException e) = case jsShowException e of
  s -> JSString s

-- GHC shows a \`SomeException\` as the exception it wraps shows itself, which
-- for the one shape this frontend has is the JavaScript error's message.
instance Show SomeException where
  showsPrec d e r = showString (unpack (displayException e)) r

-- \`raiseIO#\` does not return: it unwinds to a handler frame, so there is no
-- result to build and no unreachable value to invent.
throwIO :: SomeException -> IO a
throwIO (SomeException e) = IO (\\s -> primRaiseIO e s)

-- GHC's \`catch\`. \`h\$catch\` pushes the handler frame and jumps into the
-- action; \`h\$throw\` unwinds to that frame and applies the handler to the
-- exception and the state token. Both ends need the action to be a closure of
-- one erased argument, which is exactly what \`\\\\t -> unIO m t\` now compiles to.
catch :: IO a -> (SomeException -> IO a) -> IO a
catch m h = IO (\\s -> primCatch (\\t -> unIO m t) (\\e t -> unIO (h (SomeException e)) t) s)

-- GHC's \`bracket\`, without \`mask\`: this target runs one JS thread and has no
-- asynchronous exceptions to mask against, so the ordering \`mask\` buys is
-- already guaranteed. What matters is kept - the release action runs on the
-- exception path *before* the exception is re-thrown, and on the normal path
-- after the body.
bracket :: IO a -> (a -> IO b) -> (a -> IO c) -> IO c
bracket before after thing = before >>= bracketWith after thing

bracketWith :: (a -> IO b) -> (a -> IO c) -> a -> IO c
bracketWith after thing a = catch (thing a) (bracketFailed after a) >>= bracketDone after a

bracketFailed :: (a -> IO b) -> a -> SomeException -> IO c
bracketFailed after a e = after a >> throwIO e

bracketDone :: (a -> IO b) -> a -> c -> IO c
bracketDone after a r = after a >> pure r

`,
  "System.IO.Unsafe": `module System.IO.Unsafe (unsafePerformIO) where
`,
  // A `StablePtr` is a slot in the JS backend's own `h$stablePtrData`:
  // `h$makeStablePtr` returns `slot << 2` and `h$deRefStablePtr` shifts it
  // back, so a pointer made here is exactly the one a program's own
  // `foreign import ccall` sees - which is what `Miso.Reload` stores across a
  // reload and reads out again.
  "Foreign.StablePtr": `module Foreign.StablePtr (StablePtr, newStablePtr, deRefStablePtr, freeStablePtr) where

data StablePtr a = StablePtr IntPrim

foreign import javascript unsafe "((x) => h$makeStablePtr(x))" jsMakeStablePtr :: a -> IntPrim
foreign import javascript unsafe "((p) => h$deRefStablePtr(p))" jsDeRefStablePtr :: IntPrim -> a
foreign import javascript unsafe "((p) => { h$hs_free_stable_ptr(0, p); return 0; })" jsFreeStablePtr :: IntPrim -> IntPrim

newStablePtr :: a -> IO (StablePtr a)
newStablePtr x = IO (\\s -> newStablePtrStep s x)

newStablePtrStep :: RealWorld -> a -> IOResult (StablePtr a)
newStablePtrStep s x = case jsMakeStablePtr x of
  p -> IOResult s (StablePtr p)

deRefStablePtr :: StablePtr a -> IO a
deRefStablePtr (StablePtr p) = IO (\\s -> deRefStablePtrStep s p)

-- The slot holds the closure that was stored, thunk and all, so this returns
-- it unforced - \`deRefStablePtr\` is not a \`seq\`.
deRefStablePtrStep :: RealWorld -> IntPrim -> IOResult a
deRefStablePtrStep s p = case jsDeRefStablePtr p of
  x -> IOResult s x

freeStablePtr :: StablePtr a -> IO ()
freeStablePtr (StablePtr p) = IO (\\s -> freeStablePtrStep s p)

freeStablePtrStep :: RealWorld -> IntPrim -> IOResult ()
freeStablePtrStep s p = case jsFreeStablePtr p of
  _ -> IOResult s ()
`,
  "Foreign": `module Foreign (module Foreign.StablePtr) where
import Foreign.StablePtr
`,
  // This backend's `Int` IS a 32-bit signed machine int - `IntMulOp` is
  // `Math.imul` and `IntToInt32Op` is the identity - so `Int32` is that same
  // arithmetic, and `Int8`/`Int16` are it narrowed after every operation,
  // which is exactly what GHC's `Int8AddOp` does with its `signExtend8`.
  // Every intermediate stays inside 32 bits (two 16-bit factors reach 2^30),
  // so nothing here rounds.
  //
  // `Int64` is deliberately absent: it does not fit a JavaScript number, and
  // aliasing it to `Int` would be wrong without saying so.
  "Data.Int": `module Data.Int (Int8, Int16, Int32) where

data Int8 = I8 IntPrim
data Int16 = I16 IntPrim
data Int32 = I32 IntPrim

-- \`primIntRem\` truncates towards zero, so a negative \`n\` needs the second
-- \`rem\` to land back in [0, m). Every caller names the result with a \`case\`
-- before storing it: a Haskell function\'s result in a constructor field is a
-- THUNK, and one of these constructors is unboxed, so the field would BE the
-- thunk.
unsignedRem :: IntPrim -> IntPrim -> IntPrim
unsignedRem m n = primIntRem (primIntAdd (primIntRem n m) m) m

narrow8 :: IntPrim -> IntPrim
narrow8 n = primIntSub (unsignedRem 256 (primIntAdd n 128)) 128

narrow16 :: IntPrim -> IntPrim
narrow16 n = primIntSub (unsignedRem 65536 (primIntAdd n 32768)) 32768

instance Eq Int8 where
  (==) (I8 a) (I8 b) = primIntEq a b

instance Ord Int8 where
  (<) (I8 a) (I8 b) = primIntLt a b
  (<=) (I8 a) (I8 b) = primIntLe a b
  (>) (I8 a) (I8 b) = primIntGt a b
  (>=) (I8 a) (I8 b) = primIntGe a b

instance Num Int8 where
  (+) (I8 a) (I8 b) = case narrow8 (primIntAdd a b) of
    n -> I8 n
  (-) (I8 a) (I8 b) = case narrow8 (primIntSub a b) of
    n -> I8 n
  (*) (I8 a) (I8 b) = case narrow8 (primIntMul a b) of
    n -> I8 n
  negate (I8 a) = case narrow8 (primIntNeg a) of
    n -> I8 n
  fromInteger n = case narrow8 n of
    m -> I8 m

instance Real Int8 where
  toDoublePrim (I8 a) = primIntToDouble a

instance Show Int8 where
  show (I8 a) = show (I a)

instance Eq Int16 where
  (==) (I16 a) (I16 b) = primIntEq a b

instance Ord Int16 where
  (<) (I16 a) (I16 b) = primIntLt a b
  (<=) (I16 a) (I16 b) = primIntLe a b
  (>) (I16 a) (I16 b) = primIntGt a b
  (>=) (I16 a) (I16 b) = primIntGe a b

instance Num Int16 where
  (+) (I16 a) (I16 b) = case narrow16 (primIntAdd a b) of
    n -> I16 n
  (-) (I16 a) (I16 b) = case narrow16 (primIntSub a b) of
    n -> I16 n
  (*) (I16 a) (I16 b) = case narrow16 (primIntMul a b) of
    n -> I16 n
  negate (I16 a) = case narrow16 (primIntNeg a) of
    n -> I16 n
  fromInteger n = case narrow16 n of
    m -> I16 m

instance Real Int16 where
  toDoublePrim (I16 a) = primIntToDouble a

instance Show Int16 where
  show (I16 a) = show (I a)

instance Eq Int32 where
  (==) (I32 a) (I32 b) = primIntEq a b

instance Ord Int32 where
  (<) (I32 a) (I32 b) = primIntLt a b
  (<=) (I32 a) (I32 b) = primIntLe a b
  (>) (I32 a) (I32 b) = primIntGt a b
  (>=) (I32 a) (I32 b) = primIntGe a b

instance Num Int32 where
  (+) (I32 a) (I32 b) = I32 (primIntAdd a b)
  (-) (I32 a) (I32 b) = I32 (primIntSub a b)
  (*) (I32 a) (I32 b) = I32 (primIntMul a b)
  negate (I32 a) = I32 (primIntNeg a)
  fromInteger n = I32 n

instance Real Int32 where
  toDoublePrim (I32 a) = primIntToDouble a

instance Show Int32 where
  show (I32 a) = show (I a)
`,
  // \`Word\` is the unsigned machine word, 32 bits here as \`Int\` is signed 32.
  // What makes it unsigned is its own primops: every result comes back through
  // \`>>> 0\` and the multiply through \`Math.imul\`, so the carrier always holds a
  // number in [0, 2^32), which is why the comparisons and the conversion to
  // \`Double\` need nothing further. \`Word8\`/\`Word16\` narrow after every step.
  //
  // \`Word64\` is deliberately absent, for the reason \`Int64\` is.
  "Data.Word": `module Data.Word (Word, Word8, Word16, Word32) where

data Word = W WordPrim
data Word8 = W8 WordPrim
data Word16 = W16 WordPrim
data Word32 = W32 WordPrim

mask8 :: WordPrim -> WordPrim
mask8 n = primWordRem n (primIntToWord 256)

mask16 :: WordPrim -> WordPrim
mask16 n = primWordRem n (primIntToWord 65536)

instance Eq Word where
  (==) (W a) (W b) = primWordEq a b

instance Ord Word where
  (<) (W a) (W b) = primWordLt a b
  (<=) (W a) (W b) = primWordLe a b
  (>) (W a) (W b) = primWordGt a b
  (>=) (W a) (W b) = primWordGe a b

instance Num Word where
  (+) (W a) (W b) = W (primWordAdd a b)
  (-) (W a) (W b) = W (primWordSub a b)
  (*) (W a) (W b) = W (primWordMul a b)
  negate (W a) = W (primWordSub (primIntToWord 0) a)
  fromInteger n = W (primIntToWord n)

instance Real Word where
  toDoublePrim (W a) = primWordToDouble a

instance Eq Word8 where
  (==) (W8 a) (W8 b) = primWordEq a b

instance Ord Word8 where
  (<) (W8 a) (W8 b) = primWordLt a b
  (<=) (W8 a) (W8 b) = primWordLe a b
  (>) (W8 a) (W8 b) = primWordGt a b
  (>=) (W8 a) (W8 b) = primWordGe a b

instance Num Word8 where
  (+) (W8 a) (W8 b) = case mask8 (primWordAdd a b) of
    n -> W8 n
  (-) (W8 a) (W8 b) = case mask8 (primWordSub a b) of
    n -> W8 n
  (*) (W8 a) (W8 b) = case mask8 (primWordMul a b) of
    n -> W8 n
  negate (W8 a) = case mask8 (primWordSub (primIntToWord 0) a) of
    n -> W8 n
  fromInteger n = case mask8 (primIntToWord n) of
    m -> W8 m

instance Real Word8 where
  toDoublePrim (W8 a) = primWordToDouble a

instance Eq Word16 where
  (==) (W16 a) (W16 b) = primWordEq a b

instance Ord Word16 where
  (<) (W16 a) (W16 b) = primWordLt a b
  (<=) (W16 a) (W16 b) = primWordLe a b
  (>) (W16 a) (W16 b) = primWordGt a b
  (>=) (W16 a) (W16 b) = primWordGe a b

instance Num Word16 where
  (+) (W16 a) (W16 b) = case mask16 (primWordAdd a b) of
    n -> W16 n
  (-) (W16 a) (W16 b) = case mask16 (primWordSub a b) of
    n -> W16 n
  (*) (W16 a) (W16 b) = case mask16 (primWordMul a b) of
    n -> W16 n
  negate (W16 a) = case mask16 (primWordSub (primIntToWord 0) a) of
    n -> W16 n
  fromInteger n = case mask16 (primIntToWord n) of
    m -> W16 m

instance Real Word16 where
  toDoublePrim (W16 a) = primWordToDouble a

instance Eq Word32 where
  (==) (W32 a) (W32 b) = primWordEq a b

instance Ord Word32 where
  (<) (W32 a) (W32 b) = primWordLt a b
  (<=) (W32 a) (W32 b) = primWordLe a b
  (>) (W32 a) (W32 b) = primWordGt a b
  (>=) (W32 a) (W32 b) = primWordGe a b

instance Num Word32 where
  (+) (W32 a) (W32 b) = W32 (primWordAdd a b)
  (-) (W32 a) (W32 b) = W32 (primWordSub a b)
  (*) (W32 a) (W32 b) = W32 (primWordMul a b)
  negate (W32 a) = W32 (primWordSub (primIntToWord 0) a)
  fromInteger n = W32 (primIntToWord n)

instance Real Word32 where
  toDoublePrim (W32 a) = primWordToDouble a
`,
  // GHC's \`CInt\` is \`Int32\`, and on this backend so is \`Int\`.
  "Foreign.C.Types": `module Foreign.C.Types (CInt) where
import Data.Int (Int32)

type CInt = Int32
`,
  // GHC's \\`StableName\\` is pointer identity made observable. \\`h$makeStableName\\`
  // gives one object per heap object and \\`h$stableNameInt\\` its unique integer,
  // so comparing the integers *is* comparing the objects - which is what
  // miso's \\`dirtyCheck\\` asks for before it falls back to \\`Eq\\`.
  "System.Mem.StableName": `module System.Mem.StableName where

data StableName a = StableName StableNamePrim

makeStableName :: a -> IO (StableName a)
makeStableName x = IO (\\s -> makeStableNameStep s x)

makeStableNameStep :: RealWorld -> a -> IOResult (StableName a)
makeStableNameStep s x = case primMakeStableName x of
  n -> IOResult s (StableName n)

hashStableName :: StableName a -> Int
hashStableName (StableName n) = case primStableNameInt n of
  i -> I i

eqStableName :: StableName a -> StableName b -> Bool
eqStableName a b = hashStableName a == hashStableName b

instance Eq (StableName a) where
  (==) a b = eqStableName a b
`,
  // There is no GHC heap on this backend and nothing to collect, which is what
  // GHC's own JS backend does with \\`performGC\\`.
  "System.Mem": `module System.Mem where

performGC :: IO ()
performGC = pure ()

performMajorGC :: IO ()
performMajorGC = pure ()

performMinorGC :: IO ()
performMinorGC = pure ()
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
  // \`get\`, \`put\`, \`state\`, \`ask\` and \`tell\` are mtl's class methods, not
  // functions at one transformer, so code that is polymorphic in the monad -
  // miso's own \`Miso.Lens\` operators, whose signatures read \`MonadState record
  // m =>\` - typechecks and runs. Each class is declared in its own leaf module
  // so that every transformer can carry the lifting instances for all three
  // without importing its siblings.
  //
  // WHAT IS MISSING, AND WHY. \`local\`, \`listen\` and \`censor\` stay ordinary
  // functions at \`ReaderT\`/\`WriterT\`/\`RWST\` rather than joining their classes:
  // they are the operations that would have to be re-implemented, not merely
  // lifted, at every other transformer, and nothing in miso uses them through
  // a stack.
  //
  // \`MonadTrans\` is missing for a different reason: \`lift :: Monad m => m a ->
  // t m a\` puts a constraint on a *method*, which a class declaration here
  // cannot carry. Nothing in miso calls \`lift\`.
  "Data.Functor.Identity": `module Data.Functor.Identity (Identity, runIdentity) where

-- Record syntax, as GHC declares it. Miso.Lens writes
-- "import Control.Monad.Identity (Identity(..))" and then uses runIdentity:
-- a separate function of that name would not come with the constructor.
newtype Identity a = Identity { runIdentity :: a }

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
  // mtl's three classes. Each lives in a leaf module of its own, exactly as
  // mtl has it, so that every transformer module can declare the *lifting*
  // instances for all three without importing its siblings.
  //
  // The functional dependency is what makes them usable: `get :: MonadState s
  // m => m s` mentions `s` nowhere but the result, so `m -> s` is the only
  // thing that can decide which state type a `n <- get` produced. See the
  // improvement pass in `src/elaborate.ts`.
  "Control.Monad.State.Class": `module Control.Monad.State.Class (MonadState(..), gets, modify, modify') where

class Monad m => MonadState s m | m -> s where
  get :: m s
  put :: s -> m ()
  state :: (s -> (a, s)) -> m a

gets :: MonadState s m => (s -> a) -> m a
gets f = get >>= (\\s -> pure (f s))

-- Lazy, as GHC's is: \\\`state\\\` hands over an unforced pair, so \\\`modify (+1)\\\` on
-- a state nobody looks at costs nothing and never diverges.
modify :: MonadState s m => (s -> s) -> m ()
modify f = state (\\s -> ((), f s))

-- \\\`modify'\\\` differs only in the \\\`seq\\\`, and that is the whole point of it:
-- without forcing, a long fold leaves a chain of thunks in the state.
modify' :: MonadState s m => (s -> s) -> m ()
modify' f = get >>= (\\s -> putStrict (f s))

putStrict :: MonadState s m => s -> m ()
putStrict s = seq s (put s)
`,
  "Control.Monad.Reader.Class": `module Control.Monad.Reader.Class (MonadReader(..), asks, reader) where

class Monad m => MonadReader r m | m -> r where
  ask :: m r

asks :: MonadReader r m => (r -> a) -> m a
asks f = ask >>= (\\r -> pure (f r))

reader :: MonadReader r m => (r -> a) -> m a
reader f = asks f
`,
  "Control.Monad.Writer.Class": `module Control.Monad.Writer.Class where

class Monad m => MonadWriter w m | m -> w where
  tell :: w -> m ()
`,
  "Control.Monad.Reader": `module Control.Monad.Reader (runReaderT, runReader, local, withReaderT, module Control.Monad.Reader.Class) where
import Data.Functor.Identity
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.Writer.Class

newtype ReaderT r m a = ReaderT (r -> m a)

type Reader r = ReaderT r Identity

runReaderT :: ReaderT r m a -> r -> m a
runReaderT (ReaderT f) r = f r

runReader :: Reader r a -> r -> a
runReader m r = runIdentity (runReaderT m r)

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

instance Monad m => MonadReader r (ReaderT r m) where
  ask = ReaderT (\\r -> pure r)

-- The lifting instances. A \\\`ReaderT\\\` over a state or a writer still is one:
-- the environment is threaded past the effect and the base monad's own
-- \\\`get\\\`/\\\`tell\\\` does the work. Which \\\`s\\\` or \\\`w\\\` that is comes from the
-- fundep, one step at a time down the stack.
instance MonadState s m => MonadState s (ReaderT r m) where
  get = ReaderT (\\r -> get)
  put s = ReaderT (\\r -> put s)
  state f = ReaderT (\\r -> state f)

instance MonadWriter w m => MonadWriter w (ReaderT r m) where
  tell w = ReaderT (\\r -> tell w)
`,
  "Control.Monad.State": `module Control.Monad.State (runStateT, runState, evalState, execState, evalStateT, execStateT, withState, module Control.Monad.State.Class) where
import Data.Functor.Identity
import Control.Monad.State.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class

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

instance Monad m => MonadState s (StateT s m) where
  get = StateT (\\s -> pure (s, s))
  put s = StateT (\\_ -> pure ((), s))
  state f = StateT (\\s -> pure (f s))

instance MonadReader r m => MonadReader r (StateT s m) where
  ask = StateT (\\s -> stateAsk s)

stateAsk :: MonadReader r m => s -> m (r, s)
stateAsk s = ask >>= (\\r -> pure (r, s))

instance MonadWriter w m => MonadWriter w (StateT s m) where
  tell w = StateT (\\s -> stateTell w s)

stateTell :: MonadWriter w m => w -> s -> m ((), s)
stateTell w s = tell w >>= (\\_ -> pure ((), s))
`,
  "Control.Monad.Writer": `module Control.Monad.Writer (runWriterT, runWriter, execWriter, execWriterT, writer, listen, censor, module Control.Monad.Writer.Class) where
import Data.Functor.Identity
import Control.Monad.Writer.Class
import Control.Monad.State.Class
import Control.Monad.Reader.Class

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

instance (Monoid w, Monad m) => MonadWriter w (WriterT w m) where
  tell w = WriterT (pure ((), w))

-- Lifted through the output: each action of the base monad contributes
-- \\\`mempty\\\`, so nothing is written that the program did not \\\`tell\\\`.
instance (Monoid w, MonadState s m) => MonadState s (WriterT w m) where
  get = WriterT writerGet
  put s = WriterT (writerPut s)
  state f = WriterT (writerState f)

writerGet :: (Monoid w, MonadState s m) => m (s, w)
writerGet = get >>= (\\s -> pure (s, mempty))

writerPut :: (Monoid w, MonadState s m) => s -> m ((), w)
writerPut s = put s >>= (\\_ -> pure ((), mempty))

writerState :: (Monoid w, MonadState s m) => (s -> (a, s)) -> m (a, w)
writerState f = state f >>= (\\a -> pure (a, mempty))

instance (Monoid w, MonadReader r m) => MonadReader r (WriterT w m) where
  ask = WriterT writerAsk

writerAsk :: (Monoid w, MonadReader r m) => m (r, w)
writerAsk = ask >>= (\\r -> pure (r, mempty))
`,
  "Control.Monad.RWS": `module Control.Monad.RWS (runRWST, runRWS, evalRWS, execRWS, evalRWST, execRWST, rws, local, listen, censor, module Control.Monad.State.Class, module Control.Monad.Reader.Class, module Control.Monad.Writer.Class) where
import Data.Functor.Identity
import Control.Monad.State.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class

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

local :: (r -> r) -> RWST r w s m a -> RWST r w s m a
local f m = RWST (\\r s -> runRWST m (f r) s)

rwsStateStep :: (Monoid w, Monad m) => (a, s) -> m (a, s, w)
rwsStateStep p = case p of
  (a, s) -> pure (a, s, mempty)

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

-- One monad, all three classes: this is what makes miso's \\\`Effect\\\` accept
-- \\\`value += 1\\\` (MonadState), \\\`getProps\\\` (MonadReader) and \\\`io_\\\` (MonadWriter)
-- in the same \\\`do\\\` block.
instance (Monoid w, Monad m) => MonadState s (RWST r w s m) where
  get = RWST (\\r s -> pure (s, s, mempty))
  put s = RWST (\\r _ -> pure ((), s, mempty))
  state f = RWST (\\r s -> rwsStateStep (f s))

instance (Monoid w, Monad m) => MonadReader r (RWST r w s m) where
  ask = RWST (\\r s -> pure (r, s, mempty))

instance (Monoid w, Monad m) => MonadWriter w (RWST r w s m) where
  tell w = RWST (\\r s -> pure ((), s, w))
`,
  "Control.Monad.Trans.Maybe": `module Control.Monad.Trans.Maybe (runMaybeT, hoistMaybe) where
import Control.Monad.State.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class

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

-- Lifting through the short circuit: the effect runs in the base monad and its
-- result is always a \\\`Just\\\`, so \\\`get\\\` inside a \\\`MaybeT\\\` cannot itself fail.
instance MonadState s m => MonadState s (MaybeT m) where
  get = MaybeT (maybeTLift get)
  put s = MaybeT (maybeTLift (put s))
  state f = MaybeT (maybeTLift (state f))

maybeTLift :: Monad m => m a -> m (Maybe a)
maybeTLift m = m >>= (\\a -> pure (Just a))

instance MonadReader r m => MonadReader r (MaybeT m) where
  ask = MaybeT (maybeTLift ask)

instance MonadWriter w m => MonadWriter w (MaybeT m) where
  tell w = MaybeT (maybeTLift (tell w))
`,
  // ----------------------------------------------------------- marshalling ---
  // ghcjs-base's name for the same module. miso imports it under this name on
  // the ghcjs path and under `GHC.JS.Foreign.Callback` on the GHC one, so both
  // spellings have to resolve to the one implementation.
  "GHCJS.Foreign.Callback": `module GHCJS.Foreign.Callback (module GHC.JS.Foreign.Callback) where
import GHC.JS.Foreign.Callback
`,
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

instance ToJSValue Float where
  toJSValue (FloatBox f) = case primFloatToDouble f of
    d -> case doubleToVal d of
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

-- JavaScript has one number type, so what comes back is a double; \`Float\` is
-- the nearest single-precision value to it, which is what \`Math.fround\` gives.
instance FromJSValue Float where
  fromJSValue (JSVal x) = if isNumberVal x then fromFloatStep x else pure Nothing

fromFloatStep :: JSValPrim -> IO (Maybe Float)
fromFloatStep x = case valToDouble x of
  d -> case primDoubleToFloat d of
    f -> pure (Just (FloatBox f))

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
/** The modules this file supplies, by name. Their data constructors stay in
 * the global namespace: the Prelude and the derived-`Generic` source are
 * written against `M1`, `Just` and friends by their plain names, and neither
 * is renamed through any module's scope. */
export const libraryModuleNames: ReadonlySet<string> = new Set(Object.keys(sources));

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
