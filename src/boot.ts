/**
 * Compiler-owned boot-library interfaces.  These are module identities that
 * GHC normally obtains from wired-in packages; they are intentionally kept
 * separate from project and Miso sources so resolution never substitutes a
 * Miso implementation or silently accepts an arbitrary missing import.
 *
 * The declarations here are the initial executable/typechecked slice.  The
 * catalog is broader than that slice because package resolution must be able
 * to construct the real Miso graph before each imported interface is filled
 * in by the boot-library phase.
 */
const sources: Record<string, string> = {
  Prelude: 'module Prelude where\ndata Bool = False | True\ndata Maybe a = Nothing | Just a\ndata Either a b = Left a | Right b\n',
  'Data.Bool': 'module Data.Bool where\ndata Bool = False | True\nbool falseValue trueValue condition = if condition then trueValue else falseValue\n',
  'Data.Bifunctor': 'module Data.Bifunctor where\n',
  'Data.Maybe': `module Data.Maybe where
data Maybe a = Nothing | Just a
isJust (Just _) = True
isJust Nothing = False
isNothing Nothing = True
isNothing (Just _) = False
fromMaybe fallback Nothing = fallback
fromMaybe _ (Just value) = value
maybe fallback _ Nothing = fallback
maybe _ applyValue (Just value) = applyValue value
catMaybes [] = []
catMaybes (Nothing : values) = catMaybes values
catMaybes (Just value : values) = value : catMaybes values
listToMaybe [] = Nothing
listToMaybe (x:_) = Just x
`,
  'Data.Either': `module Data.Either where
data Either a b = Left a | Right b
isLeft (Left _) = True
isLeft (Right _) = False
isRight (Left _) = False
isRight (Right _) = True
either onLeft _ (Left value) = onLeft value
either _ onRight (Right value) = onRight value
`,
  'Data.Int': 'module Data.Int where\n',
  'Data.Ix': 'module Data.Ix where\n',
  'Data.Word': 'module Data.Word where\n',
  'Data.Kind': 'module Data.Kind where\n',
  'Data.Proxy': 'module Data.Proxy where\ndata Proxy a = Proxy\n',
  'Data.String': 'module Data.String where\n',
  'Data.Char': 'module Data.Char where\n',
  'Data.Function': `module Data.Function where
(&) value applyValue = applyValue value
`,
  'Data.Functor': `module Data.Functor where
foreign import javascript unsafe "(($1) => $1)" void :: f a -> f ()
`,
  'Data.Functor.Const': 'module Data.Functor.Const where\n',
  'Data.Foldable': `module Data.Foldable where
foreign import javascript unsafe "(($1,$2,$3) => { let acc = $2; const step = (item) => { acc = $1(acc)(item); }; const walk = (xs) => { const value = force(xs); if (value == null) return; if (Array.isArray(value)) { value.forEach(step); return; } if (value && (value.tag === '[]' || value.tag === 'Empty')) return; if (value && (value.tag === ':' || value.tag === 'Cons')) { step(force(value.fields[0])); walk(value.fields[1]); } }; walk($3); return acc; })" foldl' :: (b -> a -> b) -> b -> t a -> b
foreign import javascript unsafe "(($1) => { const value = force($1); if (value instanceof Set) return listFromArray([...value]); if (value instanceof Map) return listFromArray([...value.keys()]); if (value && (value.tag === ':' || value.tag === '[]' || value.tag === 'Cons' || value.tag === 'Empty')) return value; if (Array.isArray(value)) return listFromArray(value); const out = []; const walk = (xs) => { const v = force(xs); if (!v) return; if (v.tag === ':' || v.tag === 'Cons') { out.push(force(v.fields[0])); walk(v.fields[1]); } }; walk(value); return listFromArray(out); })" toList :: t a -> [a]
`,
  'Data.Text': 'module Data.Text where\n',
  'Data.Text.Lazy': 'module Data.Text.Lazy where\n',
  'Data.Text.Encoding': 'module Data.Text.Encoding where\n',
  'Data.Text.Lazy.Encoding': 'module Data.Text.Lazy.Encoding where\n',
  'Data.ByteString': 'module Data.ByteString where\n',
  'Data.ByteString.Lazy': 'module Data.ByteString.Lazy where\n',
  'Data.ByteString.Builder': 'module Data.ByteString.Builder where\n',
  'Data.Sequence': `module Data.Sequence where
data Seq a = Empty | Cons a (Seq a)
empty = Empty
foreign import javascript unsafe "(($1) => ({ tag: 'Cons', fields: [lazy(() => $1), lazy(() => ({ tag: 'Empty', fields: [] }))] }))" singleton :: a -> Seq a
foreign import javascript unsafe "(($1,$2) => { const snoc = (xs, x) => { const value = force(xs); if (!value || value.tag === 'Empty') return { tag: 'Cons', fields: [lazy(() => x), lazy(() => ({ tag: 'Empty', fields: [] }))] }; return { tag: 'Cons', fields: [value.fields[0], lazy(() => snoc(value.fields[1], x))] }; }; return snoc($1, $2); })" (|>) :: Seq a -> a -> Seq a
foreign import javascript unsafe "(($1,$2) => { const append = (xs, ys) => { const value = force(xs); if (!value || value.tag === 'Empty') return force(ys); return { tag: 'Cons', fields: [value.fields[0], lazy(() => append(value.fields[1], ys))] }; }; return append($1, $2); })" (<>) :: Seq a -> Seq a -> Seq a
foreign import javascript unsafe "(($1) => { const value = force($1); return !value || value.tag === 'Empty' || value.tag === '[]'; })" null :: Seq a -> Bool
foreign import javascript unsafe "(($1) => { let count = 0; let current = force($1); while (current && current.tag === 'Cons') { count++; current = force(current.fields[1]); } return count; })" length :: Seq a -> Int
foreign import javascript unsafe "(($1,$2) => { const empty = () => ({ tag: 'Empty', fields: [] }); const walk = (xs) => { const value = force(xs); if (!value || value.tag === 'Empty') return { tag: '(,)', fields: [lazy(empty), lazy(empty)] }; const keep = $1(force(value.fields[0])); const taken = keep && (keep.tag === 'True' || keep === true); if (!taken) return { tag: '(,)', fields: [lazy(empty), lazy(() => value)] }; const rest = walk(value.fields[1]); return { tag: '(,)', fields: [lazy(() => ({ tag: 'Cons', fields: [value.fields[0], rest.fields[0]] })), rest.fields[1]] }; }; return walk($2); })" spanl :: (a -> Bool) -> Seq a -> (Seq a, Seq a)
foreign import javascript unsafe "(($1,$2) => { const empty = () => ({ tag: 'Empty', fields: [] }); const walk = (n, xs) => { const value = force(xs); if (n <= 0 || !value || value.tag === 'Empty') return { tag: '(,)', fields: [lazy(empty), lazy(() => value && value.tag === 'Empty' ? value : (value ?? empty()))] }; const rest = walk(n - 1, value.fields[1]); return { tag: '(,)', fields: [lazy(() => ({ tag: 'Cons', fields: [value.fields[0], rest.fields[0]] })), rest.fields[1]] }; }; return walk(Number($1), $2); })" splitAt :: Int -> Seq a -> (Seq a, Seq a)
foreign import javascript unsafe "(($1,$2) => { const empty = () => ({ tag: 'Empty', fields: [] }); const walk = (xs) => { const value = force(xs); if (!value || value.tag === 'Empty') return empty(); const keep = $1(force(value.fields[0])); const taken = keep && (keep.tag === 'True' || keep === true); const rest = walk(value.fields[1]); return taken ? { tag: 'Cons', fields: [value.fields[0], lazy(() => rest)] } : rest; }; return walk($2); })" filter :: (a -> Bool) -> Seq a -> Seq a
`,
  'Data.Set': `module Data.Set where
data Set a = Set
foreign import javascript unsafe "(($1) => new Set(listToArray($1)))" fromList :: [a] -> Set a
foreign import javascript unsafe "(() => new Set())" empty :: Set a
foreign import javascript unsafe "(($1) => new Set([$1]))" singleton :: a -> Set a
foreign import javascript unsafe "(($1,$2) => $2.has($1))" member :: a -> Set a -> Bool
foreign import javascript unsafe "(($1,$2) => { const copy = new Set($2); copy.add($1); return copy; })" insert :: a -> Set a -> Set a
foreign import javascript unsafe "(($1,$2) => { const copy = new Set($2); copy.delete($1); return copy; })" delete :: a -> Set a -> Set a
foreign import javascript unsafe "(($1) => $1.size === 0)" null :: Set a -> Bool
foreign import javascript unsafe "(($1) => listFromArray([...$1]))" toList :: Set a -> [a]
`,
  'Data.Map': `module Data.Map where
data Map k v = Map
instance Semigroup (Map k v) where
  Map a <> Map b = Map a
instance Monoid (Map k v) where
  mempty = Map empty
foreign import javascript unsafe "(() => new Map())" empty :: Map k v
foreign import javascript unsafe "(($1) => new Map(listToArray($1).map(pair => [force(pair.fields[0]), force(pair.fields[1])])))" fromList :: [(k, v)] -> Map k v
foreign import javascript unsafe "(($1) => listFromArray([...$1.entries()].map(([k,v]) => ({ tag: '(,)', fields: [lazy(() => k), lazy(() => v)] }))))" toList :: Map k v -> [(k, v)]
foreign import javascript unsafe "(($1) => listFromArray([...$1.values()]))" elems :: Map k v -> [v]
foreign import javascript unsafe "(($1,$2) => $2.has($1) ? ({ tag: 'Just', fields: [lazy(() => $2.get($1))] }) : ({ tag: 'Nothing', fields: [] }))" lookup :: k -> Map k v -> Maybe v
foreign import javascript unsafe "(($1,$2) => $1.has($2) ? ({ tag: 'Just', fields: [lazy(() => $1.get($2))] }) : ({ tag: 'Nothing', fields: [] }))" (!?) :: Map k v -> k -> Maybe v
foreign import javascript unsafe "(($1,$2,$3) => { const copy = new Map($3); copy.set($1, $2); return copy; })" insert :: k -> v -> Map k v -> Map k v
foreign import javascript unsafe "(($1,$2) => { const copy = new Map($2); copy.delete($1); return copy; })" delete :: k -> Map k v -> Map k v
foreign import javascript unsafe "(($1) => $1.size === 0)" null :: Map k v -> Bool
foreign import javascript unsafe "(($1,$2,$3) => { const copy = new Map($3); if (copy.has($2)) copy.set($2, $1(copy.get($2))); return copy; })" adjust :: (a -> a) -> k -> Map k a -> Map k a
foreign import javascript unsafe "(($1,$2,$3) => { const copy = new Map($3); const current = copy.has($2) ? ({ tag: 'Just', fields: [lazy(() => copy.get($2))] }) : ({ tag: 'Nothing', fields: [] }); const next = $1(current); if (next && next.tag === 'Nothing') copy.delete($2); else if (next && next.tag === 'Just') copy.set($2, force(next.fields[0])); return copy; })" alter :: (Maybe a -> Maybe a) -> k -> Map k a -> Map k a
foreign import javascript unsafe "(($1,$2,$3) => $3.has($2) ? $3.get($2) : $1)" findWithDefault :: v -> k -> Map k v -> v
foreign import javascript unsafe "(($1) => { const entries = [...$1.entries()]; if (!entries.length) return { tag: 'Nothing', fields: [] }; const entry = entries[0]; return { tag: 'Just', fields: [lazy(() => ({ tag: '(,)', fields: [lazy(() => entry[0]), lazy(() => entry[1])] }))] }; })" lookupMin :: Map k a -> Maybe (k, a)
foreign import javascript unsafe "(($1,$2) => { const keys = [...$2.keys()]; const next = keys.find(k => { const left = force(k); const right = force($1); const lv = left && left.fields ? force(left.fields[0]) : left; const rv = right && right.fields ? force(right.fields[0]) : right; return lv > rv; }); if (next === undefined) return { tag: 'Nothing', fields: [] }; return { tag: 'Just', fields: [lazy(() => ({ tag: '(,)', fields: [lazy(() => next), lazy(() => $2.get(next))] }))] }; })" lookupGT :: Ord k => k -> Map k a -> Maybe (k, a)
`,
  'Data.Map.Strict': `module Data.Map.Strict where
data Map k v = Map
instance Semigroup (Map k v) where
  Map a <> Map b = Map a
instance Monoid (Map k v) where
  mempty = Map empty
foreign import javascript unsafe "(($1) => new Map(listToArray($1).map(pair => [force(pair.fields[0]), force(pair.fields[1])])))" fromList :: [(k, v)] -> Map k v
foreign import javascript unsafe "(($1) => listFromArray([...$1.entries()].map(([k,v]) => ({ tag: '(,)', fields: [lazy(() => k), lazy(() => v)] }))))" toList :: Map k v -> [(k, v)]
foreign import javascript unsafe "(($1,$2) => $2.has($1) ? ({ tag: 'Just', fields: [lazy(() => $2.get($1))] }) : ({ tag: 'Nothing', fields: [] }))" lookup :: k -> Map k v -> Maybe v
foreign import javascript unsafe "(($1,$2,$3) => { const copy = new Map($3); copy.set($1, $2); return copy; })" insert :: k -> v -> Map k v -> Map k v
foreign import javascript unsafe "(($1,$2) => { const copy = new Map($2); copy.delete($1); return copy; })" delete :: k -> Map k v -> Map k v
foreign import javascript unsafe "(($1) => $1.size === 0)" null :: Map k v -> Bool
`,
  'Data.IntMap.Strict': `module Data.IntMap.Strict where
data IntMap a = IntMap
foreign import javascript unsafe "(() => new Map())" empty :: IntMap a
foreign import javascript unsafe "(($1,$2) => { const m = $2 instanceof Map ? $2 : ($2 && $2.value instanceof Map ? $2.value : null); if (!m) return { tag: 'Nothing', fields: [] }; const key = typeof $1 === 'number' ? $1 : Number($1); if (m.has($1)) return { tag: 'Just', fields: [lazy(() => m.get($1))] }; if (m.has(key)) return { tag: 'Just', fields: [lazy(() => m.get(key))] }; for (const k of m.keys()) { if (k == $1 || k == key) return { tag: 'Just', fields: [lazy(() => m.get(k))] }; } return { tag: 'Nothing', fields: [] }; })" lookup :: Int -> IntMap a -> Maybe a
foreign import javascript unsafe "(($1,$2) => $1.get($2))" (!) :: IntMap a -> Int -> a
foreign import javascript unsafe "(($1,$2,$3) => { const copy = new Map($3 instanceof Map ? $3 : []); const key = typeof $1 === 'number' ? $1 : Number($1); copy.set(Number.isFinite(key) ? key : $1, $2); return copy; })" insert :: Int -> a -> IntMap a -> IntMap a
foreign import javascript unsafe "(($1,$2) => { const copy = new Map($2); copy.delete($1); return copy; })" delete :: Int -> IntMap a -> IntMap a
foreign import javascript unsafe "(($1) => $1.size === 0)" null :: IntMap a -> Bool
foreign import javascript unsafe "(($1) => $1.size)" size :: IntMap a -> Int
foreign import javascript unsafe "(($1) => listFromArray([...$1.values()]))" elems :: IntMap a -> [a]
foreign import javascript unsafe "(($1,$2,$3) => { const copy = new Map($3); const current = copy.has($2) ? ({ tag: 'Just', fields: [lazy(() => copy.get($2))] }) : ({ tag: 'Nothing', fields: [] }); const next = $1(current); if (next && next.tag === 'Nothing') copy.delete($2); else if (next && next.tag === 'Just') copy.set($2, force(next.fields[0])); return copy; })" alter :: (Maybe a -> Maybe a) -> Int -> IntMap a -> IntMap a
foreign import javascript unsafe "(($1,$2,$3) => $3.has($2) ? $3.get($2) : $1)" findWithDefault :: a -> Int -> IntMap a -> a
foreign import javascript unsafe "(($1,$2,$3) => { const copy = new Map($3); if (copy.has($2)) copy.set($2, $1(copy.get($2))); return copy; })" adjust :: (a -> a) -> Int -> IntMap a -> IntMap a
foreign import javascript unsafe "(($1,$2,$3,$4) => { const copy = new Map($4); copy.set($2, copy.has($2) ? $1(copy.get($2))($3) : $3); return copy; })" insertWith :: (a -> a -> a) -> Int -> a -> IntMap a -> IntMap a
`,
  'Data.IntSet': `module Data.IntSet where
data IntSet = IntSet
foreign import javascript unsafe "(() => new Set())" empty :: IntSet
foreign import javascript unsafe "(($1) => new Set(listToArray($1)))" fromList :: [Int] -> IntSet
foreign import javascript unsafe "(($1) => new Set([$1]))" singleton :: Int -> IntSet
foreign import javascript unsafe "(($1,$2) => $2.has($1))" member :: Int -> IntSet -> Bool
foreign import javascript unsafe "(($1,$2) => { const copy = new Set($2); copy.add($1); return copy; })" insert :: Int -> IntSet -> IntSet
foreign import javascript unsafe "(($1,$2) => { const copy = new Set($2); copy.delete($1); return copy; })" delete :: Int -> IntSet -> IntSet
foreign import javascript unsafe "(($1) => $1.size === 0)" null :: IntSet -> Bool
foreign import javascript unsafe "(($1) => listFromArray([...$1]))" toList :: IntSet -> [Int]
`,
  'Data.List': `module Data.List where
foreign import javascript unsafe "(($1) => { const seen = new Set(); const out = []; for (const item of listToArray($1)) { const key = typeof item === 'string' || typeof item === 'number' ? item : JSON.stringify(item); if (seen.has(key)) continue; seen.add(key); out.push(item); } return listFromArray(out); })" nub :: Eq a => [a] -> [a]
foreign import javascript unsafe "(($1,$2) => listFromArray(listToArray($2).sort((left, right) => { const a = force($1(left)); const b = force($1(right)); return a < b ? -1 : a > b ? 1 : 0; })))" sortOn :: Ord b => (a -> b) -> [a] -> [a]
`,
  'Data.Time.Clock': `module Data.Time.Clock where
data DiffTime = DiffTime
`,
  'Data.Time.Format': `module Data.Time.Format where
data TimeLocale = TimeLocale
foreign import javascript unsafe "(() => null)" defaultTimeLocale :: TimeLocale
foreign import javascript unsafe "(($1,$2,$3) => { const raw = force($2); const fmt = typeof raw === 'string' ? raw : listToArray(raw).join(''); const secs = Math.max(0, Math.floor(Number(force($3)))); const hours = Math.floor(secs / 3600); const minutes = Math.floor((secs % 3600) / 60); const seconds = secs % 60; const pad = (n) => String(n).padStart(2, '0'); return fmt.includes('%h') ? hours + ':' + pad(minutes) + ':' + pad(seconds) : pad(minutes) + ':' + pad(seconds); })" formatTime :: TimeLocale -> String -> t -> String
`,
  // These boot modules deliberately provide executable declarations, not an
  // empty interface that merely hides resolution failures.  Their small JS
  // representations are compiler runtime primitives and are shared by every
  // package; they are not a substitute for any Miso module.
  'Data.IORef': `module Data.IORef where
data IORef a = IORef a
foreign import javascript unsafe "(($1) => ({ value: $1 }))" newIORef :: a -> IO (IORef a)
foreign import javascript unsafe "(($1) => force($1.value))" readIORef :: IORef a -> IO a
foreign import javascript unsafe "(($1,$2) => { $1.value = force($2); })" writeIORef :: IORef a -> a -> IO ()
foreign import javascript unsafe "(($1,$2) => { $1.value = apply($2, lazy(() => force($1.value))); })" modifyIORef :: IORef a -> (a -> a) -> IO ()
foreign import javascript unsafe "(($1,$2) => { const next = force(apply($2, lazy(() => force($1.value)))); $1.value = next; })" modifyIORef' :: IORef a -> (a -> a) -> IO ()
foreign import javascript unsafe "(($1,$2) => { const pair = force(apply($2, lazy(() => force($1.value)))); $1.value = force(pair.fields[0]); return force(pair.fields[1]); })" atomicModifyIORef' :: IORef a -> (a -> (a, b)) -> IO b
foreign import javascript unsafe "(($1,$2) => { $1.value = force($2); })" atomicWriteIORef :: IORef a -> a -> IO ()
`,
  'Control.Applicative': `module Control.Applicative where
foreign import javascript unsafe "(($1) => $1)" empty :: f a
foreign import javascript unsafe "(($1) => $1)" many :: f a -> f [a]
foreign import javascript unsafe "(($1) => $1)" some :: f a -> f [a]
foreign import javascript unsafe "(($1) => $1)" optional :: f a -> f (Maybe a)
foreign import javascript unsafe "(($1,$2) => $1)" (<|>) :: f a -> f a -> f a
foreign import javascript unsafe "(($1,$2) => $1)" (<*) :: f a -> f b -> f a
foreign import javascript unsafe "(($1,$2) => $2)" (*>) :: f a -> f b -> f b
foreign import javascript unsafe "(($1,$2) => $1)" (<*>) :: f (a -> b) -> f a -> f b
foreign import javascript unsafe "(($1,$2,$3) => $1)" liftA2 :: (a -> b -> c) -> f a -> f b -> f c
`,
  'Control.Arrow': 'module Control.Arrow where\n',
  'Control.Category': 'module Control.Category where\n',
  'Control.Concurrent': `module Control.Concurrent where
data MVar a = MVar
data ThreadId = ThreadId
data ThreadStatus = ThreadRunning | ThreadFinished | ThreadDied | ThreadBlocked
foreign import javascript unsafe "/* ghcjs-newEmptyMVar */ (() => ({ queue: [], waiters: [] }))" newEmptyMVar :: IO (MVar a)
foreign import javascript unsafe "/* ghcjs-takeMVar */ (($1) => $1.queue.shift())" takeMVar :: MVar a -> IO a
foreign import javascript unsafe "/* ghcjs-putMVar */ (($1,$2) => { $1.queue.push($2); })" putMVar :: MVar a -> a -> IO ()
foreign import javascript unsafe "/* ghcjs-readMVar */ (($1) => $1.queue[0])" readMVar :: MVar a -> IO a
foreign import javascript unsafe "/* ghcjs-tryPutMVar */ (($1,$2) => { if ($1.queue.length) return false; $1.queue.push($2); return true; })" tryPutMVar :: MVar a -> a -> IO Bool
foreign import javascript unsafe "(($1) => setTimeout($1, 0))" forkIO :: IO () -> IO ThreadId
foreign import javascript unsafe "/* ghcjs-threadDelay */ (($1) => { const ms = Math.max(0, Number($1) / 1000); if (!(ms > 0)) return; const end = Date.now() + ms; while (Date.now() < end); })" threadDelay :: Int -> IO ()
foreign import javascript unsafe "(($1) => ({ tag: 'ThreadRunning', fields: [] }))" threadStatus :: ThreadId -> IO ThreadStatus
`,
  'GHC.Conc': `module GHC.Conc where
import Control.Concurrent (ThreadStatus(ThreadDied, ThreadFinished, ThreadRunning, ThreadBlocked), threadStatus)
`,
  'Control.Exception': `module Control.Exception where
data SomeException = SomeException
foreign import javascript unsafe "(($1) => $1)" throwIO :: e -> IO a
foreign import javascript unsafe "/* io-catch */ (($1,$2) => { try { return force($1); } catch (e) { return force(apply($2, lazy(() => e))); } })" catch :: IO a -> (e -> IO a) -> IO a
foreign import javascript unsafe "(($1,$2,$3) => { const resource = force($1); try { return force(apply($3, lazy(() => resource))); } catch (e) { try { force(apply($2, lazy(() => resource))); } catch (_) {} throw e; } })" bracket :: IO a -> (a -> IO b) -> (a -> IO c) -> IO c
`,
  'Control.Monad': `module Control.Monad where
void action = action >> pure ()
when condition action = if condition then action else pure ()
unless condition action = if condition then pure () else action
join action = action >>= id
(<=<) f g value = f =<< g value
forever action = action >> forever action
foreign import javascript unsafe "(($1,$2) => { const walk = (xs) => { const value = force(xs); if (!value || value.tag === '[]' || value.tag === 'Nothing' || value.tag === 'Empty' || value.tag === 'Left') return; if (value.tag === 'Just' || value.tag === 'Right') { force(apply($2, value.fields[0])); return; } if (value.tag === ':' || value.tag === 'Cons') { force(apply($2, value.fields[0])); walk(value.fields[1]); } }; walk($1); })" forM_ :: t a -> (a -> m b) -> m ()
forM values action = mapM action values
foldM _ initial [] = pure initial
foldM step initial (value : values) = step initial value >>= \\next -> foldM step next values
zipWithM_ _ [] _ = pure ()
zipWithM_ _ _ [] = pure ()
zipWithM_ action (left : lefts) (right : rights) = action left right >> zipWithM_ action lefts rights
foreign import javascript unsafe "(($1,$2) => $2)" mapM_ :: (a -> m b) -> [a] -> m ()
foreign import javascript unsafe "(($1) => $1)" sequence_ :: [m a] -> m ()
foreign import javascript unsafe "(($1) => undefined)" guard :: Bool -> m ()
foreign import javascript unsafe "(($1) => { throw new Error($1); })" fail :: String -> m a
`,
  'Control.Monad.Identity': 'module Control.Monad.Identity where\n',
  'Control.Monad.IO.Class': `module Control.Monad.IO.Class where
liftIO action = action
`,
  'Control.Monad.Reader': `module Control.Monad.Reader where
foreign import javascript unsafe "(() => rws.reader)" ask :: m r
foreign import javascript unsafe "(($1) => apply($1, lazy(() => rws.reader)))" asks :: (r -> a) -> m a
`,
  'Control.Monad.State': `module Control.Monad.State where
foreign import javascript unsafe "(() => rws.state)" get :: m s
foreign import javascript unsafe "(($1) => apply($1, lazy(() => rws.state)))" gets :: (s -> a) -> m a
foreign import javascript unsafe "(($1) => { rws.state = $1; return ({ tag: '()', fields: [] }); })" put :: s -> m ()
foreign import javascript unsafe "(($1) => { rws.state = apply($1, lazy(() => rws.state)); return ({ tag: '()', fields: [] }); })" modify :: (s -> s) -> m ()
foreign import javascript unsafe "(($1) => { const pair = force(apply($1, lazy(() => rws.state))); rws.state = force(pair.fields[1]); return force(pair.fields[0]); })" state :: (s -> (a, s)) -> m a
foreign import javascript unsafe "/* rws-run */ (($1,$2) => { const prevReader = rws.reader, prevState = rws.state, prevWriter = rws.writer; rws.state = $2; rws.writer = ({ tag: '[]', fields: [] }); try { const forced = force($1); if (typeof forced === 'function') { const result = force(apply(apply(lazy(() => forced), lazy(() => null)), lazy(() => $2))); if (result && result.tag === '(,,)') return force(result.fields[1]); } return rws.state; } finally { rws.reader = prevReader; rws.state = prevState; rws.writer = prevWriter; } })" execState :: m s -> s -> s
`,
  'Control.Monad.RWS': `module Control.Monad.RWS where
data RWS r w s a = RWS
foreign import javascript unsafe "(() => rws.state)" get :: m s
foreign import javascript unsafe "(($1) => apply($1, lazy(() => rws.state)))" gets :: (s -> a) -> m a
foreign import javascript unsafe "(($1) => { rws.state = $1; return ({ tag: '()', fields: [] }); })" put :: s -> m ()
foreign import javascript unsafe "(($1) => { rws.state = apply($1, lazy(() => rws.state)); return ({ tag: '()', fields: [] }); })" modify :: (s -> s) -> m ()
foreign import javascript unsafe "(($1) => { rws.writer = listFromArray(listToArray(rws.writer).concat(listToArray($1))); return ({ tag: '()', fields: [] }); })" tell :: w -> m ()
foreign import javascript unsafe "/* rws-censor */ (($1,$2) => { const saved = rws.writer; rws.writer = ({ tag: '[]', fields: [] }); force($2); rws.writer = listFromArray(listToArray(saved).concat(listToArray(apply($1, lazy(() => rws.writer))))); return ({ tag: '()', fields: [] }); })" censor :: (w -> w) -> m a -> m a
foreign import javascript unsafe "/* rws-run */ (($1,$2,$3) => { const prevReader = rws.reader, prevState = rws.state, prevWriter = rws.writer; rws.reader = $2; rws.state = $3; rws.writer = ({ tag: '[]', fields: [] }); try { const forced = force($1); if (typeof forced === 'function') { const result = force(apply(apply(lazy(() => forced), lazy(() => $2)), lazy(() => $3))); if (result && result.tag === '(,,)') return ({ tag: '(,)', fields: [result.fields[1], result.fields[2]] }); } const outState = rws.state, outWriter = rws.writer; return ({ tag: '(,)', fields: [lazy(() => outState), lazy(() => outWriter)] }); } finally { rws.reader = prevReader; rws.state = prevState; rws.writer = prevWriter; } })" execRWS :: RWS r w s a -> r -> s -> (s, w)
`,
  'Control.Monad.Trans.Maybe': 'module Control.Monad.Trans.Maybe where\n',
  'System.IO.Unsafe': `module System.IO.Unsafe where
foreign import javascript unsafe "(($1) => $1)" unsafePerformIO :: IO a -> a
`,
  Numeric: `module Numeric where
-- Keep the parsed word as its exact hexadecimal spelling.  JavaScript has
-- no lossless Word64 primitive; GHCJS likewise carries Fingerprint words as
-- an opaque representation at this boundary.
foreign import javascript unsafe "(($1) => { const s = jsString($1); if (!/^[0-9a-fA-F]+$/.test(s)) return ({ tag: '[]', fields: [] }); return ({ tag: ':', fields: [{ tag: '(,)', fields: [s.toLowerCase(), ''] }, { tag: '[]', fields: [] }] }); })" readHex :: String -> [(a, String)]
`,
  'Text.Read': `module Text.Read where
readMaybe :: String -> Maybe a
`,
  'GHC.Generics': 'module GHC.Generics where\n',
  'GHC.TypeLits': 'module GHC.TypeLits where\n',
  'GHC.Natural': 'module GHC.Natural where\n',
  'GHC.StaticPtr': `module GHC.StaticPtr where
data StaticPtr a = StaticPtr a
type StaticKey = Fingerprint
deRefStaticPtr :: StaticPtr a -> a
staticKey :: StaticPtr a -> StaticKey
unsafeLookupStaticPtr :: StaticKey -> IO (Maybe (StaticPtr a))
`,
  'GHC.Fingerprint': `module GHC.Fingerprint where
data Fingerprint = Fingerprint String
`,
  'GHC.OverloadedLabels': 'module GHC.OverloadedLabels where\n',
  Foreign: 'module Foreign where\n',
  'Foreign.C.Types': 'module Foreign.C.Types where\n',
  'System.Mem': 'module System.Mem where\n',
  'System.Mem.StableName': `module System.Mem.StableName where
data StableName a = StableName a
foreign import javascript unsafe "(($1) => $1)" makeStableName :: a -> IO (StableName a)
`,
  'Data.JSString': `module Data.JSString where
type JSString = String
foreign import javascript unsafe "(($1) => $1)" pack :: String -> JSString
foreign import javascript unsafe "(($1) => $1)" unpack :: JSString -> String
foreign import javascript unsafe "(($1) => $1.length === 0)" null :: JSString -> Bool
foreign import javascript unsafe "(($1) => $1.trim())" strip :: JSString -> JSString
foreign import javascript unsafe "(($1) => $1.toLowerCase())" toLower :: JSString -> JSString
foreign import javascript unsafe "(($1) => $1.toUpperCase())" toUpper :: JSString -> JSString
foreign import javascript unsafe "(($1,$2) => $2.includes($1))" isInfixOf :: JSString -> JSString -> Bool
foreign import javascript unsafe "(($1,$2) => $2.startsWith($1))" isPrefixOf :: JSString -> JSString -> Bool
foreign import javascript unsafe "(($1,$2) => $2.endsWith($1))" isSuffixOf :: JSString -> JSString -> Bool
foreign import javascript unsafe "(($1,$2) => $2.endsWith($1) ? ({ tag: 'Just', fields: [lazy(() => $2.slice(0, $2.length - $1.length))] }) : ({ tag: 'Nothing', fields: [] }))" stripSuffix :: JSString -> JSString -> Maybe JSString
foreign import javascript unsafe "(($1,$2) => $2.slice(0, $1))" take :: Int -> JSString -> JSString
foreign import javascript unsafe "(($1,$2) => $2.slice($1))" drop :: Int -> JSString -> JSString
foreign import javascript unsafe "(($1,$2) => { let i = 0; while (i < $2.length && $1($2[i])) i++; return $2.slice(i); })" dropWhile :: (Char -> Bool) -> JSString -> JSString
foreign import javascript unsafe "(($1) => $1.length ? ({ tag: 'Just', fields: [lazy(() => ({ tag: '(,)', fields: [lazy(() => $1[0]), lazy(() => $1.slice(1))] }))] }) : ({ tag: 'Nothing', fields: [] }))" uncons :: JSString -> Maybe (Char, JSString)
foreign import javascript unsafe "(($1,$2) => listToArray($2).join(force($1)))" intercalate :: JSString -> [JSString] -> JSString
foreign import javascript unsafe "(($1) => listToArray($1).join(''))" concat :: [JSString] -> JSString
foreign import javascript unsafe "(($1) => listToArray($1).join(' '))" unwords :: [JSString] -> JSString
foreign import javascript unsafe "(($1) => $1)" singleton :: Char -> JSString
foreign import javascript unsafe "(($1,$2) => listToArray($2).map($1).join(''))" concatMap :: (a -> JSString) -> [a] -> JSString
foreign import javascript unsafe "(($1) => listToArray($1).join(String.fromCharCode(10)))" unlines :: [JSString] -> JSString
foreign import javascript unsafe "(($1) => $1.length)" length :: JSString -> Int
foreign import javascript unsafe "(($1,$2) => $2.repeat($1))" replicate :: Int -> JSString -> JSString
`,
  'Data.JSString.Text': 'module Data.JSString.Text where\n',
  'GHCJS.Marshal': `module GHCJS.Marshal where
foreign import javascript unsafe "(($1) => $1)" toJSVal :: a -> IO JSVal
foreign import javascript unsafe "(($1) => $1)" fromJSVal :: JSVal -> IO (Maybe a)
foreign import javascript unsafe "(($1) => $1)" fromJSValUnchecked :: JSVal -> IO a
`,
  'GHCJS.Types': 'module GHCJS.Types where\ndata JSVal = JSVal\n',
  'GHC.JS.Prim': `module GHC.JS.Prim where
foreign import javascript unsafe "(($1) => $1)" jsval :: a -> JSVal
foreign import javascript unsafe "(($1) => $1 == null)" isNull :: JSVal -> Bool
foreign import javascript unsafe "(($1) => $1 === undefined)" isUndefined :: JSVal -> Bool
foreign import javascript unsafe "(() => null)" jsNull :: JSVal
`,
  'GHC.JS.Foreign.Callback': `module GHC.JS.Foreign.Callback where
data OnBlocked = ThrowWouldBlock
foreign import javascript unsafe "(($1) => { const action = $1; const cb = (...args) => { let current = action; for (const arg of args) current = apply(current, lazy(() => arg)); return force(current); }; return cb; })" asyncCallback :: IO () -> IO Callback
foreign import javascript unsafe "(($1) => { const fn = $1; const cb = (...args) => { let current = fn; for (const arg of args) current = apply(current, lazy(() => arg)); return force(current); }; return cb; })" asyncCallback1 :: (JSVal -> IO ()) -> IO Callback
foreign import javascript unsafe "(($1) => { const fn = $1; const cb = (...args) => { let current = fn; for (const arg of args) current = apply(current, lazy(() => arg)); return force(current); }; return cb; })" asyncCallback2 :: (JSVal -> JSVal -> IO ()) -> IO Callback
foreign import javascript unsafe "(($1) => { const fn = $1; const cb = (...args) => { let current = fn; for (const arg of args) current = apply(current, lazy(() => arg)); return force(current); }; return cb; })" asyncCallback3 :: (JSVal -> JSVal -> JSVal -> IO ()) -> IO Callback
foreign import javascript unsafe "(($1,$2) => { const action = $2; const cb = (...args) => { let current = action; for (const arg of args) current = apply(current, lazy(() => arg)); return force(current); }; return cb; })" syncCallback :: OnBlocked -> IO () -> IO Callback
foreign import javascript unsafe "(($1,$2) => { const fn = $2; const cb = (...args) => { let current = fn; for (const arg of args) current = apply(current, lazy(() => arg)); return force(current); }; return cb; })" syncCallback1 :: OnBlocked -> (JSVal -> IO ()) -> IO Callback
foreign import javascript unsafe "(($1,$2) => { const fn = $2; const cb = (...args) => { let current = fn; for (const arg of args) current = apply(current, lazy(() => arg)); return force(current); }; return cb; })" syncCallback2 :: OnBlocked -> (JSVal -> JSVal -> IO ()) -> IO Callback
foreign import javascript unsafe "(($1,$2) => { const fn = $2; const cb = (...args) => { let current = fn; for (const arg of args) current = apply(current, lazy(() => arg)); return force(current); }; return cb; })" syncCallback3 :: OnBlocked -> (JSVal -> JSVal -> JSVal -> IO ()) -> IO Callback
foreign import javascript unsafe "(($1) => { const action = $1; const cb = (...args) => { let current = action; for (const arg of args) current = apply(current, lazy(() => arg)); return force(current); }; return cb; })" syncCallback' :: IO JSVal -> IO Callback
foreign import javascript unsafe "(($1) => { const fn = $1; const cb = (...args) => { let current = fn; for (const arg of args) current = apply(current, lazy(() => arg)); return force(current); }; return cb; })" syncCallback1' :: (JSVal -> IO JSVal) -> IO Callback
foreign import javascript unsafe "(($1) => { const fn = $1; const cb = (...args) => { let current = fn; for (const arg of args) current = apply(current, lazy(() => arg)); return force(current); }; return cb; })" syncCallback2' :: (JSVal -> JSVal -> IO JSVal) -> IO Callback
foreign import javascript unsafe "(($1) => { const fn = $1; const cb = (...args) => { let current = fn; for (const arg of args) current = apply(current, lazy(() => arg)); return force(current); }; return cb; })" syncCallback3' :: (JSVal -> JSVal -> IO JSVal) -> IO Callback
`,
};

export function bootModuleSource(name: string): string | undefined { return sources[name]; }
