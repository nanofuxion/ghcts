/** The minimal Prelude the dictionary-passing frontend needs, as ordinary
 * Haskell compiled through the same pipeline as user code.
 *
 * Nothing here is a builtin pretending to be a class method: `+`, `==`, `show`
 * are genuine class methods, selected from genuine dictionaries. The only
 * primitives are the `prim*` names `src/desugar.ts` maps onto JS-backend
 * primops, and they are typed over the *unboxed* types `IntPrim`/`CharPrim` -
 * never over `Int`, which is the boxed `I IntPrim` this module declares.
 *
 * Two shapes are deliberate:
 *
 *   - the comparison primops return `Bool`, not `IntPrim`. `IntLtOp` yields a
 *     0/1 machine value; wrapping it into a real constructor is GHC's
 *     `tagToEnum# (<# a b)` and it happens once, in the desugarer, so no
 *     Haskell here ever has to `case` on a raw machine word.
 *   - class and instance bodies stay on one line each. Class/instance member
 *     slices are re-parsed from their tokens (`src/dictionary.ts`), which
 *     joins them with spaces and so cannot preserve layout. Anything that
 *     wants `case`/`where` lives in a top-level helper instead.
 */
export const PRELUDE_SOURCE = `module GHCTS.Prelude where

data Bool = False | True
data Int = I IntPrim
data Char = C CharPrim

class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool
  (/=) x y = not (x == y)

class Eq a => Ord a where
  (<) :: a -> a -> Bool
  (<=) :: a -> a -> Bool
  (>) :: a -> a -> Bool
  (>=) :: a -> a -> Bool

class Num a where
  (+) :: a -> a -> a
  (-) :: a -> a -> a
  (*) :: a -> a -> a
  negate :: a -> a
  fromInteger :: IntPrim -> a

class Show a where
  show :: a -> [Char]

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

instance Eq Bool where
  (==) a b = eqBool a b

instance Show Bool where
  show b = showBool b

otherwise :: Bool
otherwise = True

not :: Bool -> Bool
not b = if b then False else True

eqBool :: Bool -> Bool -> Bool
eqBool a b = if a then b else not b

showBool :: Bool -> [Char]
showBool b = if b then "True" else "False"

showInt :: Int -> [Char]
showInt (I n) = if primIntLt n 0 then C (primChr 45) : digitsOf (primIntNeg n) [] else digitsOf n []

digitsOf :: IntPrim -> [Char] -> [Char]
digitsOf n acc = if primIntLt n 10 then digitChar n : acc else digitsOf (primIntQuot n 10) (digitChar (primIntRem n 10) : acc)

digitChar :: IntPrim -> Char
digitChar n = C (primChr (primIntAdd n 48))

append :: [a] -> [a] -> [a]
append xs ys = case xs of
  [] -> ys
  (z : zs) -> z : append zs ys

foreign import javascript unsafe "(() => '')" jsEmptyString :: JSString
foreign import javascript unsafe "((s,c) => s + String.fromCharCode(c))" jsSnocChar :: JSString -> CharPrim -> JSString

toJSString :: [Char] -> JSString
toJSString cs = jsStringGo jsEmptyString cs

jsStringGo :: JSString -> [Char] -> JSString
jsStringGo acc cs = case cs of
  [] -> acc
  (C c : rest) -> jsStringGo (jsSnocChar acc c) rest
`;
