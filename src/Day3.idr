module Day3

import Util
import Data.String
import Data.Vect

%default total

isSym : Char -> Bool
isSym '.' = False
isSym c   = not $ isDigit c

addDigit : Nat -> Char -> Nat
addDigit n x = n * 10 + (cast $ ord x - 48)

lineNums :
     (num     : Nat)
  -> (include : Bool)
  -> (top, cur, bot : Vect k Char)
  -> List Nat 
lineNums n i []      []      []      = if n > 0 && i then [n] else []
lineNums n i (t::ts) (c::cs) (b::bs) =
  let i' := any {t = List} isSym [t,c,b]
   in if isDigit c
        then lineNums (addDigit n c) (i || i') ts cs bs
        else
          if n > 0 && (i || i')
            then n :: lineNums 0 i' ts cs bs
            else lineNums 0 i' ts cs bs

next : Nat -> Char -> Nat
next n c = if isDigit c then addDigit n c else 0

pre : Nat -> Vect k Char -> Nat
pre n []        = n
pre n (x :: xs) = if isDigit x then pre (addDigit n x) xs else n

num : Nat -> Char -> Vect k Char -> List Nat
num n c xs =
  if isDigit c
     then [pre (addDigit n c) xs]
     else filter (0 /=) [n,pre 0 xs]

gears : (n1,n2,n3 : Nat) -> (top, cur, bot : Vect k Char) -> List Nat 
gears n1 n2 n3 []      []        []      = []
gears n1 n2 n3 (t::ts) ('*'::cs) (b::bs) =
  case num n1 t ts ++ num n2 '*' cs ++ num n3 b bs of
    [x,y] => x * y :: gears (next n1 t) 0 (next n3 b) ts cs bs
    _     => gears (next n1 t) 0 (next n3 b) ts cs bs
gears n1 n2 n3 (t::ts) (c::cs) (b::bs) =
  gears (next n1 t) (next n2 c) (next n3 b) ts cs bs

parameters {k : Nat}
  dots : Vect k Char
  dots = replicate k '.'

  allNums : Vect k Char -> List (Vect k Char) -> List Nat
  allNums top []            = []
  allNums top [x]           = lineNums 0 False top x dots
  allNums top (x::t@(b::_)) = lineNums 0 False top x b ++ allNums x t

  allGears : Vect k Char -> List (Vect k Char) -> List Nat
  allGears top []            = []
  allGears top [x]           = gears 0 0 0 top x dots
  allGears top (x::t@(b::_)) = gears 0 0 0 top x b ++ allGears x t

klines : List String -> (k ** List (Vect k Char))
klines []        = (0 ** [])
klines (x :: xs) =
  let k := length x
   in (k ** mapMaybe (toVect k . unpack) (x::xs))

part1 : List String -> Nat
part1 ls = let (k ** css) := klines ls in sum $ allNums dots css

part2 : List String -> Nat
part2 ls = let (k ** css) := klines ls in sum $ allGears dots css

main : IO ()
main = do
  ls <- lines "day3"
  printLn (part1 ls)
  printLn (part2 ls)
