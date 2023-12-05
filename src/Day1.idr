module Day1

import Util

%default total

digit : Char -> List Nat
digit x = if isDigit x then [cast $ ord x - 48] else []

toNat : List Nat -> Nat
toNat []     = 0
toNat (h::t) = h * 10 + foldl (const id) h t

digits : List Char -> List Nat
digits []                               = []
digits ('o'::t@('n'::'e'::_))           = 1 :: digits t
digits ('t'::t@('w'::'o'::_))           = 2 :: digits t
digits ('t'::t@('h'::'r'::'e'::'e'::_)) = 3 :: digits t
digits ('f'::t@('o'::'u'::'r'::_))      = 4 :: digits t
digits ('f'::t@('i'::'v'::'e'::_))      = 5 :: digits t
digits ('s'::t@('i'::'x'::_))           = 6 :: digits t
digits ('s'::t@('e'::'v'::'e'::'n'::_)) = 7 :: digits t
digits ('e'::t@('i'::'g'::'h'::'t'::_)) = 8 :: digits t
digits ('n'::t@('i'::'n'::'e'::_))      = 9 :: digits t
digits (x :: xs)                        = digit x ++ digits xs

num : String -> Nat
num = toNat . (>>= digit) . unpack

num2 : String -> Nat
num2 = toNat . digits . unpack

main : IO ()
main = do
  ls <- lines "day1"
  printLn (sum $ toNat . digits . unpack <$> ls)
