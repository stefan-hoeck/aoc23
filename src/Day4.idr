module AOC23.Day4

import Data.Bits
import Data.SortedSet
import Data.Vect
import AOC23.Util

%default total

record Card where
  constructor C
  nr      : Nat
  copies  : Nat
  numbers : SortedSet Nat
  winning : SortedSet Nat

matches : Card -> Nat
matches c = length . SortedSet.toList $ intersection c.numbers c.winning

points : Card -> Integer
points c =
  case matches c of
    0   => 0
    S n => 1 `shiftL` n

empty : Card
empty = C 0 0 empty empty

readCard : String -> Card
readCard s =
  let [x1,x2]    := trimSplit ':' s                           | _ => empty
      ["Card",n] := words x1                                  | _ => empty
      [ns,ws]    := map (map cast . words) $ trimSplit '|' x2 | _ => empty
   in C (cast n) 1 (fromList ns) (fromList ws)

inc : Nat -> Nat -> Vect n Card -> Vect n Card
inc (S k) j (x :: xs) = {copies $= plus j} x :: inc k j xs
inc _     j xs        = xs

countCopies : Nat -> Vect n Card -> Nat
countCopies n []       = n
countCopies n (h :: t) = countCopies (n + h.copies) (inc (matches h) h.copies t)

part1 : List String -> Integer
part1 = sum . map (points . readCard)

part2 : List String -> Nat
part2 ls = countCopies 0 $ fromList (map readCard ls)

main : IO ()
main = do
  ls <- lines "day4"
  printLn (part1 ls)
  printLn (part2 ls)
