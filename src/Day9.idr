module Day9

import Data.Vect
import Util

%default total

diffs : Integer -> Vect n Integer -> Vect n Integer
diffs i []        = []
diffs i (x :: xs) = (i - x) :: diffs x xs

solve : Vect n Integer -> Integer
solve []        = 0
solve (x :: xs) = x + solve (diffs x xs)

part1 : String -> Integer
part1 xs = solve $ fromList $ (reverse . map cast . words) xs

part2 : String -> Integer
part2 xs = solve $ fromList $ (map cast . words) xs

export
main : IO ()
main = do
  ls <- lines "day9"
  putStrLn "day  9 part 1: \{show . sum $ map part1 ls}"
  putStrLn "day  9 part 2: \{show . sum $ map part2 ls}"
