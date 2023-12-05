module AOC23.Day2

import AOC23.Util
import Data.List1
import Data.Morphisms
import Data.String
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Subset
--------------------------------------------------------------------------------

record Subset where
  constructor S
  red   : Nat
  green : Nat
  blue  : Nat

%runElab derive "Subset" [Show,Eq]

Semigroup Subset where
  S r1 g1 b1 <+> S r2 g2 b2 = S (max r1 r2) (max g1 g2) (max b1 b2)

Monoid Subset where
  neutral = S 0 0 0

power : Subset -> Nat
power s = s.red * s.green * s.blue

possible : (bag, ss : Subset) -> Bool
possible bag ss = ss <+> bag == bag

--------------------------------------------------------------------------------
-- Game
--------------------------------------------------------------------------------

record Game where
  constructor G
  nr      : Nat
  subsets : List Subset

%runElab derive "Game" [Show,Eq]

possibleGame : (bag : Subset) -> Game -> Bool
possibleGame bag = all (possible bag) . subsets

--------------------------------------------------------------------------------
-- Parser
--------------------------------------------------------------------------------

readSubset : String -> Subset
readSubset s = (foldMap (val . words) (trimSplit ',' s)).applyEndo neutral
  where
    val : List String -> Endomorphism Subset
    val [n, "blue"]  = Endo {blue  := cast n}
    val [n, "red"]   = Endo {red   := cast n}
    val [n, "green"] = Endo {green := cast n}
    val _            = Endo id

readGame : String -> Either String Game
readGame s =
  let [g,ss]     := trimSplit ':' s | _ => Left "invalid input: \{s}"
      ["Game",n] := words g         | _ => Left "invalid input: \{s}"
   in Right . G (cast n) $ map readSubset (trimSplit ';' ss)

--------------------------------------------------------------------------------
-- Part 1
--------------------------------------------------------------------------------

bag : Subset
bag = S {red = 12, green = 13, blue = 14}

part1 : List Game -> Nat
part1 = sum . map nr . filter (possibleGame bag)

--------------------------------------------------------------------------------
-- Part 2
--------------------------------------------------------------------------------

part2 : List Game -> Nat
part2 = sum . map (power . concat . subsets)

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main : IO ()
main = do
  ls <- lines "day2"
  Right gs <- pure $ traverse readGame ls | Left err => putStrLn err
  printLn (part1 gs)
  printLn (part2 gs)
