module Day7

import Data.SortedMap
import Data.Vect
import Derive.Prelude
import Util

%default total
%language ElabReflection

-- `JJ` is the new interpretation of `J` in part 2
data Card = JJ | C2 | C3 | C4 | C5 | C6 | C7 | C8 | C9 | T | J | Q | K | A

%runElab derive "Card" [Show,Eq,Ord]

data Combo = High | Pair | TwoPairs | Triple | FullHouse | Four | Five

%runElab derive "Combo" [Show,Eq,Ord]

combo : (a,b,c,d,e : Card) -> Combo
combo a b c d e =
  case sort . values . fromListWith (+) $ map (,1) [a,b,c,d,e] of
    [5]       => Five
    [1,4]     => Four
    [2,3]     => FullHouse
    [1,1,3]   => Triple
    [1,2,2]   => TwoPairs
    [1,1,1,2] => Pair
    _         => High

joke : Card -> List Card -> List Card
joke JJ cs = cs
joke c _   = [c]

bestCombo : Vect 5 Card -> Combo
bestCombo [a,b,c,d,e] =
  let x  := nub [a,b,c,d,e]
      cs := [|combo (joke a x) (joke b x) (joke c x) (joke d x) (joke e x)|]
   in foldl max High cs

record Hand where
  constructor H
  combo : Combo
  cards : Vect 5 Card
  value : Nat

%runElab derive "Hand" [Show,Eq,Ord]

bestHand : Hand -> Hand
bestHand (H _ cs v) =
  let cs2 := map (\case J => JJ; c => c) cs
   in H (bestCombo cs2) cs2 v

solve : List Hand -> Nat
solve = sum . map (\(i,h) => S i * h.value) . zipWithIndex . sort

read : Char -> Card
read '2' = C2
read '3' = C3
read '4' = C4
read '5' = C5
read '6' = C6
read '7' = C7
read '8' = C8
read '9' = C9
read 'T' = T
read 'J' = J
read 'Q' = Q
read 'K' = K
read _   = A

readHand : String -> Either String Hand
readHand s =
  let [cs,v]      := words s            | _ => Left s
      [a,b,c,d,e] := read <$> unpack cs | _ => Left s
      cards       := [a,b,c,d,e]
   in Right $ H (combo  a b c d e) cards (cast v)

export
main : IO ()
main = do
  ls       <- Util.lines "day7"
  Right hs <- pure (traverse readHand ls)  | Left s => putStrLn "Invalid: \{s}"
  putStrLn "day  7 part 1: \{show $ solve hs}"
  putStrLn "day  7 part 2: \{show $ solve $ map bestHand hs}"
