module Day11

import Data.Vect
import Util

%default total

emptyIndices : Vect k (Vect m Char) -> Vect k Bool
emptyIndices = map (all ('.' ==))

emptyRowsAndCols : {m : _} -> Vect k (Vect m Char) -> (Vect k Bool, Vect m Bool)
emptyRowsAndCols xs = (emptyIndices xs, emptyIndices $ transpose xs)

parameters (factor : Nat)

  row : (r,c : Nat) -> Vect k Char -> Vect k Bool -> List (Integer, Integer)
  row r c []          []          = []
  row r c (_   :: xs) (True::bs)  = row r (c + factor) xs bs
  row r c ('#' :: xs) (False::bs) =  (cast r,cast c) :: row r (c+1) xs bs
  row r c (_   :: xs) (False::bs) = row r (c + 1) xs bs

  rows :
       (r : Nat)
     -> Vect k (Vect m Char)
     -> Vect k Bool
     -> Vect m Bool
     -> List (Integer, Integer)
  rows r []        []           zs = []
  rows r (x :: xs) (True  :: ys) zs = rows (r + factor) xs ys zs
  rows r (x :: xs) (False :: ys) zs = row r 0 x zs ++ rows (r + 1) xs ys zs

  chars : {m : _} -> Vect k (Vect m Char) -> List (Integer,Integer)
  chars css =
    let (ers, ecs) := emptyRowsAndCols css
     in rows 0 css ers ecs

dist : (Integer,Integer) -> (Integer,Integer) -> Integer
dist x y = if x < y then fst y - fst x + abs (snd y - snd x) else 0

solve : (n : Nat) -> List (List Char) -> Integer
solve n []     = (-2)
solve n (h::t) =
  let Just v  := traverse (toVect $ length h) (fromList $ h :: t) | _ => (-1)
      ps      := chars n v
   in sum [| dist ps ps |]

export
main : IO ()
main = do
  lss <- map unpack <$> lines "day11"
  putStrLn "day 11 part 1: \{show $ solve 2 lss}"
  putStrLn "day 11 part 1: \{show $ solve 1_000_000 lss}"
