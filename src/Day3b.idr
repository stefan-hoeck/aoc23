module Day3b

import Data.Graph.Indexed
import Data.List
import Data.Vect
import Text.Bounds
import Text.Lex.Manual
import Util

%default total

data Token : Type where
  N : Nat  -> Token
  S : Char -> Token

value : Token -> Nat
value (N v) = v
value _     = 0

notDot : Token -> Bool
notDot (S '.') = False
notDot _        = True

tok : Tok True e Token
tok (x::xs) = if isDigit x then N <$> dec (x::xs) else Succ (S x) xs
tok []      = eoiAt Same

tokenize : String -> (k ** Vect k (Bounded Token))
tokenize s =
  let Right ts := singleLineDropSpaces {e = Void} tok s | _ => (0 ** [])
   in (_ ** fromList (filter (notDot . val) ts))

edges : List (Fin k, Bounded Token) -> List (Edge k ())
edges xs = do
  (x, B (N _) (BS (P ll cs) (P _ ce))) <- xs | _ => []
  (y, B (S _) (BS (P l c) _))          <- xs | _ => []
  guard (minus ll 1 <= l && plus ll 1 >= l && minus cs 1 <= c && ce >= c)
  toList (mkEdge x y ())

graph : String -> Graph () Token
graph s =
  let (k ** bs) := tokenize s
   in G _ $ mkGraph (map val bs) (edges $ zip (allFinsFast k) (toList bs))

part1 : {k : _} -> IGraph k () Token -> Fin k -> Nat
part1 g ix = if deg g ix > 0 then value (lab g ix) else 0

part2 : {k : _} -> IGraph k () Token -> Fin k -> Nat
part2 g ix =
  let A (S '*') ns := adj g ix              | _ => 0
      [N x,N y]    := map (lab g) (keys ns) | _ => 0
   in x * y

run : IO ()
run = do
  G k g <- graph <$> text "day3"
  printLn (sum $ map (part1 g) (allFinsFast k))
  printLn (sum $ map (part2 g) (allFinsFast k))
