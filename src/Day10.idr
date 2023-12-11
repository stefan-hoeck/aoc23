module Day10

import Data.Nat
import Data.SortedMap
import Data.Vect
import Derive.Prelude
import Util

%language ElabReflection

data Dir  = N | S | E | W

%runElab derive "Dir" [Show,Eq,Ord]

data Conn = NE | NS | NW | SE | SW | EW

%runElab derive "Conn" [Show,Eq,Ord]

dirs : Conn -> Vect 2 Dir
dirs NE = [N,E]
dirs NS = [N,S]
dirs NW = [N,W]
dirs SE = [S,E]
dirs SW = [S,W]
dirs EW = [E,W]

fromDirs : Dir -> Dir -> Conn
fromDirs x y =
  case (min x y, max x y) of
    (N,E) => NE
    (N,S) => NS
    (N,W) => NW
    (S,E) => SE
    (S,W) => SW
    _     => EW

invert : Dir -> Dir
invert N = S
invert S = N
invert E = W
invert W = E

readConn : Char -> Maybe Conn
readConn 'L' = Just NE
readConn '|' = Just NS
readConn 'J' = Just NW
readConn 'F' = Just SE
readConn '7' = Just SW
readConn '-' = Just EW
readConn _   = Nothing

pretty : Conn -> Char
pretty NS = '\x2502'
pretty NE = '\x2514'
pretty NW = '\x2518'
pretty SE = '\x250C'
pretty SW = '\x2510'
pretty EW = '\x2500'

0 Pos : Type
Pos = (Nat,Nat)

0 Maze : Type
Maze = SortedMap Pos Conn

chars : List String -> List (Pos,Char)
chars ls = do
  (r,s) <- zipWithIndex ls 
  (c,x) <- zipWithIndex $ unpack s
  pure ((r,c),x)

maze : List (Pos,Char) -> Maze
maze = fromList . mapMaybe (\(p,c) => map (p,) (readConn c))

nextDir : Dir -> Conn -> Maybe Dir
nextDir d c =
  let [x,y] := dirs c
      di    := invert d
   in if di == x then Just y else if di == y then Just x else Nothing

nextPos : Pos -> Dir -> Pos
nextPos (r,c) N = (pred r, c)
nextPos (r,c) E = (r, S c)
nextPos (r,c) S = (S r, c)
nextPos (r,c) W = (r, pred c)

path : SnocList (Pos,Conn) -> Maze -> Pos -> Dir -> Maybe (List (Pos,Conn))
path sc m p dir =
  let p'     := nextPos p dir
      Just c := lookup p' m   | Nothing => Just (sc <>> [])
      Just d := nextDir dir c | Nothing => Nothing
   in path (sc :< (p',c)) m p' d

firstDirs : Maze -> Pos -> List Dir
firstDirs m p = mapMaybe try [N,S,E,W]
  where
    try : Dir -> Maybe Dir
    try d = (lookup (nextPos p d) m >>= nextDir d) $> d

row : (r : Nat) -> Maze -> Bool -> Maybe Dir -> (c : Nat) -> Nat
row r m b dir 0     = 0
row r m b dir (S k) =
  case lookup (r,k) m of
    Nothing    => (if b then 1 else 0) + row r m b dir k
    Just NS => row r m (not b) Nothing k
    Just NW => row r m b (Just N) k
    Just SW => row r m b (Just S) k
    Just NE =>
      case dir of
        Just N => row r m b Nothing k
        _      => row r m (not b) Nothing k
    Just SE =>
      case dir of
        Just S => row r m b Nothing k
        _      => row r m (not b) Nothing k
    Just EW    => row r m b dir k

solve2 : List String -> Maze -> List Nat
solve2 [] m = []
solve2 (h::t) m = map (\r => row r m False Nothing (length h)) [0.. length t]

prettyRow : Maze -> Nat -> Nat -> String
prettyRow m r c = pack $ map (\c => maybe ' ' pretty $ lookup (r,c) m) [0..c]

prettyMaze : List String -> Maze -> String
prettyMaze [] m = ""
prettyMaze (h::t) m =
  unlines $ map (\r => prettyRow m r (length h)) [0.. length t]

export
main : IO ()
main = do
  ls      <- lines "day10"
  cs      <- pure (chars ls)
  m1      <- pure (maze cs)
  Just p  <- pure (map fst $ find (('S' ==) . snd) cs) | _ => putStrLn "No start position"
  [x,y]   <- pure (firstDirs m1 p) | _ => putStrLn "Invalid directions to start"
  conn    <- pure (fromDirs x y)
  Just ps <- pure (path [<(p,conn)] m1 p x) | Nothing => putStrLn "No solution for part one"

  let m2 := fromList ps

  putStrLn $ prettyMaze ls m2
  putStrLn "day 10 part 1: \{show $ length ps}"
  putStrLn "day 10 part 2: \{show . sum $ solve2 ls m2}"
