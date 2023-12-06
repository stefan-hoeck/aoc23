module Day6

import Data.Array.Index
import Data.Vect

%default total

times : Vect 4 Nat
times = [62, 64, 91, 90]

distances : Vect 4 Nat
distances = [553, 1010, 1473, 1074]

t : Nat
t = 62649190

d : Nat
d = 553101014731074

-- Using a closed formula from solving the quadratic equation
closed : Nat
closed =
  let rec := the Double $ cast d
      tot := the Double $ cast t
      di  := sqrt (tot * tot - 4 * rec)
      x1  := (tot - di) / 2
      x2  := (tot + di) / 2
   in S (cast $ floor x2 - ceiling x1)

-- bruteforc using automatic counting upwards with
-- `Ix` from the array library.
brute : (tot, dist : Nat) -> Nat
brute tot dist = go 0 tot
  where
    go : Nat -> (press : Nat) -> (race : Ix press tot) => Nat
    go r 0       = r
    go r v@(S k) = go (ifThenElse (v * ixToNat race > dist) (S r) r) k

main : IO ()
main = do
  printLn . product $ zipWith brute times distances
  printLn (brute t d)
  printLn closed

