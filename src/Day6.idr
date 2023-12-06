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

closed : Nat
closed =
  let rec := the Double $ cast d
      tot := the Double $ cast t
      di  := sqrt (tot * tot - 4 * rec)
      x1  := (tot - di) / 2
      x2  := (tot + di) / 2
   in S (cast $ floor x2 - ceiling x1)

time :
     (res        : Nat)
  -> (0 tot      : Nat)
  -> (press, rec : Nat)
  -> {auto race  : Ix press tot}
  -> Nat
time res tot 0     rec = res
time res tot (S k) rec =
  let res' := if (S k * ixToNat race > rec) then S res else res
   in time res' tot k rec

main : IO ()
main = do
  printLn . product $ zipWith (\t,d => time 0 t t d) times distances
  printLn (time 0 t t d @{IZ})
  printLn closed

