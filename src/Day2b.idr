module Day2b

import Data.Nat

%default total

export
Uninhabited (Prelude.LT === GT) where
  uninhabited prf impossible

export
0 CompNatEq : {x,y : Nat} -> compareNat x y === EQ -> x === y
CompNatEq {x = 0,   y = 0}   prf = Refl
CompNatEq {x = S k, y = S j} prf = cong S $ CompNatEq prf
CompNatEq {x = 0,   y = S k} prf impossible
CompNatEq {x = S k, y = 0}   prf impossible

export
0 CompNatLT : {x,y : Nat} -> compareNat x y === LT -> LT x y
CompNatLT {x = 0,   y = S k} prf = LTESucc LTEZero
CompNatLT {x = S k, y = S j} prf = LTESucc $ CompNatLT prf
CompNatLT {x = S k, y = 0}   prf impossible
CompNatLT {x = 0,   y = 0}   prf impossible

export
0 CompNatAntisym : {x,y : Nat} -> compareNat x y === LT -> compareNat y x === GT
CompNatAntisym {x = 0,   y = S k} prf = Refl
CompNatAntisym {x = S k, y = S j} prf = CompNatAntisym prf
CompNatAntisym {x = S k, y = 0}   prf impossible
CompNatAntisym {x = 0,   y = 0}   prf impossible

export
0 CompNatAntisymGT : {x,y : Nat} -> compareNat x y === GT -> compareNat y x === LT
CompNatAntisymGT {x = 0,   y = 0}   prf impossible
CompNatAntisymGT {x = 0,   y = S _} prf = sym prf
CompNatAntisymGT {x = S k, y = S j} prf = CompNatAntisymGT prf
CompNatAntisymGT {x = S k, y = 0}   prf = Refl

export
0 CompNatSucc : {x,y : Nat} -> compareNat x y === compareNat (S x) (S y)
CompNatSucc {x = 0,   y = 0}   = Refl
CompNatSucc {x = 0,   y = S k} = Refl
CompNatSucc {x = S k, y = 0}   = Refl
CompNatSucc {x = S k, y = S j} = Refl

export
0 MaxCommutative : (k,j : Nat) -> max k j === max j k
MaxCommutative k j with (compareNat k j) proof kj | (compareNat j k) proof jk
  _ | GT | LT = Refl
  _ | GT | EQ = Refl
  _ | GT | GT = absurd (sym $ trans (sym jk) (CompNatAntisymGT kj))
  _ | LT | LT = absurd (trans (sym jk) (CompNatAntisym kj))
  _ | LT | GT = Refl
  _ | LT | EQ = CompNatEq jk
  _ | EQ | LT = sym $ CompNatEq kj
  _ | EQ | EQ = CompNatEq jk
  _ | EQ | GT = Refl

export
0 MaxEQ : (x,y : Nat) -> Either (max x y === x) (max x y === y)
MaxEQ x y with (compareNat x y)
  _ | LT = Right Refl
  _ | EQ = Right Refl
  _ | GT = Left Refl

export
0 MaxLTE : (x,y : Nat) -> LTE x (max x y)
MaxLTE x y with (compareNat x y) proof lt
  _ | LT = lteSuccLeft $ CompNatLT lt
  _ | EQ = replace {p = LTE x} (CompNatEq lt) reflexive
  _ | GT = reflexive

export
0 MaxLTE' : (x,y : Nat) -> LTE y (max x y)
MaxLTE' x y = rewrite MaxCommutative x y in MaxLTE y x
