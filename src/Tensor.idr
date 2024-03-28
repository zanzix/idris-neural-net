module Tensor 
import Data.Vect 
import Data.List.Quantifiers
import Deriving.Show 

public export
data Tensor : List Nat -> Type where 
  Scalar : Double -> Tensor Nil 
  Dim : Vect n (Tensor ns) -> Tensor (n :: ns) 

%language ElabReflection

%hint public export
tensorShow : Show (Tensor ns)
tensorShow = %runElab derive
  
public export
pointwise : (Double -> Double -> Double) -> Tensor ns -> Tensor ns -> Tensor ns 
pointwise op (Scalar dbl) (Scalar dbl1) = Scalar (dbl `op` dbl1)
pointwise op (Dim xs) (Dim ys) = Dim $ zipWith (pointwise op) xs ys 

public export
updateEnv : All Tensor ps -> All Tensor ps -> All Tensor ps 
updateEnv [] [] = []
updateEnv (x :: z) (y :: w) = pointwise (+) x y :: updateEnv z w

public export
foldElem : (Double -> Double -> Double) -> Double -> Tensor [n] -> Double
foldElem op acc (Dim []) = acc
foldElem op acc (Dim ((Scalar dbl) :: xs)) = dbl `op` foldElem op acc (Dim xs) 

public export
sumElem : Tensor [n] -> Double 
sumElem t = foldElem (+) 0 t

public export
dot : Tensor [n] -> Tensor [n] -> Tensor []
dot (Dim []) (Dim []) = Scalar 0
dot (Dim (Scalar v::v1)) (Dim (Scalar v'::v2)) = 
  let Scalar z = dot (Dim v1) (Dim v2) in 
    Scalar $ (v * v') + z
  
public export
joinM : Tensor [m, n] -> Tensor [n] -> Tensor [m] 
joinM (Dim []) (Dim vec) = Dim []
joinM (Dim (m::mat)) vec = 
  let (Dim join) = joinM (Dim mat) vec in
  Dim ((dot m vec) :: join)

public export
dist : {n : Nat} -> Tensor [m, n] -> Tensor [n, m] 
dist (Dim  []) = Dim (replicate n (Dim []))
dist (Dim (Dim v::vs)) = let Dim vs' = dist (Dim vs) in 
  Dim (zipWith cons v vs') where 
    cons : Tensor [] -> Tensor [len] -> Tensor [S len]
    cons s (Dim v) = Dim (s :: v)

public export
scalarMult : Tensor [] -> Tensor [n] -> Tensor [n]
scalarMult (Scalar s1) (Dim []) = Dim [] 
scalarMult (Scalar s1) (Dim (Scalar s2 :: xs)) = 
  let Dim xs' = scalarMult (Scalar s1) (Dim xs) in
    Dim (Scalar (s1 * s2) :: xs')

public export
outer : Tensor [m] -> Tensor [n] -> Tensor [m, n] 
outer (Dim []) (Dim ys) = Dim []
outer (Dim (x :: xs)) ys = let Dim ys' = outer (Dim xs) ys in 
  Dim (scalarMult x ys :: ys') where 

public export
dvmap : (Double -> Double) -> Tensor [n] -> Tensor [n]
dvmap f (Dim v) = Dim (map (\(Scalar s) => Scalar (f s)) v)

public export
eye : Fin n -> Fin n -> Tensor [] 
eye v1 v2 = if v1 == v2 then Scalar 1 else Scalar 0

public export
tabulate : {n, m : Nat} -> (Fin n -> Fin m -> Tensor []) -> Tensor [n, m]
tabulate f = let 
  f' = Data.Vect.Fin.tabulate f 
  vs = map (\v => Dim $ Data.Vect.Fin.tabulate v) f' in
    Dim vs 

public export
vec2 : Double -> Double -> Tensor [2] 
vec2 d1 d2 = Dim [Scalar d1, Scalar d2]
