module Morphisms 

import Data.Vect

import Graphs 
import Tensor 
import Debug.Trace 

export
linear : {n, m : Nat} -> ParaLensTensor [m, n] [n] [m] 
linear = (getter, setter) where
   getter : (Tensor [m, n], Tensor [n]) -> Tensor [m]
   getter (w, x) = (joinM w x)
   setter : ((Tensor [m, n], Tensor [n]), Tensor [m]) -> (Tensor [m, n], Tensor [n])
   setter ((w, x), y) = (outer y x, joinM (dist w) y)


-- x : ParaBiLensSet (Nat, Int) (Nat, Int) (Nat, Int) 
-- x = (?x_rhs, ?l)
 
--bias' : {n : Nat} -> ParaBiLensTensor' ([n], [n]) ([n], [n]) ([n], [n]) 
--bias' = (?gets', ?x1) 
export 
bias : {n : Nat} -> ParaLensTensor [n] [n] [n] 
bias = (getter, setter) where 
  getter : (Tensor [n], Tensor [n]) -> Tensor [n]
  getter (b, x) = pointwise (+) x b
  setter : ((Tensor [n], Tensor [n]), Tensor [n]) -> (Tensor [n], Tensor [n])
  setter ((b, x), y) = (y, y)

export
relu : ParaLensTensor [0] [n] [n] 
relu = (getter, setter) where 
  getter : (Tensor [0], Tensor [n]) -> Tensor [n] 
  getter (_, x) = dvmap (max 0.0) x
  setter : ((Tensor [0], Tensor [n]), Tensor [n]) -> (Tensor [0], Tensor [n])
  setter ((Dim [], x), y) = (Dim [], pointwise (*) y (dvmap step x)) where
    step : Double -> Double 
    step x = if x > 0 then 1 else 0

export
learningRate : ParaLensTensor [0] [] [0]
learningRate = (const (Dim []), setter) where
  setter : ((Tensor [0], Tensor []), Tensor [0]) -> (Tensor [0], Tensor [])
  setter ((_, (Scalar loss)), _) = (Dim [], Scalar (-0.2 * loss))

export
crossEntropyLoss : ParaLensTensor [n] [n] []
crossEntropyLoss = (getter, setter) where 
  getter : (Tensor [n], Tensor [n]) -> Tensor []
  getter (y', y) = 
    let Scalar dot' = dot y' y in 
    Scalar (log (sumElem (dvmap exp y)) - dot')  

  setter : ((Tensor [n], Tensor [n]), Tensor []) -> (Tensor [n], Tensor [n])
  setter ((y', y), (Scalar z)) = let 
    expY = dvmap exp y 
    sumExpY = sumElem expY in 
      (dvmap (* (-z)) y, 
        dvmap (* z) (
          ((pointwise (-) (dvmap (/sumExpY) expY) y'))))

export
softmax : {n : Nat} -> ParaLensTensor [0] [n] [n]
softmax = (getter, setter) where
  getter : (Tensor [0], Tensor [n]) -> Tensor [n]
  getter (_, x) = let 
    xMax = foldElem max (-1.0/0.0) x
    expX = dvmap exp (pointwise (-) x (Dim (replicate n (Scalar xMax))))
    denom = sumElem expX
      in dvmap (/denom) expX

  setter : ((Tensor [0], Tensor [n]), Tensor [n]) -> (Tensor [0], Tensor [n])
  setter ((_, x), y) = let
    z = getter (Dim [], x) 
    cols = Dim (replicate n z) 
    mat = pointwise (*) cols (pointwise (-) (tabulate eye) (dist cols)) in 
    (Dim [], joinM mat y)
