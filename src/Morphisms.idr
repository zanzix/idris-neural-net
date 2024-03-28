module Morphisms 

import Data.Vect

import Graphs 
import Tensor 

export
linear : {n, m : Nat} -> ParaLensTensor [m, n] [n] [m] 
linear = (getter, setter) where
   getter : (Tensor [m, n], Tensor [n]) -> Tensor [m]
   getter (w, x) = (joinM w x)
   setter : ((Tensor [m, n], Tensor [n]), Tensor [m]) -> (Tensor [m, n], Tensor [n])
   setter ((w, x), y) = (outer y x, joinM (dist w) y)

export
bias : {n : Nat} -> ParaLensTensor [n] [n] [n] 
bias = (getter, setter) where 
  getter : (Tensor [n], Tensor [n]) -> Tensor [n]
  getter (b, x) = pointwise (+) b x
  setter : ((Tensor [n], Tensor [n]), Tensor [n]) -> (Tensor [n], Tensor [n])
  setter ((b, x), y) = (y, y)

export
relu : ParaLensTensor [0] [n] [n] 
relu = (getter, setter) where 
  getter : (Tensor [0], Tensor [n]) -> Tensor [n] 
  getter (_, x) = dvmap (max 0.0) x
  setter : ((Tensor [0], Tensor [n]), Tensor [n]) -> (Tensor [0], Tensor [n])
  setter ((z, x), y) = (z, pointwise (*) y (dvmap step x)) where
    step : Double -> Double 
    step x = if x > 0 then 1 else 0

export
learningRate : ParaLensTensor [0] [] [0]
learningRate = (const (Dim []), setter) where
  setter : ((Tensor [0], Tensor []), Tensor [0]) -> (Tensor [0], Tensor [])
  setter ((_, (Scalar loss)), _) = (Dim [], Scalar (-0.01 * loss))

export
crossEntropyLoss : ParaLensTensor [n] [n] []
crossEntropyLoss = (getter, setter) where 
  getter : (Tensor [n], Tensor [n]) -> Tensor []
  getter (y', y) = Scalar (log (foldElem (+) 0 (dvmap exp y)) - foldElem (+) 0 (pointwise (*) y' y))  
  setter : ((Tensor [n], Tensor [n]), Tensor []) -> (Tensor [n], Tensor [n])
  setter ((y', y), (Scalar z)) = let 
    expY = dvmap exp y 
    sumExpY = foldElem (+) 0 expY in 
      (dvmap (* (-z)) y, dvmap (* z) (dvmap (/sumExpY) (pointwise (-) expY y')))
  
export
softmax : {n : Nat} -> ParaLensTensor [0] [n] [n]
softmax = (getter, setter) where
  getter : (Tensor [0], Tensor [n]) -> Tensor [n]
  getter (_, x) = let 
    xMax = foldElem max 0 x
    expX = dvmap exp (pointwise (-) x (Dim (replicate n (Scalar xMax))))
    denom = foldElem (+) 0 expX
      in dvmap (/denom) expX

  setter : ((Tensor [0], Tensor [n]), Tensor [n]) -> (Tensor [0], Tensor [n])
  setter ((_, x), y) = let
    z = getter (Dim [], x) 
    cols = Dim (replicate n z) 
    mat = update (*) cols (update (-) (tabulate eye) (dist cols)) in 
    (Dim [], joinM mat y)
