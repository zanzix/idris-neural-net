module Train 

import Data.SnocList.Quantifiers
import Data.Vect

import Graphs 
import Path 
import Morphisms 
import Tensor 


public export
updateParam : {a : List Nat} -> {n : Nat} -> {p : SnocList (List Nat)} -> 
  GPath ParaLensTensor p a [n] -> All Tensor [< a, [n]] -> All Tensor p -> All Tensor p
updateParam model [< a, b] p = let  
  (_, bw) = eval (model :< crossEntropyLoss :< learningRate)
  ((p' :< ns :< Dim []), y) = bw (((p :< b :< Dim []), a), Dim [])
    in updateEnv p p' 

public export
train : {n : Nat} -> {p : SnocList (List Nat)} -> {a : List Nat} -> 
  GPath ParaLensTensor p a [n] -> List (All Tensor [< a, [n]]) -> All Tensor p -> All Tensor p
train model dataset initParam = foldl (\p, d => updateParam model d p) initParam dataset
