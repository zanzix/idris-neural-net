module Train 

import Data.List.Quantifiers
import Data.Vect

import Graphs 
import Path 
import Morphisms 
import Tensor 

public export
updateParam : {a : List Nat} -> {n : Nat} -> {p : List (List Nat)} -> 
  GPath ParaLensTensor p a [n] -> All Tensor [a, [n]] -> All Tensor p -> All Tensor p
updateParam model [a, b] p = let  
  (_, bw) = eval (learningRate :: crossEntropyLoss :: model)
  ((Dim []::ns::p'), y) = bw (((Dim [] :: b :: p), a), Dim [])
    in updateEnv p p' 

public export
train : {n : Nat} -> {p : List (List Nat)} -> {a : List Nat} -> 
  GPath ParaLensTensor p a [n] -> List (All Tensor [a, [n]]) -> All Tensor p -> All Tensor p
train model dataset initParam = foldl (\p, d => updateParam model d p) initParam dataset

