module Main 

import Data.Colist as Co 
import Data.List.Quantifiers
import Data.Vect 

import Graphs 
import Tensor 
import Path 
import Morphisms 
import Train 

model : GPath ParaLensTensor [[2, 2], [2], [0], [2, 2], [2], [0]] [2] [2]
model = [linear, bias, relu, linear, bias, relu] 


dataset : Nat -> List (All Tensor [[2], [2]])
dataset n = take n $ cycle
  [ [vec2 0 0, vec2 1 0]
  , [vec2 0 1, vec2 0 1]
  , [vec2 1 0, vec2 0 1]
  , [vec2 1 1, vec2 1 0]
  ]

k : Double 
k = 1.224

-- some random parameters, picked from a genuinely random list 
initParams : (All Tensor [[2, 2], [2], [0], [2, 2], [2], [0]])
initParams = [w1, b1, Dim [], w2, b2, Dim []] where 
  w1 : Tensor [2, 2]
  w1 = Dim [vec2 (-1.141 * k) (-0.181 * k), vec2 (-0.583 * k) (0.069 * k)]
  b1 : Tensor [2]
  b1 = vec2 (0.491 * k) (-0.670 * k)
  w2 : Tensor [2, 2]
  w2 = Dim [vec2 (0.313 * k) (-1.575 * k), vec2 (1.022 * k) (0.745 * k)]
  b2 : Tensor [2]
  b2 = vec2 (0.386 * k) (0.745 * k)

public export
finally : Nat -> IO () 
finally n = let 
  ev = (eval (softmax :: model)) 
  trained = train model (dataset n) initParams in do 
    putStr "\n(0, 0): "
    print  . getOneProb $ runPara ev (Dim []::trained) (vec2 0 0)
    putStr "\n(0, 1): "
    print . getOneProb $ runPara ev (Dim []::trained) (vec2 0 1)
    putStr "\n(1, 0): "
    print . getOneProb $ runPara ev (Dim []::trained) (vec2 1 0)
    putStr "\n(1, 1): "
    print . getOneProb $ runPara ev (Dim []::trained) (vec2 1 1)
    putStr "\n"
  where 
    getOneProb : Tensor [2] -> Double
    getOneProb t = let Scalar d = dot (vec2 0 1) t in d

