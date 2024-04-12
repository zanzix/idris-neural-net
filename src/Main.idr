module Main 

import System.Random
import Data.Colist as Co 
import Data.SnocList.Quantifiers
import Data.Vect 

import Graphs 
import Tensor 
import Path 
import Morphisms 
import Train 

model : GPath ParaLensTensor [< [4, 2], [4], [0], [2, 4], [2], [0]] [2] [2]
model = [< linear, bias, relu, linear, bias, relu] 

layer : GPath ParaLensTensor [< [3, 3], [3], [0]] [3] [3]
layer  = [< linear, bias, relu]

dataset : Nat -> List (All Tensor [< [2], [2]])
dataset n = take n $ cycle
  [ [< vec2 0 0, vec2 1 0]
  , [< vec2 0 1, vec2 0 1]
  , [< vec2 1 0, vec2 0 1]
  , [< vec2 1 1, vec2 1 0]
  ]

vec2IO : IO $ Tensor [2]
vec2IO = do 
  s1 <- randomRIO (-1.0, 1.0)
  s2 <- randomRIO (-1.0, 1.0)
  pure $ vec2 s1 s2

vec4IO : IO $ Tensor [4]
vec4IO = do
  s1 <- randomRIO (-1.0, 1.0)
  s2 <- randomRIO (-1.0, 1.0)
  s3 <- randomRIO (-1.0, 1.0)
  s4 <- randomRIO (-1.0, 1.0)
  pure $ vec4 s1 s2 s3 s4

mat24IO : IO $ Tensor [4, 2]
mat24IO = do 
  v1 <- vec2IO
  v2 <- vec2IO
  v3 <- vec2IO
  v4 <- vec2IO
  pure $ Dim [v1, v2, v3, v4]

mat42IO : IO $ Tensor [2, 4]
mat42IO = do 
  v1 <- vec4IO
  v2 <- vec4IO
  pure $ Dim [v1, v2]

public export
finally : Nat -> IO () 
finally n = let 
  ev = (eval (model :< softmax )) 
  in do
    b1 <- vec4IO
    w1 <- mat24IO
    b2 <- vec2IO
    w2 <- mat42IO
    trained <- pure $ train model (dataset n) [< w1, b1, Dim [], w2, b2, Dim []]
    putStr "\n(0, 0): "
    print  . getOneProb $ runGet ev (trained :< Dim []) (vec2 0 0)
    putStr "\n(0, 1): "
    print . getOneProb $ runGet ev (trained :< Dim []) (vec2 0 1)
    putStr "\n(1, 0): "
    print . getOneProb $ runGet ev (trained :< Dim []) (vec2 1 0)
    putStr "\n(1, 1): "
    print . getOneProb $ runGet ev (trained :< Dim []) (vec2 1 1)
    putStr "\n"
  where 
    getOneProb : Tensor [2] -> Double
    getOneProb t = let Scalar d = dot (vec2 0 1) t in d

