import Data.SnocList.Quantifiers
import Data.Vect

import Graphs 
import Path 
import Morphisms 
import Tensor 

-- Vectors 
vec111 : Tensor [3] 
vec111 = Dim [Scalar 1, Scalar (-1.0), Scalar 1]

public export
vec3 : Tensor [3] 
vec3 = Dim [Scalar 1, Scalar 2, Scalar 3]

public export
vec3' : Tensor [3] 
vec3' = Dim [Scalar 4, Scalar 5, Scalar 6]

public export
vec3a : Tensor [3] 
vec3a = Dim [Scalar 6, Scalar 6, Scalar 6]

vec3a' : Tensor [3] 
vec3a' = Dim [Scalar 9, Scalar 9, Scalar 9]

public export
vec3b : Tensor [3] 
vec3b = Dim [Scalar 7, Scalar 8, Scalar 9]

public export
vec3'' : Tensor [3] 
vec3'' = Dim [Scalar (-1), Scalar 0, Scalar 1]

public export
vec3''' : Tensor [3] 
vec3''' = Dim [Scalar 2, Scalar 3, Scalar 4]

public export
mat1 : Tensor [2, 3] 
mat1 = Dim [
  Dim [Scalar 1.0, Scalar (-2.0), Scalar (3.0)],
  Dim [Scalar (-4.0), Scalar (5.0), Scalar (-6.0)]]

matones : Tensor [2, 3] 
matones = Dim [
  Dim [Scalar 1.0, Scalar 1.0, Scalar 1.0],
  Dim [Scalar 1.0, Scalar 1.0, Scalar 1.0]]

public export
mat2 : Tensor [3, 2] 
mat2 = Dim [
   Dim [Scalar 1.0, Scalar (-2.0)],
   Dim [Scalar (-3.0), Scalar 4.0],
   Dim [Scalar 5.0, Scalar (-6.0)]]

namespace Numeric 
  public export
  outTest : Tensor [3, 3]
  outTest = outer vec3 vec3' 

linearTestFw : Tensor [3] 
linearTestFw = let fw = fst linear in fw (outTest, vec3a) 

linearTestFw1 : Tensor [2] 
linearTestFw1 = runGet linear mat1 vec111 

linearTestFw2 : Tensor [3] 
linearTestFw2 = runGet linear outTest vec111 

linearTestBw : (Tensor [2, 3], Tensor [3]) 
linearTestBw = let bw = snd linear in bw ((mat1, vec111), Dim [Scalar 1.0, Scalar (-1.0)])

public export
linset : (Tensor [3, 3], Tensor [3])
linset = let bw = snd linear in bw ((outTest, vec3a), vec3a') 

linId : GPath ParaLensTensor [< [2, 3]]  [3] [2]
linId = [< linear]
  
biasId : GPath ParaLensTensor [< [3]] [3] [3]
biasId = [< bias]
  
reluId : GPath ParaLensTensor [< [0]] [3] [3] 
reluId = [< relu]
  
layer : GPath ParaLensTensor [< [2, 3], [2], [0]]  [3] [2]
layer = [< linear, bias, relu]

testLayer1 : (All Tensor [<[2, 3]], Tensor [3])
testLayer1 = let bw = snd $ eval linId in 
  bw (([< mat1], vec111), Dim [Scalar 1.0, Scalar (-1.0)])

testLayerBw : (All Tensor [<[2, 3], [2], [0]], Tensor [3])
testLayerBw = let bw = snd $ eval layer in 
  bw (([< mat1, Dim [Scalar 1.0, Scalar (-1.0)], Dim []], vec111), Dim [Scalar 1.0, Scalar (-1.0)])

testBiasBw : (All Tensor [<[3]], Tensor [3])
testBiasBw = let bw = snd $ eval biasId in
  bw (([< vec3], vec3'), vec3b) 


-- public export
-- testLayer' : Tensor [2]
-- testLayer' = let 
--   fw = fst $ eval layer' 
--    in fw ([< mat1', vec2 1 2, Dim []], vec3')

-- public export
-- testBackLayer : (All Tensor [<[3, 3], [3], [0]], Tensor [3])
-- testBackLayer = let 
--   bw = snd $ eval layer 
--    in bw (([< outTest, vec3, Dim []], vec3'), vec3b)

-- public export
-- testBackLayer' : (All Tensor [< [2, 3], [2], [0]], Tensor [3])
-- testBackLayer' = let 
--   bw = snd $ eval layer' 
--    in bw (([< mat1', vec2 1 2, Dim []], vec3'), vec2 6 7)

--(pars, vec3 1 1 1) ^. linear
--(vector [2.0,-5.0] :: R 2)

namespace Linear 

namespace Relu 

  public export
  reluGet : Tensor [3]
  reluGet = let fw = fst relu in fw (Dim [], vec3'')


  public export
  reluSet : (Tensor [0], Tensor [3]) 
  reluSet = let bw = snd relu in bw ((Dim [], vec3''), vec3''') 

public export
learTest : (Tensor [0], Tensor []) 
learTest = let bw = snd learningRate in bw ((Dim [], Scalar 1), Dim [])


namespace Bias 
  public export
  biasFw : Tensor [3]
  biasFw = let fw = fst bias in fw (vec3, vec3')

  public export
  biasbw : (Tensor [3], Tensor [3])
  biasbw = let bw = snd bias in bw ((vec3, vec3'), vec3b) 

namespace Softmax 
  public export
  dvmaptest : Tensor [3] -> Tensor [] -> Tensor [3] 
  dvmaptest y (Scalar z) = dvmap (* (-z)) y

  sndtest : Tensor [3] -> Tensor [3] -> Tensor [] -> Tensor [3]
  sndtest =  ?xs --dvmap (* z) (dvmap (/sumExpY) (pointwise (-) expY y'))


  public export
  runCrossGet : Tensor []
  runCrossGet = let fw = fst crossEntropyLoss in fw (vec3, vec3')

  public export
  runCrossSet : (Tensor [3], Tensor [3])
  runCrossSet = let bw = snd crossEntropyLoss in bw ((vec3, vec3'), Scalar 8)

public export
runSoft : (Tensor [0], Tensor [3])
runSoft = let fw = snd softmax in fw ((Dim [], vec3), vec3')

testSoft : Tensor [1]
testSoft = let (g, s) = softmax in g (Dim [], Dim [Scalar 1])

public export
testSoft1 : Tensor [2]
testSoft1 = let (g, s) = softmax in g (Dim [], Dim [Scalar 1, Scalar 1])

public export
testSoft2 : Tensor [3]
testSoft2 = let (g, s) = softmax in g (Dim [], Dim [Scalar 1.0, Scalar 2.0, Scalar 3.0])

public export
testSoft3 : Tensor [4]
testSoft3 = let (g, s) = softmax in g (Dim [], Dim [Scalar 1, Scalar 1, Scalar 1, Scalar 4])

run1 : Tensor [2] -> Tensor [2] -> Tensor [] 
run1  = runGet crossEntropyLoss 
