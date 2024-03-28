module Main

main : IO ()
main = putStrLn "Test successful!"

{-}
public export
testSoft : Tensor [1]
testSoft = let (g, s) = softmax in g (Dim [], Dim [Scalar 1])

public export
testSoft1 : Tensor [2]
testSoft1 = let (g, s) = softmax in g (Dim [], Dim [Scalar 1, Scalar 1])

  public export
  testSoft2 : Tensor [3]
  testSoft2 = let (g, s) = softmax in g (Dim [], Dim [Scalar 1, Scalar 1, Scalar 1])
