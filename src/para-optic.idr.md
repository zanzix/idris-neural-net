---
title: "Building a Neural Network from First Principles using Free Categories and Para(Optic)"
author: Zanzi
date: Mar 13, 2023
tags: []
description: Building a Neural Network from First Principles using Free Categories and Para(Optic)
image: code.jpg
---

## Introduction
Category theory for machine learning has been a big topic recently, both with [Bruno's thesis](https://arxiv.org/abs/2403.13001) dropping, and the [DeepMind paper on using the Para construction for Deep Learning](https://arxiv.org/abs/2402.15332). 

In this blog post we will look at how dependent types can allow us to almost effortlessly implement the category theory directly, opening up a path to new generalisations. 

I will be making heavy use of Tatsuya Hirose's [code that implements the Para(Optic) construction in Haskell](https://zenn.dev/lotz/articles/14458f024674e14f4134). Our goal here is to show that when we make the category theory in the code explicit, it becomes a powerful scaffolding that lets us structure out program.  

All in all, our goal is to formulate this: A simple neural network with static types enforicng the parameters and input and output dimension. 

```idris
import Data.Fin 
import Data.Vect 

-- model : GPath ParaLensTensor [< [4, 2], [4], [0], [2, 4], [2], [0]] [2] [2]
-- model = [< linear, bias, relu, linear, bias, relu] 
```

The cruicial part is the Para construction, which lets us accumulate parameters along the composition of edges. This let's us state the parameters of each edge separately, and then compose them into a larger whole as we go along. 

## Graded Monoids 
Para forms a graded category, and in order to understand what this is we will start with a graded monoid first. 

```idris
namespace Monoid
  data Env : (par -> Type) -> List par -> Type where 
    -- Empty list
    Nil : Env f []
    -- Add an element to the list, and accumulate its parameter
    (::) : {f : par -> Type} -> f n -> Env f ns -> Env f (n::ns)

-- Compare this to the standard free monoid 
-- data List : Type -> Type where 
--   Nil : List a 
--   (::) : a -> List a -> List a 
```
We've seen this data-type in a [previous blog post](https://zanzix.github.io/posts/stlc-idris.html) where we used it to represent variable environments. 

We can use it for much more, though. For instance, let's say that we want to aggregate a series of vectors, and later perform some computation on them. 

Our free graded monoid lets us accumulate a list of vectors, while keeping their sizes in a type-level list. 

```idris 
  Vec : Nat -> Type 
  Vec n = Fin n -> Double

  f1 : Vec 1 
  f2 : Vec 2
  f3 : Vec 3

  fins : Env Vec [1, 2, 3]
  fins = [f1, f2, f3] 
```
As we will soon see, Para works the same way, but instead of forming a graded monoid, it forms a graded category. 

## Free Categories 
Before we look at free graded categories, let's first look at how to work with a plain free category. We've seen them in another [previous blog post](https://zanzix.github.io/posts/bcc.html). 
A nice trick that I've learned from Andre Videla is that we can use Idris notation for lists with free categories too, we just need to name the constructors appropriately. 

```idris
Graph : Type -> Type 
Graph obj = obj -> obj -> Type 

-- The category of Types and Functions
Set : Graph Type
Set a b = a -> b

namespace Cat
  data Path : Graph obj -> Graph obj where 
    -- Empty Path
    Nil : Path g a a
    -- Add an edge to the path 
    (::) : g a b -> Path g b c -> Path g a c

```
While Vectors form graded monoids, matrices form categories.

```idris
  Matrix : Graph Nat 
  Matrix n m = Fin n -> Fin m -> Double 
  
  mat1 : Matrix 2 3 
  mat2 : Matrix 3 1 

  matrixPath : Path Matrix 2 1
  matrixPath = [mat1, mat2]
  -- matrixPath = (mat1 :: mat2 :: Nil)
```
Just as we did at the start of the blog post, we are using the inbuilt syntactic sugar to represent a list of edges. We will now generalise from free paths to their parameterised variant!

## Free Graded Categories  
A free graded category looks not unlike a free category, except now we are accumulating an additional parameter, just as we did with graded monoids: 

```idris
ParGraph : Type -> Type -> Type 
ParGraph par obj = par -> obj -> obj -> Type 

-- A free graded path over a parameterised graph
data GPath : ParGraph par obj -> ParGraph (List par) obj where 
  -- Empty path, with an empty list of grades
  Nil : GPath g [] a a 
  -- Add an edge to the path, and accumulate its parameter
  (::) : {g : par -> obj -> obj -> Type} -> {a, b, c : obj} 
    -> g p a b -> GPath g ps b c -> GPath g (p :: ps) a c 
```
So a free graded path will take in a parameterised graph, and give back a path of edges with an accumulated parameter. 
Where could we find such parameterised graphs? This is where the Para construction comes in. 
Para takes a category C, an action of a monoidal category (A x C -> C), and gives us a parameterised category over C. 

```idris
-- Para over a monoidal category C 
Para : (c : Graph obj) -> (act : par -> obj -> obj) -> ParGraph par obj 
Para c act p x y = (act p x) `c` y 
```

In other words, we have morphisms and an accumulating parameter. 
A simple example is the graded co-reader comonad, also known as the pair comonad.

```idris 
ParaSet : ParGraph Type Type 
ParaSet a p b = Para Set Pair a p b
-- A function Nat -> Double, parameterised by Nat
pair1 : ParaSet Nat Nat Double 
  
-- A function Double -> Int, parameterised by String
pair2 : ParaSet String Double Int 

-- A function Nat -> Int, parameterised by [Nat, String]
ex : GPath ParaSet [Nat, String] Nat Int 
ex = [pair1, pair2]
```
It works a lot like the standard pair comonad, but it now accumulates parameters as we compose functions. 

## The category of Lenses 
Functional programers tend to be familiar with lenses. They are often presented as coalgebras of the costate comonad, and their links to automatic differentiation [are starting to become well known](https://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/). 

Monomorphic lenses corresponds to the plain costate comonad, and polymorphic lenses correspond to the indexed version. 

```idris
-- Monomorphic Lens
MLens : Type -> Type -> Type 
MLens s a = (s -> a, (s, a) -> s)

-- Polymorphic Lens, Haskell-style
Lens : Type -> Type -> Type -> Type -> Type
Lens s t a b = s -> ((a, b) -> t)
```
Idris allows us to bundle up the arguments for a polymorphic lens into a pair, conventionally called a boundary. This will help us form the category of parametric lenses more cleanly, as well as cut down on the number of types that we need to wrangle.  
```
Boundary : Type 
Boundary = (Type, Type) 

-- Polymorphic Lenses are morphisms of boundaries
Lens : Boundary -> Boundary -> Type 
Lens (s, t) (a, b) = ((s -> a), (s -> b -> t))
```
Both lenses and polymorphic lenses form categories. But before we look at them, let's generalise our notion of lens away from Set and towards arbitrary (cartesian) monoidal categories. 

In other words, given a monoidal category C, we want to form the category Lens(C) of Lenses over C. 

```idris
-- take a category C, and a monoidal product Ten, to give back the category LensC 
LensC : (c : Graph obj) -> (ten: obj -> obj -> obj) -> Graph obj 
LensC c ten s a = ((s `c` a), ((ten s a) `c` s))
```

We then take Para of this construction, giving us the category Para(Lens(C)).
```idris 
ParaLensSet : ParGraph Type Type 
ParaLensSet p s t = Para (LensC Set Pair) Pair p s t 
```

We now have all the theoretical pieces together. At this point, we could simply implement Para(Optic(Set)), which would give us the morphisms of our neural network. However, there is one more trick up our sleeve - rather than working in the category of sets, we would like to work in the category of vector spaces.

This means that we will parameterise the above construction to work over some monoidal functor k->Set.

```idris
ParaLensF : (f : k -> Type) -> ParGraph k k
ParaLensF f p m l = ParaLensSet (f p) (f m) (f l)  
```

And now, let us proceed to do machine learning. 

## Tensor Algebra from First Principles

First we will introduce the type of tensors of arbitrary rank. Our first instinct would be to do this with a function 
```idris 
Tensor' : List Nat -> Type 
Tensor' [] = Double 
Tensor' (n::ns) = Fin n -> Tensor' ns
```
But unfortunately this will mess up with type inference down the line. Dependent types tend to struggle when it comes to inferring types whose codomain contains arbitrary computation. This is what Conor McBride calls "green slime", and is one of the major pitfalls that functional programmers encounter when they try to make the jump to dependent types. 

For this reason, we will represent our rank-n tensors using a data-type, which will allow Idris to infer the types much easier down the line. Luckily, tensors are easily represented using an alternative data-type that's popular in Haskell.  

```idris
data Tensor : List Nat -> Type where 
  Scalar : Double -> Tensor Nil 
  Dimension : Vect n (Tensor ns) -> Tensor (n :: ns) 
```
This is essentially a nesting of vectors, which accumulates their sizes. 

All together, our data-type of parameterised lenses over tensors becomes 
```idris
ParaLensTensor : ParGraph (List Nat) (List Nat) 
ParaLensTensor ns ms ls = ParaLensF Tensor ns ms ls
```
We can now start writing neural networks. I'll be mostly adapting [Tatsuya's code](https://zenn.dev/lotz/articles/14458f024674e14f4134) in the following section. The full code for our project can be found [here](https://github.com/zanzix/idris-neural-net), and I'll only include the most interesting bits. 

Unlike the original code, we will be using a heterogeneous list - rather than nested tuples - to keep track of all of our parameters, which is why the resulting dimensions will be much easier to track. 

```idris 
linear : {n, m : Nat} -> ParaLensTensor [m, n] [n] [m] 
linear = (getter, setter) where
   getter : (Tensor [m, n], Tensor [n]) -> Tensor [m]
   getter (w, x) = (joinM w x)
   setter : ((Tensor [m, n], Tensor [n]), Tensor [m]) -> (Tensor [m, n], Tensor [n])
   setter ((w, x), y) = (outer y x, joinM (dist w) y)

bias : {n : Nat} -> ParaLensTensor [n] [n] [n] 
bias = (getter, setter) where 
  getter : (Tensor [n], Tensor [n]) -> Tensor [n]
  getter (b, x) = pointwise (+) x b
  setter : ((Tensor [n], Tensor [n]), Tensor [n]) -> (Tensor [n], Tensor [n])
  setter ((b, x), y) = (y, y)

relu : ParaLensTensor [0] [n] [n] 
relu = (getter, setter) where 
  getter : (Tensor [0], Tensor [n]) -> Tensor [n] 
  getter (_, x) = dvmap (max 0.0) x
  setter : ((Tensor [0], Tensor [n]), Tensor [n]) -> (Tensor [0], Tensor [n])
  setter ((Dim [], x), y) = (Dim [], pointwise (*) y (dvmap step x)) where
    step : Double -> Double 
    step x = if x > 0 then 1 else 0

learningRate : ParaLensTensor [0] [] [0]
learningRate = (const (Dim []), setter) where
  setter : ((Tensor [0], Tensor []), Tensor [0]) -> (Tensor [0], Tensor [])
  setter ((_, (Scalar loss)), _) = (Dim [], Scalar (-0.2 * loss))

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

-- Our final model:             parameters                          source target
model : GPath ParaLensTensor [< [4, 2], [4], [0], [2, 4], [2], [0]] [2]    [2]
model = [< linear, bias, relu, linear, bias, relu] 

```
All that remains is to implement an algebra for this structure. Normally we would use the generic recursion-schemes machinery to do this, but for now we will implement a one-off fold specialized to graded paths. 

```idris 
-- Evaluate the free graded category over ParaLensTensor
eval : GPath ParaLensTensor ps s t -> ParaLensTensorEnvS ps s t
eval [<] = (\(_, s) => s, \((l, s'), s) => ([<], s))
eval (es :< (fw, bw)) = let (fw', bw') = eval es in 
  (\((ps :< p), s) => let b = fw' (ps, s) in fw (p, b), 
  (\(((ps :< p), s), dt) => let 
    b = fw' (ps, s)
    (p', b') = bw ((p, b), dt)
    (ps', s') = bw' ((ps, s), b') 
    in (ps' :< p', s')))
```
It would actually be possible to write an individual algebra for Lens(C) and Para(C) and then compose them into an algebra Para(Lens(C)), but we can leave that for a future blog post. 

## Defunctionalizing and Working with the FFI
Running a neural network in Idris compared to NumPy is going to be obviously slow. However, since we're working entirely with free categories, it means that we don't have to actually evaluate our functions in Idris!  

What we can do is organise all of our functions into a signature, where each constructor corresponds to a primitive function in the target language. We could then use the FFI to interpret them, allowing us to get both the static guarantees of Idris and the performance of NumPy. 

```idris
data TensorSig : ParGraph (List Nat) (List Nat) where 
  Linear : TensorSig [m, n] [n] [m]
  Bias : TensorSig [n] [n] [n]
  Relu : TensorSig [0] [m] [n]
  LearningRate : TensorSig [0] [1] [0]
  CrossEntropyLoss : TensorSig [n] [n] []
  SoftMax : TensorSig [0] [n] [n]

model' : GPath PTensorSig [< [4, 2], [4], [0], [2, 4], [2], [0]] [2]    [2]
model' = [< Linear, Bias, Relu, Linear, Bias, Relu] 
```
We've also only sketched out the tensor operations, but we could take this a step forward and develop a proper tensor library in Idris. 

In a future post, we will see how to enhance the above with auto-diff: meaning that the user needs to only supply the getter, and the setter will be derived automatically. 