module Graphs 

import Data.List.Quantifiers
import Data.SnocList.Quantifiers
import Tensor
import Data.SnocList 

public export
Graph : Type -> Type 
Graph obj = obj -> obj -> Type 

public export
Id : a -> a 
Id a = a 

public export
Set : Type -> Type -> Type 
Set a b = a -> b 

public export
Act : Type -> Type -> Type 
Act obj par = par -> obj -> obj 

-- ParGraph is flipped from normal
public export
ParGraph : Type -> Type -> Type
ParGraph par obj = par -> obj -> obj -> Type 

-- Generic Lens
public export
LensC : (c : obj -> obj -> Type) -> (act: obj -> obj -> obj) -> obj -> obj -> Type 
LensC c act s a = ((s `c` a), ((act s a) `c` s))

public export
LensSet : Type -> Type -> Type 
LensSet a b = LensC Set Pair a b 

-- Generic Para
public export
ParaC : (c : obj -> obj -> Type) -> (act : par -> obj -> obj) -> par -> obj -> obj -> Type 
ParaC c act p x y = (act p x) `c` y 

public export
(*) : (Type, Type) -> (Type, Type) -> (Type, Type)
(x, dx) * (y, dy) = ((x, y), (dx, dy))

public export
ParaLensSet : Type -> Type -> Type -> Type 
ParaLensSet p s t = ParaC (LensC Set Pair) Pair p s t 

public export
ParaLensF : (par : p -> Type) -> (f : o -> Type) -> p -> o -> o -> Type
ParaLensF par f p m l = ParaLensSet (par p) (f m) (f l)  

public export
ParaLensTensor : ParGraph (List Nat) (List Nat) 
ParaLensTensor ps ms ls = ParaLensF Tensor Tensor ps ms ls

public export
ParaLensTensorEnv : ParGraph (List (List Nat)) (List Nat) 
ParaLensTensorEnv ps ms ls = ParaLensF (All Tensor) Tensor ps ms ls

public export
ParaLensTensorEnvS : ParGraph (SnocList (List Nat)) (List Nat) 
ParaLensTensorEnvS ps ms ls = ParaLensF (All Tensor) Tensor ps ms ls

public export
runGet : ParaLensSet p a b -> p -> a -> b
runGet (get, _) params input = get (params, input)

