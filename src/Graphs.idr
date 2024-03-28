module Graphs 

import Data.List.Quantifiers

import Tensor

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
ParaLensSet : Type -> Type -> Type -> Type 
ParaLensSet p s t = ParaC (LensC Set Pair) Pair p s t 

public export
runPara : ParaLensSet p a b -> p -> a -> b
runPara (get, _) params input = get (params, input)

public export
ParaLensF : (par : p -> Type) -> (f : o -> Type) -> p -> o -> o -> Type
ParaLensF par f p m l = ParaLensSet (par p) (f m) (f l)  

public export
ParaLensTensor : ParGraph (List Nat) (List Nat) 
ParaLensTensor ps ms ls = ParaLensF Tensor Tensor ps ms ls

public export
ParaLensTensorEnv : ParGraph (List (List Nat)) (List Nat) 
ParaLensTensorEnv ps ms ls = ParaLensF (All Tensor) Tensor ps ms ls


{-}

infixr 1 |> 
infixr 5 !>
infixr 1 <| 

public export 
Lens : Boundary -> Boundary -> Type 
Lens (x, dx) (y, dy) = ((x -> y), (x, dy) -> dx)

public export
LensL : BoundaryL -> BoundaryL -> Type 
LensL (xs, dxs) (ys, dys) = ((Env xs -> Env ys), (Env (xs ++ dys)) -> Env dxs)

public export 
-- | Lenses
(|>) : Lens (b, db) (c, dc) -> Lens (a, da) (b, db) -> Lens (a, da) (c, dc)
(|>) (get1, set1) (get2, set2) = (get1 . get2, \x => set2 (fst x, set1 (get2 (fst x), snd x)))

(<|) : Lens (a, da) (b, db) -> Lens (b, db) (c, dc) -> Lens (a, da) (c, dc)
(<|) (get1, set1) (get2, set2) = (get2 . get1, \x => set1 (fst x, set2 (get1 (fst x), snd x)))

--  parallel : Lens (a, da) (b, db) -> Lens (x, dx) (y, dy) -> Lens ((a, x), (da, dx)) ((b, y), (db, dy)) 
-- parallel l1 l2 = MkLens (bimap l1.get l2.get) (\x => bimap (l1.set (fst x)) (l2.set (snd x)))


--  unit : Lens ((Unit, Unit) * (Unit, Unit)) (Unit, Unit)
--  unit = (\x => (), \x => fst x)


public export 
(*) : Boundary -> Boundary -> Boundary
(x, dx) * (y, dy) = ((x, y), (dx, dy))

public export 
(++) : BoundaryL -> BoundaryL -> BoundaryL
(xs, dxs) ++ (ys, dys) = ((xs ++ ys), (dxs ++ dys))

public export 
Chart : Boundary -> Boundary -> Type 
Chart (x, dx) (y, dy) = ((x -> y), (x, dx) -> dy)

public export 
Unit : Boundary
Unit = (Unit, Unit)

public export 
Para : (c : Graph obj) -> Act obj par -> ParGraph obj par 
Para c act x p y = (act p x) `c` y 
