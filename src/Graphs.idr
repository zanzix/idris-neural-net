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

LensC' : (c : obj -> obj -> Type) -> (act: obj -> obj -> obj) -> (obj, obj) -> (obj, obj) -> Type 
LensC' c act (x, dx) (y, dy) = ((x `c` y), ((act x dy) `c` dx))

public export
LensSet : Type -> Type -> Type 
LensSet a b = LensC Set Pair a b 

-- Generic Para
public export
ParaC : (c : obj -> obj -> Type) -> (act : par -> obj -> obj) -> par -> obj -> obj -> Type 
ParaC c act p x y = (act p x) `c` y 

public export
ParaC' : (c : (obj, obj) -> (obj, obj) -> Type) -> (act : (par, par) -> (obj, obj) -> (obj, obj)) 
  -> (par, par) -> (obj, obj) -> (obj, obj) -> Type 
ParaC' c act (p, px) (x, dx) (y, dy) = (act (p, px) (x, dx)) `c` (y, dy) 

public export
(*) : (Type, Type) -> (Type, Type) -> (Type, Type)
(x, dx) * (y, dy) = ((x, y), (dx, dy))


public export
ParaBiLensSet : (Type, Type) -> (Type, Type) -> (Type, Type) -> Type 
ParaBiLensSet (p, px) (m, mx) (l, lx) = ParaC' (LensC' Set Pair) (*) (p, px) (m, mx) (l, lx) 

x : ParaBiLensSet (Nat, Int) (Nat, Int) (Nat, Int) 
x = (?x_rhs, ?l)

public export
ParaLensSet : Type -> Type -> Type -> Type 
ParaLensSet p s t = ParaC (LensC Set Pair) Pair p s t 


-- public export
-- runPara : ParaLensSet p a b -> p -> a -> b
-- runPara (get, _) params input = get (params, input)

public export
ParaLensF : (par : p -> Type) -> (f : o -> Type) -> p -> o -> o -> Type
ParaLensF par f p m l = ParaLensSet (par p) (f m) (f l)  

public export
ParaLensF2 : (p1 -> Type, p2 -> Type) -> (f : o -> Type) -> (p1, p2) -> o -> o -> Type
ParaLensF2 (par1, par2) f (p1, p2) m l = ParaLensSet (par1 p1, par2 p2) (f m) (f l)  

public export
ParaLensTensor : ParGraph (List Nat) (List Nat) 
ParaLensTensor ps ms ls = ParaLensF Tensor Tensor ps ms ls

public export
ParaLensTensorEnv : ParGraph (List (List Nat)) (List Nat) 
ParaLensTensorEnv ps ms ls = ParaLensF (All Tensor) Tensor ps ms ls


public export
ParaBiLensF : (par : (p -> Type)) -> (f : o -> Type) -> (p, p) -> (o, o) -> (o, o) -> Type
ParaBiLensF par f (p, px) (m, mx) (l, lx) = ParaBiLensSet (par p, par px) (f m, f mx) (f l, f lx)  

public export
ParaBiLensTensor : ParGraph (List Nat, List Nat) (List Nat, List Nat) 
ParaBiLensTensor (p, px) (m, mx) (l, lx) = ParaBiLensF Tensor Tensor (p, px) (m, mx) (l, lx)

public export
ParaBiLensF' : (par : (p, p) -> (Type, Type)) -> (f : (o, o) -> (Type, Type)) -> (p, p) -> (o, o) -> (o, o) -> Type
ParaBiLensF' par f (p, px) (m, mx) (l, lx) = ParaBiLensSet (par (p, px)) (f (m, mx)) (f (l, lx))  

-- ParaBiLensF'' : (par : (p, p) -> Type) -> (f : (o, o) -> Type) -> (p, p) -> (o, o) -> (o, o) -> Type
-- ParaBiLensF'' par f (p, px) (m, mx) (l, lx) = ParaBiLensSet (par (p, px)) (f (m, mx)) (f (l, lx))  

public export
BiTens : (List Nat, List Nat) -> (Type, Type)
BiTens (ls, ns) = (Tensor ls, Tensor ns) 

public export
ParaBiLensTensor' : ParGraph (List Nat, List Nat) (List Nat, List Nat)
ParaBiLensTensor' (p, px) (m, mx) (l, lx) = ParaBiLensF' BiTens BiTens (p, px) (m, mx) (l, lx)  


bitest1 : ParaBiLensTensor ([n], [n]) ([n], [n]) ([n], [n]) 
bitest1 = (?x_rhs', ?l')

bitest2 : ParaBiLensTensor' ([n], [n]) ([n], [n]) ([n], [n]) 
bitest2 = (?x_rhs'', ?l'')

-- public export
-- ParaBiLensTensorEnv : ParGraph (List (List Nat)) (List Nat) 
-- ParaBiLensTensorEnv ps ms ls = ParaBiLensF (All Tensor) Tensor ps ms ls

public export
ParaLensTensorEnvS : ParGraph (SnocList (List Nat)) (List Nat) 
ParaLensTensorEnvS ps ms ls = ParaLensF (All Tensor) Tensor ps ms ls

public export
BiEnv : (SnocList (List Nat), SnocList (List Nat)) -> (Type, Type)
BiEnv (ls, ns) = (Data.SnocList.Quantifiers.All.All Tensor ls, Data.SnocList.Quantifiers.All.All Tensor ns) 

public export
unzip : SnocList (List Nat, List Nat) -> (SnocList (List Nat), SnocList (List Nat))
unzip [<] = ([<], [<])
unzip (sx :< (x, y)) = let (x', y') = unzip sx in (x' :< x, y' :< y) 

public export
ParaBiLensTensorEnvS : ParGraph (SnocList (List Nat), SnocList (List Nat)) (List Nat, List Nat) 
ParaBiLensTensorEnvS ps ms ls = ParaBiLensF (Data.SnocList.Quantifiers.All.All Tensor) Tensor ps ms ls

public export
ParaBiLensTensorEnvS' : ParGraph (SnocList (List Nat), SnocList (List Nat)) (List Nat, List Nat) 
ParaBiLensTensorEnvS' ps ms ls = ParaBiLensF' BiEnv BiTens ps ms ls

public export
ParaBiLensTensorEnvS'' : ParGraph (SnocList (List Nat, List Nat)) (List Nat, List Nat) 
ParaBiLensTensorEnvS'' ps ms ls = ParaBiLensF' BiEnv BiTens (unzip ps) ms ls

data GPath : ParGraph (par, par) (obj, obj) -> ParGraph (SnocList (par, par)) (obj, obj) where 
  Lin : GPath g [<] a a 
  (:<) :  GPath g ps a b -> g p b c -> GPath g (ps :< p) a c 

eval : GPath ParaBiLensTensor' ps s t -> ParaBiLensTensorEnvS'' ps s t
eval [<] = ?wtf
eval (x :< y) = ?eval_rhs_1

bitest2' : ParaBiLensTensorEnvS'' [< ([n], [n])] ([n], [n]) ([n], [n]) 
bitest2' = (?x_rhs''', ?l''')

public export
ParaLensTensorEnv2 : ParGraph (List (List Nat), SnocList (List Nat)) (List Nat) 
ParaLensTensorEnv2 (psl, psr) ms ls = ParaLensF2 (All Tensor, SnocList.Quantifiers.All.All Tensor) Tensor (psl, psr) ms ls


public export
runGet : ParaLensSet p a b -> p -> a -> b
runGet (get, _) params input = get (params, input)

public export
runSet : ParaLensSet p a b -> p -> a -> b
runSet (get, set) params input = ?sets 

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

