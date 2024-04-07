import Data.SnocList.Quantifiers
import Tensor
import Data.SnocList 

(*) : (Type, Type) -> (Type, Type) -> (Type, Type)
(x, dx) * (y, dy) = ((x, y), (dx, dy))

public export
ParGraph : Type -> Type -> Type
ParGraph par obj = par -> obj -> obj -> Type 

Set : Type -> Type -> Type 
Set x y = x -> y 

LensC : (c : obj -> obj -> Type) -> (act: obj -> obj -> obj) -> (obj, obj) -> (obj, obj) -> Type 
LensC c act (x, dx) (y, dy) = ((x `c` y), ((act x dy) `c` dx))

LensCSet : (Type, Type) -> (Type, Type) -> Type 
LensCSet (x, dx) (y, dy) = ((x -> y), ((x, dy) -> dx))

ParaC : (c : (obj, obj) -> (obj, obj) -> Type) -> (act : (par, par) -> (obj, obj) -> (obj, obj)) 
  -> (par, par) -> (obj, obj) -> (obj, obj) -> Type 
ParaC c act (p, px) (x, dx) (y, dy) = (act (p, px) (x, dx)) `c` (y, dy) 

-- ParaCLensSet : (Type, Type) -> (Type, Type) -> (Type, Type) -> Type 
-- ParaCLensSet (p, px) (x, dx) (y, dy) = (p, px) * (x, dx) 
-- Original

ParaBiLensSet : (Type, Type) -> (Type, Type) -> (Type, Type) -> Type 
ParaBiLensSet (p, px) (m, mx) (l, lx) = ParaC (LensC Set Pair) (*) (p, px) (m, mx) (l, lx) 

ParaBiLensF : (par : (p -> Type)) -> (f : o -> Type) -> (p, p) -> (o, o) -> (o, o) -> Type
ParaBiLensF par f (p, px) (m, mx) (l, lx) = ParaBiLensSet (par p, par px) (f m, f mx) (f l, f lx)  


ParaBiLensSet' : (Type, Type) -> (Type, Type) -> (Type, Type) -> Type 
ParaBiLensSet' (p, px) (x, dx) (y, dy) = ((p, x) -> y, ((p, x), dy) -> (px, dx)) 

-- ParaBiLensF : (par : (p -> Type)) -> (f : o -> Type) -> (p, p) -> (o, o) -> (o, o) -> Type
-- ParaBiLensF par f (p, px) (x, dx) (y, dy) = ((par p, f x) -> f y, ((par p, f x), f dy) -> (par px, f dx)) 

--ParaBiLensSet (par p, par px) (f m, f mx) (f l, f lx)  


ex : ParaBiLensSet (p, px) (x, dx) (y, dy)
ex = ?ex_rhs


unzip : SnocList (List Nat, List Nat) -> (SnocList (List Nat), SnocList (List Nat))
unzip [<] = ([<], [<])
unzip (sx :< (x, y)) = let (x', y') = unzip sx in (x' :< x, y' :< y) 

namespace Mono 
  public export
  data GPath : ParGraph (par, par) (obj, obj) -> ParGraph (SnocList (par, par)) (obj, obj) where 
    Lin : GPath g [<] (a', ax) (a', ax) 
    (:<) : {g : (par, par) -> (obj, obj) -> (obj, obj) -> Type} -> 
      GPath g ps (a', ax) (b, bx) -> g p (b, bx) (c, cx) -> GPath g (ps :< p) (a', ax) (c, cx) 
-- Unzip version
  eval : GPath (ParaBiLensF Tensor Tensor) ps (s, sx) (t, tx) -> 
               (ParaBiLensF (All Tensor) Tensor) (unzip ps) (s, sx) (t, tx)
  eval [<] = (\(_, s) => s, \((l, s'), s) => ([<], s))
  eval (es :< g) =  (?no, ?wyh)
  
BiTens : (List Nat, List Nat) -> (Type, Type)
BiTens (ls, ns) = (Tensor ls, Tensor ns) 

BiEnv : (SnocList (List Nat), SnocList (List Nat)) -> (Type, Type)
BiEnv (ls, ns) = (All Tensor ls, All Tensor ns) 

ParaBiLensF' : (par : (p, p) -> (Type, Type)) -> (f : (o, o) -> (Type, Type)) -> (p, p) -> (o, o) -> (o, o) -> Type
ParaBiLensF' par f (p, px) (m, mx) (l, lx) = ParaBiLensSet (par (p, px)) (f (m, mx)) (f (l, lx))  

namespace Poly 
  data GPath : ParGraph (par, par) (obj, obj) -> ParGraph (SnocList par, SnocList par) (obj, obj) where 
    Lin : GPath g ([<], [<]) a a 
    (:<) :  GPath g (ps, ps') a b -> g (p, p') b c -> GPath g (ps :< p, ps' :< p') a c 


  eval : GPath (ParaBiLensF' BiTens BiTens) (p, px) (s, sx) (t, tx) -> (ParaBiLensF' BiEnv BiTens) (p, px) (s, sx) (t, tx)
  eval [<] = (\(_, s) => s, \((l, s'), s) => ([<], s))
  eval (x :< (fw, bw)) = ?eval_rhs_1

--  data GPath : ParGraph (par, par) (obj, obj) -> ParGraph (SnocList (par, par)) (obj, obj) where 
--    Lin : GPath g [<] a a 
--    (:<) :  GPath g ps a b -> g p b c -> GPath g (ps :< p) a c 
--
