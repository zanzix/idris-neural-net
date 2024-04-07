module Path 

import Graphs 
import Tensor 
import Data.List.Quantifiers 
import Data.SnocList.Quantifiers


public export
data GPath : ParGraph par obj -> ParGraph (SnocList par) obj where 
  Lin : GPath g [<] a a 
  (:<) : {g : par -> obj -> obj -> Type} -> {a, b, c : obj} 
    -> GPath g ps a b -> g p b c -> GPath g (ps :< p) a c 

public export
eval : GPath ParaLensTensor ps s t -> ParaLensTensorEnvS ps s t
eval [<] = (\(_, s) => s, \((l, s'), s) => ([<], s))
eval (es :< (fw, bw)) = let (fw', bw') = eval es in 
  (\((ps :< p), s) => let b = fw' (ps, s) in fw (p, b), 
  (\(((ps :< p), s), dt) => let 
    b = fw' (ps, s)
    (p', b') = bw ((p, b), dt)
    (ps', s') = bw' ((ps, s), b') 
    in (ps' :< p', s')))

{-
namespace Bi 
    eval : GPath ParaBiLensTensor' ps s t -> ParaBiLensTensorEnvS' ?ps' s t

namespace Poly 
  data GPath : ParGraph (par, par) (obj, obj) -> ParGraph (SnocList (par, par)) (obj, obj) where 
    Lin : GPath g [<] a a 
    (:<) :  Poly.GPath g ps a b -> g p b c -> GPath g (ps :< p) a c 

  eval : Poly.GPath ParaBiLensTensor ps s t -> ParaBiLensTensorEnvS'' ps s t
  eval [<] = ?eval_rhs_0
  eval (x :< y) = ?eval_rhs_1
--  eval [<] = (?eval_rhs_0, ?x000)
--  eval (x :< y) = ?eval_rhs_1

data Merge : (ps : List a) -> (pls : List a) -> (prs : SnocList a) -> Type where 
  Empty : Merge [] [] [<] 
  Left  : Merge ps pls prs -> Merge (x::ps) (x::pls) prs 
  Right : Merge ps pls prs -> Merge (y::ps) pls (prs :< y) 

merge : Merge ps pls prs -> All Tensor pls -> All Tensor prs -> All Tensor ps
merge Empty [] [<] = [] 
merge (Left x) (y :: pls) prs = (y :: merge x pls prs) 
merge (Right x) pls (prs :< z) = (z :: merge x pls prs) 

--public export
--data GPath : ParGraph par obj -> ParGraph (List par) obj where 
--  Nil : GPath g [] a a 
--  (::) : {g : par -> obj -> obj -> Type} -> {a, b, c : obj} 
--    -> g p a b -> GPath g ps b c -> GPath g (p :: ps) a c 


{--  (++) : {g : par -> obj -> obj -> Type} -> {a, b, c : obj} 
--    -> GPath g ps a b -> GPath g ps' b c -> GPath g (ps ++ ps') a c

public export
eval : GPath ParaLensTensor ps s t -> ParaLensTensorEnv ps s t
eval [] = (\(_, s) => s, \(l, s) => ([], s))
eval ((fw, bw)::es) = let (fw', bw') = eval es in 
  (\((p::ps), s) => let b = fw' (ps, s) in fw (p, b), 
  (\(((p::ps), s), t) => let 
    b = fw' (ps, s)
    t = fw (p, b) 
    (p', b') = bw ((p, b), t)
    (ps', s') = bw' ((ps, s), b') 
    in (p'::ps', s')))
--eval (e ++ es) = let (fw, bw) = eval e in ?z

namespace Two
  public export
  data GPath : ParGraph par obj -> ParGraph (List par, SnocList par) obj where 
    Nil : GPath g ([], [<]) a a 
    (::) : {g : par -> obj -> obj -> Type} -> {a, b, c : obj} 
      -> g p b c -> GPath g (pls, prs) a b -> GPath g (p :: pls, prs) a c 
    (:<) : {g : par -> obj -> obj -> Type} -> {a, b, c : obj} ->
      GPath g (pls, prs) a b -> g p b c -> GPath g (pls, prs :< p) a c 

  public export
  eval : Merge ps pls prs 
    -> GPath ParaLensTensor ps s t 
    -> ParaLensF2 (All Tensor, All Tensor) Tensor (pls, prs) s t 
  eval Empty Nil = ((\(_, s) => s), \(l, s) => (([], [<]), s))
  eval (Left z) ((fw, bw) :: es) = let (fw', bw') = eval es in 
    (\((p::pls, prs), s) => let b = fw' (merge z pls prs, s) in fw (p, b), ?y) 
  eval (Right z) ((fw, bw) :: es) = let (fw', bw') = eval es in 
    ((\((pls, prs :< p), s) => let b = fw' (merge z pls prs, s) in fw (p, b)), ?bwx) 
