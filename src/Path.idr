module Path 

import Graphs 
import Tensor 
import Data.List.Quantifiers 
import Data.SnocList.Quantifiers

public export
data GPath : ParGraph par obj -> ParGraph (List par) obj where 
  Nil : GPath g [] a a 
  (::) : {g : par -> obj -> obj -> Type} -> {a, b, c : obj} 
    -> g p b c -> GPath g ps a b -> GPath g (p :: ps) a c 

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

data Merge : (ps : List a) -> (pls : List a) -> (prs : SnocList a) -> Type where 
  Empty : Merge [] [] [<] 
  Left  : Merge ps pls prs -> Merge (x::ps) (x::pls) prs 
  Right : Merge ps pls prs -> Merge (y::ps) pls (prs :< y) 

namespace Two
  public export
  data GPath : ParGraph par obj -> ParGraph (List par, SnocList par) obj where 
    Nil : GPath g ([], [<]) a a 
    (::) : {g : par -> obj -> obj -> Type} -> {a, b, c : obj} 
      -> g p b c -> GPath g (psl, psr) a b -> GPath g (p :: psl, psr) a c 
    (:<) : {g : par -> obj -> obj -> Type} -> {a, b, c : obj} ->
      GPath g (psl, psr) a b -> g p b c -> GPath g (psl, psr :< p) a c 

  public export
  eval : Merge ps psl psr 
    -> GPath ParaLensTensor ps s t 
    -> ParaLensF2 (All Tensor, SnocList.Quantifiers.All.All Tensor) Tensor (psl, psr) s t 
  eval Empty Nil = ((\(_, s) => s), \(l, s) => (([], [<]), s))
  eval (Left z) (x :: y) = ?nxope_2 
  eval (Right z) (x :: y) = ?nxope_3 