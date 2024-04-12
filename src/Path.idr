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

