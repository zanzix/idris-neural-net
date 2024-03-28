module Path 

import Graphs 
import Tensor 
import Data.List.Quantifiers 

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
