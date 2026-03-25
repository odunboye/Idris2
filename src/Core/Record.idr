module Core.Record

import Core.Name
import Core.TT

%default covering

-- Extract the head name from the return type of a Pi chain.
-- Used to find the record type name from a constructor's type.
export
returnTyCon : Term vars -> Maybe Name
returnTyCon (Bind _ _ (Pi {}) sc) = returnTyCon sc
returnTyCon t = go t where
  go : Term vars -> Maybe Name
  go (App _ f _) = go f
  go (Ref _ _ n) = Just n
  go _ = Nothing

-- Build the projector namespace for a record type.
-- In Idris2, projections are declared with extendNS using the record's own name,
-- so they live in a namespace one level deeper than the record type's namespace.
-- e.g. record Pair' in module EtaRecord → projectors in EtaRecord.Pair'
export
projectorNS : Name -> Namespace
projectorNS n =
  let (outer, inner) = splitNS n
  in outer <.> mkNamespace (nameRoot inner)

-- Walk a constructor's Pi chain, yielding for each binder:
--   Nothing  = erased implicit (a type parameter)
--   Just p   = the projector name for this explicit field
export
getConProjectors : {0 vars : _} -> Namespace -> Term vars -> List (Maybe Name)
getConProjectors ns (Bind _ n (Pi _ rc info _) sc)
    = let root = nameRoot n
          proj = if isErased rc || root == "_"
                 then Nothing
                 else Just (NS ns (UN (Field root)))
      in proj :: getConProjectors ns sc
getConProjectors _ _ = []
