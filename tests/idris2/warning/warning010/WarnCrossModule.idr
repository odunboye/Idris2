module WarnCrossModule

-- %warning on an imported name: the warning is TTC-serialised and fires
-- in the importing module too.  This file defines the warned definition.

%warning "use newHelper instead"
export
oldHelper : String -> String
oldHelper s = "old: " ++ s
