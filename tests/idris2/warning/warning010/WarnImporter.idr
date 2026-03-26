module WarnImporter

import WarnCrossModule

-- Calling oldHelper should fire the warning from WarnCrossModule.
export
answer : String
answer = oldHelper "hello"
