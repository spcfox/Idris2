module Main

import Language.Reflection

%language ElabReflection

-- script : Elab ()
-- script = do

readAndLog : (path : String) -> Elab (List Bits8)
readAndLog path = do
  logMsg "elab" 0 "Reading \{path}:"
  Just v <- readBinaryFile CurrentModuleDir path
    | Nothing => do logMsg "elab" 0 "Error during read"
                    pure []
  logMsg "elab" 0 $ "Successfully read " ++ show (length v) ++ " bytes"
  pure v

writeAndLog : (path : String) -> List Bits8 -> Elab ()
writeAndLog path v = do
  logMsg "elab" 0 "Writting to \{path}"
  writeBinaryFile CurrentModuleDir path v

script : Elab ()
script = readAndLog "logo.png" >>= writeAndLog "copy.png"

%runElab script
