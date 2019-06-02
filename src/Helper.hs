module Helper where

import qualified Data.Text.IO as Text
import Data.Text (Text)

readAndParse :: ([Char] -> Text) -> IO ()
readAndParse f = do
    str <- readFile "testFile"
    putStrLn (init str)
    Text.putStrLn (f (init str))
    
