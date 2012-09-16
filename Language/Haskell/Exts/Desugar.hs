module Language.Haskell.Exts.Desugar  where

import qualified Prelude
import Control.Applicative  ((<$>),(<*>))
import Language.Haskell.Exts.Unique

class Desugar a where
  desugar :: a -> Unique a 

-- Applicative style of applying desugaring 

infixl 4 **,$$
(**) :: Desugar a => Unique (a -> b) -> a -> Unique b 
x ** y = x <*> desugar y

($$) :: Desugar a => (a -> b) -> a -> Unique b
x $$ y = x <$> desugar y
