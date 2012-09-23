{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
module Language.Haskell.Exts.Desugar.Pattern where

import qualified Prelude
import Language.Haskell.Exts hiding (name)
import Language.Haskell.Exts.Unique
import Language.Haskell.Exts.Desugar
import Language.Haskell.Exts.Desugar.Basic ()
import Prelude (($),(++),return,length,foldr,concat)
import Control.Applicative ((<$>))

instance Desugar Pat where
  -- no desugaring 
  desugar (PVar name)            = 
    PVar $$ name
  
  -- no desugaring
  desugar (PLit literal)         = 
    PLit $$ literal
  
  -- no desugaring
  desugar (PApp qName pats)      = 
    PApp $$ qName ** pats
  
  -- no desugaring
  desugar (PAsPat name pat)      = 
    PAsPat $$ name ** pat
  
  -- no desugaring
  desugar (PNPlusK name integer) =   
    PNPlusK $$ name ** integer
  
  -- no desugaring
  desugar (PViewPat eexp pat)    = 
    PViewPat eexp $$ pat
 
  -- no desugaring
  desugar (PIrrPat pat)          = 
    PIrrPat $$ pat
  
  -- no desugaring
  desugar (PBangPat pat)         = 
    PBangPat $$ pat
    
  -- no desugaring
  desugar PWildCard              = 
    return $ PWildCard 
    
  -- no desugaring
  desugar (PRec qName patFields) = 
    PRec $$ qName ** patFields
  
  -- no desugaring
  -- should be removed from HSE
  -- and replaced with literals
  desugar (PNeg (PLit (Int x)))       = 
    desugar $ PLit (Int (-x))
  desugar (PNeg (PLit (Frac y)))      = 
    desugar $ PLit (Frac (-y))
  desugar (PNeg _other)               = 
    error $ "In Patterns, negation can only "
    ++      "be applied to numeric literals!"
   
  -- HSE
  desugar (PParen pat)                = 
    desugar $ pat
  
  -- HSE
  desugar (PInfixApp pat1 qName pat2) =
    desugar $ PApp qName [pat1,pat2]
  
  -- HSE
  desugar (PTuple [])                 = 
    desugar $ PApp (Special UnitCon) []
  desugar (PTuple [p])                = 
    desugar $ p  
  desugar (PTuple pats)               = 
    desugar $ PApp (Special $ TupleCon Boxed $ length pats) pats
  
  -- HSE
  desugar (PList [])                  = 
    desugar $ PApp (Special ListCon) []
  desugar (PList pats)                =
    desugar $ foldr (\p a -> PApp (Special Cons) [p,a]) (PList [])  pats
    
  -- not supported
  desugar (PatTypeSig   {}) = error "Not supported!"                  
  desugar (PExplTypeArg {}) = error "Not supported!"       
  desugar (PQuasiQuote  {}) = error "Not supported!"
  desugar (PRPat        {}) = error "Not supported!"                  
  desugar (PXTag        {}) = error "Not supported!" 
  desugar (PXETag       {}) = error "Not supported!" 
  desugar (PXPcdata     {}) = error "Not supported!"               
  desugar (PXPatTag     {}) = error "Not supported!"                  
  desugar (PXRPats      {}) = error "Not supported!" 
  
instance Desugar PatField where
  desugar (PFieldPat qName p) = 
    PFieldPat $$ qName ** p
  desugar (PFieldPun n)       =  
    desugar $ PFieldPat (UnQual n) (PVar n)
  desugar PFieldWildcard      =  
    error "PFieldWildcard is not supported!"

-- variables / name bound in a pattern
patVar :: Pat -> [Name]      
patVar (PVar name)  = [name]  
patVar (PLit _) = []                   
patVar (PatTypeSig _ pat _) = patVar pat  
patVar (PApp _ pats) = concat (patVar <$> pats)
patVar (PAsPat name pat) = name : (patVar pat)  
patVar (PParen pat) = patVar pat  
patVar (PIrrPat pat) = patVar pat 
patVar (PBangPat pat) = patVar pat 
patVar (PNeg _) = [] 
patVar (PInfixApp pat1 _ pat2) = (patVar pat1) ++ (patVar pat2)
patVar (PTuple pats) =  concat $ patVar <$> pats    
patVar (PList pats) = concat $ patVar <$> pats  
patVar PWildCard  = []  
patVar (PNPlusK _ _) = []
patVar (PViewPat _ pat) = patVar pat  
patVar x = Prelude.error $ "Pattern " ++ (prettyPrint x) ++ " is not supported!"