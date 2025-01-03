{-
  Agda formalisation of the results
  in Martin-Löf's type theory of:
  
  i. “A Topological Counterpart of Well-founded Trees
  in Dependent Type Theory”

  ii. “A Topological Reading of Coinductive Predicates
  in Dependent Type Theory”
-}

module everything where

import Inductive.Constructors.Ind-types
import Inductive.Constructors.DW-types
import Inductive.Constructors.▹-types
import Inductive.Constructors.W-types
import Inductive.Equivalences.▹-give-W
import Inductive.Equivalences.DW-give-Ind
import Inductive.Equivalences.Ind-give-▹
import Inductive.Equivalences.W-give-DW

import Coinductive.Constructors.Coind-types
import Coinductive.Constructors.⋊-types
import Coinductive.Constructors.Endofunctors
import Coinductive.Equivalences.Coind-gives-⋊
import Coinductive.Equivalences.⋊-gives-Coind
import Coinductive.Equivalences.DM-gives-Coind