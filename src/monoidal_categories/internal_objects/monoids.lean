-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .semigroups

open categories
open categories.monoidal_category

namespace categories.internal_objects

universe u

class MonoidObject  {C : Type (u+1)} [category C] [m : monoidal_category C] (A : C) extends SemigroupObject A := 
  ( unit : m.tensor_unit ⟶ A )
  ( left_identity  : (unit ⊗ (𝟙 A)) ≫ (SemigroupObject.μ A) = (left_unitor A) ≫ (𝟙 A) )
  ( right_identity : ((𝟙 A) ⊗ unit) ≫ (SemigroupObject.μ A) = (right_unitor A) ≫ (𝟙 A) )

def ι {C : Type (u+1)} [category C] [m : monoidal_category C] (A : C) [s : MonoidObject A] : m.tensor_unit ⟶ A := s.unit

attribute [simp,ematch] MonoidObject.left_identity
attribute [simp,ematch] MonoidObject.right_identity

-- instance MonoidObject_coercion_to_SemigroupObject { C : MonoidalCategory } : has_coe (MonoidObject C) (SemigroupObject C) :=
--   { coe := MonoidObject.to_SemigroupObject }

end categories.internal_objects