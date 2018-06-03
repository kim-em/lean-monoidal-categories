-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .semigroups

open categories
open categories.monoidal_category

namespace categories.internal_objects

universes u v

class MonoidObject {C : Type u} [𝒞 : monoidal_category.{u v} C] (A : C) extends SemigroupObject A := 
  ( ι : 𝒞.tensor_unit ⟶ A )
  ( left_identity  : (ι ⊗ (𝟙 A)) ≫ (SemigroupObject.μ A) = (left_unitor A) ≫ (𝟙 A) )
  ( right_identity : ((𝟙 A) ⊗ ι) ≫ (SemigroupObject.μ A) = (right_unitor A) ≫ (𝟙 A) )

attribute [simp,ematch] MonoidObject.left_identity
attribute [simp,ematch] MonoidObject.right_identity

end categories.internal_objects