-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..monoidal_category

open categories
open categories.monoidal_category

namespace categories.internal_objects

universes u v

class SemigroupObject {C : Type u} [monoidal_category.{u v} C] (A : C) :=
  (μ : A ⊗ A ⟶ A)
  (associativity : (μ ⊗ (𝟙 A)) ≫ μ = (associator A A A) ≫ ((𝟙 A) ⊗ μ) ≫ μ)

attribute [ematch] SemigroupObject.associativity

end categories.internal_objects