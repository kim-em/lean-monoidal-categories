-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

open categories
open categories.functor
open categories.products
open categories.natural_transformation

namespace categories.monoidal_category

universe variables u

variables {C : Type (u+1)} [category C] [monoidal_category C]

definition tensor_on_left (Z : C) : C ↝ C :=
{ onObjects := λ X, Z ⊗ X,
  onMorphisms := λ X Y f, 1 ⊗ f }

definition tensor_on_right (Z : C) : C ↝ C :=
{ onObjects := λ X, X ⊗ Z,
  onMorphisms := λ X Y f, f ⊗ 1 }

end categories.monoidal_category