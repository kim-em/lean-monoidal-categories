-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

open categories
open categories.functor
open categories.products
open categories.natural_transformation

namespace categories.monoidal_category

universe variables u v

variables {C : Type u} [𝒞 : monoidal_category.{u v} C]
include 𝒞

definition tensor_on_left (Z : C) : C ↝ C :=
{ onObjects := λ X, Z ⊗ X,
  onMorphisms := λ X Y f, (𝟙 Z) ⊗ f }

definition tensor_on_right (Z : C) : C ↝ C :=
{ onObjects := λ X, X ⊗ Z,
  onMorphisms := λ X Y f, f ⊗ (𝟙 Z) }

end categories.monoidal_category