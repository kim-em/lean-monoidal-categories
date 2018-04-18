-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category
import categories.products.switch

namespace categories.braided_monoidal_category

open categories
open categories.functor
open categories.natural_transformation
open categories.products
open categories.monoidal_category

universe variables u v

/-
-- I don't really understand why the universe annotations are needed in Braiding and in squaredBraiding.
-- My guess is that it is related to
-- https://groups.google.com/d/msg/lean-user/3qzchWkut0g/0QR6_cS8AgAJ
-/

@[reducible] definition Commutor (C : Type (u+1)) [category C] [m : monoidal_category C] := 
  (m.tensor) ⇔ ((SwitchProductCategory C C) ⋙ m.tensor)

variables {C : Type (u+1)} [category C] [monoidal_category C]

@[reducible] definition Hexagon_1 (β : Commutor C) :=
  ∀ X Y Z : C,
      ((𝟙 X) ⊗ (β.morphism.components (Y, Z)))
      ≫ (inverse_associator X Z Y)
      ≫ ((β.morphism.components (X, Z)) ⊗ (𝟙 Y)) = 
      (inverse_associator X Y Z) 
      ≫ (β.morphism.components (X ⊗ Y, Z))
      ≫ (inverse_associator Z X Y)

@[reducible] definition Hexagon_2 (β : Commutor C) :=
  ∀ X Y Z : C,
      ((𝟙 X) ⊗ (β.inverse.components (Z, Y)))
      ≫ (inverse_associator X Z Y)
      ≫ ((β.inverse.components (Z, X)) ⊗ (𝟙 Y)) = 
      (inverse_associator X Y Z) 
      ≫ (β.inverse.components (Z, X ⊗ Y))
      ≫ (inverse_associator Z X Y)

class Braiding (C : Type (u+1)) [category C] [monoidal_category C] :=
  ( braiding: Commutor C )
  ( hexagon_1 : Hexagon_1 braiding )
  ( hexagon_2 : Hexagon_2 braiding )

attribute [ematch] Braiding.hexagon_1 Braiding.hexagon_2
-- PROJECT a theorem showing the hexagons hold as natural transformations

class Symmetry (C : Type (u+1)) [category C] [monoidal_category C] extends Braiding C :=
  (symmetry: Π X Y : C, (braiding.morphism.components ⟨X, Y⟩) ≫ (braiding.morphism.components ⟨Y, X⟩) = 𝟙 (X ⊗ Y) )

attribute [simp,ematch] Symmetry.symmetry

end categories.braided_monoidal_category