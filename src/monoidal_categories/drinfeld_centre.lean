-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .braided_monoidal_category
import .tensor_with_object

open categories
open categories.functor
open categories.products
open categories.natural_transformation
open categories.monoidal_category

namespace categories.drinfeld_centre

universes u v

structure HalfBraiding (C : Type u) [monoidal_category.{u v} C] : Type (max u v) :=
    (object   : C)
    (commutor : (tensor_on_left object) ⇔ (tensor_on_right object))

variables {C : Type u} [monoidal_category.{u v} C]

structure HalfBraidingMorphism (X Y : HalfBraiding C) : Type v :=
  (morphism : X.object ⟶ Y.object)
  (witness : ∀ Z : C, (X.commutor.morphism.components Z) ≫ ((𝟙 Z) ⊗ morphism) = (morphism ⊗ (𝟙 Z)) ≫ (Y.commutor.morphism.components Z) . obviously)

make_lemma HalfBraidingMorphism.witness
attribute [simp,ematch] HalfBraidingMorphism.witness_lemma

@[applicable] lemma HalfBraidingMorphism_equal
  { X Y : HalfBraiding.{u v} C }
  { f g : HalfBraidingMorphism X Y }
  ( w : f.morphism = g.morphism ) : f = g :=
  begin
    induction f,
    induction g,
    tidy,
  end

instance DrinfeldCentre : category.{(max u v) v} (HalfBraiding C) := 
{ Hom      := λ X Y, HalfBraidingMorphism X Y,
  identity := λ X, { morphism := 𝟙 (X.object) },
  compose  := λ _ _ _ f g, { morphism := f.morphism ≫ g.morphism } }

end categories.drinfeld_centre