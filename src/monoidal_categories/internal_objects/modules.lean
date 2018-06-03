-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .semigroup_modules
import .monoids

open categories
open categories.monoidal_category

namespace categories.internal_objects

universes u v

open MonoidObject

structure ModuleObject {C : Type u} [𝒞 : monoidal_category.{u v} C] (A : C) [MonoidObject A] extends SemigroupModuleObject A :=
  (identity  : (inverse_left_unitor module) ≫ ((ι A) ⊗ (𝟙 module)) ≫ action = 𝟙 module)

attribute [simp,ematch] ModuleObject.identity

variables {C : Type u} [𝒞 : monoidal_category.{u v} C] {A : C} [MonoidObject A]
include 𝒞

structure ModuleMorphism ( X Y : ModuleObject A )
  extends SemigroupModuleMorphism X.to_SemigroupModuleObject Y.to_SemigroupModuleObject

@[applicable] lemma ModuleMorphism_pointwise_equal
  { X Y : ModuleObject A }
  ( f g : ModuleMorphism X Y )
  ( w : f.map = g.map ) : f = g :=
  begin
    induction f with f_underlying,
    induction g with g_underlying,
    tidy,
  end

definition CategoryOfModules : category.{(max u v) v} (ModuleObject A) :=
{ Hom := λ X Y, ModuleMorphism X Y,
  identity := λ X, ⟨ ⟨ 𝟙 X.module, by obviously ⟩ ⟩, -- we need double ⟨ ⟨ ... ⟩ ⟩ because we're using structure extension
  compose  := λ _ _ _ f g, ⟨ ⟨ f.map ≫ g.map, by obviously ⟩ ⟩ }

end categories.internal_objects