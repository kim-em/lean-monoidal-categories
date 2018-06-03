-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .semigroups

open categories
open categories.monoidal_category

namespace categories.internal_objects

universes u v

open SemigroupObject

structure SemigroupModuleObject {C : Type u} [monoidal_category.{u v} C] (A : C) [SemigroupObject A] :=
  (module : C)
  (action : (A ⊗ module) ⟶ module)
  (associativity : ((μ A) ⊗ (𝟙 module)) ≫ action = (associator A A module) ≫ ((𝟙 A) ⊗ action) ≫ action)

attribute [ematch] SemigroupModuleObject.associativity

variables {C : Type u} [𝒞 : monoidal_category.{u v} C] {A : C} [SemigroupObject A]
include 𝒞

structure SemigroupModuleMorphism (X Y : SemigroupModuleObject A) :=
  (map : X.module ⟶ Y.module)
  (compatibility : ((𝟙 A) ⊗ map) ≫ Y.action = X.action ≫ map)

attribute [simp,ematch] SemigroupModuleMorphism.compatibility

@[applicable] lemma SemigroupModuleMorphism_pointwise_equal
  {X Y : SemigroupModuleObject A}
  (f g : SemigroupModuleMorphism X Y)
  (w : f.map = g.map) : f = g :=
  begin
    induction f,
    induction g,
    tidy
  end

definition CategoryOfSemigroupModules : category.{(max u v) v} (SemigroupModuleObject A) :=
{ Hom := λ X Y, SemigroupModuleMorphism X Y,
  identity := λ X, ⟨ 𝟙 X.module, by obviously ⟩,
  compose  := λ X Y Z f g, ⟨ f.map ≫ g.map, by obviously ⟩ }

end categories.internal_objects