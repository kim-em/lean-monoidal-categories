-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..monoidal_category

open categories
open categories.functor
open categories.products
open categories.natural_transformation

namespace categories.monoidal_category

universe variables u v

variables (C : Type u) [𝒞 : monoidal_category.{u v} C]
include 𝒞

@[reducible] definition pentagon_3step_1 :=
  let α := 𝒞.associator_transformation in
  whisker_on_right
    (α.morphism × IdentityNaturalTransformation (IdentityFunctor C))
    𝒞.tensor

@[reducible] definition pentagon_3step_2 { C : Category.{u v} } ( m : MonoidalStructure C ) :=
  let α := m.associator_transformation in
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator C C C × IdentityFunctor C)
      ((IdentityFunctor C × m.tensor) × IdentityFunctor C))
    α.morphism

@[reducible] definition pentagon_3step_3 { C : Category.{u v} } ( m : MonoidalStructure C ) :=
  let α := m.associator_transformation in
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator C C C × IdentityFunctor C)
      (ProductCategoryAssociator C (C × C) C))
    (whisker_on_right
      (IdentityNaturalTransformation (IdentityFunctor C) × α.morphism)
      m.tensor)

@[reducible] definition pentagon_3step { C : Category.{u v} } ( m : MonoidalStructure C ) :=
  vertical_composition_of_NaturalTransformations
    (vertical_composition_of_NaturalTransformations
      (pentagon_3step_1 m)
      (pentagon_3step_2 m))
    (pentagon_3step_3 m)

@[reducible] definition pentagon_2step_1 { C : Category.{u v} } ( m : MonoidalStructure C ) :=
  let α := m.associator_transformation in
  whisker_on_left
    ((m.tensor × IdentityFunctor C) × IdentityFunctor C)
    α.morphism

@[reducible] definition pentagon_2step_2 { C : Category.{u v} } ( m : MonoidalStructure C ) :=
  let α := m.associator_transformation in
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator (C × C) C C)
      (IdentityFunctor (C × C) × m.tensor))
    α.morphism

@[reducible] definition pentagon_2step { C : Category.{u v} } ( m : MonoidalStructure C ) :=
  vertical_composition_of_NaturalTransformations
    (pentagon_2step_1 m)
    (pentagon_2step_2 m)

end categories.monoidal_category