-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..monoidal_category
import categories.functor_categories.whiskering

open categories
open categories.functor
open categories.products
open categories.natural_transformation
open categories.functor_categories

namespace categories.monoidal_category

universe variables u v

variables (C : Type u) [𝒞 : monoidal_category.{u v} C]
include 𝒞

open monoidal_category

@[reducible] definition pentagon_3step_1 :=
  let α := associator_transformation C in
  whisker_on_right
    (α.morphism × IdentityNaturalTransformation (IdentityFunctor C))
    𝒞.tensor

@[reducible] definition pentagon_3step_2 :=
  let α := associator_transformation C in
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator C C C × IdentityFunctor C)
      ((IdentityFunctor C × tensor C) × IdentityFunctor C))
    α.morphism

@[reducible] definition pentagon_3step_3 :=
  let α := associator_transformation C in
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator C C C × IdentityFunctor C)
      (ProductCategoryAssociator C (C × C) C))
    (whisker_on_right
      (IdentityNaturalTransformation (IdentityFunctor C) × α.morphism)
      (tensor C))

@[reducible] definition pentagon_3step  :=
      (pentagon_3step_1 C) ⊟
      (pentagon_3step_2 C) ⊟
      (pentagon_3step_3 C)

@[reducible] definition pentagon_2step_1 :=
  let α := associator_transformation C in
  whisker_on_left
    ((tensor C × IdentityFunctor C) × IdentityFunctor C)
    α.morphism

@[reducible] definition pentagon_2step_2 :=
  let α := associator_transformation C in
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator (C × C) C C)
      (IdentityFunctor (C × C) × tensor C))
    α.morphism

@[reducible] definition pentagon_2step :=
    (pentagon_2step_1 C) ⊟ 
    (pentagon_2step_2 C)

end categories.monoidal_category