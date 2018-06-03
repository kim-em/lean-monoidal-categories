-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..monoidal_category

open categories
open categories.monoidal_category

namespace categories.examples

universe u

local attribute [ematch] semigroup.mul_assoc

definition turtle (α : Type u) : Type u := punit.{u+1}

instance monoid_as_category (α : Type u) [monoid α] : category.{u u} (turtle α) :=
{ Hom      := λ _ _, α,
  compose  := λ _ _ _ f g, f * g,
  identity := λ _, 1 }

local attribute [applicable] has_one.one

definition comm_monoid_as_monoidal_category (α : Type) [comm_monoid α] : monoidal_category (turtle α) :=
{ (examples.monoid_as_category α) with 
  tensor := 
    { onObjects     := λ _, punit.star,
      onMorphisms   := λ _ _ p, p.1 * p.2 },
  tensor_unit := punit.star,
  -- TODO: ugh, it sucks that by obviously is so much slower in the following:
  associator_transformation   := { morphism := { components := by obviously, naturality := by obviously }, inverse := { components := by obviously, naturality := by obviously }, witness_1 := by obviously, witness_2 := by obviously },
  left_unitor_transformation  := { morphism := { components := by obviously, naturality := by obviously }, inverse := { components := by obviously, naturality := by obviously }, witness_1 := by obviously, witness_2 := by obviously },
  right_unitor_transformation := { morphism := { components := by obviously, naturality := by obviously }, inverse := { components := by obviously, naturality := by obviously }, witness_1 := by obviously, witness_2 := by obviously }, }

end categories.examples