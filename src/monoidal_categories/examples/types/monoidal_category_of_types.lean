-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...braided_monoidal_category
import category_theory.types

namespace categories.types

open categories
open categories.monoidal_category
open categories.braided_monoidal_category

-- PROJECT really this should be a special case of the (uniquely braided, symmetric) monoidal structure coming from a product.

definition TensorProductOfTypes : TensorProduct CategoryOfTypes :=
{
  onObjects     := λ p, p.1 × p.2,
  onMorphisms   := λ _ _ p q, (p.1 q.1, p.2 q.2),
  identities    := ♯,
  functoriality := ♮
}

-- PROJECT it would be great to generate all these inverse and witness fields via refine
definition MonoidalCategoryOfTypes : MonoidalStructure CategoryOfTypes :=
{
  tensor      := TensorProductOfTypes,
  tensor_unit := punit,
  associator_transformation := {
    morphism := {
      components := λ p t, (t.1.1, (t.1.2, t.2)),
      naturality := ♮
    },
    inverse := {
      components := λ p t, ((t.1, t.2.1), t.2.2),
      naturality := ♮
    },
    witness_1 := ♯,
    witness_2 := ♯
  },
  left_unitor_transformation := {
    morphism := {
      components := λ p t, t.2,
      naturality := ♮
    },
    inverse := {
      components := λ p t, (punit.star, t),
      naturality := ♮
    },
    witness_1 := ♯,
    witness_2 := ♮
  },
  right_unitor_transformation := {
    morphism := {
      components := λ p t, t.1,
      naturality := ♮
    },
    inverse := {
      components := λ p t, (t, punit.star),
      naturality := ♮
    },
    witness_1 := ♯,
    witness_2 := ♮
  },
  pentagon := ♯,
  triangle := ♯
}

definition SymmetricMonoidalCategoryOfTypes : Symmetry MonoidalCategoryOfTypes := {
  braiding := {
   morphism  := {
     components := λ p t, (t.snd, t.fst),
     naturality := ♮
   },
   inverse   := {
     components := λ p t, (t.snd, t.fst),
     naturality := ♮
   },
   witness_1 := ♯,
   witness_2 := ♯ 
  },
  hexagon_1 := ♯,
  hexagon_2 := ♯,
  symmetry  := ♯
}

end categories.types
