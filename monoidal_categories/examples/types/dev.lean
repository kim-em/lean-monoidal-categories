-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.isomorphism
import category_theory.types

namespace categories.examples.types

open categories
open categories.isomorphism
open categories.types

-- definition TensorProductOfTypes : TensorProduct CategoryOfTypes :=
-- {
--   onObjects     := λ p, p.1 × p.2,
--   onMorphisms   := λ _ _ p q, (p.1 q.1, p.2 q.2),
--   identities    := ♯,
--   functoriality := ♮
-- }

structure IsomorphicTypes ( α β : Type ) :=
  ( morphism : α → β )
  ( inverse  : β → α )
  ( witness_1 : morphism ∘ inverse = id )
  ( witness_2 : inverse ∘ morphism = id )

open list
open tactic monad expr


definition test : IsomorphicTypes (((ℕ × ℕ) × ℕ)) (ℕ × (ℕ × ℕ)) :=
begin
    refine {
        morphism := λ t, (t.1.1, (t.1.2, t.2)),
        inverse  := _,
        witness_1 := _,
        witness_2 := _
    },
    tidy,
end

definition test' : Isomorphism CategoryOfTypes ((ℕ × ℕ) × ℕ) (ℕ × (ℕ × ℕ)) :=
begin
    refine {
        morphism := λ t, (t.1.1, (t.1.2, t.2)),
        inverse  := _,
        witness_1 := _,
        witness_2 := _
    },
    tidy,
end

-- definition AssociatorForTypes : Associator TensorProductOfTypes :=
-- begin
--     refine {
--         morphism := {
--             components := λ p t, (t.1.1, (t.1.2, t.2)),
--             naturality := ♮
--         },
--         inverse := _,
--         witness_1 := _,
--         witness_2 := _
--     },

    
-- end

end categories.examples.types