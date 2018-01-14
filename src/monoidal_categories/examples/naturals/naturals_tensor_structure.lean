-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import categories.examples.naturals
import ...monoidal_category

namespace categories.examples.naturals

open categories
open categories.functor
open categories.natural_transformation
open categories.products
open categories.monoidal_category

-- definition ℕTensorProduct : TensorProduct ℕCategory :=
--   { onObjects     := prod.fst,
--     onMorphisms   := λ _ _ n, n.fst + n.snd,
--     identities    := ♮,
--     functoriality := ♯
--   }

-- -- local attribute [simp] id_locked_eq

-- -- PROJECT What follows involves a lot of boring natural transformations
-- -- Can we construct them automatically?
-- definition ℕMonoidalCategory : MonoidalStructure ℕCategory :=
-- begin
-- refine { 
--    tensor                    := ℕTensorProduct,
--    tensor_unit               := (),
--    associator_transformation := {
--      morphism := { components := λ _, 0, naturality := ♯ },
--      inverse  := { components := λ _, _, naturality := _ },
--      witness_1 := _,
--      witness_2 := _
--    },
--    left_unitor := sorry,
--    right_unitor := sorry,
--   --  left_unitor               := {
--   --    morphism := { components := λ _, 0, naturality := ♯ },
--   --    inverse  := { components := λ _, 0, naturality := ♯ },
--   --    witness_1 := ♮,
--   --    witness_2 := ♮
--   --  },
--   --  right_unitor              := {
--   --    morphism := { components := λ _, 0, naturality := ♯ },
--   --    inverse  := { components := λ _, 0, naturality := ♯ },
--   --    witness_1 := ♮,
--   --    witness_2 := ♮
--   --  },
--    pentagon := sorry,
--    triangle := sorry
--  },
-- --  dsimp,
-- --  dsimp at _x,
-- --  unfold ProductCategory at _x,
-- --  dsimp at _x,
 
--  all_goals { intros_and_inductions },
--  all_goals { unfold_unfoldable_hypotheses },
-- --  all_goals { dunfold ℕCategory at snd },
-- --  all_goals { dsimp at snd }
-- --  all_goals { dsimp },
-- --  all_goals { unfold_unfoldable },
--   all_goals { admit }
--  end 

end categories.examples.naturals
