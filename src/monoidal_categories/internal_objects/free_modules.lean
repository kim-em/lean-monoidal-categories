-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoids

open categories
open categories.functor
open categories.monoidal_category

namespace categories.internal_objects

-- set_option pp.max_steps 50000
-- set_option pp.implicit true
-- set_option pp.universes true
-- set_option pp.coercions true
-- set_option pp.all true
-- set_option pp.implicit false

-- local attribute [elab_simple] prod.mk
universe u

variables {C : Type (u+1)} [category C] [m : monoidal_category C]
include m

def fmod (A : C) [MonoidObject A] := C

definition CategoryOfFreeModules (A : C) [MonoidObject A]  : category (fmod A) :=
{ Hom := λ X Y : C, X ⟶ (A ⊗ Y),
  identity := λ X : C, (inverse_left_unitor X) ≫ ((ι A) ⊗ (𝟙 X)),
  compose := λ _ _ Z f g, f ≫ ((𝟙 A) ⊗ g) ≫ (inverse_associator A A Z) ≫ (μ A ⊗ (𝟙 Z)),
  left_identity := begin
                    -- PROJECT dealing with associativity here is quite tedious.
                    -- PROJECT this is a great example problem for clever automation.
                    -- A human quickly sees that we need to combine A.unit and A.multiplication to make them cancel,
                    -- and then performs the necessary rewrites to get there.
                    intros,
                    conv {
                      to_lhs,                      
                      rewrite category.associativity,
                      congr, skip,
                      rewrite ← category.associativity,
                      rewrite ← interchange_identities,
                      rewrite category.associativity,
                      congr, skip,
                      rewrite ← category.associativity,
                      rewrite ← tensor_identities,
                      rewrite inverse_associator_naturality_0,
                      rewrite category.associativity,
                      congr, skip,
                      rewrite interchange_left_identity,
                      congr,
                      rewrite [MonoidObject.left_identity] {tactic.rewrite_cfg . md := semireducible},
                    },
                    simp,
                    conv {
                      to_lhs,
                      rewrite ← category.associativity,
                      congr,
                      rewrite [← m.left_unitor_transformation.inverse.naturality] {tactic.rewrite_cfg . md := semireducible},                    
                    },
                    simp,
                    dunfold IdentityFunctor, dsimp,
                    -- PROJECT this needs Proposition 2.2.4 of Etingof's "Tensor Categories" to finish; and that seems awkward to prove in our setup!
                    exact sorry
                   end,
  right_identity := sorry,
  associativity := sorry
}

-- PROJECT show that after idempotent completing the category of free modules we get the category of modules??
-- PROJECT bimodules
-- PROJECT commutative algebras; modules give bimodules

end categories.internal_objects