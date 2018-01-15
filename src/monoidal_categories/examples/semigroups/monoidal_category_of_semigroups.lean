-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...braided_monoidal_category
import categories.universal.instances
import ...monoidal_structure_from_products
import categories.examples.semigroups

open categories.natural_transformation

namespace categories.examples.semigroups

open categories.monoidal_category

local attribute [applicable] semigroup.mul_assoc

definition {u} semigroup_product { α β : Type u } ( s : semigroup α ) ( t: semigroup β ) : semigroup (α × β) := {
  mul := λ p q, (p.fst * q.fst, p.snd * q.snd),
  mul_assoc := ♯
}

definition {u} semigroup_morphism_product
  { α β γ δ : Type u }
  { s_f : semigroup α } { s_g: semigroup β } { t_f : semigroup γ } { t_g: semigroup δ }
  ( f : semigroup_morphism s_f t_f ) ( g : semigroup_morphism s_g t_g )
  : semigroup_morphism (semigroup_product s_f s_g) (semigroup_product t_f t_g) := {
  map := λ p, (f p.1, g p.2),
  multiplicative := ♯
}

-- PROJECT really this should be a special case of the (uniquely braided, symmetric) monoidal structure coming from a product.

open categories.products
open categories.universal

-- instance Semigroups_has_TerminalObject : has_TerminalObject CategoryOfSemigroups := {
--   terminal_object := {
--     terminal_object := ⟨ punit, trivial_semigroup ⟩,
--     morphism_to_terminal_object_from := ♯,
--     uniqueness_of_morphisms_to_terminal_object := begin tidy, admit end
--   }
-- }

-- instance Semigroups_has_BinaryProducts : has_BinaryProducts CategoryOfSemigroups := {
--   binary_product := λ s t, {
--     product             := ⟨ s.1 × t.1, semigroup_product s.2 t.2 ⟩ ,
--     left_projection     := {
--       map := prod.fst,
--       multiplicative := ♯
--     },
--     right_projection    := {
--       map := prod.snd,
--       multiplicative := ♯
--     },
--     map                 := λ r f g, {
--       map := λ x, (f.map x, g.map x),
--       multiplicative := ♯ 
--     },
--     left_factorisation  := ♯,
--     right_factorisation := ♯,
--     uniqueness          := λ r f g w₁ w₂, begin
--       apply semigroup_morphism_pointwise_equality,
--       intro x,
--       apply pairs_componentwise_equal,
--       admit,
--       admit
--     end
--   }
-- }


-- definition MonoidalStructureOnCategoryOfSemigroups : MonoidalStructure CategoryOfSemigroups := MonoidalStructure_from_Products CategoryOfSemigroups


-- Below, I was doing it directly:

-- definition TensorProduct_for_Semigroups : TensorProduct CategoryOfSemigroups := {
--     onObjects     := λ p, ⟨ p.1.1 × p.2.1, semigroup_product p.1.2 p.2.2 ⟩,
--     onMorphisms   := λ s t f, semigroup_morphism_product f.1 f.2,
--     identities    := ♯,
--     functoriality := ♮
--   }

-- definition Associator_for_Semigroups : Associator TensorProduct_for_Semigroups := {
--     morphism := {
--       components := λ _, {
--         map := λ t, (t.1.1, (t.1.2, t.2)),
--         multiplicative := ♮
--       },
--       naturality := ♮ 
--     },
--     inverse := {
--       components := λ _, {
--         map := λ t, ((t.1, t.2.1), t.2.2),
--         multiplicative := ♮
--       },
--       naturality := ♮  
--     },
--     witness_1 := ♯,
--     witness_2 := ♯
--   }

-- definition TensorUnit_for_Semigroups : CategoryOfSemigroups.Obj := ⟨ punit, trivial_semigroup ⟩  -- punit is just a universe-parameterized version of unit

-- definition LeftUnitor_for_Semigroups : @LeftUnitor CategoryOfSemigroups TensorUnit_for_Semigroups TensorProduct_for_Semigroups := {
--     morphism := {
--       components := λ _, {
--         map := λ t, t.2,
--         multiplicative := ♮
--       },
--       naturality := ♮ 
--     },
--     inverse := {
--       components := λ _, {
--         map := λ t, (punit.star, t),
--         multiplicative := ♮
--       },
--       naturality := ♮ 
--     },
--     witness_1 := ♯,
--     witness_2 := ♮
--   }

-- definition RightUnitor_for_Semigroups : @RightUnitor CategoryOfSemigroups TensorUnit_for_Semigroups TensorProduct_for_Semigroups := {
--     morphism := {
--       components := λ _, {
--         map := λ t, t.1,
--         multiplicative := ♮
--       },
--       naturality := ♮ 
--     },
--     inverse := {
--       components := λ _, {
--         map := λ t, (t, punit.star),
--         multiplicative := ♮
--       },
--       naturality := ♮ 
--     },
--     witness_1 := ♯,
--     witness_2 := ♮
--   }

-- definition MonoidalStructureOnCategoryOfSemigroups : MonoidalStructure CategoryOfSemigroups := 
-- {
--   tensor                      := TensorProduct_for_Semigroups,
--   tensor_unit                 := TensorUnit_for_Semigroups,
--   associator_transformation   := Associator_for_Semigroups,
--   left_unitor_transformation  := LeftUnitor_for_Semigroups,
--   right_unitor_transformation := RightUnitor_for_Semigroups,
--   pentagon                    := ♯,
--   triangle                    := ♯
-- }

-- open categories.natural_transformation
-- open categories.braided_monoidal_category

-- definition SymmetryOnCategoryOfSemigroups : Symmetry MonoidalStructureOnCategoryOfSemigroups := {
--   braiding := {
--     morphism  := {
--       components := λ _, {
--                            map := λ p, (p.2, p.1),
--                            multiplicative := ♮
--                          },
--       naturality := ♮
--     },
--     inverse   := {
--       components := λ _, {
--                            map := λ p, (p.2, p.1), -- PROJECT this is sufficiently obvious that automation should be doing it for us!
--                            multiplicative := ♮
--                          },
--       naturality := ♮
--     },
--     witness_1 := ♯,
--     witness_2 := ♯
--   },
--   hexagon_1 := ♯,
--   hexagon_2 := ♯,
--   symmetry  := ♯
-- }

end categories.examples.semigroups
