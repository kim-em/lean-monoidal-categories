-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...braided_monoidal_category
import categories.universal.instances
import ...monoidal_structure_from_products
import categories.examples.semigroups

open categories.natural_transformation
open categories.monoidal_category

namespace categories.examples.semigroups

-- PROJECT really this should be a special case of the (uniquely braided, symmetric) monoidal structure coming from a product.

open categories.products
open categories.universal
definition MonoidalStructureOnCategoryOfSemigroups : MonoidalStructure CategoryOfSemigroups := MonoidalStructure_from_Products CategoryOfSemigroups

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
