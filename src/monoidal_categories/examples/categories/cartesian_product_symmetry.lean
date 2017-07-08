-- -- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- -- Released under Apache 2.0 license as described in the file LICENSE.
-- -- Authors: Stephen Morgan, Scott Morrison
-- import .cartesian_product
-- import ...braided_monoidal_category

-- open categories
-- open categories.functor
-- open categories.products
-- open categories.natural_transformation
-- open categories.braided_monoidal_category

-- namespace categories.monoidal_category

-- local attribute [applicable] Functors_pointwise_equal

-- definition SymmetryOnCartesianProductOfCategories : Symmetry CartesianProductOfCategories := {
--   braiding             := {
--     morphism  := {
--       components := λ p, SwitchProductCategory p.1 p.2,
--       naturality := ♮
--     },
--     inverse   := {
--       components := λ p, SwitchProductCategory p.2 p.1,
--       naturality := ♮
--     },
--     witness_1 := ♯,
--     witness_2 := ♯
--   },
--   hexagon_1 := ♯,
--   hexagon_2 := ♯,
--   symmetry  := ♯
-- }

-- end categories.monoidal_category