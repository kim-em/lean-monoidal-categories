-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import .monoidal_structure_from_products

open categories
open categories.functor
open categories.products
open categories.natural_transformation
open categories.monoidal_category
open categories.universal

namespace categories.monoidal_category

-- FIXME where do these lost meta-variables come from?
definition LeftUnitor_for_Products ( C : Category ) [ has_TerminalObject C ] [ has_BinaryProducts C ] : LeftUnitor terminal_object (TensorProduct_from_Products C) :=
begin
  tidy, 
end

-- definition RightUnitor_for_Products ( C : Category ) [ has_BinaryProducts C ] : RightUnitor terminal_object (TensorProduct_from_Products C) :=
-- begin
--   tidy, 
-- end

-- definition MonoidalStructure_from_Products { C : Category } [ has_BinaryProducts C ] : MonoidalStructure C :=
-- {
--     tensor := TensorProduct_from_Products C,
--     tensor_unit := terminal_object,
--     associator_transformation := Associator_for_Products C,
--     left_unitor               := LeftUnitor_for_Products C,
--     right_unitor              := RightUnitor_for_Products C,
--     pentagon := ♯,
--     triangle := sorry
-- }

-- PROJECT show that this monoidal structure is uniquely braided
-- PROJECT and that braiding is symmetric

end categories.monoidal_category