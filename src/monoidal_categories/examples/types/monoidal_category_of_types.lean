-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...braided_monoidal_category
import ...monoidal_structure_from_products
import categories.types

namespace categories.types

open categories
open categories.monoidal_category
open categories.braided_monoidal_category

definition MonoidalCategoryOfTypes : MonoidalStructure CategoryOfTypes := MonoidalStructure_from_Products CategoryOfTypes

definition SymmetricMonoidalCategoryOfTypes : Symmetry MonoidalCategoryOfTypes := Symmetry_on_MonoidalStructure_from_Products CategoryOfTypes

end categories.types
