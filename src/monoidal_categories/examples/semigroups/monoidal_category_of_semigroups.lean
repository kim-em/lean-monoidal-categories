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

open categories.products
open categories.universal
definition MonoidalStructureOnCategoryOfSemigroups : MonoidalStructure CategoryOfSemigroups := MonoidalStructure_from_Products CategoryOfSemigroups

open categories.braided_monoidal_category
definition SymmetryOnCategoryOfSemigroups : Symmetry MonoidalStructureOnCategoryOfSemigroups := Symmetry_on_MonoidalStructure_from_Products CategoryOfSemigroups 

end categories.examples.semigroups
