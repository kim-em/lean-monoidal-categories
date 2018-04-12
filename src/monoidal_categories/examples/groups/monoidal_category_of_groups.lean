-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...braided_monoidal_category
import categories.universal.instances
import ...monoidal_structure_from_products
import categories.examples.groups

open categories.natural_transformation
open categories.monoidal_category

namespace categories.examples.groups

open categories.products
open categories.universal
definition MonoidalStructureOnCategoryOfGroups : MonoidalStructure CategoryOfGroups := MonoidalStructure_from_Products CategoryOfGroups

open categories.braided_monoidal_category
definition SymmetryOnCategoryOfGroups : Symmetry MonoidalStructureOnCategoryOfGroups := Symmetry_on_MonoidalStructure_from_Products CategoryOfGroups 

end categories.examples.groups
