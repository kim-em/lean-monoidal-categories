-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .pentagon_in_terms_of_natural_transformations_definitions
import tidy.its

open categories
open categories.functor
open categories.products
open categories.natural_transformation

namespace categories.monoidal_category

universe variables u v

lemma pentagon_in_terms_of_natural_transformations
   { C : Category.{u v} } ( m : MonoidalStructure C ) :
  pentagon_3step m = pentagon_2step m :=
  begin 
    dsimp',
    apply NaturalTransformations_componentwise_equal,
    intros WXYZ,
    induction WXYZ with WXY Z,
    induction WXY with WX Y,
    induction WX with W X,
    {
      tidy,
      have p := m.pentagon W X Y Z,
      tidy,
    },
end

end categories.monoidal_category
