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

variables (C : Type u) [𝒞 : monoidal_category.{u v} C]
include 𝒞

local attribute [tidy] dsimp_all'


set_option trace.check true

-- TODO tidy this up
lemma pentagon_in_terms_of_natural_transformations :
  pentagon_3step C = pentagon_2step C :=
  begin 
    dsimp',
    apply NaturalTransformations_componentwise_equal,
    intros WXYZ,
    induction WXYZ with WXY Z,
    induction WXY with WX Y,
    induction WX with W X,
    {
      tidy,
      -- erw rewrite_tensor_as_otimes, -- FIXME terrifying: equalities between objects are evil, and hence rewriting along them is hard
      have p := monoidal_category.pentagon C W X Y Z,
      -- have p := monoidal_category.pentagon C X_fst_fst_fst X_fst_fst_snd X_fst_snd X_snd,
      obviously, -- FIXME
    },
end

end categories.monoidal_category
