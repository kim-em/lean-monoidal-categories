-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..braided_monoidal_category
import categories.functor_categories.isomorphisms
import tidy.its

open categories
open categories.functor
open categories.products
open categories.natural_transformation
open categories.monoidal_category
open categories.functor_categories

namespace categories.braided_monoidal_category

@[reducible] definition {u v} squared_Braiding {C : Type u} [𝒞 : monoidal_category.{u v} C] (commutor : Commutor C)
  : NaturalTransformation 𝒞.tensor 𝒞.tensor :=
  begin
   exact (commutor.morphism
           ⊟ (whisker_on_left (SwitchProductCategory C C) commutor.morphism)
           ⊟ (FunctorComposition_associator _ _ _).inverse
           ⊟ (whisker_on_right (SwitchSymmetry _ _).morphism 𝒞.tensor)
           ⊟ (FunctorComposition_left_unitor 𝒞.tensor).morphism)
  end 

lemma {u v} symmetry_in_terms_of_natural_transformations {C : Type u} [𝒞 : monoidal_category.{u v} C] (β : Symmetry C) : squared_Braiding (β.braiding) = IdentityNaturalTransformation 𝒞.tensor := by obviously

lemma {u v} symmetric_in_terms_of_components {C : Type u} [𝒞 : monoidal_category.{u v} C] (β : Braiding C) (e : squared_Braiding (β.braiding) = IdentityNaturalTransformation 𝒞.tensor) : Symmetry C :=
{ β with 
    symmetry := λ X Y : C, begin
                             its congr_fun (congr_arg NaturalTransformation.components e) (X, Y),
                             obviously
                           end }

end categories.braided_monoidal_category
