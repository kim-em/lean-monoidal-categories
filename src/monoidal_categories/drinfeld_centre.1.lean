-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .drinfeld_centre

open categories
open categories.functor
open categories.products
open categories.natural_transformation
open categories.monoidal_category

namespace categories.drinfeld_centre

universes u v

variables {C : Type u} [𝒞 : monoidal_category.{u v} C]
include 𝒞

definition DrinfeldCentreTensorUnit : HalfBraiding C := 
{ object := 𝒞.tensor_unit,
  commutor := vertical_composition_of_NaturalIsomorphisms 𝒞.left_unitor_transformation 𝒞.right_unitor_transformation.reverse }

open categories.monoidal_category.monoidal_category

definition DrinfeldCentreTensorProduct : TensorProduct (HalfBraiding C) := {
    onObjects   := λ p, {
      object   := p.1.object ⊗ p.2.object,
      commutor := {
        morphism := {
          components := λ X,
              associator p.1.object p.2.object X
              ≫ ((𝟙 p.1.object) ⊗ (p.2.commutor.morphism.components X))
              ≫ inverse_associator p.1.object X p.2.object
              ≫ ((p.1.commutor.morphism.components X) ⊗ (𝟙 p.2.object))
              ≫ associator X p.1.object p.2.object,
          naturality := begin obviously, end -- This is silly; we need nice notation that lets us write the commutor in components, but remembers that it is natural because it's built from natural things.
        },
        inverse := {
          components := sorry,
          naturality := sorry
        },
        witness_1 := sorry,
        witness_2 := sorry
      }
    },
    onMorphisms := sorry,
    identities := sorry,
    functoriality := sorry
  }

-- definition DrinfeldCentreAssociator { C : Category } ( m : MonoidalStructure C ) : Associator (DrinfeldCentreTensorProduct m) := {
--     components := sorry, --λ t, ⟨ m.associator_transformation ((t.1.1.object, t.1.2.object), t.2.object), sorry ⟩,
--     naturality := sorry
--   }

-- definition DrinfeldCentreAsMonoidalCategory { C : Category } ( m : MonoidalStructure C ) : MonoidalStructure (DrinfeldCentre m) := {
--   tensor_unit := DrinfeldCentreTensorUnit m,
--   tensor := DrinfeldCentreTensorProduct m,
--   associator_transformation := DrinfeldCentreAssociator m,
--   associator_is_isomorphism := sorry,
--   left_unitor  := {
--     components := sorry, --λ X, ⟨ m.left_unitor X.object, sorry ⟩,
--     naturality := sorry
--   },
--   right_unitor  := {
--     components := sorry, --λ X, ⟨ m.right_unitor X.object, sorry ⟩,
--     naturality := sorry
--   },
--   left_unitor_is_isomorphism  := sorry,
--   right_unitor_is_isomorphism := sorry,
--   pentagon := sorry,
--   triangle := sorry
-- }

-- PROJECT Drinfeld centre as a braided category.

end categories.drinfeld_centre
