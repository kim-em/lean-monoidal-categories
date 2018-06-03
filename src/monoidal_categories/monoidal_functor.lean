-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

open categories
open categories.functor
open categories.natural_transformation
open categories.monoidal_category
open categories.isomorphism

namespace categories.monoidal_functor

universe variables u₁ v₁ u₂ v₂ u₃ v₃

section
variables (C : Type u₁) [𝒞 : monoidal_category.{u₁ v₁} C]
variables (D : Type u₂) [𝒟 : monoidal_category.{u₂ v₂} D]
include 𝒞 𝒟 

structure MonoidalFunctor extends Functor C D :=
  ( tensorator : (𝒞.tensor ⋙ to_Functor) ⇔ ((to_Functor × to_Functor) ⋙ 𝒟.tensor) )
  ( associativity : ∀ X Y Z : C, 
      (tensorator.morphism.components (X ⊗ Y, Z)) ≫ ((tensorator.morphism.components (X, Y)) ⊗ (𝟙 (onObjects Z))) ≫ (associator (onObjects X) (onObjects Y) (onObjects Z))
      = (onMorphisms (associator X Y Z)) ≫ (tensorator.morphism.components (X, Y ⊗ Z)) ≫ ((𝟙 (onObjects X)) ⊗ (tensorator.morphism.components (Y, Z)))
  )
  ( identerator : (onObjects 𝒞.tensor_unit) ≅ 𝒟.tensor_unit)
  ( left_identity  : ∀ X : C, (tensorator.morphism.components (𝒞.tensor_unit, X)) ≫ (identerator.morphism ⊗ (𝟙 (onObjects X))) ≫ (left_unitor  (onObjects X)) = onMorphisms (left_unitor X)  )
  ( right_identity : ∀ X : C, (tensorator.morphism.components (X, 𝒞.tensor_unit)) ≫ ((𝟙 (onObjects X)) ⊗ identerator.morphism) ≫ (right_unitor (onObjects X)) = onMorphisms (right_unitor X) )
  
attribute [simp,ematch] MonoidalFunctor.left_identity
attribute [simp,ematch] MonoidalFunctor.right_identity
attribute [ematch]      MonoidalFunctor.associativity
end

section
variables {C : Type u₁} [𝒞 : monoidal_category.{u₁ v₁} C]
variables {D : Type u₂} [𝒟 : monoidal_category.{u₂ v₂} D]
include 𝒞 𝒟 

-- PROJECT composition of MonoidalFunctors

-- PROJECT Automation should construct even the tensorator! Perhaps we need to mark certain transformations and isomorphisms as allowed.

-- definition MonoidalFunctorComposition
--   { C : Category.{u1 v1} }
--   { D : Category.{u2 v2} }
--   { E : Category.{u3 v3} }
--   { m : MonoidalStructure C }
--   { n : MonoidalStructure D }
--   { o : MonoidalStructure E }
--   ( F : MonoidalFunctor m n ) ( G : MonoidalFunctor n o ) : MonoidalFunctor m o :=
-- {
--   functor        := @FunctorComposition C D E F G,
--   tensorator     := {
--     morphism  := begin                   
--                    rewrite ← FunctorComposition.associativity,
--                    exact sorry
--                  end,
--     inverse   := sorry,
--     witness_1 := sorry,
--     witness_2 := sorry
--   },
--   associativity  := sorry,
--   identerator    := sorry,
--   left_identity  := sorry,
--   right_identity := sorry
-- }

structure MonoidalNaturalTransformation ( F G : MonoidalFunctor.{u₁ v₁ u₂ v₂ } C D ) extends NaturalTransformation F.to_Functor G.to_Functor :=
  ( compatibility_with_tensor : ∀ X Y : C, (F.tensorator.morphism.components (X, Y)) ≫ ((components X) ⊗ (components Y)) = (components (X ⊗ Y)) ≫ (G.tensorator.morphism.components (X, Y)) )
  ( compatibility_with_unit   : (components 𝒞.tensor_unit) ≫ G.identerator.morphism = F.identerator.morphism )

end

attribute [simp,ematch] MonoidalNaturalTransformation.compatibility_with_tensor
attribute [simp,ematch] MonoidalNaturalTransformation.compatibility_with_unit

-- @[applicable] lemma MonoidalNaturalTransformation_componentwise_equal
--   { C : Category.{u1 v1} }
--   { D : Category.{u2 v2} }
--   { m : MonoidalStructure C }
--   { n : MonoidalStructure D }
--   ( F G : MonoidalFunctor m n )
--   ( α β : MonoidalNaturalTransformation F G )
--   ( w : α.natural_transformation = β.natural_transformation ) : α = β :=
--   begin
--     induction α with α_components α_naturality,
--     induction β with β_components β_naturality,
--     dsimp at w,
--     -- blast
--   end

-- instance MonoidalNaturalTransformation_coercion_to_NaturalTransformation
--   { C : Category.{u1 v1} }
--   { D : Category.{u2 v2} }
--   { m : MonoidalStructure C }
--   { n : MonoidalStructure D }
--   ( F G : MonoidalFunctor m n ) : has_coe (MonoidalNaturalTransformation F G) (NaturalTransformation F.functor G.functor) :=
--   { coe := MonoidalNaturalTransformation.natural_transformation }

-- definition IdentityMonoidalNaturalTransformation
--   { C : Category.{u1 v1} }
--   { D : Category.{u2 v2} }
--   { m : MonoidalStructure C }
--   { n : MonoidalStructure D }
--   ( F : MonoidalFunctor m n ) : MonoidalNaturalTransformation F F :=
--     ⟨ IdentityNaturalTransformation F.functor, ♮, ♮ ⟩

-- definition vertical_composition_of_MonoidalNaturalTransformations
--   { C : Category.{u1 v1} }
--   { D : Category.{u2 v2} }
--   { m : MonoidalStructure C }
--   { n : MonoidalStructure D }
--   { F G H : MonoidalFunctor m n } 
--   ( α : MonoidalNaturalTransformation F G ) 
--   ( β : MonoidalNaturalTransformation G H ) : MonoidalNaturalTransformation F H :=
-- {
--   natural_transformation    := vertical_composition_of_NaturalTransformations α.natural_transformation β.natural_transformation,
--   compatibility_with_tensor := begin
--                                 -- abstract {
--                                   -- TODO It seems that one round of blast should succeed here!
--                                   -- blast,
--                                   intros, dsimp,
--                                   rewrite D.interchange,
--                                   rewrite ← D.associativity,
--                                   rewrite α.compatibility_with_tensor,
--                                   -- blast, -- This blast seems to cause the CPU to pin at maximum, and start ignoring earlier edits.
--                                   rewrite D.associativity,
--                                   rewrite β.compatibility_with_tensor,
--                                   blast -- What is this blast even doing? It seems dsimp should be enough.
--                                 -- }
--                                end,
--   compatibility_with_unit   := ♮                               
-- }

-- PROJECT horizontal_composition_of_MonoidalNaturalTransformations
-- definition horizontal_composition_of_MonoidalNaturalTransformations
--   { C : Category.{u1 v1} }
--   { D : Category.{u2 v2} }
--   { E : Category.{u3 v3} }
--   { m : MonoidalStructure C }
--   { n : MonoidalStructure C }
--   { o : MonoidalStructure C }
--   { F G : MonoidalFunctor m n } 
--   { H K : MonoidalFunctor n o } 
--   ( α : MonoidalNaturalTransformation F G ) 
--   ( β : MonoidalNaturalTransformation H K ) : MonoidalNaturalTransformation (MonoidalFunctorComposition F H) (MonoidalFunctorComposition G K) :=
-- {
--   natural_transformation    := α.natural_transformation ∘ₕ β.natural_transformation,
--   compatibility_with_tensor := sorry,
--   compatibility_with_unit   := sorry
-- }


-- definition CategoryOfMonoidalFunctors   
--   { C : Category.{u1 v1} }
--   { D : Category.{u2 v2} }
--   { m : MonoidalStructure C }
--   { n : MonoidalStructure D } : Category :=
-- {
--   Obj := MonoidalFunctor C D,
--   Hom := MonoidalNaturalTransformation,
--   identity := IdentityMonoidalNaturalTransformation,
--   compose  := λ _ _ _ α β, vertical_composition_of_MonoidalNaturalTransformations α β,

--   left_identity  := ♮,
--   right_identity := ♮,
--   associativity  := ♮
-- }

end categories.monoidal_functor