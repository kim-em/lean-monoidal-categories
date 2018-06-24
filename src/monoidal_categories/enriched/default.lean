import ..monoidal_category
import categories.types

open categories
open categories.monoidal_category

universes u₁ v₁

class enriched_category (C : Type u₁) extends category.{u₁ v₁} C :=
  (V : Type (v₁+1))
  [𝒱 : monoidal_category V]
  (F : V ↝ (Type v₁)) -- needs to be a monoidal functor
  (enriched_hom : C → C → V)
  (enriched_identity : Π X : C, (monoidal_category.tensor_unit V) ⟶ (enriched_hom X X))
  (enriched_composition : Π X Y Z : C, (enriched_hom X Y) ⊗ (enriched_hom Y Z) ⟶ (enriched_hom X Z))
  (underlying_type_of_enriched_hom : Π X Y : C, F +> (enriched_hom X Y) = (X ⟶ Y))
  (underlying_function_of_enriched_identity : Π X : C, sorry)
  (underlying_function_of_enriched_composition : Π X Y Z : C, sorry)

class enriched_category' (C : Type u₁) (V : Type v₁) [𝒱 : monoidal_category V] :=
  (Hom : C → C → V)
  (identity : Π X : C, (monoidal_category.tensor_unit V) ⟶ (Hom X X))
  (compose  : Π {X Y Z : C}, (Hom X Y) ⊗ (Hom Y Z) ⟶ Hom X Z)
  (left_identity  : ∀ {X Y : C}, sorry)
  (right_identity : ∀ {X Y : C}, sorry)
  (associativity  : ∀ {W X Y Z : C}, sorry)

