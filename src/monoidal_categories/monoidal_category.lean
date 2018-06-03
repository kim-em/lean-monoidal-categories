-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .tensor_product

open categories
open categories.functor
open categories.products
open categories.natural_transformation

namespace categories.monoidal_category

universes u v

class monoidal_category (C : Type u) extends category.{u v} C :=
  (tensor                      : TensorProduct C)
  (tensor_unit                 : C)
  (associator_transformation   : Associator tensor)
  (left_unitor_transformation  : LeftUnitor tensor_unit tensor)
  (right_unitor_transformation : RightUnitor tensor_unit tensor)

  (pentagon                  : Pentagon associator_transformation . obviously)
  (triangle                  : Triangle left_unitor_transformation right_unitor_transformation associator_transformation . obviously)

variables {C : Type u} --[category.{u v} C]

make_lemma monoidal_category.pentagon
make_lemma monoidal_category.triangle
attribute [ematch] monoidal_category.pentagon_lemma
attribute [simp,ematch] monoidal_category.triangle_lemma

open  monoidal_category

variable [𝒞 : monoidal_category.{u v} C]
include 𝒞

-- Convenience methods which take two arguments, rather than a pair. (This seems to often help the elaborator avoid getting stuck on `prod.mk`.)
definition tensorObjects (X Y : C) : C := (tensor C) +> (X, Y)

infixr ` ⊗ `:80 := tensorObjects -- type as \otimes

definition tensorMorphisms {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : (W ⊗ Y) ⟶ (X ⊗ Z) := 𝒞.tensor &> ⟨f, g⟩

infixr ` ⊗ `:80 := tensorMorphisms -- type as \otimes

@[reducible] definition left_unitor (X : C) : (𝒞.tensor_unit ⊗ X) ⟶ X := ((left_unitor_transformation C).components X).morphism
  
@[reducible] definition right_unitor (X : C) : (X ⊗ 𝒞.tensor_unit) ⟶ X := ((right_unitor_transformation C).components X).morphism

@[reducible] definition inverse_left_unitor (X : C) : X ⟶ (𝒞.tensor_unit ⊗ X) := 𝒞.left_unitor_transformation.inverse.components X
  
@[reducible] definition inverse_right_unitor (X : C) : X ⟶ (X ⊗ 𝒞.tensor_unit) := 𝒞.right_unitor_transformation.inverse.components X

@[reducible] definition associator (X Y Z : C) : ((X ⊗ Y) ⊗ Z) ⟶ (X ⊗ (Y ⊗ Z)) :=
  ((associator_transformation C).components ⟨⟨X, Y⟩, Z⟩).morphism

@[reducible] definition inverse_associator (X Y Z : C) : (X ⊗ (Y ⊗ Z)) ⟶ ((X ⊗ Y) ⊗ Z) :=
  (associator_transformation C).inverse.components ⟨⟨X, Y⟩, Z⟩

variables {U V W X Y Z : C}

@[ematch] definition interchange (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z) :
  (f ≫ g) ⊗ (h ≫ k) = (f ⊗ h) ≫ (g ⊗ k) :=
  @Functor.functoriality (C × C) _ C _ 𝒞.tensor ⟨U, X⟩ ⟨V, Y⟩ ⟨W, Z⟩ ⟨f, h⟩ ⟨g, k⟩

@[simp,ematch] lemma interchange_left_identity (f : W ⟶ X) (g : X ⟶ Y) :
  (f ⊗ 𝟙 Z) ≫ (g ⊗ 𝟙 Z) = (f ≫ g) ⊗ (𝟙 Z)
    := by obviously

@[simp,ematch] lemma interchange_right_identity (f : W ⟶ X) (g : X ⟶ Y) :
  (𝟙 Z ⊗ f) ≫ (𝟙 Z ⊗ g) = (𝟙 Z) ⊗ (f ≫ g)
    := by obviously

@[ematch] lemma interchange_identities (f : W ⟶ X) (g : Y ⟶ Z) :
  ((𝟙 Y) ⊗ f) ≫ (g ⊗ (𝟙 X)) = (g ⊗ (𝟙 W)) ≫ ((𝟙 Z) ⊗ f) := by obviously

@[simp,ematch] lemma tensor_identities (X Y : C) :
   (𝟙 X) ⊗ (𝟙 Y) = 𝟙 (X ⊗ Y) := 𝒞.tensor.identities ⟨X, Y⟩

lemma inverse_associator_naturality_0
  (f : U ⟶ V ) (g : W ⟶ X) (h : Y ⟶ Z) : (f ⊗ (g ⊗ h)) ≫ (inverse_associator V X Z) = (inverse_associator U  W Y) ≫ ((f ⊗ g) ⊗ h) :=
  begin
    apply @NaturalTransformation.naturality _ _ _ _ _ _ ((𝒞.associator_transformation).inverse) ((U, W), Y) ((V, X), Z) ((f, g), h)
  end

end categories.monoidal_category
