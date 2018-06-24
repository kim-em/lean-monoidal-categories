-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import .braided_monoidal_category
import categories.universal.instances
import categories.types
import categories.universal.types

open categories
open categories.functor
open categories.products
open categories.natural_transformation
open categories.monoidal_category
open categories.universal

namespace categories.monoidal_category

universes u v
variables {C : Type u} [category.{u v} C] [has_BinaryProducts.{u v} C] {W X Y Z : C}

@[reducible,applicable] definition left_associated_triple_Product_projection_1 : (binary_product (binary_product.{u v} X Y).product Z).product ⟶ X :=
  (BinaryProduct.left_projection _) ≫ (BinaryProduct.left_projection _)
@[reducible,applicable] definition left_associated_triple_Product_projection_2 : (binary_product (binary_product.{u v} X Y).product Z).product ⟶ Y :=
  (BinaryProduct.left_projection _) ≫ (BinaryProduct.right_projection _)
@[reducible,applicable] definition right_associated_triple_Product_projection_2 : (binary_product X (binary_product.{u v} Y Z).product).product ⟶ Y :=
  (BinaryProduct.right_projection _) ≫ (BinaryProduct.left_projection _)
@[reducible,applicable] definition right_associated_triple_Product_projection_3 : (binary_product X (binary_product.{u v} Y Z).product).product ⟶ Z :=
  (BinaryProduct.right_projection _) ≫ (BinaryProduct.right_projection _)

@[simp] lemma left_factorisation_associated_1 (h : W ⟶ Z) (f : Z ⟶ X ) (g : Z ⟶ Y) : (h ≫ ((binary_product.{u v} X Y).map f g)) ≫ (binary_product X Y).left_projection = h ≫ f := by obviously
@[simp] lemma left_factorisation_associated_2 (h : X ⟶ W) (f : Z ⟶ X ) (g : Z ⟶ Y) : ((binary_product.{u v} X Y).map f g) ≫ ((binary_product X Y).left_projection ≫ h) = f ≫ h := by obviously
@[simp] lemma right_factorisation_associated_1 (h : W ⟶ Z) (f : Z ⟶ X ) (g : Z ⟶ Y) : (h ≫ ((binary_product.{u v} X Y).map f g)) ≫ (binary_product X Y).right_projection = h ≫ g := by obviously
@[simp] lemma right_factorisation_associated_2 (h : Y ⟶ W) (f : Z ⟶ X ) (g : Z ⟶ Y) : ((binary_product.{u v} X Y).map f g) ≫ ((binary_product X Y).right_projection ≫ h) = g ≫ h := by obviously

definition TensorProduct_from_Products (C : Type u) [category.{u v} C] [has_BinaryProducts.{u v} C] : TensorProduct C := 
{ onObjects     := λ p, (binary_product.{u v} p.1 p.2).product,
  onMorphisms   := λ X Y f, ((binary_product Y.1 Y.2).map
                                ((binary_product X.1 X.2).left_projection ≫ (f.1))
                                ((binary_product X.1 X.2).right_projection ≫ (f.2))) }

local attribute [simp] category.associativity

definition Associator_for_Products : Associator (TensorProduct_from_Products C) := by tidy

definition LeftUnitor_for_Products [has_TerminalObject C] : LeftUnitor terminal_object (TensorProduct_from_Products C) := by tidy

definition RightUnitor_for_Products [has_TerminalObject C] : RightUnitor terminal_object (TensorProduct_from_Products C) := by tidy

instance MonoidalStructure_from_Products (C : Type u) [category.{u v} C] [has_TerminalObject C] [has_BinaryProducts.{u v} C] : monoidal_category.{u v} C :=
{ tensor := TensorProduct_from_Products C,
  tensor_unit := terminal_object,
  associator_transformation   := Associator_for_Products C,
  left_unitor_transformation  := LeftUnitor_for_Products C,
  right_unitor_transformation := RightUnitor_for_Products C,
  pentagon := by obviously,
  triangle := by obviously }

open categories.braided_monoidal_category

definition Symmetry_on_MonoidalStructure_from_Products (C : Type u) [category.{u v} C] [has_TerminalObject C] [has_BinaryProducts.{u v} C] : Symmetry (MonoidalStructure_from_Products C) := by tidy
open categories.types

private definition symmetry_on_types := (Symmetry_on_MonoidalStructure_from_Products CategoryOfTypes).braiding.morphism.components 

private example : symmetry_on_types (ℕ, bool) (3, ff) == (ff, 3) := by obviously

end categories.monoidal_category