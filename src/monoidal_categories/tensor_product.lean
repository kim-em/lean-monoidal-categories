-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import categories.products.associator
import categories.natural_isomorphism

open categories
open categories.functor
open categories.products
open categories.natural_transformation

namespace categories.monoidal_category

universe variables u v

-- TODO can we avoid these @[reducible]s?
@[reducible] definition TensorProduct (C : Type (u+1)) [category C] := Functor ( C × C ) C

variables {C : Type (u+1)} [category C]

definition left_associated_triple_tensor ( tensor : TensorProduct C ) : Functor ((C × C) × C) C :=
  FunctorComposition (tensor × IdentityFunctor C) tensor
definition right_associated_triple_tensor ( tensor : TensorProduct C ) : Functor (C × (C × C)) C :=
  FunctorComposition (IdentityFunctor C × tensor) tensor

@[reducible] definition Associator ( tensor : TensorProduct C ) :=
  NaturalIsomorphism
    (left_associated_triple_tensor tensor)
    (FunctorComposition (ProductCategoryAssociator C C C) (right_associated_triple_tensor tensor))

@[reducible] definition RightUnitor ( I : C ) ( tensor : TensorProduct C ) :=
  NaturalIsomorphism
    (FunctorComposition (RightInjectionAt I) tensor)
    (IdentityFunctor C)

@[reducible] definition LeftUnitor ( I : C ) ( tensor : TensorProduct C ) :=
  NaturalIsomorphism
    (FunctorComposition (LeftInjectionAt I) tensor)
    (IdentityFunctor C)

-- TODO all the let statements cause problems later...
@[reducible] definition Pentagon { tensor : TensorProduct C } ( associator : Associator tensor ) :=
  let α ( X Y Z : C ) := associator.morphism.components ⟨⟨X, Y⟩, Z⟩,
      tensorObjects ( X Y : C ) := tensor.onObjects ⟨X, Y⟩,
      tensorMorphisms { W X Y Z : C } ( f : W ⟶ X ) ( g : Y ⟶ Z ) : (tensorObjects W Y) ⟶ (tensorObjects X Z) := tensor.onMorphisms ⟨f, g⟩ in
  ∀ W X Y Z : C,
    (tensorMorphisms (α W X Y) (𝟙 Z)) ≫ (α W (tensorObjects X Y) Z) ≫ (tensorMorphisms (𝟙 W) (α X Y Z))
  = (α (tensorObjects W X) Y Z) ≫ (α W X (tensorObjects Y Z)) 

@[reducible] definition Triangle { tensor : TensorProduct C } ( I : C ) ( left_unitor : LeftUnitor I tensor ) ( right_unitor : RightUnitor I tensor ) ( associator : Associator tensor ) :=
  let α ( X Y Z : C ) := associator.morphism.components ⟨⟨X, Y⟩, Z⟩,
      tensorObjects ( X Y : C ) := tensor.onObjects ⟨X, Y⟩,
      tensorMorphisms { W X Y Z : C } ( f : W ⟶ X ) ( g : Y ⟶ Z ) : (tensorObjects W Y) ⟶ (tensorObjects X Z) := tensor.onMorphisms ⟨f, g⟩ in
  ∀ X Y : C,
    (α X I Y) ≫ (tensorMorphisms (𝟙 X) (left_unitor.morphism.components Y))
  = tensorMorphisms (right_unitor.morphism.components X) (𝟙 Y)

end categories.monoidal_category
