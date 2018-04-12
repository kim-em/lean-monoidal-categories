-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .tensor_product

open categories
open categories.functor
open categories.products
open categories.natural_transformation

namespace categories.monoidal_category

universe u

class MonoidalStructure (C : Type (u+1)) [category C] :=
  (tensor                      : TensorProduct C)
  (tensor_unit                 : C)
  (associator_transformation   : Associator tensor)
  (left_unitor_transformation  : LeftUnitor tensor_unit tensor)
  (right_unitor_transformation : RightUnitor tensor_unit tensor)

  (pentagon                  : Pentagon associator_transformation . obviously)
  (triangle                  : Triangle tensor_unit left_unitor_transformation right_unitor_transformation associator_transformation . obviously)

variables {C : Type (u+1)} [category C]

make_lemma MonoidalStructure.pentagon
make_lemma MonoidalStructure.triangle
attribute [ematch] MonoidalStructure.pentagon_lemma
attribute [simp,ematch] MonoidalStructure.triangle_lemma

namespace MonoidalStructure

-- Convenience methods which take two arguments, rather than a pair. (This seems to often help the elaborator avoid getting stuck on `prod.mk`.)
@[reducible] definition tensorObjects [ m : MonoidalStructure C ] ( X Y : C ) : C := tensor C ⟨X, Y⟩
@[reducible] definition tensorMorphisms [ m : MonoidalStructure C ] { W X Y Z : C } ( f : W ⟶ X ) ( g : Y ⟶ Z ) : (tensor C ⟨W, Y⟩) ⟶ (tensor C ⟨X, Z⟩) := m.tensor.onMorphisms ⟨f, g⟩

infixr ` ⊗ `:80 := tensorObjects -- type as \gg
infixr ` ⊗ `:80 := tensorMorphisms -- type as \gg

@[reducible] definition left_unitor
  [ m : MonoidalStructure C ]
  ( X : C ) : (m.tensor_unit ⊗ X) ⟶ X := ((left_unitor_transformation C).components X).morphism
  
@[reducible] definition right_unitor
  [ m : MonoidalStructure C ]
  ( X : C ) : (X ⊗ m.tensor_unit) ⟶ X := ((right_unitor_transformation C).components X).morphism

@[reducible] definition MonoidalStructure.inverse_left_unitor
  [ m : MonoidalStructure C ]
  ( X : C ) : X ⟶ (m.tensor_unit ⊗ X) := m.left_unitor_transformation.inverse.components X
  
@[reducible] definition MonoidalStructure.inverse_right_unitor
  [ m : MonoidalStructure C ]
  ( X : C) : X ⟶ (X ⊗ m.tensor_unit) := m.right_unitor_transformation.inverse.components X

@[reducible] definition MonoidalStructure.associator
  [ m : MonoidalStructure C ]
  ( X Y Z : C ) : ((X ⊗ Y) ⊗ Z) ⟶ (X ⊗ (Y ⊗ Z)) :=
  ((associator_transformation C).components ⟨⟨X, Y⟩, Z⟩).morphism

@[reducible] definition MonoidalStructure.inverse_associator
  [ m : MonoidalStructure C ]
  ( X Y Z : C ) : (X ⊗ (Y ⊗ Z)) ⟶ ((X ⊗ Y) ⊗ Z) :=
  m.associator_transformation.inverse.components ⟨⟨X, Y⟩, Z⟩

@[ematch] definition MonoidalStructure.interchange
  [ m : MonoidalStructure C ]
  { U V W X Y Z: C }
  ( f : U ⟶ V )( g : V ⟶ W )( h : X ⟶ Y )( k : Y ⟶ Z ) :
  @Functor.onMorphisms _ _ _ _ m.tensor ⟨U, X⟩ ⟨W, Z⟩ ⟨(f ≫ g), (h ≫ k)⟩
  = (@Functor.onMorphisms _ _ _ _ m.tensor ⟨U, X⟩ ⟨V, Y⟩ ⟨f, h⟩) ≫ 
    (@Functor.onMorphisms _ _ _ _ m.tensor ⟨V, Y⟩ ⟨W, Z⟩ ⟨g, k⟩) :=
  @Functor.functoriality (C × C) _ C _ m.tensor ⟨U, X⟩ ⟨V, Y⟩ ⟨W, Z⟩ ⟨f, h⟩ ⟨g, k⟩

@[simp,ematch] lemma MonoidalStructure.interchange_left_identity
  [ m : MonoidalStructure C ]
  { W X Y Z : C }
  ( f : W ⟶ X ) ( g : X ⟶ Y ) :
  (@Functor.onMorphisms _ _ _ _ m.tensor (W, Z) (X, Z) (f, 𝟙 Z)) ≫ (@Functor.onMorphisms _ _ _ _ m.tensor (X, Z) (Y, Z) (g, 𝟙 Z))
    = @Functor.onMorphisms _ _ _ _ m.tensor ⟨W, Z⟩ ⟨Y, Z⟩ ⟨f ≫ g, 𝟙 Z⟩
    := by obviously

@[simp,ematch] lemma MonoidalStructure.interchange_right_identity
  [ m : MonoidalStructure C ]
  { W X Y Z : C }
  ( f : W ⟶ X ) ( g : X ⟶ Y ) :
  (@Functor.onMorphisms _ _ _ _ m.tensor (Z, W) (Z, X) (𝟙 Z, f)) ≫ (@Functor.onMorphisms _ _ _ _  m.tensor (Z, X) (Z, Y) (𝟙 Z, g)) 
    = @Functor.onMorphisms _ _ _ _ m.tensor ⟨Z, W⟩ ⟨Z, Y⟩ ⟨𝟙 Z, f ≫ g⟩
    := by obviously

@[ematch] lemma MonoidalStructure.interchange_identities
  { C : Category }
  ( m : MonoidalStructure C )
  { W X Y Z : C.Obj }
  ( f : C.Hom W X ) ( g : C.Hom Y Z ) :
  C.compose (m.tensorMorphisms (C.identity Y) f) (m.tensorMorphisms g (C.identity X))
    = C.compose (m.tensorMorphisms g (C.identity W)) (m.tensorMorphisms (C.identity Z) f) :=
    begin
    tidy,
     rewrite ← MonoidalStructure.interchange,
     simp,
     rewrite ← MonoidalStructure.interchange,
     simp
    end

@[simp,ematch] lemma MonoidalStructure.tensor_identities
  { C : Category }
  ( m : MonoidalStructure C )
  ( X Y : C.Obj ) :
   @Functor.onMorphisms _ _ (m.tensor) (X, Y) (X, Y) (C.identity X, C.identity Y) = C.identity (m.tensor.onObjects (X, Y)) := 
   begin
     rewrite ← m.tensor.identities,
     tidy
   end

lemma MonoidalStructure.inverse_associator_naturality_0
  { C : Category }
  ( m : MonoidalStructure C )
  { U V W X Y Z : C.Obj }
  (f : C.Hom U V ) ( g : C.Hom W X ) ( h : C.Hom Y Z ) :
    C.compose
      (@Functor.onMorphisms _ _ m.tensor (U, _) (V, _) (f, (@Functor.onMorphisms _ _ m.tensor (W, _) (X, _) (g, h))))
      (((m.associator_transformation).inverse).components ((V, X), Z))
    = C.compose
      (((m.associator_transformation).inverse).components ((U, W), Y))
      (@Functor.onMorphisms _ _ m.tensor (_, Y) (_, Z) ((@Functor.onMorphisms _ _ m.tensor (U, _) (V, _) (f, g)), h)) :=
  begin
    dsimp,
    apply @NaturalTransformation.naturality _ _ _ _ ((m.associator_transformation).inverse) ((U, W), Y) ((V, X), Z) ((f, g), h)
  end

structure {u v} MonoidalCategory extends C : Category.{u v} :=
  ( m : MonoidalStructure C )

definition {u v} MonoidalCategory_coercion_to_Category : has_coe MonoidalCategory.{u v} Category.{u v} :=
  { coe := MonoidalCategory.C }

attribute [instance] MonoidalCategory_coercion_to_Category

end categories.monoidal_category
