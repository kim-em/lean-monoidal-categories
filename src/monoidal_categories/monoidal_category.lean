-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .tensor_product

open categories
open categories.functor
open categories.products
open categories.natural_transformation

namespace categories.monoidal_category

structure {u v} MonoidalStructure ( C : Category.{u v} ) :=
  (tensor                      : TensorProduct C)
  (tensor_unit                 : C.Obj)
  (associator_transformation   : Associator tensor)
  (left_unitor_transformation  : LeftUnitor tensor_unit tensor)
  (right_unitor_transformation : RightUnitor tensor_unit tensor)

  (pentagon                  : Pentagon associator_transformation . obviously)
  (triangle                  : Triangle tensor_unit left_unitor_transformation right_unitor_transformation associator_transformation . obviously)

make_lemma MonoidalStructure.pentagon
make_lemma MonoidalStructure.triangle
attribute [ematch] MonoidalStructure.pentagon_lemma
attribute [simp,ematch] MonoidalStructure.triangle_lemma

instance MonoidalStructure_coercion_to_TensorProduct { C : Category } : has_coe (MonoidalStructure C) (TensorProduct C) :=
  { coe := MonoidalStructure.tensor }

-- Convenience methods which take two arguments, rather than a pair. (This seems to often help the elaborator avoid getting stuck on `prod.mk`.)
@[reducible] definition MonoidalStructure.tensorObjects { C : Category } ( m : MonoidalStructure C ) ( X Y : C.Obj ) : C.Obj := m ⟨X, Y⟩
@[reducible] definition MonoidalStructure.tensorMorphisms { C : Category } ( m : MonoidalStructure C ) { W X Y Z : C.Obj } ( f : C.Hom W X ) ( g : C.Hom Y Z ) : C.Hom (m ⟨W, Y⟩) (m ⟨X, Z⟩) := m.tensor.onMorphisms ⟨f, g⟩

@[reducible] definition MonoidalStructure.left_unitor
  { C : Category }
  ( m : MonoidalStructure C )
  ( X : C.Obj ) : C.Hom (m.tensorObjects m.tensor_unit X) X := m.left_unitor_transformation X
  
@[reducible] definition MonoidalStructure.right_unitor
  { C : Category }
  ( m : MonoidalStructure C )
  ( X : C.Obj ) : C.Hom (m.tensorObjects X m.tensor_unit) X := m.right_unitor_transformation X

@[reducible] definition MonoidalStructure.inverse_left_unitor
  { C : Category }
  ( m : MonoidalStructure C )
  ( X : C.Obj ) : C.Hom X (m.tensorObjects m.tensor_unit X) := m.left_unitor_transformation.inverse.components X
  
@[reducible] definition MonoidalStructure.inverse_right_unitor
  { C : Category }
  ( m : MonoidalStructure C )
  ( X : C.Obj ) : C.Hom X (m.tensorObjects X m.tensor_unit) := m.right_unitor_transformation.inverse.components X

@[reducible] definition MonoidalStructure.associator
  { C : Category }
  ( m : MonoidalStructure C )
  ( X Y Z : C.Obj ) : C.Hom (m.tensorObjects (m.tensorObjects X Y) Z) (m.tensorObjects X (m.tensorObjects Y Z)) :=
  m.associator_transformation ⟨⟨X, Y⟩, Z⟩

@[reducible] definition MonoidalStructure.inverse_associator
  { C : Category }
  ( m : MonoidalStructure C )
  ( X Y Z : C.Obj ) : C.Hom (m.tensorObjects X (m.tensorObjects Y Z)) (m.tensorObjects (m.tensorObjects X Y) Z) :=
  m.associator_transformation.inverse.components ⟨⟨X, Y⟩, Z⟩

@[ematch] definition MonoidalStructure.interchange
  { C : Category }
  ( m : MonoidalStructure C )
  { U V W X Y Z: C.Obj }
  ( f : C.Hom U V )( g : C.Hom V W )( h : C.Hom X Y )( k : C.Hom Y Z ) :
  @Functor.onMorphisms _ _ m.tensor ⟨U, X⟩ ⟨W, Z⟩ ⟨(C.compose f g), (C.compose h k)⟩
  = C.compose
      (@Functor.onMorphisms _ _ m.tensor ⟨U, X⟩ ⟨V, Y⟩ ⟨f, h⟩)
      (@Functor.onMorphisms _ _ m.tensor ⟨V, Y⟩ ⟨W, Z⟩ ⟨g, k⟩) :=
  @Functor.functoriality (C × C) C m.tensor ⟨U, X⟩ ⟨V, Y⟩ ⟨W, Z⟩ ⟨f, h⟩ ⟨g, k⟩

@[simp,ematch] lemma MonoidalStructure.interchange_left_identity
  { C : Category }
  ( m : MonoidalStructure C )
  { W X Y Z : C.Obj }
  ( f : C.Hom W X ) ( g : C.Hom X Y ) :
  C.compose (@Functor.onMorphisms _ _ m.tensor (W, Z) (X, Z) (f, C.identity Z)) (@Functor.onMorphisms _ _ m.tensor (X, Z) (Y, Z) (g, C.identity Z))
    = @Functor.onMorphisms _ _ m.tensor ⟨W, Z⟩ ⟨Y, Z⟩ ⟨C.compose f g, C.identity Z⟩
    := ♯

@[simp,ematch] lemma MonoidalStructure.interchange_right_identity
  { C : Category }
  ( m : MonoidalStructure C )
  { W X Y Z : C.Obj }
  ( f : C.Hom W X ) ( g : C.Hom X Y ) :
  C.compose (@Functor.onMorphisms _ _ m.tensor (Z, W) (Z, X) (C.identity Z, f)) (@Functor.onMorphisms _ _ m.tensor (Z, X) (Z, Y) (C.identity Z, g)) 
    = @Functor.onMorphisms _ _ m.tensor ⟨Z, W⟩ ⟨Z, Y⟩ ⟨C.identity Z, C.compose f g⟩
    := ♯

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
