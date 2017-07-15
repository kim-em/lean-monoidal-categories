-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..monoidal_category

namespace categories.enriched

open categories
open categories.monoidal_category

structure {u v w} EnrichedCategory { V: Category.{v w} } ( m : MonoidalStructure V ) :=
  (Obj : Type u)
  (Hom : Obj → Obj → V.Obj)
  (compose :  Π ( X Y Z : Obj ), V.Hom (m.tensorObjects (Hom X Y) (Hom Y Z)) (Hom X Z))
  (identity : Π X : Obj, V.Hom m.tensor_unit (Hom X X))
  (left_identity  : ∀ { X Y : Obj }, 
    V.compose 
      (m.inverse_left_unitor (Hom X Y))
    (V.compose 
      (m.tensorMorphisms (identity X) (V.identity (Hom X Y))) 
      (compose _ _ _)
    ) = V.identity (Hom X Y) )
  (right_identity  : ∀ { X Y : Obj }, 
    V.compose 
      (m.inverse_right_unitor (Hom X Y)) 
    (V.compose 
      (m.tensorMorphisms (V.identity (Hom X Y)) (identity Y)) 
      (compose _ _ _)
    ) = V.identity (Hom X Y) )
  (associativity : ∀ { W X Y Z : Obj },
    V.compose 
      (m.tensorMorphisms (compose _ _ _) (V.identity (Hom Y Z))) 
      (compose _ _ _)
   = V.compose 
      (m.associator (Hom W X) (Hom X Y) (Hom Y Z)) 
    (V.compose 
      (m.tensorMorphisms (V.identity (Hom W X)) (compose _ _ _))
      (compose _ _ _)) )

attribute [simp,ematch] EnrichedCategory.left_identity
attribute [simp,ematch] EnrichedCategory.right_identity
attribute [ematch] EnrichedCategory.associativity

-- instance EnrichedCategory_to_Hom { V : Category } { m : MonoidalStructure V } : has_coe_to_fun (EnrichedCategory m) :=
-- { F   := λ C, C.Obj → C.Obj → V.Obj,
--   coe := EnrichedCategory.Hom }

-- definition {u v w} UnderlyingCategory { V: Category.{v w} } { m : MonoidalStructure V } ( C : EnrichedCategory m ) : Category := {
--   Obj := C.Obj,
--   Hom := λ X Y, V.Hom m.tensor_unit (C.Hom X Y),
--   identity       := C.identity,
--   compose        := λ X Y Z f g, begin
--                                    have p := m.tensorMorphisms f g, 
--                                    tidy, 
--                                    have p' := V.compose p (C.compose X Y Z), 
--                                    have p'' := m.inverse_left_unitor m.tensor_unit,
--                                    tidy,
--                                    exact V.compose p'' p'
--                                  end,
--   left_identity  := begin
--                       tidy, 
--                       have p := C.left_identity, 
--                       have p' := @p X Y, 
--                       have p'' := congr_arg (λ x, V.compose f x) p',
--                       dsimp at *,
--                       admit,
--                     end,
--   right_identity := sorry,
--   associativity  := begin
--                       tidy,
--                       -- PROJECT
--                       -- These are great examples of things that are trivial in string diagrams, but horrific here.
--                       admit,
--                     end,
-- }

structure Functor { V : Category } { m : MonoidalStructure V } ( C D : EnrichedCategory m ) :=
  ( onObjects : C.Obj → D.Obj )
  ( onMorphisms : ∀ { X Y : C.Obj }, V.Hom (C.Hom X Y) (D.Hom (onObjects X) (onObjects Y)) )
  ( identities : ∀ X : C.Obj, V.compose (C.identity X) onMorphisms = D.identity (onObjects X) )
  -- TODO fix this
  -- ( functoriality : ∀ { X Y Z : C.Obj }, V.compose C.compose (@onMorphisms X Z) = V.compose (m.tensorMorphisms (@onMorphisms X Y) (@onMorphisms Y Z)) D.compose )

attribute [simp,ematch] Functor.identities
-- attribute [simp,ematch] Functor.functoriality

  -- PROJECT natural transformations don't always exist; you need various limits!
  
end categories.enriched