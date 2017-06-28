-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

open categories
open categories.functor
open categories.products
open categories.natural_transformation

namespace categories.monoidal_category

universe variables u v

local attribute [ematch] MonoidalStructure.interchange_right_identity

definition MonoidalStructure.tensor_on_left { C: Category.{u v} } ( m : MonoidalStructure C ) ( Z: C.Obj ) : Functor.{u v u v} C C :=
{
  onObjects := λ X, m.tensorObjects Z X,
  onMorphisms := λ X Y f, m.tensorMorphisms (C.identity Z) f,
  identities := ♮, -- This uses lemma TensorProduct_identities
  functoriality := ♯ -- This uses lemma MonoidalStructure.interchange_right_identity
}

local attribute [ematch] MonoidalStructure.interchange_left_identity

definition MonoidalStructure.tensor_on_right { C: Category.{u v} } ( m : MonoidalStructure C ) ( Z: C.Obj ) : Functor.{u v u v} C C :=
{
  onObjects := λ X, m.tensorObjects X Z,
  onMorphisms := λ X Y f, m.tensorMorphisms f (C.identity Z),
  identities := ♮, -- This uses lemma TensorProduct_identities
  functoriality := ♯ -- This uses lemma MonoidalStructure.interchange_left_identity
}

end categories.monoidal_category