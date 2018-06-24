import .monoidal_category

open categories.monoidal_category

universes u₁ v₁ 

variables {C : Type u₁} [𝒞 : monoidal_category.{u₁ v₁} C]
include 𝒞


inductive monoidal_coherence_step : C → Type u₁ 
| left_unitor : Π X : C, monoidal_coherence_step ((monoidal_category.tensor_unit C) ⊗ X)
| left_tensor : Π (X Y : C) [monoidal_coherence_step Y], monoidal_coherence_step (X ⊗ Y)

def monoidal_coherence_step_result : Π (X : C) [monoidal_coherence_step X], C
| _ (monoidal_coherence_step.left_unitor Y) := Y
| _ (@monoidal_coherence_step.left_tensor _ _ X Y S) := X ⊗ (@monoidal_coherence_step_result Y S)

inductive monoidal_coherence : C → C → Type u₁ 
| identity : Π X : C, monoidal_coherence X X
| compose : Π {X Y : C} [S : monoidal_coherence_step Y], monoidal_coherence X Y → monoidal_coherence X (@monoidal_coherence_step_result _ _ _ S)

attribute [class] monoidal_coherence_step monoidal_coherence
attribute [instance] monoidal_coherence_step.left_unitor monoidal_coherence_step.left_tensor
attribute [instance] monoidal_coherence.identity monoidal_coherence.compose monoidal_coherence.compose

example (X : C) : monoidal_coherence_step ((monoidal_category.tensor_unit C) ⊗ X) := by apply_instance
example (X Y : C) : monoidal_coherence_step (Y ⊗ ((monoidal_category.tensor_unit C) ⊗ X)) := by apply_instance

example (X : C) : monoidal_coherence X X := by apply_instance
example (X : C) : monoidal_coherence ((monoidal_category.tensor_unit C) ⊗ X) X :=
begin

end
example (X : C) : monoidal_coherence ((monoidal_category.tensor_unit C) ⊗ ((monoidal_category.tensor_unit C) ⊗ X)) X := 
begin
  sorry
end

class monoidal_coherence_isomorphism (X Y : C) :=
  (iso : X ≅ Y)

#print monoidal_coherence_isomorphism

instance coherent_identity (X : C) : @monoidal_coherence_isomorphism C 𝒞 X X :=
{ iso := sorry }

instance coherent_identity (X Y Z: C) : @monoidal_coherence_isomorphism C 𝒞 ((X ⊗ Y) ⊗ Z) (X ⊗ (Y ⊗ Z)) :=
{ iso := sorry }