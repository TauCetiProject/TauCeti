/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Instances.ZMod
public import TauCeti.GroupTheory.GroupExtension.ZModFour
public import TauCeti.Topology.Algebra.Group.Profinite.Section
import TauCeti.Topology.Circle.Degree

/-!
# Checks for continuous sections of coefficient surjections

`AddMonoidHom.exists_continuous_section_of_surjective` gives a continuous surjective additive
homomorphism `f : A → B` from a profinite additive group onto a Hausdorff one a continuous section
`s` with `s 0 = 0`. The examples below show what the theorem does and does not give:

* the section need not be additive: the reduction `ZMod.castHom : ℤ/4 → ℤ/2` has continuous
  normalised sections (`exists_continuous_section_castHom_four_two`) but no additive one
  (`not_exists_addMonoidHom_section_castHom_four_two`, read off from
  `TauCeti.isEmpty_splitting_zmodFourExtension`);
* profiniteness is needed: the squaring map of the circle group is a continuous surjective
  homomorphism of compact groups without a continuous section
  (`not_exists_continuous_section_circle_sq`), since a continuous square root on the circle does
  not exist;
* the identity of an additive group has the identity as its unique section.
-/

public section

open Multiplicative

namespace TauCeti

/-- The reduction `ℤ/4 → ℤ/2` has a continuous section sending `0` to `0`. -/
theorem exists_continuous_section_castHom_four_two :
    ∃ s : ZMod 2 → ZMod 4, Continuous s ∧
      (∀ b, ZMod.castHom (by decide : (2 : ℕ) ∣ 4) (ZMod 2) (s b) = b) ∧ s 0 = 0 :=
  (ZMod.castHom (by decide : (2 : ℕ) ∣ 4) (ZMod 2)).toAddMonoidHom
    |>.exists_continuous_section_of_surjective continuous_of_discreteTopology
      (ZMod.castHom_surjective (by decide : (2 : ℕ) ∣ 4))

/-- The reduction `ℤ/4 → ℤ/2` has no additive section: the space of additive sections is empty. -/
theorem not_exists_addMonoidHom_section_castHom_four_two :
    ¬∃ s : ZMod 2 →+ ZMod 4, ∀ b, ZMod.castHom (by decide : (2 : ℕ) ∣ 4) (ZMod 2) (s b) = b := by
  rintro ⟨s, hs⟩
  exact isEmpty_splitting_zmodFourExtension.elim
    { toMonoidHom := AddMonoidHom.toMultiplicative s
      rightInverse_rightHom := fun b ↦ toAdd.injective <| by simpa using hs (toAdd b) }

/-- **Profiniteness is needed.** The squaring map `z ↦ z²` of the circle group is a continuous
surjective homomorphism of compact groups, but it has no continuous section: there is no
continuous square root on the circle. -/
theorem not_exists_continuous_section_circle_sq :
    ¬∃ s : Circle → Circle, Continuous s ∧ ∀ z, s z ^ 2 = z := by
  rintro ⟨s, hs, hsq⟩
  -- The loop `s ∘ expLoop` squares to `expLoop`, of degree `1`, so its degree would be `1/2`.
  have h := Circle.degree_congr ((Circle.expLoop.map hs).map (continuous_pow 2)) Circle.expLoop
    fun t ↦ by simp [hsq]
  rw [Circle.degree_map_pow, Circle.degree_expLoop] at h
  omega

/-- The identity of an additive group has the identity as its unique section. -/
example {A : Type*} [AddGroup A] (s : A → A) (hs : ∀ a, AddMonoidHom.id A (s a) = a) : s = id :=
  funext fun a ↦ by simpa using hs a

end TauCeti
