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
import TauCeti.Analysis.Complex.Circle.Basic

/-!
# Checks for continuous sections of coefficient surjections

`AddMonoidHom.exists_continuous_section_of_surjective` gives a continuous surjective additive
homomorphism `f : A → B` from a profinite additive group onto a Hausdorff one a continuous section
`s` with `s 0 = 0`. The examples below show what the theorem does and does not give:

* the section need not be additive: the reduction `ℤ/4 → ℤ/2` has continuous normalised sections
  (`exists_continuous_section_zmod_four_two`) but no additive one
  (`not_exists_addMonoidHom_section_zmod_four_two`, read off from
  `TauCeti.isEmpty_splitting_zmodFourExtension`);
* profiniteness is needed: the squaring map of the circle group is a continuous surjective
  homomorphism of compact groups without a continuous section
  (`not_exists_continuous_section_circle_sq`), since a continuous square root on the circle does
  not exist;
* the identity of an additive group has the identity as its unique section.
-/

public section

open Multiplicative Real

namespace TauCeti

/-- The reduction `ℤ/4 → ℤ/2` as an additive homomorphism: the projection of
`TauCeti.zmodFourExtension`, written additively. -/
abbrev zmodFourToTwo : ZMod 4 →+ ZMod 2 :=
  AddMonoidHom.toMultiplicative.symm zmodFourExtension.rightHom

/-- The reduction `ℤ/4 → ℤ/2` has a continuous section sending `0` to `0`. -/
theorem exists_continuous_section_zmod_four_two :
    ∃ s : ZMod 2 → ZMod 4, Continuous s ∧ (∀ b, zmodFourToTwo (s b) = b) ∧ s 0 = 0 :=
  zmodFourToTwo.exists_continuous_section_of_surjective continuous_of_discreteTopology
    (toAdd.surjective.comp (zmodFourExtension.rightHom_surjective.comp ofAdd.surjective))

/-- The reduction `ℤ/4 → ℤ/2` has no additive section: the space of additive sections is empty. -/
theorem not_exists_addMonoidHom_section_zmod_four_two :
    ¬∃ s : ZMod 2 →+ ZMod 4, ∀ b, zmodFourToTwo (s b) = b := by
  rintro ⟨s, hs⟩
  exact isEmpty_splitting_zmodFourExtension.elim
    { toMonoidHom := AddMonoidHom.toMultiplicative s
      rightInverse_rightHom := fun b ↦ congrArg ofAdd (hs (toAdd b)) }

/-- **Profiniteness is needed.** The squaring map `z ↦ z²` of the circle group is a continuous
surjective homomorphism of compact groups, but it has no continuous section: there is no
continuous square root on the circle. -/
theorem not_exists_continuous_section_circle_sq :
    ¬∃ s : Circle → Circle, Continuous s ∧ ∀ z, s z ^ 2 = z := by
  rintro ⟨s, hs, hsq⟩
  -- Along `t ↦ s (exp (2πt)) / exp (πt)`, whose square is `1`, the real part takes only the
  -- values `±1`, yet changes sign between `t = 0` and `t = 1`.
  let u : ℝ → Circle := fun t ↦ s (Circle.exp (2 * π * t)) * (Circle.exp (π * t))⁻¹
  have hu : Continuous u := by fun_prop
  have hu2 : ∀ t, u t ^ 2 = 1 := fun t ↦ by
    have hexp : Circle.exp (π * t) ^ 2 = Circle.exp (2 * π * t) := by
      rw [sq, ← Circle.exp_add]
      ring_nf
    simp [u, mul_pow, hsq, hexp]
  have hre : ∀ t, ((u t : ℂ)).re ≠ 0 := fun t ↦ by
    rcases (Circle.sq_eq_one_iff (u t)).mp (hu2 t) with h1 | h1 <;> simp [h1]
  let h : ℝ → ℝ := fun t ↦ ((u t : ℂ)).re
  have hh : Continuous h := by fun_prop
  have h0 : h 0 = ((s 1 : ℂ)).re := by simp [h, u]
  have h1 : h 1 = -((s 1 : ℂ)).re := by simp [h, u, Circle.coe_inv]
  have hmem : (0 : ℝ) ∈ Set.uIcc (h 0) (h 1) := by
    rw [h0, h1, Set.mem_uIcc]
    rcases le_total 0 ((s 1 : ℂ)).re with hc | hc
    · exact Or.inr ⟨by linarith, hc⟩
    · exact Or.inl ⟨hc, by linarith⟩
  obtain ⟨t, -, ht⟩ := intermediate_value_uIcc hh.continuousOn hmem
  exact hre t ht

/-- The identity of an additive group has the identity as its unique section. -/
example {A : Type*} [AddGroup A] (s : A → A) (hs : ∀ a, AddMonoidHom.id A (s a) = a) : s = id :=
  funext fun a ↦ by simpa using hs a

end TauCeti
