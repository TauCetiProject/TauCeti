/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UnitDisc.Basic

/-!
# Basic API for the complex unit disc

This file collects small API lemmas for Mathlib's `Complex.UnitDisc`.

* The `Circle` action on the disc: it fixes the origin and preserves nonzero points
  (`Complex.UnitDisc.circle_smul_zero`, `Complex.UnitDisc.circle_smul_eq_zero`), it is jointly
  continuous, a rotation is determined by its value at any one nonzero point
  (`Complex.UnitDisc.circle_smul_left_injective`), and hence the circle acts faithfully on the
  disc, which is nontrivial.
* Compactness of the disc points of Euclidean norm at most `ρ < 1`
  (`Complex.UnitDisc.isCompact_setOf_norm_le`).
* Transport between a self-map of the bundled disc and a scalar representative `ℂ → ℂ` of it:
  such a representative maps `Metric.ball 0 1` into itself
  (`TauCeti.mapsTo_ball_of_forall_unitDisc_coe_eq`), and bijectively onto itself when the bundled
  map is an equivalence (`TauCeti.bijOn_ball_of_unitDiscEquiv`).
* The slit-plane criterion `TauCeti.one_sub_div_mem_slitPlane` for a disc point and a circle
  point.
-/

public section

open Metric Set
open scoped Complex.UnitDisc

namespace Complex.UnitDisc

/-- Rotating the disc origin by a circle element fixes it. This is the `smul_zero`
normalization for Mathlib's `Circle` action on `Complex.UnitDisc`, which is a bare
`MulAction` and so does not get the generic `smul_zero` simp lemma. -/
@[simp]
lemma circle_smul_zero (u : Circle) : u • (0 : 𝔻) = 0 := by
  ext
  simp

/-- A circle rotation of a disc point vanishes exactly when the point does. This is the
`smul_eq_zero` normalization for Mathlib's `Circle` action on `Complex.UnitDisc`. -/
@[simp]
lemma circle_smul_eq_zero (u : Circle) {z : 𝔻} : u • z = 0 ↔ z = 0 := by
  simp [← coe_eq_zero]

/-- The set of unit-disc points of Euclidean norm at most `ρ < 1` is compact: it is the preimage
of the closed Euclidean ball of radius `ρ`, which the hypothesis `ρ < 1` places inside the open
disc. -/
lemma isCompact_setOf_norm_le {ρ : ℝ} (hρ : ρ < 1) : IsCompact {z : 𝔻 | ‖(z : ℂ)‖ ≤ ρ} := by
  convert isEmbedding_coe.isInducing.isCompact_preimage' (isCompact_closedBall (0 : ℂ) ρ) _
  · simp
  · exact fun w hw => ⟨mk w ((mem_closedBall_zero_iff.1 hw).trans_lt hρ), rfl⟩

/-- Circle rotations act jointly continuously on the bundled open unit disc. -/
instance instContinuousSMulCircle : ContinuousSMul Circle 𝔻 :=
  inferInstanceAs <| ContinuousSMul (sphere (0 : ℂ) 1) (ball (0 : ℂ) 1)

/-- The open unit disc has more than one point: `0` and `1 / 2` are both in it. -/
instance instNontrivial : Nontrivial 𝔻 :=
  ⟨⟨mk 2⁻¹ (by norm_num), 0, by simp⟩⟩

/-- **A rotation is determined by its value at a single nonzero point of the disc.** Multiplication
by a nonzero complex number is injective, and the disc inherits that from `ℂ`. -/
theorem circle_smul_left_injective {z : 𝔻} (hz : z ≠ 0) :
    Function.Injective fun u : Circle => u • z := fun u v h => by
  simpa [← coe_inj, ← Circle.coe_inj, hz] using h

/-- **The circle acts faithfully on the unit disc.** Only the trivial rotation fixes the whole
disc, because the disc contains a nonzero point. -/
instance instFaithfulSMulCircle : FaithfulSMul Circle 𝔻 where
  eq_of_smul_eq_smul h := by
    obtain ⟨z, hz⟩ := exists_ne (0 : 𝔻)
    exact circle_smul_left_injective hz (h z)

end Complex.UnitDisc

namespace TauCeti

open Complex

/-- For `w` on the unit circle and `ζ` in the open unit disc, `1 - ζ / w` lies in the slit plane,
since `ζ / w` has norm less than one. -/
theorem one_sub_div_mem_slitPlane (w : Circle) {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    1 - ζ / w ∈ slitPlane := by
  rw [sub_eq_add_neg]
  apply mem_slitPlane_of_norm_lt_one
  simpa using hζ

/-- A scalar representative of a self-map of the disc maps the open unit ball into itself. -/
lemma mapsTo_ball_of_forall_unitDisc_coe_eq {e : 𝔻 → 𝔻} {f : ℂ → ℂ}
    (hf : ∀ z : 𝔻, (e z : ℂ) = f z) : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := fun w hw => by
  lift w to 𝔻 using mem_ball_zero_iff.1 hw
  simpa [← hf] using (e w).norm_lt_one

/-- A self-equivalence of `Complex.UnitDisc`, read through a scalar representative, is a bijection
of `Metric.ball 0 1` onto itself. -/
lemma bijOn_ball_of_unitDiscEquiv (E : 𝔻 ≃ 𝔻) {φ : ℂ → ℂ} (hφ : ∀ z : 𝔻, (E z : ℂ) = φ z) :
    BijOn φ (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  refine ⟨mapsTo_ball_of_forall_unitDisc_coe_eq hφ, fun w₁ h₁ w₂ h₂ h => ?_, fun v hv => ?_⟩
  · lift w₁ to 𝔻 using mem_ball_zero_iff.1 h₁
    lift w₂ to 𝔻 using mem_ball_zero_iff.1 h₂
    simpa [← hφ] using h
  · lift v to 𝔻 using mem_ball_zero_iff.1 hv
    exact ⟨E.symm v, by simpa using (E.symm v).norm_lt_one, by simp [← hφ]⟩

end TauCeti
