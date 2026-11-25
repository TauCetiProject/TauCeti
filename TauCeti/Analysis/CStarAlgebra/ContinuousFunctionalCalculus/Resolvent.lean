/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import TauCeti.Algebra.Algebra.Spectrum

/-!
# The resolvent in the continuous functional calculus

For an element `a` satisfying the predicate of a continuous functional calculus and a point `z` of
its resolvent set, the function `w ↦ (z - w)⁻¹` is continuous on the spectrum of `a`, and its
functional calculus is the resolvent `(z - a)⁻¹`. Likewise, for a self-adjoint `a` and a real `k`
with `1 + k a` invertible, `a (1 + k a)⁻¹` is the image of `a` under the fractional linear function
`x ↦ x / (1 + k x)`.

## Main results

* `TauCeti.continuousOn_inv_sub_of_mem_resolventSet`: `w ↦ (z - w)⁻¹` is continuous on the
  spectrum of `a` for `z` in the resolvent set of `a`.
* `TauCeti.cfc_inv_sub_eq_resolvent`: `cfc (fun w ↦ (z - w)⁻¹) a = resolvent a z` for `z` in the
  resolvent set of `a`.
* `IsSelfAdjoint.cfc_div_one_add_mul`: `cfc (fun x ↦ x / (1 + k x)) a = a (1 + k a)⁻¹` when
  `1 + k a` is invertible.
-/

public section

namespace TauCeti

/-- For `z` in the resolvent set of `a`, the function `w ↦ (z - w)⁻¹` is continuous on the
spectrum of `a`, since `z - w` does not vanish there. -/
theorem continuousOn_inv_sub_of_mem_resolventSet {R A : Type*} [Field R] [TopologicalSpace R]
    [IsTopologicalRing R] [ContinuousInv₀ R] [Ring A] [Algebra R A] {a : A} {z : R}
    (hz : z ∈ resolventSet R a) : ContinuousOn (fun w ↦ (z - w)⁻¹) (spectrum R a) :=
  (continuousOn_const.sub continuousOn_id).inv₀ fun w hw h0 =>
    hw ((sub_eq_zero.mp h0 : z = w) ▸ hz)

variable {R A : Type*} {p : A → Prop} [Field R] [StarRing R] [MetricSpace R]
  [IsTopologicalRing R] [ContinuousStar R] [ContinuousInv₀ R] [TopologicalSpace A] [Ring A]
  [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- **The resolvent through the functional calculus.** For `z` in the resolvent set of
`a`, the functional calculus of `w ↦ (z - w)⁻¹` at `a` is the resolvent `(z - a)⁻¹`. -/
theorem cfc_inv_sub_eq_resolvent {a : A} {z : R} (hz : z ∈ resolventSet R a)
    (ha : p a := by cfc_tac) : cfc (fun w ↦ (z - w)⁻¹) a = resolvent a z := by
  have hne : ∀ w ∈ spectrum R a, z - w ≠ 0 := fun w hw h0 =>
    hw ((sub_eq_zero.mp h0 : z = w) ▸ hz)
  rw [cfc_inv (fun w ↦ z - w) a hne, cfc_sub (fun _ ↦ z) (fun w ↦ w) a, cfc_const z a,
    cfc_id' R a, resolvent]

end TauCeti

namespace IsSelfAdjoint

variable {A : Type*} [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {a : A}

/-- For a self-adjoint `a` with `1 + k a` invertible, `a (1 + k a)⁻¹` is the image of `a` under the
fractional linear function `x ↦ x / (1 + k x)`. -/
theorem cfc_div_one_add_mul (ha : IsSelfAdjoint a) {k : ℝ} (hk : IsUnit (1 + k • a)) :
    cfc (fun x : ℝ ↦ x / (1 + k * x)) a = a * Ring.inverse (1 + k • a) := by
  have hne := spectrum.isUnit_one_add_smul_iff.1 hk
  simp_rw [div_eq_mul_inv]
  rw [cfc_mul (fun x : ℝ ↦ x) (fun x ↦ (1 + k * x)⁻¹) a,
    cfc_inv (fun x : ℝ ↦ 1 + k * x) a hne]
  simp [cfc_id' ℝ a, cfc_const_add 1 (fun x : ℝ ↦ k * x) a, cfc_const_mul_id k a]

end IsSelfAdjoint
