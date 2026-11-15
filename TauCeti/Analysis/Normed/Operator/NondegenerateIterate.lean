/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.GDelta.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic

/-!
# Generic nondegeneracy of the iterates of a perturbed linear map

Let `L` be an endomorphism of a finite-dimensional normed space `E`, for instance the linearized
return map of a periodic orbit. Composing a map with a perturbation `ψ` fixing a point `p` of the
orbit changes the linearized return map from `L` to `L * A`, where `A` is the derivative of `ψ` at
`p` (`HasFDerivAt.iterate_comp_of_eventuallyEq_id`). The `m`-fold cover of the orbit is
nondegenerate when `(L * A) ^ m` does not have `1` as an eigenvalue, that is, when
`det (1 - (L * A) ^ m) ≠ 0`.

This file shows that these conditions hold for a generic `A`:

* for each `m ≥ 1` the operators `A` with `det (1 - (L * A) ^ m) ≠ 0` form an open dense set
  (`ContinuousLinearMap.isOpen_setOf_det_one_sub_pow_mul_ne_zero`,
  `ContinuousLinearMap.dense_setOf_det_one_sub_pow_mul_ne_zero`);
* for a set `s` of positive integers, for instance all of them, the operators satisfying all of
  these conditions for `m ∈ s` form a dense `Gδ` set, which is open when `s` is finite
  (`ContinuousLinearMap.dense_setOf_forall_det_one_sub_pow_mul_ne_zero`,
  `ContinuousLinearMap.isGδ_setOf_forall_det_one_sub_pow_mul_ne_zero`,
  `ContinuousLinearMap.isOpen_setOf_forall_det_one_sub_pow_mul_ne_zero`).

In particular there are operators `A` arbitrarily close to the identity for which all the covers
of the orbit up to any given multiplicity are nondegenerate. This includes the resonant case: if
`L` has the eigenvalue `-1`, the orbit itself may be nondegenerate while its double cover is not,
and a perturbation chosen only to remove the eigenvalue `1` of `L * A` need not remove it from
`(L * A) ^ 2`. No invertibility of `L` is assumed.

The proof is the identity principle. The function `A ↦ det (1 - (L * A) ^ m)` is analytic on the
whole space of operators, since the determinant is smooth of every order including `ω`
(`ContinuousLinearMap.contDiff_det`), and it takes the value `det 1 = 1` at `A = 0` when `m ≥ 1`.
So it does not vanish identically, and its nonvanishing set is dense
(`AnalyticOnNhd.dense_setOf_ne_zero`). Countable intersections of dense open sets are dense by
the Baire category theorem, the space of operators being complete.

## References

* J. Palis and W. de Melo, *Geometric Theory of Dynamical Systems*, Springer, 1982, Chapter 3, §3
  (the Kupka–Smale theorem, where the return maps of the closed orbits of bounded period are made
  hyperbolic by local perturbations).
* M. M. Peixoto, *On an approximation theorem of Kupka and Smale*, J. Differential Equations
  **3** (1967), 214–227, §2.
-/

public section

open scoped ContDiff

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The operators `A` for which `(L * A) ^ m` does not have the eigenvalue `1` form an open set. -/
theorem isOpen_setOf_det_one_sub_pow_mul_ne_zero (L : E →L[ℝ] E) (m : ℕ) :
    IsOpen {A : E →L[ℝ] E | (1 - (L * A) ^ m).det ≠ 0} :=
  isOpen_ne_fun (continuous_det.comp (by fun_prop)) continuous_const

/-- For every set `s` of exponents, the operators `A` for which no power `(L * A) ^ m` with
`m ∈ s` has the eigenvalue `1` form a `Gδ` set. -/
theorem isGδ_setOf_forall_det_one_sub_pow_mul_ne_zero (L : E →L[ℝ] E) (s : Set ℕ) :
    IsGδ {A : E →L[ℝ] E | ∀ m ∈ s, (1 - (L * A) ^ m).det ≠ 0} := by
  simpa only [Set.ofPred_forall] using
    IsGδ.biInter_of_isOpen s.to_countable fun m _ ↦ isOpen_setOf_det_one_sub_pow_mul_ne_zero L m

/-- For a finite set `s`, the operators `A` for which no power `(L * A) ^ m` with `m ∈ s` has the
eigenvalue `1` form an open set. -/
theorem isOpen_setOf_forall_det_one_sub_pow_mul_ne_zero (L : E →L[ℝ] E) {s : Set ℕ}
    (hs : s.Finite) : IsOpen {A : E →L[ℝ] E | ∀ m ∈ s, (1 - (L * A) ^ m).det ≠ 0} := by
  simpa only [Set.ofPred_forall] using
    hs.isOpen_biInter fun m _ ↦ isOpen_setOf_det_one_sub_pow_mul_ne_zero L m

/-- **Generic nondegeneracy of one iterate.** For `m ≠ 0`, the operators `A` for which
`(L * A) ^ m` does not have the eigenvalue `1` form a dense set. -/
theorem dense_setOf_det_one_sub_pow_mul_ne_zero (L : E →L[ℝ] E) {m : ℕ} (hm : m ≠ 0) :
    Dense {A : E →L[ℝ] E | (1 - (L * A) ^ m).det ≠ 0} := by
  have hcd : ContDiff ℝ ω fun A : E →L[ℝ] E ↦ 1 - (L * A) ^ m := by fun_prop
  have han : AnalyticOnNhd ℝ (fun A : E →L[ℝ] E ↦ (1 - (L * A) ^ m).det) Set.univ :=
    (contDiff_det.comp hcd).analyticOnNhd
  refine han.dense_setOf_ne_zero (z₀ := 0) ?_
  simp [zero_pow hm, ContinuousLinearMap.det]

/-- **Generic nondegeneracy of all the iterates in a set.** For a set `s` of positive integers,
the operators `A` for which no power `(L * A) ^ m` with `m ∈ s` has the eigenvalue `1` form a dense
set. Taking for `s` all positive integers, a generic `A` makes every cover of the orbit
nondegenerate. Over an infinite-dimensional space every determinant is `1` by convention, and the
set is everything. -/
theorem dense_setOf_forall_det_one_sub_pow_mul_ne_zero (L : E →L[ℝ] E) {s : Set ℕ}
    (h0 : 0 ∉ s) : Dense {A : E →L[ℝ] E | ∀ m ∈ s, (1 - (L * A) ^ m).det ≠ 0} := by
  by_cases hE : FiniteDimensional ℝ E
  · have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
    simpa only [Set.ofPred_forall] using
      dense_biInter_of_isOpen (fun m _ ↦ isOpen_setOf_det_one_sub_pow_mul_ne_zero L m)
        s.to_countable
        fun m hm ↦ dense_setOf_det_one_sub_pow_mul_ne_zero L (ne_of_mem_of_not_mem hm h0)
  · simp [ContinuousLinearMap.det, LinearMap.det_eq_one_of_not_module_finite hE]

/-- **Small perturbations of the identity making the iterates in a set nondegenerate.** For a
set `s` of positive integers and every `δ > 0` there is an operator `B` with `‖B‖ < δ` such that no
power `(L * (1 + B)) ^ m` with `m ∈ s` has the eigenvalue `1`. -/
theorem exists_norm_lt_forall_det_one_sub_pow_mul_one_add_ne_zero (L : E →L[ℝ] E) {s : Set ℕ}
    (h0 : 0 ∉ s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : E →L[ℝ] E, ‖B‖ < δ ∧ ∀ m ∈ s, (1 - (L * (1 + B)) ^ m).det ≠ 0 := by
  have hd : Dense ((fun B : E →L[ℝ] E ↦ 1 + B) ⁻¹'
      {A : E →L[ℝ] E | ∀ m ∈ s, (1 - (L * A) ^ m).det ≠ 0}) :=
    (dense_setOf_forall_det_one_sub_pow_mul_ne_zero L h0).preimage
      (Homeomorph.addLeft (1 : E →L[ℝ] E)).isOpenMap
  obtain ⟨B, hB, hBs⟩ := hd.exists_mem_open Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self hδ⟩
  exact ⟨B, by simpa using hBs, hB⟩

end ContinuousLinearMap
