/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.QuotientDeriv
public import TauCeti.Analysis.Quaternion.ComplexCoords
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Rigidity of left quaternionic quotient differentiation

On a connected open subset of the real quaternions, the functions with a left quotient
slope at every point are exactly `q ↦ a + q * b`. No continuity of the derivative is assumed.

The real derivative becomes complex-linear in `Quaternion.leftComplexCoords`. The
several-variable complex analyticity theorem then supplies smoothness. Symmetry of the
second derivative forces the slope to have zero derivative, so it is constant on each
connected open component. Integrating the resulting constant derivative gives the affine form.

## References

* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979),
  199–225, Theorem 1, for the classification of one-sided quaternionic differentiation.
* O. Dzagnidze, *On the differentiability of quaternion functions*, arXiv:1203.5619v1,
  §1, p. 2, for the ordered quotient convention and the affine classification.
-/

public section

open Filter Topology Quaternion Set
open scoped ContDiff

namespace TauCeti

variable {f : ℍ → ℍ} {s : Set ℍ}

/-- Pointwise left quotient differentiability on an open set implies real smoothness.
The regularity is a consequence, not a hypothesis, of the one-sided derivative condition. -/
theorem LeftQuotientDifferentiableOn.contDiffOn (hf : LeftQuotientDifferentiableOn f s)
    (hs : IsOpen s) {n : ℕ∞ω} : ContDiffOn ℝ n f s := by
  let e := Quaternion.leftComplexCoords
  have hd : DifferentiableOn ℂ (e ∘ f ∘ e.symm) (e '' s) := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨b, hb⟩ := leftQuotientDifferentiableAt_iff.mp
      (leftQuotientDifferentiableOn_iff.mp hf q hq)
    exact hb.hasFDerivAt.leftComplexCoords.differentiableAt.differentiableWithinAt
  have ha := (hd.analyticOnNhd_of_finiteDimensional (e.isOpenMap _ hs)).restrictScalars (𝕜 := ℝ)
  have hc : ContDiffOn ℝ n (e.symm ∘ (e ∘ f ∘ e.symm) ∘ e) s :=
    e.symm.contDiff.contDiffOn.comp
      (ha.contDiffOn_of_completeSpace.comp e.contDiff.contDiffOn (mapsTo_image _ _))
      (mapsTo_univ _ _)
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hc

/-- The slope field of a left quotient differentiable function has zero derivative on an
open set. This is the infinitesimal rigidity responsible for the affine classification. -/
theorem LeftQuotientDifferentiableOn.hasFDerivAt_slope (hf : LeftQuotientDifferentiableOn f s)
    (hs : IsOpen s) {q : ℍ} (hq : q ∈ s) :
    HasFDerivAt (fun x ↦ fderiv ℝ f x 1) (0 : ℍ →L[ℝ] ℍ) q := by
  let b := fun x ↦ fderiv ℝ f x 1
  have hb : DifferentiableOn ℝ b s :=
    ((hf.contDiffOn hs (n := 2)).fderiv_of_isOpen hs (by norm_num) (m := 1)).differentiableOn
      (by norm_num) |>.clm_apply (differentiableOn_const 1)
  let B := fderiv ℝ b q
  have hbq : HasFDerivAt b B q := (hb.differentiableAt (hs.mem_nhds hq)).hasFDerivAt
  have hsym (h k : ℍ) : k * B h = h * B k := by
    have hne : ∀ᶠ x in 𝓝 q,
        HasFDerivAt f ((ContinuousLinearMap.mul ℝ ℍ).flip (b x)) x := by
      filter_upwards [hs.mem_nhds hq] with x hx
      exact (leftQuotientDifferentiableOn_iff.mp hf x hx).hasLeftQuotientFDerivAt.hasFDerivAt
    have hD := ((ContinuousLinearMap.mul ℝ ℍ).flip.hasFDerivAt.comp q hbq)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply'] using
      second_derivative_symmetric_of_eventually hne hD h k
  have hB (h : ℍ) : B h = h * B 1 := by simpa using hsym h 1
  have hc : B 1 = 0 := by
    let i : ℍ := ⟨0, 1, 0, 0⟩
    let j : ℍ := ⟨0, 0, 1, 0⟩
    have hij : j * i - i * j ≠ 0 := by
      intro h
      have := congrArg QuaternionAlgebra.imK h
      norm_num [i, j] at this
    have hmul : (j * i - i * j) * B 1 = 0 := by
      rw [sub_mul, mul_assoc, mul_assoc, ← hB, ← hB, sub_eq_zero]
      exact hsym i j
    exact (mul_eq_zero.mp hmul).resolve_left hij
  have hzero : B = 0 := by
    apply ContinuousLinearMap.ext
    intro h
    simp [hB h, hc]
  simpa only [hzero] using hbq

/-- **Left quotient rigidity.** On a connected open set (including the empty set),
pointwise existence of a left quotient slope is equivalent to a single left-affine formula.
Only the function's values on the set are constrained. -/
theorem leftQuotient_rigidity (hs : IsOpen s) (hc : IsPreconnected s) :
    LeftQuotientDifferentiableOn f s ↔ ∃ a b : ℍ, ∀ q ∈ s, f q = a + q * b := by
  constructor
  · intro hf
    have hb : DifferentiableOn ℝ (fun x ↦ fderiv ℝ f x 1) s :=
      fun x hx ↦ (hf.hasFDerivAt_slope hs hx).differentiableAt.differentiableWithinAt
    obtain ⟨b, hb⟩ := hs.exists_is_const_of_fderiv_eq_zero hc hb
      (fun x hx ↦ (hf.hasFDerivAt_slope hs hx).fderiv)
    have hmul := fun q ↦ hasLeftQuotientFDerivAt_mul_const b q
    obtain ⟨a, ha⟩ := hs.exists_eq_add_of_fderiv_eq hc hf.differentiableOn
      (fun q _ ↦ (hmul q).hasFDerivAt.differentiableAt.differentiableWithinAt)
      (fun q hq ↦ by
        rw [(leftQuotientDifferentiableOn_iff.mp hf q hq).hasLeftQuotientFDerivAt.fderiv,
          (hmul q).fderiv, hb q hq])
    exact ⟨a, b, fun q hq ↦ (ha hq).trans (add_comm _ _)⟩
  · rintro ⟨a, b, hab⟩
    apply leftQuotientDifferentiableOn_iff.mpr
    intro q hq
    exact ((hasLeftQuotientFDerivAt_mul_const b q).const_add a).congr_of_eventuallyEq
      (eventually_of_mem (hs.mem_nhds hq) fun x hx ↦ hab x hx) |>.leftQuotientDifferentiableAt

/-- On a nonempty connected open set the intercept and the left quotient slope in the
rigidity theorem are unique. -/
theorem LeftQuotientDifferentiableOn.existsUnique_affine
    (hf : LeftQuotientDifferentiableOn f s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hne : s.Nonempty) : ∃! p : ℍ × ℍ, ∀ q ∈ s, f q = p.1 + q * p.2 := by
  obtain ⟨a, b, hab⟩ := (leftQuotient_rigidity hs hc).mp hf
  obtain ⟨q, hq⟩ := hne
  have hder (c d : ℍ) (hcd : ∀ x ∈ s, f x = c + x * d) :
      HasLeftQuotientFDerivAt f q d :=
    ((hasLeftQuotientFDerivAt_mul_const d q).const_add c).congr_of_eventuallyEq
      (eventually_of_mem (hs.mem_nhds hq) fun x hx ↦ hcd x hx)
  refine ⟨(a, b), hab, ?_⟩
  rintro ⟨c, d⟩ hcd
  have hdb := (hder c d hcd).unique (hder a b hab)
  apply Prod.ext
  · dsimp only
    apply add_right_cancel (b := q * b)
    simpa only [hdb] using (hcd q hq).symm.trans (hab q hq)
  · exact hdb

/-- On an arbitrary open set, left quotient differentiability is equivalent to an affine
formula on each connected component; different components may have different slopes. -/
theorem leftQuotientDifferentiableOn_iff_affine_on_connectedComponentIn (hs : IsOpen s) :
    LeftQuotientDifferentiableOn f s ↔
      ∀ q ∈ s, ∃ a b : ℍ, ∀ x ∈ connectedComponentIn s q, f x = a + x * b := by
  constructor
  · intro hf q _
    exact (leftQuotient_rigidity hs.connectedComponentIn
      isPreconnected_connectedComponentIn).mp (hf.mono (connectedComponentIn_subset s q))
  · intro hf
    apply leftQuotientDifferentiableOn_iff.mpr
    intro q hq
    obtain ⟨a, b, hab⟩ := hf q hq
    have hmem := hs.connectedComponentIn.mem_nhds (mem_connectedComponentIn hq)
    exact ((hasLeftQuotientFDerivAt_mul_const b q).const_add a).congr_of_eventuallyEq
      (eventually_of_mem hmem fun x hx ↦ hab x hx) |>.leftQuotientDifferentiableAt

end TauCeti
