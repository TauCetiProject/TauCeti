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
# Rigidity of quaternionic quotient differentiation

On a connected open subset of the real quaternions, the functions with a left quotient
slope at every point are exactly `q ↦ a + q * b`, those with a right quotient slope at every
point are exactly `q ↦ a + b * q`, and those with both are exactly `q ↦ a + r • q` with `r`
real. No continuity of the derivative is assumed.

For the left classification, the real derivative becomes complex-linear in
`Quaternion.leftComplexCoords`. The several-variable complex analyticity theorem then supplies
smoothness. Symmetry of the second derivative forces the slope to have zero derivative, so it is
constant on each connected open component. Integrating the resulting constant derivative gives
the affine form. The right classification follows by the reflection `x ↦ star (f (star x))`,
which exchanges left and right slopes and maps a connected open set `s` to the connected open
set `star s`. In the two-sided case a left and a right slope at a single point already coincide
and are real.

## References

* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979),
  199–225, Theorem 1, for the classification of one-sided quaternionic differentiation.
* O. Dzagnidze, *On the differentiability of quaternion functions*, arXiv:1203.5619v1,
  §1, p. 2, for the ordered quotient convention and the affine classification.
-/

public section

open Filter Topology Quaternion Set
open scoped ContDiff Pointwise

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

/-- **Right quotient rigidity.** On a connected open set (including the empty set),
pointwise existence of a right quotient slope is equivalent to a single right-affine formula.
Only the function's values on the set are constrained. -/
theorem rightQuotient_rigidity (hs : IsOpen s) (hc : IsPreconnected s) :
    RightQuotientDifferentiableOn f s ↔ ∃ a b : ℍ, ∀ q ∈ s, f q = a + b * q := by
  have hs' : IsOpen (star s) := hs.preimage continuous_star
  have hc' : IsPreconnected (star s) := by
    simpa only [image_star] using hc.image _ continuous_star.continuousOn
  rw [← leftQuotientDifferentiableOn_star_star_iff, leftQuotient_rigidity hs' hc']
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨star a, star b, fun q hq ↦ ?_⟩
    simpa using congrArg star (hab (star q) (by simpa using hq))
  · rintro ⟨a, b, hab⟩
    refine ⟨star a, star b, fun x hx ↦ ?_⟩
    simp [hab (star x) hx]

/-- On a nonempty connected open set the intercept and the right quotient slope in the
rigidity theorem are unique. -/
theorem RightQuotientDifferentiableOn.existsUnique_affine
    (hf : RightQuotientDifferentiableOn f s) (hs : IsOpen s) (hc : IsPreconnected s)
    (hne : s.Nonempty) : ∃! p : ℍ × ℍ, ∀ q ∈ s, f q = p.1 + p.2 * q := by
  obtain ⟨a, b, hab⟩ := (rightQuotient_rigidity hs hc).mp hf
  obtain ⟨q, hq⟩ := hne
  have hder (c d : ℍ) (hcd : ∀ x ∈ s, f x = c + d * x) :
      HasRightQuotientFDerivAt f q d :=
    ((hasRightQuotientFDerivAt_const_mul d q).const_add c).congr_of_eventuallyEq
      (eventually_of_mem (hs.mem_nhds hq) hcd)
  refine ⟨(a, b), hab, ?_⟩
  rintro ⟨c, d⟩ hcd
  have hdb := (hder c d hcd).unique (hder a b hab)
  apply Prod.ext
  · dsimp only
    apply add_right_cancel (b := b * q)
    simpa only [hdb] using (hcd q hq).symm.trans (hab q hq)
  · exact hdb

/-- On an arbitrary open set, right quotient differentiability is equivalent to an affine
formula on each connected component; different components may have different slopes. -/
theorem rightQuotientDifferentiableOn_iff_affine_on_connectedComponentIn (hs : IsOpen s) :
    RightQuotientDifferentiableOn f s ↔
      ∀ q ∈ s, ∃ a b : ℍ, ∀ x ∈ connectedComponentIn s q, f x = a + b * x := by
  have hrig (q : ℍ) := rightQuotient_rigidity (f := f) hs.connectedComponentIn
    (isPreconnected_connectedComponentIn (F := s) (x := q))
  constructor
  · intro hf q _
    exact (hrig q).mp (hf.mono (connectedComponentIn_subset s q))
  · intro hf
    exact rightQuotientDifferentiableOn_iff.mpr fun q hq ↦
      rightQuotientDifferentiableOn_iff.mp ((hrig q).mpr (hf q hq)) q (mem_connectedComponentIn hq)

/-- **Two-sided quotient rigidity.** On a connected open set (including the empty set),
pointwise existence of both a left and a right quotient slope is equivalent to the affine
formula `q ↦ a + r • q` with a real slope `r`. -/
theorem twoSidedQuotient_rigidity (hs : IsOpen s) (hc : IsPreconnected s) :
    LeftQuotientDifferentiableOn f s ∧ RightQuotientDifferentiableOn f s ↔
      ∃ (a : ℍ) (r : ℝ), ∀ q ∈ s, f q = a + r • q := by
  constructor
  · rintro ⟨hl, hr⟩
    obtain ⟨a, b, hab⟩ := (leftQuotient_rigidity hs hc).mp hl
    rcases s.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
    · exact ⟨0, 0, by simp⟩
    have hb : HasLeftQuotientFDerivAt f q b :=
      ((hasLeftQuotientFDerivAt_mul_const b q).const_add a).congr_of_eventuallyEq
        (eventually_of_mem (hs.mem_nhds hq) hab)
    obtain ⟨c, hqc⟩ := rightQuotientDifferentiableAt_iff.mp
      (rightQuotientDifferentiableOn_iff.mp hr q hq)
    have hre : (b.re : ℍ) = b := by
      simpa [hb.im_eq_zero_of_hasRightQuotientFDerivAt hqc] using re_add_im b
    refine ⟨a, b.re, fun x hx ↦ ?_⟩
    rw [hab x hx, ← hre, mul_coe_eq_smul, re_coe]
  · rintro ⟨a, r, h⟩
    exact ⟨(leftQuotient_rigidity hs hc).mpr ⟨a, r, fun x hx ↦ by rw [h x hx, mul_coe_eq_smul]⟩,
      (rightQuotient_rigidity hs hc).mpr ⟨a, r, fun x hx ↦ by rw [h x hx, coe_mul_eq_smul]⟩⟩

end TauCeti
