/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Hadamard's lemma along normal segments

On a product `E × N`, think of `E × {0}` as a zero section and of `N` as the normal directions.
For a set `Ω ⊆ E × N`, `TauCeti.normalSegmentDomain Ω` is the set of parameters `(a, z, W)` for
which the normal segment from `(z, 0)` to `(z, a W)` lies in `Ω`; it is open when `Ω` is.
Hadamard's lemma along these segments writes the quotient `a⁻¹ (f(z, a W) - f(z, 0))` of a
function `f` that is `C¹` on `Ω` as the average `∫₀¹ ∂_W f(z, t a W) W dt` of its normal
derivative, which stays smooth in `(a, z, W)` at `a = 0`. This is the step behind the normal
dilations of fields and of maps along a curve, where `a → 0` magnifies the normal directions.

## Main definitions

* `TauCeti.normalSegmentDomain Ω`: the parameters whose normal segments lie in `Ω`.

## Main results

* `TauCeti.isOpen_normalSegmentDomain`: `normalSegmentDomain Ω` is open when `Ω` is.
* `TauCeti.exists_isCompact_forall_segment_subset`: over a compact set whose zero-section points
  lie in an open `Ω`, the normal segments lie in one compact subset of `Ω` for all small `a`.
* `ContDiffOn.comp_normalSegmentDomain`: a function `Cⁿ` on `Ω`, evaluated at `(z, a W)`, is `Cⁿ`
  in `(a, z, W)` on `normalSegmentDomain Ω`.
* `TauCeti.contDiffOn_integral_fderiv_normalSegmentDomain`: the average normal derivative of a
  function `C^(n+1)` on an open `Ω` is `Cⁿ` on `normalSegmentDomain Ω`, including `a = 0`.
* `TauCeti.inv_smul_sub_eq_integral_fderiv_of_mem_normalSegmentDomain`: for `a ≠ 0` this average
  is `a⁻¹ (f(z, a W) - f(z, 0))`.
* `TauCeti.integral_clm_fderiv_eq_integral_fderiv_of_mem_normalSegmentDomain`: a fixed continuous
  linear map passes through the average.
-/

public section

noncomputable section

open Filter Set Topology

namespace TauCeti

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup N]
  [NormedSpace ℝ N]

/-- The parameters `(a, z, W)` for which the normal segment from `(z, 0)` to `(z, a W)` lies in
`Ω`. Hadamard's lemma along these segments writes normal dilations of fields and maps defined on
`Ω` as functions of `(a, z, W)` that stay smooth at `a = 0`. -/
def normalSegmentDomain (Ω : Set (E × N)) : Set (ℝ × (E × N)) :=
  {q | ∀ t ∈ Icc (0 : ℝ) 1, (q.2.1, t • q.1 • q.2.2) ∈ Ω}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp]
theorem mem_normalSegmentDomain {Ω : Set (E × N)} {q : ℝ × (E × N)} :
    q ∈ normalSegmentDomain Ω ↔ ∀ t ∈ Icc (0 : ℝ) 1, (q.2.1, t • q.1 • q.2.2) ∈ Ω :=
  Iff.rfl

omit [NormedSpace ℝ E] in
theorem isOpen_normalSegmentDomain {Ω : Set (E × N)} (hΩ : IsOpen Ω) :
    IsOpen (normalSegmentDomain Ω) := by
  refine isOpen_iff_mem_nhds.2 fun q hq ↦ ?_
  have hc : Continuous fun y : (ℝ × (E × N)) × ℝ ↦ ((y.1.2.1, y.2 • y.1.1 • y.1.2.2) : E × N) :=
    by fun_prop
  exact isCompact_Icc.eventually_forall_of_forall_eventually (P := fun (q : ℝ × (E × N)) (t : ℝ) ↦
    (q.2.1, t • q.1 • q.2.2) ∈ Ω) fun t ht ↦ hc.continuousAt.preimage_mem_nhds
      (hΩ.mem_nhds (hq t ht))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem zero_mem_normalSegmentDomain {Ω : Set (E × N)} {p : E × N} (hp : (p.1, 0) ∈ Ω) :
    ((0 : ℝ), p) ∈ normalSegmentDomain Ω := fun t _ ↦ by simpa using hp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The base point of a segment in `normalSegmentDomain Ω` lies in `Ω`. -/
theorem mk_zero_mem_of_mem_normalSegmentDomain {Ω : Set (E × N)} {q : ℝ × (E × N)}
    (hq : q ∈ normalSegmentDomain Ω) : (q.2.1, 0) ∈ Ω := by
  simpa using hq 0 (left_mem_Icc.2 zero_le_one)

/-- Over a compact set `K` of points whose zero-section points lie in an open set `Ω`, the normal
segments from `(z, 0)` to `(z, a W)`, `(z, W) ∈ K`, lie in one compact subset of `Ω` for all small
`a`. This makes bounds of continuous functions on `Ω` uniform along these segments. -/
theorem exists_isCompact_forall_segment_subset {Ω K : Set (E × N)} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : ∀ p ∈ K, (p.1, 0) ∈ Ω) :
    ∃ S ⊆ Ω, IsCompact S ∧ ∀ᶠ a in 𝓝 (0 : ℝ), ∀ p ∈ K, segment ℝ (p.1, 0) (p.1, a • p.2) ⊆ S := by
  have hU : ∀ᶠ a in 𝓝 (0 : ℝ), ∀ p ∈ K, (a, p) ∈ normalSegmentDomain Ω :=
    hK.eventually_forall_of_forall_eventually fun p hp ↦
      (isOpen_normalSegmentDomain hΩ).mem_nhds (zero_mem_normalSegmentDomain (hKΩ p hp))
  obtain ⟨ε, hε, hεU⟩ := Metric.eventually_nhds_iff.1 hU
  refine ⟨(fun q : ℝ × (E × N) ↦ ((q.2.1, q.1 • q.2.2) : E × N)) ''
    (Icc (-(ε / 2)) (ε / 2) ×ˢ K), ?_, (isCompact_Icc.prod hK).image (by fun_prop), ?_⟩
  · rintro _ ⟨⟨s, p⟩, ⟨hs, hp⟩, rfl⟩
    have hs' : dist s 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    simpa using (mem_normalSegmentDomain.1 (hεU hs' p hp)) 1 (right_mem_Icc.2 zero_le_one)
  · filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) (half_pos hε)] with a ha p hp
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at ha
    -- A point of the segment is `(z, (β a) W)` with `0 ≤ β ≤ 1`.
    rintro _ ⟨α, β, hα, hβ, hαβ, rfl⟩
    refine ⟨(β * a, p), ⟨abs_le.1 ?_, hp⟩, ?_⟩
    · rw [abs_mul, abs_of_nonneg hβ]
      nlinarith [abs_nonneg a]
    · ext
      · simp [← add_smul, hαβ]
      · simp [mul_smul]

section HadamardNormalSegment

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A function `Cⁿ` on `Ω`, evaluated at the far end `(z, a W)` of the normal segments in `Ω`, is
`Cⁿ` in `(a, z, W)` on `normalSegmentDomain Ω`. -/
theorem _root_.ContDiffOn.comp_normalSegmentDomain {Φ : E × N → G} {Ω : Set (E × N)}
    {n : WithTop ℕ∞} (hΦ : ContDiffOn ℝ n Φ Ω) :
    ContDiffOn ℝ n (fun q : ℝ × (E × N) ↦ Φ (q.2.1, q.1 • q.2.2)) (normalSegmentDomain Ω) :=
  hΦ.comp (by fun_prop : ContDiff ℝ n fun q : ℝ × (E × N) ↦
    ((q.2.1, q.1 • q.2.2) : E × N)).contDiffOn fun q hq ↦ by
      simpa using hq 1 (right_mem_Icc.2 zero_le_one)

/-- **Hadamard's lemma along normal segments: smoothness.** If `f` is `C^(n+1)` on an open set
`Ω`, the average `∫₀¹ ∂_W f(z, t a W) W dt` of its normal derivative along the segment from
`(z, 0)` to `(z, a W)` is `Cⁿ` in `(a, z, W)` on `normalSegmentDomain Ω`, including `a = 0`. -/
theorem contDiffOn_integral_fderiv_normalSegmentDomain {f : E × N → G} {Ω : Set (E × N)}
    (hΩ : IsOpen Ω) {n : ℕ∞} (hf : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) f Ω) :
    ContDiffOn ℝ n (fun q : ℝ × (E × N) ↦ ∫ t in (0 : ℝ)..1,
      fderiv ℝ f (q.2.1, t • q.1 • q.2.2) (0, q.2.2)) (normalSegmentDomain Ω) := by
  refine ContDiffOn.parametric_intervalIntegral (isOpen_normalSegmentDomain hΩ) ?_
  -- The derivative of `f` along the segments is `Cⁿ` in `(a, z, W, t)`.
  have hpt : ContDiffOn ℝ n (fun y : (ℝ × (E × N)) × ℝ ↦
      fderiv ℝ f (y.1.2.1, y.2 • y.1.1 • y.1.2.2)) (normalSegmentDomain Ω ×ˢ uIcc 0 1) :=
    (hf.fderiv_of_isOpen hΩ le_rfl).comp (by fun_prop : ContDiff ℝ n fun y : (ℝ × (E × N)) × ℝ ↦
      ((y.1.2.1, y.2 • y.1.1 • y.1.2.2) : E × N)).contDiffOn fun y hy ↦ by
      rw [uIcc_of_le zero_le_one] at hy
      exact hy.1 y.2 hy.2
  exact hpt.clm_apply (by fun_prop)

/-- **Hadamard's lemma along normal segments.** If `f` is `C¹` on an open set `Ω` containing the
segment from `(z, 0)` to `(z, a W)`, with `a ≠ 0`, then the quotient `a⁻¹ (f(z, a W) - f(z, 0))`
is the average `∫₀¹ ∂_W f(z, t a W) W dt` of the normal derivative of `f` along the segment. -/
theorem inv_smul_sub_eq_integral_fderiv_of_mem_normalSegmentDomain [CompleteSpace G]
    {f : E × N → G} {Ω : Set (E × N)} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω) {a : ℝ}
    {p : E × N} (ha : a ≠ 0) (hq : (a, p) ∈ normalSegmentDomain Ω) :
    a⁻¹ • (f (p.1, a • p.2) - f (p.1, 0)) =
      ∫ t in (0 : ℝ)..1, fderiv ℝ f (p.1, t • a • p.2) (0, p.2) := by
  -- Along the normal segment, `t ↦ f(z, t a W)` has derivative `a ∂_W f(z, t a W) W`.
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ ↦ f (p.1, t • a • p.2))
      (a • fderiv ℝ f (p.1, t • a • p.2) (0, p.2)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hft : HasFDerivAt f (fderiv ℝ f (p.1, t • a • p.2)) (p.1, t • a • p.2) :=
      ((hf.contDiffAt (hΩ.mem_nhds (hq t ht))).differentiableAt one_ne_zero).hasFDerivAt
    have hγ : HasDerivAt (fun t : ℝ ↦ ((p.1, t • a • p.2) : E × N)) ((0 : E), a • p.2) t := by
      simpa using (hasDerivAt_const t p.1).prodMk ((hasDerivAt_id t).smul_const (a • p.2))
    have hv : ((0 : E), a • p.2) = a • ((0 : E), p.2) := by simp
    have h := hft.comp_hasDerivAt t hγ
    rwa [hv, map_smul] at h
  have hc : ContinuousOn (fun t : ℝ ↦ a • fderiv ℝ f (p.1, t • a • p.2) (0, p.2)) (uIcc 0 1) := by
    refine continuousOn_const.smul (((hf.continuousOn_fderiv_of_isOpen hΩ le_rfl).comp
      (by fun_prop : Continuous fun t : ℝ ↦ ((p.1, t • a • p.2) : E × N)).continuousOn
      fun t ht ↦ ?_).clm_apply continuousOn_const)
    rw [uIcc_of_le zero_le_one] at ht
    exact hq t ht
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  simp only [one_smul, zero_smul, intervalIntegral.integral_smul] at hI
  rw [← hI, inv_smul_smul₀ ha]

/-- On `normalSegmentDomain Ω`, a fixed continuous linear map `L` commutes with the average normal
derivative of a function `f` that is differentiable on the open set `Ω`. -/
theorem integral_clm_fderiv_eq_integral_fderiv_of_mem_normalSegmentDomain {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G →L[ℝ] H) {f : E × N → G} {Ω : Set (E × N)}
    (hΩ : IsOpen Ω) (hf : DifferentiableOn ℝ f Ω) {q : ℝ × (E × N)}
    (hq : q ∈ normalSegmentDomain Ω) :
    ∫ t in (0 : ℝ)..1, L (fderiv ℝ f (q.2.1, t • q.1 • q.2.2) (0, q.2.2)) =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun x ↦ L (f x)) (q.2.1, t • q.1 • q.2.2) (0, q.2.2) := by
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  rw [← Function.comp_def, L.fderiv_comp_left (hf.differentiableAt (hΩ.mem_nhds (hq t ht))),
    ContinuousLinearMap.comp_apply]

end HadamardNormalSegment

end TauCeti
