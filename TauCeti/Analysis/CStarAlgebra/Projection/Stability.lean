/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Algebra.Star.Orthogonal
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Topology.Algebra.Indicator
public import Mathlib.Topology.Order.DenselyOrdered
public import TauCeti.Analysis.CStarAlgebra.Basic
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import TauCeti.Topology.Algebra.Indicator

/-!
# Norm stability of projections and finite orthogonal projection families in C⋆-algebras

When lifting projections from quotients, passing to inductive limits of C⋆-algebras, or
approximating elements in locally finite-dimensional subalgebras, one encounters elements `e` that
satisfy the star-projection relations `e = star e` and `e * e = e` only up to a small norm error,
and finite families `d : ι → A` that are also approximately pairwise orthogonal (`‖d i * d j‖ < δ`
for `i ≠ j`).

This file proves that single star projections and finite families of pairwise-orthogonal star
projections are **uniformly norm-stable** across all (not necessarily unital) C⋆-algebras:
* for every `ε > 0` (and finite index type `ι`), there exists a tolerance `δ > 0` depending **only**
  on `ε` (and `card ι`), independent of the C⋆-algebra `A`, such that any `δ`-approximate
  projection (or `δ`-approximately orthogonal projection family) in a closed non-unital
  `ℂ`-`⋆`-subalgebra `s` of `A` lies within `ε` of an exact star projection (or pairwise
  star-orthogonal family of star projections) inside `s`;
* quantitatively, for a single self-adjoint element `a` with `‖a * a - a‖ < 1 / 4`, its `(1 / 2, ∞)`
  spectral projection `spectralProjectionIoiHalf a` is an exact star projection at distance at most
  `2 * ‖a * a - a‖` from `a`, while the companion functional-calculus inverse square root
  `cfcₙ ((Set.Ioi (1 / 2)).indicator fun t ↦ (√t)⁻¹) a` supplies the polar normalization needed for
  approximate partial isometries in `TauCeti.Analysis.CStarAlgebra.PartialIsometry`.

## Main definitions

* `TauCeti.spectralProjectionIoiHalf`: `cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator 1) a`, the
  `(1 / 2, ∞)` spectral projection when `a` is self-adjoint with `1 / 2 ∉ quasispectrum ℝ a` (and
  `0` otherwise).

## Main results

* `IsStarProjection.eq_of_le_of_norm_sub_lt_one`: comparable star projections `p ≤ q` in a
  star-ordered C⋆-algebra with `‖p - q‖ < 1` are equal.
* `TauCeti.isStarProjection_spectralProjectionIoiHalf`,
  `IsSelfAdjoint.norm_spectralProjectionIoiHalf_sub_le`,
  `IsSelfAdjoint.cfcₙ_indicator_Ioi_half_inv_sqrt_mul_self_mul`,
  `IsSelfAdjoint.norm_cfcₙ_indicator_Ioi_half_inv_sqrt_sub_spectralProjectionIoiHalf_le`.
* `TauCeti.exists_isStarProjection_mem_of_approx`, `TauCeti.exists_pos_isStarProjection_mem`,
  `TauCeti.exists_pos_isStarProjection`.
* `TauCeti.exists_pos_pairwise_isStarOrtho_isStarProjection_mem`,
  `TauCeti.exists_pos_pairwise_isStarOrtho_isStarProjection`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23.
* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C*-Algebras*,
  Cambridge Univ. Press (2000), Lemma 2.2.6.
-/

public section

open Function
open scoped NonUnitalContinuousFunctionalCalculus

/-- Comparable star projections `p ≤ q` in a star-ordered C⋆-algebra with `‖p - q‖ < 1` are
equal. -/
theorem IsStarProjection.eq_of_le_of_norm_sub_lt_one {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hle : p ≤ q) (h : ‖p - q‖ < 1) : p = q :=
  hp.eq_of_mul_eq_left_of_norm_sub_lt_one hq ((hp.le_iff_mul_eq_left hq).mp hle) h

namespace TauCeti

section SpectralProjection

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The non-unital functional-calculus element `cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator 1) a`, which
is the `(1 / 2, ∞)` spectral projection of `a` when `a` is self-adjoint with
`1 / 2 ∉ quasispectrum ℝ a` (in particular when `‖a * a - a‖ < 1 / 4`), and `0` otherwise. -/
noncomputable def spectralProjectionIoiHalf (a : A) : A :=
  cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) a

/-- Unfold `TauCeti.spectralProjectionIoiHalf`. -/
theorem spectralProjectionIoiHalf_def (a : A) :
    spectralProjectionIoiHalf a = cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) a := (rfl)

/-- `spectralProjectionIoiHalf a` is always a star projection. -/
@[simp] theorem isStarProjection_spectralProjectionIoiHalf (a : A) :
    IsStarProjection (spectralProjectionIoiHalf a) :=
  isStarProjection_cfcₙ_indicator a (Set.Ioi (1 / 2 : ℝ))

/-- The `(1 / 2, ∞)` spectral projection of `0` is `0` (`simp` already proves this via
`IsStarProjection.spectralProjectionIoiHalf_eq` and `IsStarProjection.zero`). -/
theorem spectralProjectionIoiHalf_zero : spectralProjectionIoiHalf (0 : A) = 0 := by
  simp [spectralProjectionIoiHalf_def]

/-- `spectralProjectionIoiHalf a` belongs to every closed non-unital `𝕜'`-`⋆`-subalgebra (for any
scalar action `𝕜'` over `ℝ`, including `ℝ` and `ℂ`) containing `a`. -/
theorem spectralProjectionIoiHalf_mem {𝕜' S : Type*} [Monoid 𝕜'] [MulAction 𝕜' A] [SetLike S A]
    [NonUnitalSubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A] [SMulMemClass S 𝕜' A]
    [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {a : A} (ha : a ∈ s) :
    spectralProjectionIoiHalf a ∈ s := by
  rw [spectralProjectionIoiHalf_def]
  exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := 𝕜') _ ha

end SpectralProjection

end TauCeti

namespace IsSelfAdjoint

open TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A] {a : A}

/-- Pointwise quasispectral estimate `|t * t - t| ≤ ‖a * a - a‖` for self-adjoint `a`. -/
theorem abs_mul_self_sub_le_norm (ha : IsSelfAdjoint a) {t : ℝ} (ht : t ∈ quasispectrum ℝ a) :
    |t * t - t| ≤ ‖a * a - a‖ := by
  have hcont_sq : ContinuousOn (fun x : ℝ ↦ x * x) (quasispectrum ℝ a) :=
    (continuous_id.mul continuous_id).continuousOn
  have hcfc : cfcₙ (fun x : ℝ ↦ x * x - x) a = a * a - a := by
    rw [cfcₙ_sub (fun x : ℝ ↦ x * x) (fun x : ℝ ↦ x) a hcont_sq (mul_zero 0) continuousOn_id rfl,
      cfcₙ_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ x) a continuousOn_id rfl continuousOn_id rfl,
      cfcₙ_id' ℝ a]
  simpa [Real.norm_eq_abs, hcfc] using
    norm_apply_le_norm_cfcₙ (fun x : ℝ ↦ x * x - x) a ht (hcont_sq.sub continuousOn_id)
      (by simp) ha

/-- When `IsSelfAdjoint a` and `‖a * a - a‖ < 1 / 4`, `1 / 2 ∉ quasispectrum ℝ a`. -/
theorem notMem_quasispectrum_half_of_norm_mul_self_sub_lt (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) : (1 / 2 : ℝ) ∉ quasispectrum ℝ a := fun hmem ↦ by
  have hle := ha.abs_mul_self_sub_le_norm hmem; norm_num at hle; linarith

/-- Continuity of `indicator (Ioi (1 / 2)) 1` on `quasispectrum ℝ a` when
`1 / 2 ∉ quasispectrum ℝ a`. -/
theorem continuousOn_indicator_Ioi_half_of_notMem (ha : (1 / 2 : ℝ) ∉ quasispectrum ℝ a) :
    ContinuousOn ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) (quasispectrum ℝ a) :=
  continuousOn_const.continuousOn_indicator_of_disjoint_frontier <| by
    rwa [frontier_Ioi, Set.disjoint_singleton_left]

/-- Continuity of `indicator (Ioi (1 / 2)) 1` on `quasispectrum ℝ a` when `‖a * a - a‖ < 1 / 4`. -/
theorem continuousOn_indicator_Ioi_half (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    ContinuousOn ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) (quasispectrum ℝ a) :=
  continuousOn_indicator_Ioi_half_of_notMem (ha.notMem_quasispectrum_half_of_norm_mul_self_sub_lt h)

/-- Continuous non-unital `⋆`-algebra homomorphisms preserve `TauCeti.spectralProjectionIoiHalf` at
any self-adjoint element `a` with `1 / 2 ∉ quasispectrum ℝ a`. -/
theorem map_spectralProjectionIoiHalf {B F : Type*} [NonUnitalCStarAlgebra B] [FunLike F A B]
    [NonUnitalAlgHomClass F ℝ A B] [StarHomClass F A B] (ha : IsSelfAdjoint a)
    (h : (1 / 2 : ℝ) ∉ quasispectrum ℝ a) (φ : F) (hφ : Continuous φ) :
    φ (spectralProjectionIoiHalf a) = spectralProjectionIoiHalf (φ a) := by
  rw [spectralProjectionIoiHalf_def, spectralProjectionIoiHalf_def]
  exact NonUnitalStarAlgHomClass.map_cfcₙ φ _ a
    (continuousOn_indicator_Ioi_half_of_notMem h) (by simp) hφ ha (ha.map φ)

/-- Sharp bound `‖spectralProjectionIoiHalf a - a‖ ≤ 2 * ‖a * a - a‖` when `‖a * a - a‖ < 1 / 4`. -/
theorem norm_spectralProjectionIoiHalf_sub_le (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    ‖spectralProjectionIoiHalf a - a‖ ≤ 2 * ‖a * a - a‖ := by
  rw [spectralProjectionIoiHalf_def]
  set f : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)
  rw [show cfcₙ f a - a = cfcₙ (fun t : ℝ ↦ f t - t) a by
    rw [cfcₙ_sub f (fun t : ℝ ↦ t) a (ha.continuousOn_indicator_Ioi_half h) (by simp [f])
      continuousOn_id rfl, cfcₙ_id' ℝ a]]
  refine norm_cfcₙ_le fun t ht ↦ ?_
  rw [Real.norm_eq_abs]; dsimp only [f]
  have hqt := ha.abs_mul_self_sub_le_norm ht
  have hprod : |t * t - t| = |t| * |1 - t| := by
    rw [show t * t - t = t * (t - 1) by ring, abs_mul, abs_sub_comm]
  by_cases hgt : t ∈ Set.Ioi (1 / 2 : ℝ)
  · rw [Set.indicator_of_mem hgt, Pi.one_apply]
    rw [abs_of_pos (a := t) (by linarith [Set.mem_Ioi.mp hgt])] at hprod
    nlinarith [abs_nonneg (1 - t), Set.mem_Ioi.mp hgt]
  · rw [Set.indicator_of_notMem hgt, zero_sub, abs_neg]
    rw [abs_of_pos (a := 1 - t) (by linarith [not_lt.mp hgt])] at hprod
    nlinarith [abs_nonneg t, not_lt.mp hgt]

/-- Continuity of `(Set.Ioi (1 / 2)).indicator fun t ↦ (√t)⁻¹` on `quasispectrum ℝ a` when
`‖a * a - a‖ < 1 / 4`. -/
theorem continuousOn_indicator_Ioi_half_inv_sqrt (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) :
    ContinuousOn ((Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) (quasispectrum ℝ a) := by
  refine (Real.continuous_sqrt.continuousOn.inv₀ fun t ht ↦ ?_)
    |>.continuousOn_indicator_of_disjoint_frontier ?_
  · have ht_gt : (1 / 2 : ℝ) < t := interior_subset ht
    exact (Real.sqrt_pos.mpr (by linarith)).ne'
  · rw [frontier_Ioi, Set.disjoint_singleton_left]
    exact ha.notMem_quasispectrum_half_of_norm_mul_self_sub_lt h

/-- For self-adjoint `a` with `‖a * a - a‖ < 1 / 4`, the truncated inverse square root
`w = cfcₙ ((Set.Ioi (1 / 2)).indicator fun t ↦ (√t)⁻¹) a` satisfies
`w * a * w = spectralProjectionIoiHalf a`. -/
theorem cfcₙ_indicator_Ioi_half_inv_sqrt_mul_self_mul (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) :
    cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) a * a *
        cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) a =
      spectralProjectionIoiHalf a := by
  set g : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹
  have hg_cont := ha.continuousOn_indicator_Ioi_half_inv_sqrt h
  have hg0 : g 0 = 0 := by simp [g]
  rw [spectralProjectionIoiHalf_def]
  conv_lhs => lhs; rhs; rw [← cfcₙ_id' ℝ a]
  rw [← cfcₙ_mul g (fun t : ℝ ↦ t) a hg_cont hg0 continuousOn_id rfl,
    ← cfcₙ_mul (fun t : ℝ ↦ g t * t) g a (hg_cont.mul continuousOn_id) (by simp [hg0])
      hg_cont hg0]
  refine cfcₙ_congr fun t _ ↦ ?_
  by_cases ht : t ∈ Set.Ioi (1 / 2 : ℝ)
  · have ht_pos : 0 < t := by linarith [Set.mem_Ioi.mp ht]
    have hne : √t ≠ 0 := (Real.sqrt_pos.mpr ht_pos).ne'
    simp only [g, Set.indicator_of_mem ht, Pi.one_apply]
    conv_lhs => lhs; rhs; rw [← Real.mul_self_sqrt ht_pos.le]
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul, mul_inv_cancel₀ hne]
  · simp only [g, Set.indicator_of_notMem ht, zero_mul]

/-- Quantitative estimate
`‖cfcₙ ((Set.Ioi (1 / 2)).indicator fun t ↦ (√t)⁻¹) a - spectralProjectionIoiHalf a‖ ≤`
`4 * ‖a * a - a‖` for self-adjoint `a` with `‖a * a - a‖ < 1 / 4`. -/
theorem norm_cfcₙ_indicator_Ioi_half_inv_sqrt_sub_spectralProjectionIoiHalf_le
    (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    ‖cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) a - spectralProjectionIoiHalf a‖ ≤
      4 * ‖a * a - a‖ := by
  set g : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹
  set ind : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)
  rw [spectralProjectionIoiHalf_def, ← cfcₙ_sub g ind a
    (ha.continuousOn_indicator_Ioi_half_inv_sqrt h) (by simp [g])
    (ha.continuousOn_indicator_Ioi_half h) (by simp [ind])]
  refine norm_cfcₙ_le fun t ht ↦ ?_
  rw [Real.norm_eq_abs]
  have hqt := ha.abs_mul_self_sub_le_norm ht
  by_cases hgt : t ∈ Set.Ioi (1 / 2 : ℝ)
  · simp only [g, ind, Set.indicator_of_mem hgt, Pi.one_apply]
    have ht_pos : 0 < t := by linarith [Set.mem_Ioi.mp hgt]
    have hsqrt_half : (1 / 2 : ℝ) < √t := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [Set.mem_Ioi.mp hgt])
    have hne : √t ≠ 0 := (Real.sqrt_pos.mpr ht_pos).ne'
    have h1t : 1 - t = ((√t)⁻¹ - 1) * (√t * (1 + √t)) := by
      calc 1 - t = 1 - √t * √t := by rw [Real.mul_self_sqrt ht_pos.le]
        _ = ((√t)⁻¹ * √t - √t) * (1 + √t) := by rw [inv_mul_cancel₀ hne]; ring
        _ = ((√t)⁻¹ - 1) * (√t * (1 + √t)) := by ring
    have hprod_sqrt : |1 - t| = |(√t)⁻¹ - 1| * (√t * (1 + √t)) := by
      rw [h1t, abs_mul, abs_of_pos (a := √t * (1 + √t)) (by positivity)]
    have hprod_t : |t * t - t| = t * |1 - t| := by
      rw [show t * t - t = t * (t - 1) by ring, abs_mul, abs_of_pos ht_pos, abs_sub_comm]
    have hD : 3 / 4 ≤ √t * (1 + √t) := by nlinarith
    have h1 : (3 / 4) * |(√t)⁻¹ - 1| ≤ |1 - t| := by nlinarith [abs_nonneg ((√t)⁻¹ - 1)]
    nlinarith [abs_nonneg (1 - t), Set.mem_Ioi.mp hgt]
  · simp only [g, ind, Set.indicator_of_notMem hgt, sub_zero, abs_zero]; positivity

end IsSelfAdjoint

/-- Every star projection `p` is fixed by `TauCeti.spectralProjectionIoiHalf`. -/
@[simp] theorem IsStarProjection.spectralProjectionIoiHalf_eq {A : Type*} [NonUnitalCStarAlgebra A]
    {p : A} (hp : IsStarProjection p) : TauCeti.spectralProjectionIoiHalf p = p := by
  have hzero : p * p - p = 0 := sub_eq_zero.mpr hp.isIdempotentElem.eq
  have hle := hp.isSelfAdjoint.norm_spectralProjectionIoiHalf_sub_le
    (by rw [hzero, norm_zero]; norm_num)
  rw [hzero, norm_zero, mul_zero] at hle
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hle)

namespace TauCeti

section SingleProjection

variable {A : Type*} [NonUnitalCStarAlgebra A]

private lemma symmetrize_bounds (e : A) :
    let a : A := (2 : ℝ)⁻¹ • (e + star e)
    IsSelfAdjoint a ∧ ‖a - e‖ = (1 / 2) * ‖e - star e‖ ∧
      ‖a * a - a‖ ≤ ‖e * e - e‖ + (1 / 4) * ‖e - star e‖ ^ 2 := by
  set a : A := (2 : ℝ)⁻¹ • (e + star e)
  have ha_sa : IsSelfAdjoint a := by
    rw [IsSelfAdjoint, star_smul, star_trivial, star_add, star_star, add_comm]
  have h2 : ∀ x : A, (2 : ℝ)⁻¹ • (x + x) = x := fun x ↦ by
    rw [← two_smul ℝ x, inv_smul_smul₀ (by norm_num)]
  have ha_sub : ‖a - e‖ = (1 / 2) * ‖e - star e‖ := by
    have hsub : a - e = (2 : ℝ)⁻¹ • (star e - e) := by
      dsimp [a]; conv_lhs => rhs; rw [← h2 e]
      rw [← smul_sub]; congr 1; abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num), norm_sub_rev, one_div]
  have hid : a * a - a = (2 : ℝ)⁻¹ • ((e * e - e) + star (e * e - e)) -
      (4 : ℝ)⁻¹ • ((e - star e) * (e - star e)) := by
    have hmul : a * a = (4 : ℝ)⁻¹ • ((e + star e) * (e + star e)) := by
      dsimp [a]; rw [smul_mul_smul_comm]; norm_num
    have h4 : ∀ x : A, (2 : ℝ)⁻¹ • x = (4 : ℝ)⁻¹ • (x + x) := fun x ↦ by
      rw [← two_smul ℝ x, smul_smul]; norm_num
    rw [hmul]; dsimp [a]
    rw [h4 (e + star e), h4 ((e * e - e) + star (e * e - e)), ← smul_sub, ← smul_sub]
    congr 1; simp only [star_sub, star_mul, mul_add, add_mul, sub_mul, mul_sub]; abel
  refine ⟨ha_sa, ha_sub, ?_⟩
  rw [hid]
  have h1 : ‖(2 : ℝ)⁻¹ • ((e * e - e) + star (e * e - e))‖ ≤ ‖e * e - e‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have hsum := norm_add_le (e * e - e) (star (e * e - e)); rw [norm_star] at hsum; linarith
  have h2' : ‖(4 : ℝ)⁻¹ • ((e - star e) * (e - star e))‖ ≤ (1 / 4) * ‖e - star e‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num), one_div, sq]
    gcongr; exact norm_mul_le _ _
  linarith [norm_sub_le ((2 : ℝ)⁻¹ • ((e * e - e) + star (e * e - e)))
    ((4 : ℝ)⁻¹ • ((e - star e) * (e - star e)))]

/-- Every approximate projection with `‖x - star x‖ < 1` and `‖x * x - x‖ < 1` has `‖x‖ < 3`. -/
theorem norm_lt_three_of_approx_projection {x : A} (hsa : ‖x - star x‖ < 1)
    (hidem : ‖x * x - x‖ < 1) : ‖x‖ < 3 := by
  obtain ⟨ha_sa, ha_sub, ha_def⟩ := symmetrize_bounds x
  set a : A := (2 : ℝ)⁻¹ • (x + star x)
  have hsq : ‖x - star x‖ ^ 2 < 1 := by nlinarith [norm_nonneg (x - star x)]
  have ha_norm : ‖a‖ * ‖a‖ - ‖a‖ ≤ ‖a * a - a‖ := by
    simpa [← CStarRing.norm_star_mul_self, ha_sa.star_eq] using norm_sub_norm_le (a * a) a
  have ha_le : ‖a‖ ≤ 2 := by nlinarith
  have htri : ‖x‖ ≤ ‖a‖ + ‖a - x‖ := norm_le_norm_add_norm_sub a x
  linarith

/-- **Quantitative norm stability of projections** in a closed non-unital `ℂ`-`⋆`-subalgebra `s`:
if `e ∈ s` satisfies `‖e - star e‖ < δ` and `‖e * e - e‖ < δ` with `δ ≤ 1 / 5`, there exists a
star projection `p ∈ s` with `‖p - e‖ < 3 * δ`. -/
theorem exists_isStarProjection_mem_of_approx {S : Type*} [SetLike S A] [NonUnitalSubringClass S A]
    [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {e : A} (hes : e ∈ s)
    {δ : ℝ} (hδ : δ ≤ 1 / 5) (hsa : ‖e - star e‖ < δ) (hidem : ‖e * e - e‖ < δ) :
    ∃ p ∈ s, IsStarProjection p ∧ ‖p - e‖ < 3 * δ := by
  obtain ⟨ha_sa, ha_sub, ha_def⟩ := symmetrize_bounds e
  set a : A := (2 : ℝ)⁻¹ • (e + star e)
  have ha_mem : a ∈ s := by
    simpa only [Complex.coe_smul] using
      SMulMemClass.smul_mem (((2 : ℝ)⁻¹ : ℝ) : ℂ) (add_mem hes (star_mem hes))
  have hsq : ‖e - star e‖ ^ 2 ≤ ‖e - star e‖ := by nlinarith [norm_nonneg (e - star e)]
  have ha_lt : ‖a * a - a‖ < 1 / 4 := by linarith
  refine ⟨spectralProjectionIoiHalf a, spectralProjectionIoiHalf_mem (𝕜' := ℂ) ha_mem,
    isStarProjection_spectralProjectionIoiHalf a, ?_⟩
  have hp_a := ha_sa.norm_spectralProjectionIoiHalf_sub_le ha_lt
  linarith [norm_sub_le_norm_sub_add_norm_sub (spectralProjectionIoiHalf a) a e]

/-- **Quantitative norm stability of projections**: if `‖e - star e‖ < δ` and `‖e * e - e‖ < δ`
with `δ ≤ 1 / 5`, there exists a star projection `p` with `‖p - e‖ < 3 * δ`. -/
theorem exists_isStarProjection_of_approx {e : A} {δ : ℝ} (hδ : δ ≤ 1 / 5)
    (hsa : ‖e - star e‖ < δ) (hidem : ‖e * e - e‖ < δ) :
    ∃ p : A, IsStarProjection p ∧ ‖p - e‖ < 3 * δ := by
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨p, -, hp, hnorm⟩ :=
    exists_isStarProjection_mem_of_approx (s := (⊤ : NonUnitalStarSubalgebra ℂ A))
      trivial hδ hsa hidem
  exact ⟨p, hp, hnorm⟩

end SingleProjection

/-- **Uniform norm stability of projections in closed `ℂ`-`⋆`-subalgebras**: for every `ε > 0`,
there exists `δ > 0` depending only on `ε` (independent of the C⋆-algebra `A`) such that any
`e ∈ s` in a closed non-unital `ℂ`-`⋆`-subalgebra `s` with `‖e - star e‖ < δ` and `‖e * e - e‖ < δ`
lies within `ε` of a star projection `p ∈ s`. -/
theorem exists_pos_isStarProjection_mem {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A S : Type*} [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
      [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {e : A},
      e ∈ s → ‖e - star e‖ < δ → ‖e * e - e‖ < δ →
      ∃ p ∈ s, IsStarProjection p ∧ ‖p - e‖ < ε := by
  refine ⟨min (1 / 5) (ε / 3), by positivity, fun hes hsa hidem ↦ ?_⟩
  obtain ⟨p, hps, hp, hpe⟩ :=
    exists_isStarProjection_mem_of_approx hes (min_le_left _ _) hsa hidem
  exact ⟨p, hps, hp, hpe.trans_le (by linarith [min_le_right (1 / 5) (ε / 3)])⟩

/-- **Uniform norm stability of projections**: for every `ε > 0`, there exists `δ > 0` depending
only on `ε` (independent of the C⋆-algebra `A`) such that any `e : A` with `‖e - star e‖ < δ` and
`‖e * e - e‖ < δ` lies within `ε` of a star projection `p : A`. -/
theorem exists_pos_isStarProjection {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {e : A},
      ‖e - star e‖ < δ → ‖e * e - e‖ < δ → ∃ p : A, IsStarProjection p ∧ ‖p - e‖ < ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_pos_isStarProjection_mem hε
  refine ⟨δ, hδ_pos, fun {A} _ {_} hsa hidem ↦ ?_⟩
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨p, -, hp, hpe⟩ := hδ (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) trivial hsa hidem
  exact ⟨p, hp, hpe⟩

section OrthogonalFamily

private def orthoCornerSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    (s : NonUnitalStarSubalgebra ℂ A) (P : A) (hP : IsStarProjection P) :
    NonUnitalStarSubalgebra ℂ A where
  carrier := {a : A | a ∈ s ∧ P * a = 0 ∧ a * P = 0}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by rw [mul_add, ha.2.1, hb.2.1, add_zero],
    by rw [add_mul, ha.2.2, hb.2.2, add_zero]⟩
  zero_mem' := ⟨zero_mem s, mul_zero P, zero_mul P⟩
  mul_mem' ha hb := ⟨mul_mem ha.1 hb.1, by rw [← mul_assoc, ha.2.1, zero_mul],
    by rw [mul_assoc, hb.2.2, mul_zero]⟩
  smul_mem' c _ ha := ⟨SMulMemClass.smul_mem c ha.1, by rw [mul_smul_comm, ha.2.1, smul_zero],
    by rw [smul_mul_assoc, ha.2.2, smul_zero]⟩
  star_mem' ha := ⟨star_mem ha.1,
    by rw [← hP.isSelfAdjoint.star_eq, ← star_mul, ha.2.2, star_zero],
    by rw [← hP.isSelfAdjoint.star_eq, ← star_mul, ha.2.1, star_zero]⟩

private lemma coe_orthoCornerSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    (s : NonUnitalStarSubalgebra ℂ A) (P : A) (hP : IsStarProjection P) :
    (orthoCornerSubalgebra s P hP : Set A) = {a : A | a ∈ s ∧ P * a = 0 ∧ a * P = 0} := rfl

private lemma mem_orthoCornerSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    {s : NonUnitalStarSubalgebra ℂ A} {P : A} {hP : IsStarProjection P} {a : A} :
    a ∈ orthoCornerSubalgebra s P hP ↔ a ∈ s ∧ P * a = 0 ∧ a * P = 0 := Iff.rfl

private lemma isClosed_orthoCornerSubalgebra {A : Type*} [NonUnitalCStarAlgebra A]
    {s : NonUnitalStarSubalgebra ℂ A} (hs : IsClosed (s : Set A)) (P : A)
    (hP : IsStarProjection P) :
    IsClosed (orthoCornerSubalgebra s P hP : Set A) := by
  rw [coe_orthoCornerSubalgebra]
  exact hs.and
    ((isClosed_eq (continuous_const.mul continuous_id) continuous_const).and
      (isClosed_eq (continuous_id.mul continuous_const) continuous_const))

private lemma orthoCorner_compress {A : Type*} [NonUnitalCStarAlgebra A]
    {s : NonUnitalStarSubalgebra ℂ A} {m : ℕ} {p₀ d₀ : Fin m → A}
    {P : A} (hP_def : P = ∑ j : Fin m, p₀ j)
    (hP_mem : P ∈ s) (hP_proj : IsStarProjection P)
    {η δ : ℝ} (hp₀_dist : ∀ j, ‖p₀ j - d₀ j‖ < η)
    {x : A} (hx_mem : x ∈ s) (hx_norm : ‖x‖ ≤ 3)
    (hdx : ∀ j, ‖d₀ j * x‖ < δ) (hxd : ∀ j, ‖x * d₀ j‖ < δ) :
    let y := x - P * x - x * P + P * x * P
    y ∈ orthoCornerSubalgebra s P hP_proj ∧ ‖y - x‖ ≤ 3 * (m : ℝ) * (3 * η + δ) := by
  dsimp only
  set y : A := x - P * x - x * P + P * x * P
  have hy_mem : y ∈ orthoCornerSubalgebra s P hP_proj := mem_orthoCornerSubalgebra.mpr
    ⟨add_mem (sub_mem (sub_mem hx_mem (mul_mem hP_mem hx_mem)) (mul_mem hx_mem hP_mem))
      (mul_mem (mul_mem hP_mem hx_mem) hP_mem),
     by dsimp [y]; simp only [mul_add, mul_sub, ← mul_assoc, hP_proj.isIdempotentElem.eq]; abel,
     by dsimp [y]; simp only [add_mul, sub_mul, mul_assoc, hP_proj.isIdempotentElem.eq]; abel⟩
  have hPx : ‖P * x‖ ≤ (m : ℝ) * (3 * η + δ) := by
    have hj (j : Fin m) : ‖p₀ j * x‖ ≤ 3 * η + δ := by
      rw [show p₀ j * x = (p₀ j - d₀ j) * x + d₀ j * x by rw [sub_mul, sub_add_cancel],
        mul_comm 3 η]
      exact norm_add_le_of_le (norm_mul_le_of_le (hp₀_dist j).le hx_norm) (hdx j).le
    rw [hP_def, Finset.sum_mul]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ ↦ hj j).trans (by simp; linarith))
  have hxP : ‖x * P‖ ≤ (m : ℝ) * (3 * η + δ) := by
    have hj (j : Fin m) : ‖x * p₀ j‖ ≤ 3 * η + δ := by
      rw [show x * p₀ j = x * (p₀ j - d₀ j) + x * d₀ j by rw [mul_sub, sub_add_cancel]]
      exact norm_add_le_of_le (norm_mul_le_of_le hx_norm (hp₀_dist j).le) (hxd j).le
    rw [hP_def, Finset.mul_sum]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ ↦ hj j).trans (by simp; linarith))
  have hPxP : ‖P * x * P‖ ≤ ‖P * x‖ :=
    (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hP_proj.norm_le P))
  have htri : ‖y - x‖ ≤ 2 * ‖P * x‖ + ‖x * P‖ := by
    rw [show y - x = -(P * x) + -(x * P) + P * x * P by dsimp [y]; abel]
    exact norm_add₃_le.trans (by rw [norm_neg, norm_neg]; linarith)
  exact ⟨hy_mem, by linarith⟩

private lemma approx_projection_of_close {A : Type*} [NonUnitalCStarAlgebra A] {x y : A}
    {δ μ δ₁ : ℝ} (hμ_half : μ ≤ 1 / 2) (hδ_δ₁ : δ ≤ δ₁ / 5) (hμ_δ₁ : μ ≤ δ₁ / 10)
    (hx_norm : ‖x‖ < 3) (hx_sa : ‖x - star x‖ < δ) (hx_idem : ‖x * x - x‖ < δ)
    (hy_sub_x : ‖y - x‖ < μ) :
    ‖y - star y‖ < δ₁ ∧ ‖y * y - y‖ < δ₁ := by
  have hy_norm : ‖y‖ ≤ 4 := by linarith [norm_le_norm_add_norm_sub' y x]
  have hy_sa : ‖y - star y‖ < δ₁ := by
    rw [show y - star y = (y - x) + (x - star x) + -star (y - x) by simp [star_sub]]
    exact norm_add₃_le.trans_lt (by rw [norm_neg, norm_star]; linarith [norm_nonneg (y - x)])
  have hy_idem : ‖y * y - y‖ < δ₁ := by
    rw [show y * y - y = (y - x) * y + x * (y - x) + (x * x - x) + -(y - x) by
      simp only [sub_mul, mul_sub]; abel]
    refine norm_add₄_le.trans_lt ?_
    rw [norm_neg]
    linarith [norm_mul_le_of_le hy_sub_x.le hy_norm, norm_mul_le_of_le hx_norm.le hy_sub_x.le]
  exact ⟨hy_sa, hy_idem⟩

private lemma isStarOrtho_of_sum_mul_eq_zero {A : Type*} [NonUnitalCStarAlgebra A] {m : ℕ}
    {p₀ : Fin m → A} (hp₀_proj : ∀ j, IsStarProjection (p₀ j))
    (hp₀_ortho : Pairwise (IsStarOrtho on p₀)) {q : A} (hq_proj : IsStarProjection q)
    (hPq : (∑ k : Fin m, p₀ k) * q = 0) (j : Fin m) :
    IsStarOrtho (p₀ j) q := by
  rw [(hp₀_proj j).isSelfAdjoint.isStarOrtho_iff_mul_eq_zero hq_proj.isSelfAdjoint]
  have hp₀P : p₀ j * ∑ k : Fin m, p₀ k = p₀ j := by
    rw [Finset.mul_sum, Finset.sum_eq_single j
      (fun k _ hkj ↦ (hp₀_ortho hkj.symm).mul_eq_zero' (hp₀_proj k).isSelfAdjoint)
      (fun hj ↦ (hj (Finset.mem_univ j)).elim)]
    exact (hp₀_proj j).isIdempotentElem.eq
  rw [← hp₀P, mul_assoc, hPq, mul_zero]

private lemma exists_pos_pairwise_isStarOrtho_isStarProjection_fin :
    ∀ (m : ℕ) {ε : ℝ}, 0 < ε →
      ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A]
        {s : NonUnitalStarSubalgebra ℂ A}, IsClosed (s : Set A) →
        ∀ {d : Fin m → A}, (∀ i, d i ∈ s) → (∀ i, ‖d i - star (d i)‖ < δ) →
        (∀ i, ‖d i * d i - d i‖ < δ) → (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
        ∃ p : Fin m → A, (∀ i, p i ∈ s) ∧ (∀ i, IsStarProjection (p i)) ∧
          Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε
  | 0, _, _ => ⟨1, zero_lt_one, fun _ _ _ _ _ _ ↦
      ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩⟩
  | m + 1, ε, hε => by
      obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := exists_pos_isStarProjection_mem (half_pos hε)
      set μ : ℝ := min (1 / 2) (min (ε / 2) (δ₁ / 10))
      have hμ_pos : 0 < μ := by positivity
      set η : ℝ := min ε (μ / (12 * (m + 1 : ℝ)))
      obtain ⟨δ_ih, hδ_ih_pos, h_ih⟩ :=
        exists_pos_pairwise_isStarOrtho_isStarProjection_fin m (show 0 < η by positivity)
      set δ : ℝ := min (1 / 2) (min δ_ih (min (δ₁ / 5) (μ / (12 * (m + 1 : ℝ)))))
      refine ⟨δ, by positivity, fun {A} _ {s} hs {d} hd_mem hd_sa hd_idem hd_ortho ↦ ?_⟩
      have hδ_half : δ ≤ 1 / 2 := min_le_left _ _
      have hδ_le_ih : δ ≤ δ_ih := (min_le_right _ _).trans (min_le_left _ _)
      -- Step 1: Stabilize the first `m` approximate projections by the induction hypothesis.
      obtain ⟨p₀, hp₀_mem, hp₀_proj, hp₀_ortho, hp₀_dist⟩ :=
        h_ih hs (d := fun j : Fin m ↦ d j.castSucc) (fun j ↦ hd_mem j.castSucc)
          (fun j ↦ (hd_sa j.castSucc).trans_le hδ_le_ih)
          (fun j ↦ (hd_idem j.castSucc).trans_le hδ_le_ih)
          (fun i j hij ↦
            (hd_ortho i.castSucc j.castSucc (Fin.castSucc_inj.not.mpr hij)).trans_le hδ_le_ih)
      -- Step 2: Compress `x = d (Fin.last m)` into the orthogonal corner of `P = ∑ j, p₀ j`.
      set P : A := ∑ j : Fin m, p₀ j
      have hP_proj : IsStarProjection P :=
        IsStarProjection.sum (fun j _ ↦ hp₀_proj j) (hp₀_ortho.set_pairwise _)
      set x : A := d (Fin.last m)
      have hx_norm : ‖x‖ < 3 := norm_lt_three_of_approx_projection
        ((hd_sa (Fin.last m)).trans_le (hδ_half.trans (by norm_num)))
        ((hd_idem (Fin.last m)).trans_le (hδ_half.trans (by norm_num)))
      obtain ⟨hy_mem_corner, hy_dist_le⟩ :=
        orthoCorner_compress rfl (sum_mem fun j _ ↦ hp₀_mem j) hP_proj
          hp₀_dist (hd_mem (Fin.last m)) hx_norm.le
          (fun j ↦ hd_ortho j.castSucc (Fin.last m) (Fin.castSucc_lt_last j).ne)
          (fun j ↦ hd_ortho (Fin.last m) j.castSucc (Fin.castSucc_lt_last j).ne')
      set y : A := x - P * x - x * P + P * x * P
      have hy_sub_x : ‖y - x‖ < μ := by
        have hδ_le_μ : δ ≤ μ / (12 * (m + 1 : ℝ)) :=
          (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
        have hsum_le : 3 * η + δ ≤ 4 * (μ / (12 * (m + 1 : ℝ))) := by
          linarith [min_le_right ε (μ / (12 * (m + 1 : ℝ)))]
        refine hy_dist_le.trans_lt ?_
        calc 3 * (m : ℝ) * (3 * η + δ)
            ≤ 3 * (m : ℝ) * (4 * (μ / (12 * (m + 1 : ℝ)))) := by gcongr
          _ = ((m : ℝ) / (m + 1 : ℝ)) * μ := by field_simp; ring
          _ < 1 * μ := by gcongr; rw [div_lt_one (by positivity)]; linarith
          _ = μ := one_mul μ
      -- Step 3: Perturb `y` inside the closed corner subalgebra and append `q` to `p₀`.
      obtain ⟨hy_sa, hy_idem⟩ := approx_projection_of_close (min_le_left _ _)
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
        ((min_le_right _ _).trans (min_le_right _ _))
        hx_norm (hd_sa (Fin.last m)) (hd_idem (Fin.last m)) hy_sub_x
      have : IsClosed (orthoCornerSubalgebra s P hP_proj : Set A) :=
        isClosed_orthoCornerSubalgebra hs P hP_proj
      obtain ⟨q, hq_corner, hq_proj, hq_dist⟩ :=
        hδ₁ (s := orthoCornerSubalgebra s P hP_proj) hy_mem_corner hy_sa hy_idem
      obtain ⟨hq_mem, hPq, -⟩ := mem_orthoCornerSubalgebra.mp hq_corner
      have hq_sub_x : ‖q - x‖ < ε := by
        linarith [norm_sub_le_norm_sub_add_norm_sub q y x,
          show μ ≤ ε / 2 from (min_le_right _ _).trans (min_le_left _ _)]
      have hortho_p₀_q := isStarOrtho_of_sum_mul_eq_zero hp₀_proj hp₀_ortho hq_proj hPq
      refine ⟨Fin.snoc p₀ q,
        Fin.lastCases (by simpa using hq_mem) (fun j ↦ by simpa using hp₀_mem j),
        Fin.lastCases (by simpa using hq_proj) (fun j ↦ by simpa using hp₀_proj j), ?_,
        Fin.lastCases (by simpa [x] using hq_sub_x)
          (fun j ↦ by simpa using (hp₀_dist j).trans_le (min_le_left _ _))⟩
      intro i k
      refine Fin.lastCases ?_ (fun i' ↦ ?_) i <;> refine Fin.lastCases ?_ (fun k' ↦ ?_) k <;>
        intro hik <;> simp only [onFun, Fin.snoc_last, Fin.snoc_castSucc]
      exacts [(hik rfl).elim, (hortho_p₀_q k').symm, hortho_p₀_q i',
        hp₀_ortho fun h ↦ hik (congrArg Fin.castSucc h)]

/-- **Uniform norm stability of finite families of pairwise-orthogonal projections in closed
`ℂ`-`⋆`-subalgebras**: for every finite index type `ι` and `ε > 0`, there exists `δ > 0` depending
only on `card ι` and `ε` (independent of the C⋆-algebra `A`) such that any family `d : ι → A` in a
closed non-unital `ℂ`-`⋆`-subalgebra `s` satisfying `‖d i - star (d i)‖ < δ`,
`‖d i * d i - d i‖ < δ`, and `‖d i * d j‖ < δ` for `i ≠ j` lies entrywise within `ε` of a pairwise
star-orthogonal family `p : ι → A` of star projections in `s`. -/
theorem exists_pos_pairwise_isStarOrtho_isStarProjection_mem (ι : Type*) [Finite ι] {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A S : Type*} [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
      [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {d : ι → A},
      (∀ i, d i ∈ s) → (∀ i, ‖d i - star (d i)‖ < δ) → (∀ i, ‖d i * d i - d i‖ < δ) →
      (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
      ∃ p : ι → A, (∀ i, p i ∈ s) ∧ (∀ i, IsStarProjection (p i)) ∧
        Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε := by
  cases nonempty_fintype ι
  let σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    exists_pos_pairwise_isStarOrtho_isStarProjection_fin (Fintype.card ι) hε
  refine ⟨δ, hδ_pos, fun {A S} _ _ _ _ _ {s} hs {d} hd_mem hd_sa hd_idem hd_ortho ↦ ?_⟩
  obtain ⟨p_fin, hp_mem, hp_proj, hp_ortho, hp_dist⟩ :=
    hδ (s := NonUnitalStarSubalgebra.ofClass s) hs (d := fun k ↦ d (σ.symm k))
      (fun k ↦ hd_mem (σ.symm k)) (fun k ↦ hd_sa (σ.symm k)) (fun k ↦ hd_idem (σ.symm k))
      (fun k l hkl ↦ hd_ortho (σ.symm k) (σ.symm l) (σ.symm.injective.ne hkl))
  exact ⟨fun i ↦ p_fin (σ i), fun i ↦ hp_mem (σ i), fun i ↦ hp_proj (σ i),
    fun _ _ hij ↦ hp_ortho (σ.injective.ne hij), fun i ↦ by simpa using hp_dist (σ i)⟩

/-- **Uniform norm stability of finite families of pairwise-orthogonal projections**: for every
finite index type `ι` and `ε > 0`, there exists `δ > 0` depending only on `card ι` and `ε`
(independent of the C⋆-algebra `A`) such that any family `d : ι → A` satisfying
`‖d i - star (d i)‖ < δ`, `‖d i * d i - d i‖ < δ`, and `‖d i * d j‖ < δ` for `i ≠ j` lies
entrywise within `ε` of a pairwise star-orthogonal family `p : ι → A` of star projections. -/
theorem exists_pos_pairwise_isStarOrtho_isStarProjection (ι : Type*) [Finite ι] {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {d : ι → A},
      (∀ i, ‖d i - star (d i)‖ < δ) → (∀ i, ‖d i * d i - d i‖ < δ) →
      (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
      ∃ p : ι → A, (∀ i, IsStarProjection (p i)) ∧
        Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_pos_pairwise_isStarOrtho_isStarProjection_mem ι hε
  refine ⟨δ, hδ_pos, fun {A} _ {_} hd_sa hd_idem hd_ortho ↦ ?_⟩
  have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
  obtain ⟨p, -, hp_proj, hp_ortho, hp_dist⟩ :=
    hδ (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) (fun _ ↦ trivial) hd_sa hd_idem hd_ortho
  exact ⟨p, hp_proj, hp_ortho, hp_dist⟩

end OrthogonalFamily

end TauCeti
