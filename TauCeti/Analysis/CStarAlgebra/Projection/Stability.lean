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

Single star projections and finite pairwise-orthogonal projection families are **uniformly
norm-stable** across all (not necessarily unital) C⋆-algebras: for every `ε > 0` (and finite `ι`),
there exists `δ > 0` depending only on `ε` (and `card ι`) such that any `δ`-approximate projection
(or family) in a closed non-unital `ℂ`-`⋆`-subalgebra `s` lies within `ε` of an exact one in `s`.
For self-adjoint `a` with `‖a * a - a‖ < 1 / 4`, `spectralProjectionIoiHalf a` lies within
`2 * ‖a * a - a‖` of `a`, and the truncated inverse square root powers polar perturbation in
`TauCeti.Analysis.CStarAlgebra.PartialIsometry`.

## Main results

* `TauCeti.spectralProjectionIoiHalf`, `IsStarProjection.eq_of_le_of_norm_sub_lt_one`,
  `IsSelfAdjoint.norm_spectralProjectionIoiHalf_sub_le`,
  `TauCeti.exists_isStarProjection_mem_of_approx`, `TauCeti.exists_pos_isStarProjection[_mem]`,
  `TauCeti.exists_pos_pairwise_isStarOrtho_isStarProjection[_mem]`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23.
* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C*-Algebras*,
  Cambridge Univ. Press (2000), Lemma 2.2.6.
-/

public section

open Function
open scoped NonUnitalContinuousFunctionalCalculus

/-- Star projections `p ≤ q` in a star-ordered C⋆-algebra with `‖p - q‖ < 1` are equal. -/
theorem IsStarProjection.eq_of_le_of_norm_sub_lt_one {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hle : p ≤ q) (h : ‖p - q‖ < 1) : p = q :=
  hp.eq_of_mul_eq_left_of_norm_sub_lt_one hq ((hp.le_iff_mul_eq_left hq).mp hle) h

namespace TauCeti
variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- `cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator 1) a`, the `(1 / 2, ∞)` spectral projection when `a` is
self-adjoint with `1 / 2 ∉ quasispectrum ℝ a`, and `0` otherwise. -/
noncomputable def spectralProjectionIoiHalf (a : A) : A :=
  cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) a

/-- Unfold `TauCeti.spectralProjectionIoiHalf`. -/
theorem spectralProjectionIoiHalf_def (a : A) :
    spectralProjectionIoiHalf a = cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) a := (rfl)

/-- `spectralProjectionIoiHalf a` is always a star projection. -/
@[simp] theorem isStarProjection_spectralProjectionIoiHalf (a : A) :
    IsStarProjection (spectralProjectionIoiHalf a) :=
  isStarProjection_cfcₙ_indicator a (Set.Ioi (1 / 2 : ℝ))

/-- The `(1 / 2, ∞)` spectral projection of `0` is `0`. -/
theorem spectralProjectionIoiHalf_zero : spectralProjectionIoiHalf (0 : A) = 0 := by
  simp [spectralProjectionIoiHalf_def]

/-- `spectralProjectionIoiHalf a` belongs to every closed non-unital `𝕜'`-`⋆`-subalgebra containing
`a` (for any scalar action `𝕜'` over `ℝ`, including `ℝ` and `ℂ`). -/
theorem spectralProjectionIoiHalf_mem {𝕜' S : Type*} [Monoid 𝕜'] [MulAction 𝕜' A] [SetLike S A]
    [NonUnitalSubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A] [SMulMemClass S 𝕜' A]
    [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {a : A} (ha : a ∈ s) :
    spectralProjectionIoiHalf a ∈ s :=
  spectralProjectionIoiHalf_def a ▸ cfcₙ_mem (𝕜 := ℝ) (𝕜' := 𝕜') _ ha
end TauCeti

namespace IsSelfAdjoint
open TauCeti
variable {A : Type*} [NonUnitalCStarAlgebra A] {a : A}

/-- Pointwise quasispectral estimate `|t * t - t| ≤ ‖a * a - a‖` for self-adjoint `a`. -/
theorem abs_mul_self_sub_le_norm (ha : IsSelfAdjoint a) {t : ℝ} (ht : t ∈ quasispectrum ℝ a) :
    |t * t - t| ≤ ‖a * a - a‖ := by
  have hsq : ContinuousOn (fun x : ℝ ↦ x * x) (quasispectrum ℝ a) := by fun_prop
  simpa [Real.norm_eq_abs, cfcₙ_sub (fun x : ℝ ↦ x * x) (fun x : ℝ ↦ x) a hsq (mul_zero 0)
      continuousOn_id rfl, cfcₙ_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ x) a continuousOn_id rfl
      continuousOn_id rfl, cfcₙ_id' ℝ a] using
    norm_apply_le_norm_cfcₙ (fun x : ℝ ↦ x * x - x) a ht (hsq.sub continuousOn_id) (by simp) ha

/-- When `IsSelfAdjoint a` and `‖a * a - a‖ < 1 / 4`, `1 / 2 ∉ quasispectrum ℝ a`. -/
theorem notMem_quasispectrum_half_of_norm_mul_self_sub_lt (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) : (1 / 2 : ℝ) ∉ quasispectrum ℝ a := fun hmem ↦ by
  have hle := ha.abs_mul_self_sub_le_norm hmem; norm_num at hle; linarith

/-- Continuity of `indicator (Ioi (1 / 2)) 1` on `quasispectrum ℝ a` when `‖a * a - a‖ < 1 / 4`. -/
theorem continuousOn_indicator_Ioi_half (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    ContinuousOn ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) (quasispectrum ℝ a) :=
  continuousOn_const.continuousOn_indicator_of_disjoint_frontier <| by
    simpa [frontier_Ioi] using ha.notMem_quasispectrum_half_of_norm_mul_self_sub_lt h

/-- Continuous non-unital `⋆`-algebra homomorphisms preserve `TauCeti.spectralProjectionIoiHalf`
whenever `1 / 2 ∉ quasispectrum ℝ a`. -/
theorem map_spectralProjectionIoiHalf {B F : Type*} [NonUnitalCStarAlgebra B] [FunLike F A B]
    [NonUnitalAlgHomClass F ℝ A B] [StarHomClass F A B] (ha : IsSelfAdjoint a)
    (h : (1 / 2 : ℝ) ∉ quasispectrum ℝ a) (φ : F) (hφ : Continuous φ) :
    φ (spectralProjectionIoiHalf a) = spectralProjectionIoiHalf (φ a) :=
  NonUnitalStarAlgHomClass.map_cfcₙ φ _ a
    (continuousOn_const.continuousOn_indicator_of_disjoint_frontier <| by
      rwa [frontier_Ioi, Set.disjoint_singleton_left]) (by simp) hφ ha (ha.map φ)

/-- Sharp bound `‖spectralProjectionIoiHalf a - a‖ ≤ 2 * ‖a * a - a‖` when `‖a * a - a‖ < 1 / 4`. -/
theorem norm_spectralProjectionIoiHalf_sub_le (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    ‖spectralProjectionIoiHalf a - a‖ ≤ 2 * ‖a * a - a‖ := by
  set f : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator 1
  rw [spectralProjectionIoiHalf_def, show cfcₙ f a - a = cfcₙ (fun t : ℝ ↦ f t - t) a by
    rw [cfcₙ_sub f (fun t : ℝ ↦ t) a (ha.continuousOn_indicator_Ioi_half h) (by simp [f])
      continuousOn_id rfl, cfcₙ_id' ℝ a]]
  refine norm_cfcₙ_le fun t ht ↦ ?_; rw [Real.norm_eq_abs]; dsimp only [f]
  have hprod : |t| * |1 - t| ≤ ‖a * a - a‖ := by
    rw [abs_sub_comm, ← abs_mul, show t * (t - 1) = t * t - t by ring]
    exact ha.abs_mul_self_sub_le_norm ht
  by_cases hgt : (1 / 2 : ℝ) < t
  · simp only [Set.indicator_of_mem (Set.mem_Ioi.mpr hgt), Pi.one_apply]
    nlinarith [abs_of_pos (by linarith : 0 < t), abs_nonneg (1 - t)]
  · simp only [Set.indicator_of_notMem (Set.mem_Ioi.not.mpr hgt), zero_sub, abs_neg]
    nlinarith [abs_of_pos (by linarith : 0 < 1 - t), abs_nonneg t]

/-- Continuity of `(Set.Ioi (1 / 2)).indicator fun t ↦ (√t)⁻¹` on `quasispectrum ℝ a` when
`‖a * a - a‖ < 1 / 4`. -/
theorem continuousOn_indicator_Ioi_half_inv_sqrt (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    ContinuousOn ((Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) (quasispectrum ℝ a) :=
  ContinuousOn.continuousOn_indicator_of_disjoint_frontier
    (Real.continuous_sqrt.continuousOn.inv₀ fun _ ht ↦
      (Real.sqrt_pos.mpr (by linarith [show (1 / 2 : ℝ) < _ from interior_subset ht])).ne')
    (by simpa [frontier_Ioi] using ha.notMem_quasispectrum_half_of_norm_mul_self_sub_lt h)

/-- For self-adjoint `a` with `‖a * a - a‖ < 1 / 4`, `w = cfcₙ ((Ioi (1 / 2)).indicator (√·)⁻¹) a`
satisfies `w * a * w = spectralProjectionIoiHalf a`. -/
theorem cfcₙ_indicator_Ioi_half_inv_sqrt_mul_self_mul (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) :
    cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) a * a *
        cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) a =
      spectralProjectionIoiHalf a := by
  have hg := ha.continuousOn_indicator_Ioi_half_inv_sqrt h
  rw [spectralProjectionIoiHalf_def]; conv_lhs => lhs; rhs; rw [← cfcₙ_id' ℝ a]
  rw [← cfcₙ_mul _ (fun t : ℝ ↦ t) a hg (by simp) continuousOn_id rfl,
    ← cfcₙ_mul _ _ a (hg.fun_mul (continuousOn_id' _)) (by simp) hg (by simp)]
  refine cfcₙ_congr fun t _ ↦ ?_; by_cases ht : (1 / 2 : ℝ) < t
  · simp only [Set.indicator_of_mem (Set.mem_Ioi.mpr ht), Pi.one_apply]
    field_simp [(Real.sqrt_pos.mpr (by linarith)).ne']; exact (Real.sq_sqrt (by linarith)).symm
  · simp only [Set.indicator_of_notMem (Set.mem_Ioi.not.mpr ht), zero_mul]

/-- Estimate `‖cfcₙ ((Ioi (1 / 2)).indicator (√·)⁻¹) a - spectralProjectionIoiHalf a‖ ≤`
`4 * ‖a * a - a‖` for self-adjoint `a` with `‖a * a - a‖ < 1 / 4`. -/
theorem norm_cfcₙ_indicator_Ioi_half_inv_sqrt_sub_spectralProjectionIoiHalf_le
    (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    ‖cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) a - spectralProjectionIoiHalf a‖ ≤
      4 * ‖a * a - a‖ := by
  rw [spectralProjectionIoiHalf_def, ← cfcₙ_sub _ _ a
    (ha.continuousOn_indicator_Ioi_half_inv_sqrt h) (by simp)
    (ha.continuousOn_indicator_Ioi_half h) (by simp)]
  refine norm_cfcₙ_le fun t ht ↦ ?_; rw [Real.norm_eq_abs]; by_cases hgt : (1 / 2 : ℝ) < t
  · simp only [Set.indicator_of_mem (Set.mem_Ioi.mpr hgt), Pi.one_apply]
    have hsq : √t ^ 2 = t := Real.sq_sqrt (by linarith)
    have hs : (1 / 2 : ℝ) < √t := by nlinarith [Real.sqrt_nonneg t]
    have h1 : |t * t - t| = |(√t)⁻¹ - 1| * (t * √t * (1 + √t)) := by
      rw [show t * t - t = -(((√t)⁻¹ - 1) * (t * √t * (1 + √t))) by
          field_simp [(Real.sqrt_pos.mpr (by linarith)).ne']; nlinarith,
        abs_neg, abs_mul, abs_of_pos (show 0 < t * √t * (1 + √t) by positivity)]
    have : (1 / 4 : ℝ) ≤ t * √t := by nlinarith
    nlinarith [ha.abs_mul_self_sub_le_norm ht, abs_nonneg ((√t)⁻¹ - 1),
      show (3 / 8 : ℝ) ≤ t * √t * (1 + √t) by nlinarith]
  · simp only [Set.indicator_of_notMem (Set.mem_Ioi.not.mpr hgt), sub_self, abs_zero]; positivity
end IsSelfAdjoint

/-- Every star projection `p` is fixed by `TauCeti.spectralProjectionIoiHalf`. -/
@[simp] theorem IsStarProjection.spectralProjectionIoiHalf_eq {A : Type*} [NonUnitalCStarAlgebra A]
    {p : A} (hp : IsStarProjection p) : TauCeti.spectralProjectionIoiHalf p = p := by
  have hz : p * p - p = 0 := sub_eq_zero.mpr hp.isIdempotentElem.eq
  simpa [hz, sub_eq_zero] using
    hp.isSelfAdjoint.norm_spectralProjectionIoiHalf_sub_le (by simp [hz])

namespace TauCeti

section
variable {A : Type*} [NonUnitalCStarAlgebra A]

private lemma symmetrize_bounds (e : A) :
    let a : A := (2 : ℝ)⁻¹ • (e + star e)
    IsSelfAdjoint a ∧ ‖a - e‖ = (1 / 2) * ‖e - star e‖ ∧
      ‖a * a - a‖ ≤ ‖e * e - e‖ + (1 / 4) * ‖e - star e‖ ^ 2 := by
  set a : A := (2 : ℝ)⁻¹ • (e + star e)
  have hsub : a - e = (2 : ℝ)⁻¹ • (star e - e) :=
    smul_right_injective A (by norm_num : (2 : ℝ) ≠ 0) <| by
      simp only [a, smul_sub, smul_smul]; norm_num
      simp only [one_smul, ← one_add_one_eq_two, add_smul]; abel
  have hid : a * a - a = (2 : ℝ)⁻¹ • ((e * e - e) + star (e * e - e)) -
      (4 : ℝ)⁻¹ • ((e - star e) * (e - star e)) :=
    smul_right_injective A (by norm_num : (4 : ℝ) ≠ 0) <| by
      simp only [a, smul_mul_smul_comm, smul_sub, smul_smul]; norm_num
      simp only [one_smul, ← one_add_one_eq_two, add_smul, mul_add, add_mul, sub_mul, mul_sub]; abel
  refine ⟨by rw [IsSelfAdjoint, star_smul, star_trivial, star_add, star_star, add_comm],
    by rw [hsub, norm_smul, Real.norm_of_nonneg (by positivity), norm_sub_rev, one_div], ?_⟩
  rw [hid]; refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    linarith [norm_add_le (e * e - e) (star (e * e - e)), norm_star (e * e - e)]
  · rw [norm_smul, Real.norm_of_nonneg (by positivity), one_div, sq]; gcongr; exact norm_mul_le _ _

/-- Every approximate projection with `‖x - star x‖ < 1` and `‖x * x - x‖ < 1` has `‖x‖ < 3`. -/
theorem norm_lt_three_of_approx_projection {x : A} (hsa : ‖x - star x‖ < 1)
    (hidem : ‖x * x - x‖ < 1) : ‖x‖ < 3 := by
  obtain ⟨ha_sa, ha_sub, ha_def⟩ := symmetrize_bounds x
  set a : A := (2 : ℝ)⁻¹ • (x + star x)
  have ha_norm : ‖a‖ * ‖a‖ - ‖a‖ ≤ ‖a * a - a‖ := by
    simpa [← CStarRing.norm_star_mul_self, ha_sa.star_eq] using norm_sub_norm_le (a * a) a
  nlinarith [norm_nonneg (x - star x), norm_le_norm_add_norm_sub a x]

/-- **Quantitative norm stability of projections** in a closed non-unital `ℂ`-`⋆`-subalgebra `s`:
if `e ∈ s`, `‖e - star e‖ < δ`, `‖e * e - e‖ < δ` with `δ ≤ 1 / 5`, there exists a star projection
`p ∈ s` with `‖p - e‖ < 3 * δ`. -/
theorem exists_isStarProjection_mem_of_approx {S : Type*} [SetLike S A] [NonUnitalSubringClass S A]
    [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {e : A} (hes : e ∈ s)
    {δ : ℝ} (hδ : δ ≤ 1 / 5) (hsa : ‖e - star e‖ < δ) (hidem : ‖e * e - e‖ < δ) :
    ∃ p ∈ s, IsStarProjection p ∧ ‖p - e‖ < 3 * δ := by
  obtain ⟨ha_sa, ha_sub, ha_def⟩ := symmetrize_bounds e
  set a : A := (2 : ℝ)⁻¹ • (e + star e)
  have ha_mem : (2 : ℝ)⁻¹ • (e + star e) ∈ s := Complex.coe_smul (2 : ℝ)⁻¹ (e + star e) ▸
    SMulMemClass.smul_mem (((2 : ℝ)⁻¹ : ℝ) : ℂ) (add_mem hes (star_mem hes))
  refine ⟨spectralProjectionIoiHalf a, spectralProjectionIoiHalf_mem (𝕜' := ℂ) ha_mem,
    isStarProjection_spectralProjectionIoiHalf a, ?_⟩
  nlinarith [norm_nonneg (e - star e),
    ha_sa.norm_spectralProjectionIoiHalf_sub_le (by nlinarith [norm_nonneg (e - star e)]),
    norm_sub_le_norm_sub_add_norm_sub (spectralProjectionIoiHalf a) a e]
end

/-- **Uniform norm stability of projections in closed `ℂ`-`⋆`-subalgebras**: for every `ε > 0`,
there exists `δ > 0` (independent of `A` and `s`) such that any `e ∈ s` with `‖e - star e‖ < δ`
and `‖e * e - e‖ < δ` lies within `ε` of a star projection `p ∈ s`. -/
theorem exists_pos_isStarProjection_mem {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A S : Type*} [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
      [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {e : A},
      e ∈ s → ‖e - star e‖ < δ → ‖e * e - e‖ < δ →
      ∃ p ∈ s, IsStarProjection p ∧ ‖p - e‖ < ε :=
  ⟨min (1 / 5) (ε / 3), by positivity, fun hes hsa hidem ↦
    let ⟨p, hps, hp, hpe⟩ := exists_isStarProjection_mem_of_approx hes (min_le_left _ _) hsa hidem
    ⟨p, hps, hp, hpe.trans_le (by linarith [min_le_right (1 / 5) (ε / 3)])⟩⟩

/-- **Uniform norm stability of projections**: for every `ε > 0`, there exists `δ > 0` (independent
of `A`) such that any `e : A` with `‖e - star e‖ < δ` and `‖e * e - e‖ < δ` lies within `ε` of a
star projection `p : A`. -/
theorem exists_pos_isStarProjection {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {e : A},
      ‖e - star e‖ < δ → ‖e * e - e‖ < δ → ∃ p : A, IsStarProjection p ∧ ‖p - e‖ < ε :=
  let ⟨δ, hδ_pos, hδ⟩ := exists_pos_isStarProjection_mem hε
  ⟨δ, hδ_pos, fun {A} _ {_} hsa hidem ↦ by
    have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
    obtain ⟨p, -, h⟩ := hδ (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) trivial hsa hidem; exact ⟨p, h⟩⟩

section
variable {A : Type*} [NonUnitalCStarAlgebra A]

private def orthoCornerSubalgebra (s : NonUnitalStarSubalgebra ℂ A) (P : A)
    (hP : IsStarProjection P) : NonUnitalStarSubalgebra ℂ A where
  carrier := {a : A | a ∈ s ∧ P * a = 0 ∧ a * P = 0}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1,
    by simp [mul_add, ha.2.1, hb.2.1], by simp [add_mul, ha.2.2, hb.2.2]⟩
  zero_mem' := ⟨zero_mem s, mul_zero P, zero_mul P⟩
  mul_mem' ha hb := ⟨mul_mem ha.1 hb.1,
    by rw [← mul_assoc, ha.2.1, zero_mul], by rw [mul_assoc, hb.2.2, mul_zero]⟩
  smul_mem' c _ ha := ⟨SMulMemClass.smul_mem c ha.1,
    by simp [mul_smul_comm, ha.2.1], by simp [smul_mul_assoc, ha.2.2]⟩
  star_mem' ha := ⟨star_mem ha.1, by rw [← hP.isSelfAdjoint.star_eq, ← star_mul, ha.2.2, star_zero],
    by rw [← hP.isSelfAdjoint.star_eq, ← star_mul, ha.2.1, star_zero]⟩

private lemma coe_orthoCornerSubalgebra (s : NonUnitalStarSubalgebra ℂ A) (P : A)
    (hP : IsStarProjection P) :
    (orthoCornerSubalgebra s P hP : Set A) = {a : A | a ∈ s ∧ P * a = 0 ∧ a * P = 0} := rfl

private lemma mem_orthoCornerSubalgebra {s : NonUnitalStarSubalgebra ℂ A} {P : A}
    {hP : IsStarProjection P} {a : A} :
    a ∈ orthoCornerSubalgebra s P hP ↔ a ∈ s ∧ P * a = 0 ∧ a * P = 0 := Iff.rfl

private lemma isClosed_orthoCornerSubalgebra {s : NonUnitalStarSubalgebra ℂ A}
    (hs : IsClosed (s : Set A)) (P : A) (hP : IsStarProjection P) :
    IsClosed (orthoCornerSubalgebra s P hP : Set A) :=
  coe_orthoCornerSubalgebra s P hP ▸ hs.and
    ((isClosed_eq (continuous_const.mul continuous_id) continuous_const).and
      (isClosed_eq (continuous_id.mul continuous_const) continuous_const))

private lemma orthoCorner_compress {s : NonUnitalStarSubalgebra ℂ A} {m : ℕ} {p₀ d₀ : Fin m → A}
    {P : A} (hP_def : P = ∑ j : Fin m, p₀ j) (hP_mem : P ∈ s) (hP_proj : IsStarProjection P)
    {η δ : ℝ} (hp₀_dist : ∀ j, ‖p₀ j - d₀ j‖ < η) {x : A} (hx_mem : x ∈ s) (hx_norm : ‖x‖ ≤ 3)
    (hdx : ∀ j, ‖d₀ j * x‖ < δ) (hxd : ∀ j, ‖x * d₀ j‖ < δ) :
    let y := x - P * x - x * P + P * x * P
    y ∈ orthoCornerSubalgebra s P hP_proj ∧ ‖y - x‖ ≤ 3 * (m : ℝ) * (3 * η + δ) := by
  dsimp only; set y : A := x - P * x - x * P + P * x * P
  have hPx : ‖P * x‖ ≤ (m : ℝ) * (3 * η + δ) := by
    rw [hP_def, Finset.sum_mul]
    refine (norm_sum_le _ _).trans <| (Finset.sum_le_card_nsmul _ _ (η * 3 + δ) fun j _ ↦ by
      rw [show p₀ j * x = (p₀ j - d₀ j) * x + d₀ j * x by rw [sub_mul, sub_add_cancel]]
      exact norm_add_le_of_le (norm_mul_le_of_le (hp₀_dist j).le hx_norm) (hdx j).le).trans_eq
      (by simp; ring)
  have hxP : ‖x * P‖ ≤ (m : ℝ) * (3 * η + δ) := by
    rw [hP_def, Finset.mul_sum]
    refine (norm_sum_le _ _).trans <| (Finset.sum_le_card_nsmul _ _ (3 * η + δ) fun j _ ↦ by
      rw [show x * p₀ j = x * (p₀ j - d₀ j) + x * d₀ j by rw [mul_sub, sub_add_cancel]]
      exact norm_add_le_of_le (norm_mul_le_of_le hx_norm (hp₀_dist j).le) (hxd j).le).trans_eq
      (by simp; ring)
  refine ⟨mem_orthoCornerSubalgebra.mpr
    ⟨add_mem (sub_mem (sub_mem hx_mem (mul_mem hP_mem hx_mem)) (mul_mem hx_mem hP_mem))
        (mul_mem (mul_mem hP_mem hx_mem) hP_mem),
      by dsimp [y]; simp only [mul_add, mul_sub, ← mul_assoc, hP_proj.isIdempotentElem.eq]; abel,
      by dsimp [y]; simp only [add_mul, sub_mul, mul_assoc, hP_proj.isIdempotentElem.eq]; abel⟩, ?_⟩
  rw [show y - x = -(P * x) + -(x * P) + P * x * P by dsimp [y]; abel]
  refine norm_add₃_le.trans ?_; rw [norm_neg, norm_neg]
  linarith [norm_mul_le_of_le hPx (hP_proj.norm_le _)]

private lemma approx_projection_of_close {x y : A} {δ μ δ₁ : ℝ} (hμ_half : μ ≤ 1 / 2)
    (hδ_δ₁ : δ ≤ δ₁ / 5) (hμ_δ₁ : μ ≤ δ₁ / 10) (hx_norm : ‖x‖ < 3) (hx_sa : ‖x - star x‖ < δ)
    (hx_idem : ‖x * x - x‖ < δ) (hy_sub_x : ‖y - x‖ < μ) :
    ‖y - star y‖ < δ₁ ∧ ‖y * y - y‖ < δ₁ := by
  have hy_norm : ‖y‖ ≤ 4 := by linarith [norm_le_norm_add_norm_sub' y x]
  refine ⟨?_, ?_⟩
  · rw [show y - star y = (y - x) + (x - star x) + -star (y - x) by simp [star_sub]]
    exact norm_add₃_le.trans_lt (by rw [norm_neg, norm_star]; linarith [norm_nonneg (y - x)])
  · rw [show y * y - y = (y - x) * y + x * (y - x) + (x * x - x) + -(y - x) by
      simp only [sub_mul, mul_sub]; abel]
    refine norm_add₄_le.trans_lt ?_; rw [norm_neg]
    linarith [norm_mul_le_of_le hy_sub_x.le hy_norm, norm_mul_le_of_le hx_norm.le hy_sub_x.le]

private lemma isStarOrtho_of_sum_mul_eq_zero {m : ℕ} {p₀ : Fin m → A}
    (hp₀_proj : ∀ j, IsStarProjection (p₀ j)) (hp₀_ortho : Pairwise (IsStarOrtho on p₀))
    {q : A} (hq_proj : IsStarProjection q) (hPq : (∑ k : Fin m, p₀ k) * q = 0) (j : Fin m) :
    IsStarOrtho (p₀ j) q := by
  rw [(hp₀_proj j).isSelfAdjoint.isStarOrtho_iff_mul_eq_zero hq_proj.isSelfAdjoint,
    ← show p₀ j * ∑ k : Fin m, p₀ k = p₀ j by
      rw [Finset.mul_sum, Finset.sum_eq_single_of_mem j (Finset.mem_univ j) fun k _ hkj ↦
          (hp₀_ortho hkj.symm).mul_eq_zero' (hp₀_proj k).isSelfAdjoint,
        (hp₀_proj j).isIdempotentElem.eq],
    mul_assoc, hPq, mul_zero]
end

private lemma exists_pos_pairwise_isStarOrtho_isStarProjection_fin :
    ∀ (m : ℕ) {ε : ℝ}, 0 < ε →
      ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {s : NonUnitalStarSubalgebra ℂ A},
        IsClosed (s : Set A) → ∀ {d : Fin m → A}, (∀ i, d i ∈ s) → (∀ i, ‖d i - star (d i)‖ < δ) →
        (∀ i, ‖d i * d i - d i‖ < δ) → (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
        ∃ p : Fin m → A, (∀ i, p i ∈ s) ∧ (∀ i, IsStarProjection (p i)) ∧
          Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε
  | 0, _, _ => ⟨1, zero_lt_one, fun _ _ _ _ _ _ ↦
      ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩⟩
  | m + 1, ε, hε => by
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := exists_pos_isStarProjection_mem (half_pos hε)
    set μ : ℝ := min (1 / 2) (min (ε / 2) (δ₁ / 10)); have : 0 < μ := by positivity
    set η : ℝ := min ε (μ / (12 * (m + 1 : ℝ)))
    obtain ⟨δ_ih, hδ_ih_pos, h_ih⟩ :=
      exists_pos_pairwise_isStarOrtho_isStarProjection_fin m (by positivity : 0 < η)
    set δ : ℝ := min (1 / 2) (min δ_ih (min (δ₁ / 5) η))
    refine ⟨δ, by positivity, fun {A} _ {s} hs {d} hd_mem hd_sa hd_idem hd_ortho ↦ ?_⟩
    have hδ_ih : δ ≤ δ_ih := (min_le_right _ _).trans (min_le_left _ _)
    -- Step 1: Stabilize the first `m` approximate projections by the induction hypothesis.
    obtain ⟨p₀, hp₀_mem, hp₀_proj, hp₀_ortho, hp₀_dist⟩ := h_ih hs (d := fun j ↦ d j.castSucc)
      (fun j ↦ hd_mem j.castSucc) (fun j ↦ (hd_sa _).trans_le hδ_ih)
      (fun j ↦ (hd_idem _).trans_le hδ_ih)
      (fun i j hij ↦ (hd_ortho _ _ (Fin.castSucc_inj.not.mpr hij)).trans_le hδ_ih)
    -- Step 2: Compress `x = d (Fin.last m)` into the orthogonal corner of `P = ∑ j, p₀ j`.
    set P : A := ∑ j : Fin m, p₀ j; set x : A := d (Fin.last m)
    have hP_proj : IsStarProjection P :=
      IsStarProjection.sum (fun j _ ↦ hp₀_proj j) (hp₀_ortho.set_pairwise _)
    have hx_norm : ‖x‖ < 3 := norm_lt_three_of_approx_projection
      ((hd_sa _).trans_le ((min_le_left _ _).trans (by norm_num)))
      ((hd_idem _).trans_le ((min_le_left _ _).trans (by norm_num)))
    obtain ⟨hy_mem_corner, hy_dist_le⟩ := orthoCorner_compress rfl (sum_mem fun j _ ↦ hp₀_mem j)
      hP_proj hp₀_dist (hd_mem _) hx_norm.le (fun j ↦ hd_ortho _ _ (Fin.castSucc_lt_last j).ne)
      (fun j ↦ hd_ortho _ _ (Fin.castSucc_lt_last j).ne')
    set y : A := x - P * x - x * P + P * x * P
    have hy_sub_x : ‖y - x‖ < μ := hy_dist_le.trans_lt <| by
      have hη : 12 * (m + 1 : ℝ) * η ≤ μ := (le_div_iff₀' (by positivity)).mp (min_le_right _ _)
      have hδη : δ ≤ η := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      nlinarith [Nat.cast_nonneg (α := ℝ) m, show (0 : ℝ) < η by positivity]
    -- Step 3: Perturb `y` inside the closed corner subalgebra and append `q` to `p₀`.
    obtain ⟨hy_sa, hy_idem⟩ := approx_projection_of_close (min_le_left _ _)
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      ((min_le_right _ _).trans (min_le_right _ _)) hx_norm (hd_sa _) (hd_idem _) hy_sub_x
    have := isClosed_orthoCornerSubalgebra hs P hP_proj
    obtain ⟨q, hq_corner, hq_proj, hq_dist⟩ := hδ₁ hy_mem_corner hy_sa hy_idem
    obtain ⟨hq_mem, hPq, -⟩ := mem_orthoCornerSubalgebra.mp hq_corner
    have hortho := isStarOrtho_of_sum_mul_eq_zero hp₀_proj hp₀_ortho hq_proj hPq
    refine ⟨Fin.snoc p₀ q, Fin.lastCases (by simpa) (fun j ↦ by simpa using hp₀_mem j),
      Fin.lastCases (by simpa) (fun j ↦ by simpa using hp₀_proj j), fun i k ↦ ?_,
      Fin.lastCases (by simpa [x] using (show ‖q - x‖ < ε by
        linarith [norm_sub_le_norm_sub_add_norm_sub q y x,
          show μ ≤ ε / 2 from (min_le_right _ _).trans (min_le_left _ _)]))
        (fun j ↦ by simpa using (hp₀_dist j).trans_le (min_le_left _ _))⟩
    refine Fin.lastCases ?_ (fun i' ↦ ?_) i <;> refine Fin.lastCases ?_ (fun k' ↦ ?_) k <;>
      intro hik <;> simp only [onFun, Fin.snoc_last, Fin.snoc_castSucc]
    exacts [(hik rfl).elim, (hortho k').symm, hortho i',
      hp₀_ortho fun h ↦ hik (congrArg Fin.castSucc h)]

/-- **Uniform norm stability of finite pairwise-orthogonal projection families in closed
`ℂ`-`⋆`-subalgebras**: for finite `ι` and `ε > 0`, there exists `δ > 0` (independent of `A` and
`s`) such that any `δ`-approximately orthogonal projection family in `s` lies entrywise within `ε`
of a pairwise star-orthogonal family of star projections in `s`. -/
theorem exists_pos_pairwise_isStarOrtho_isStarProjection_mem (ι : Type*) [Finite ι] {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A S : Type*} [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A]
      [SMulMemClass S ℂ A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {d : ι → A},
      (∀ i, d i ∈ s) → (∀ i, ‖d i - star (d i)‖ < δ) → (∀ i, ‖d i * d i - d i‖ < δ) →
      (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
      ∃ p : ι → A, (∀ i, p i ∈ s) ∧ (∀ i, IsStarProjection (p i)) ∧
        Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε := by
  cases nonempty_fintype ι; let σ := Fintype.equivFin ι
  obtain ⟨δ, hδ_pos, hδ⟩ := exists_pos_pairwise_isStarOrtho_isStarProjection_fin (Fintype.card ι) hε
  refine ⟨δ, hδ_pos, fun {A S} _ _ _ _ _ {s} hs {d} hd_mem hd_sa hd_idem hd_ortho ↦ ?_⟩
  obtain ⟨p, hp_mem, hp_proj, hp_ortho, hp_dist⟩ := hδ (s := NonUnitalStarSubalgebra.ofClass s) hs
    (d := fun k ↦ d (σ.symm k)) (fun _ ↦ hd_mem _) (fun _ ↦ hd_sa _) (fun _ ↦ hd_idem _)
    (fun _ _ hkl ↦ hd_ortho _ _ (σ.symm.injective.ne hkl))
  exact ⟨fun i ↦ p (σ i), fun _ ↦ hp_mem _, fun _ ↦ hp_proj _,
    fun _ _ hij ↦ hp_ortho (σ.injective.ne hij), fun i ↦ by simpa using hp_dist (σ i)⟩

/-- **Uniform norm stability of finite pairwise-orthogonal projection families**: for finite `ι`
and `ε > 0`, there exists `δ > 0` (independent of `A`) such that any `δ`-approximately orthogonal
projection family lies entrywise within `ε` of a pairwise star-orthogonal family of projections. -/
theorem exists_pos_pairwise_isStarOrtho_isStarProjection (ι : Type*) [Finite ι] {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ {A : Type*} [NonUnitalCStarAlgebra A] {d : ι → A},
      (∀ i, ‖d i - star (d i)‖ < δ) → (∀ i, ‖d i * d i - d i‖ < δ) →
      (∀ i j, i ≠ j → ‖d i * d j‖ < δ) →
      ∃ p : ι → A, (∀ i, IsStarProjection (p i)) ∧
        Pairwise (IsStarOrtho on p) ∧ ∀ i, ‖p i - d i‖ < ε :=
  let ⟨δ, hδ_pos, hδ⟩ := exists_pos_pairwise_isStarOrtho_isStarProjection_mem ι hε
  ⟨δ, hδ_pos, fun {A} _ {_} hd_sa hd_idem hd_ortho ↦ by
    have : IsClosed ((⊤ : NonUnitalStarSubalgebra ℂ A) : Set A) := isClosed_univ
    obtain ⟨p, -, h⟩ := hδ (s := (⊤ : NonUnitalStarSubalgebra ℂ A)) (fun _ ↦ trivial)
      hd_sa hd_idem hd_ortho; exact ⟨p, h⟩⟩
end TauCeti
