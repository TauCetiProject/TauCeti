/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.AnnularRing.Eval.Basic
public import TauCeti.NumberTheory.Padics.AnnularRing.Gauge

/-!
# Annulus evaluations and the `T`-adic Tate gauge on `H[1/T]`

This file compares the annulus evaluations `TauCeti.AnnularRing.localizedEval₂` and
`TauCeti.AnnularRing.localizedEvalAt` with the `T`-adic Tate gauge
`TauCeti.Huber.awayNormedCommRing` of radius `α ∈ (0, 1)` on any localization `A = H[1/T]` away
from `T`.

Every annulus evaluation is continuous for the `T`-adic Tate gauge of any radius `α ∈ (0, 1)`
(`TauCeti.AnnularRing.continuous_localizedEval₂_awayNormedCommRing`). However, for evaluation at a
point `t` in a complete normed division ring `K / ℚ_[p]` with `p⁻¹ < ‖t‖ < 1`:
* when `α = ‖t‖`, evaluation is contractive: `‖localizedEvalAt t x‖ ≤ ‖x‖`
  (`TauCeti.AnnularRing.norm_localizedEvalAt_le_of_eq`);
* when `α ≠ ‖t‖`, evaluation is not bounded by any constant multiple of the `α`-gauge norm, and in
  particular is not Lipschitz (`TauCeti.AnnularRing.not_exists_bound_localizedEvalAt_of_ne`,
  `TauCeti.AnnularRing.not_lipschitzWith_localizedEvalAt_of_ne`): for `α < ‖t‖` the powers `T ^ n`
  blow up `(‖t‖ / α) ^ n`, while for `‖t‖ < α` the negative powers `T ^ (-n)` blow up
  `(α / ‖t‖) ^ n`.

## Main results

* `TauCeti.AnnularRing.continuous_localizedEval₂_awayNormedCommRing`: continuity of
  `localizedEval₂` for the `α`-gauge.
* `TauCeti.AnnularRing.norm_localizedEvalAt_le_of_eq`: contractivity of `localizedEvalAt` for the
  `‖t‖`-gauge.
* `TauCeti.AnnularRing.not_exists_bound_localizedEvalAt_of_ne`,
  `TauCeti.AnnularRing.not_lipschitzWith_localizedEvalAt_of_ne`: failure of boundedness and
  Lipschitz continuity when `α ≠ ‖t‖`.

## References

* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

open Filter Topology

namespace TauCeti.AnnularRing

private theorem p_pos {p : ℕ} [Fact p.Prime] : (0 : ℝ) < p :=
  Nat.cast_pos.2 (Fact.out : p.Prime).pos

section LocalizedEval₂

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedRing K] [CompleteSpace K]
  (f : ℤ_[p] →+* K) (hf : ∃ C : ℝ, ∀ a : ℤ_[p], ‖f a‖ ≤ C * ‖a‖)
  (t : Kˣ) (ht : ‖(t : K)‖ < 1) (htinv : ‖((t⁻¹ : Kˣ) : K)‖ < p)
  {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
  [IsLocalization.Away (T : AnnularRing p) A]

/-- Every annulus evaluation `H[1/T] →+* K` is continuous for the `T`-adic Tate gauge of any radius
`α ∈ (0, 1)`. -/
theorem continuous_localizedEval₂_awayNormedCommRing {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    letI := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
    Continuous (localizedEval₂ f hf t ht htinv (A := A)) := by
  let := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
  exact continuous_localizedEval₂ f hf t ht htinv
    (Huber.hasBasis_nhds_zero_awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors
      hα₀ hα₁)

end LocalizedEval₂

section LocalizedEvalAt

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedDivisionRing K] [NormedAlgebra ℚ_[p] K]
  [CompleteSpace K] {A : Type*} [CommRing A] [Algebra (AnnularRing p) A]
  [IsLocalization.Away (T : AnnularRing p) A]

/-- When the `T`-gauge radius equals `‖t‖`, evaluation at `t` is contractive:
`‖localizedEvalAt t x‖ ≤ ‖x‖`. -/
theorem norm_localizedEvalAt_le_of_eq (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (x : A) :
    letI := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors
      ((inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)).trans ht₀) ht₁
    ‖localizedEvalAt t ht₀ ht₁ x‖ ≤ ‖x‖ := by
  have htpos : 0 < ‖t‖ := (inv_pos.2 (p_pos (p := p))).trans ht₀
  let := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors htpos ht₁
  rw [Huber.norm_awayNormedCommRing]
  set d := Huber.awayTateNormDatum
    (Huber.hasBasis_nhds_zero_awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors
      htpos ht₁)
    htpos ht₁
  refine le_of_forall_gt fun r hr ↦ ?_
  obtain ⟨n, hmem, hnr⟩ := (Huber.tateNorm_lt_iff d).1 hr
  rw [Huber.awayTateNormDatum_pseudoUniformizer, Huber.awayTateNormDatum_ringOfDefinition] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hx : x = (((IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit ^ n : Aˣ) : A) *
      algebraMap (AnnularRing p) A a :=
    (T_zpow_neg_mul_eq_iff (p := p) n x (algebraMap (AnnularRing p) A a)).mp ha.symm
  have hr' : ‖t‖ ^ n < r := by simpa only [d, Huber.awayTateNormDatum_radius] using hnr
  calc ‖localizedEvalAt t ht₀ ht₁ x‖
      = ‖t ^ n * evalAt t ht₀ ht₁ a‖ := by
        rw [hx, map_mul, localizedEvalAt_T_zpow, localizedEvalAt_algebraMap]
    _ = ‖t‖ ^ n * ‖evalAt t ht₀ ht₁ a‖ := by rw [norm_mul, norm_zpow]
    _ ≤ ‖t‖ ^ n := mul_le_of_le_one_right (zpow_nonneg (norm_nonneg _) _)
        (norm_evalAt_le_one t ht₀ ht₁ a)
    _ < r := hr'

/-- For any `T`-gauge radius `α ∈ (0, 1)` different from `‖t‖`, evaluation at `t` is not bounded
by any constant multiple of the `α`-gauge norm (even though it is continuous for the `T`-adic
topology): positive powers `T ^ n` witness unboundedness when `α < ‖t‖`, and negative powers
`T ^ (-n)` witness it when `‖t‖ < α`. -/
theorem not_exists_bound_localizedEvalAt_of_ne {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (hne : α ≠ ‖t‖) :
    letI := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
    ¬ ∃ C : ℝ, ∀ x : A, ‖localizedEvalAt t ht₀ ht₁ x‖ ≤ C * ‖x‖ := by
  let := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
  have : Nontrivial A := (algebraMap_injective (p := p) (A := A)).nontrivial
  have : NormOneClass A :=
    Huber.normOneClass_awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
  rintro ⟨C, hC⟩
  have htpos : 0 < ‖t‖ := (inv_pos.2 (p_pos (p := p))).trans ht₀
  have hpow (k : ℤ) : ‖t‖ ^ k ≤ C * α ^ k := by
    set u : Aˣ := (IsLocalization.Away.algebraMap_isUnit (T : AnnularRing p)).unit
    have hnorm_u : ‖((u ^ k : Aˣ) : A)‖ = α ^ k := by
      have h1 := Huber.norm_pseudoUniformizer_zpow_mul_awayNormedCommRing
        (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁ k 1
      rw [mul_one, norm_one, mul_one] at h1
      exact h1
    have hc := hC ((u ^ k : Aˣ) : A)
    rw [hnorm_u] at hc
    rwa [localizedEvalAt_T_zpow, norm_zpow] at hc
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨n, hn⟩ :=
      ((tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hα₀).2 hlt)).eventually_gt_atTop C).exists
    have hle : (‖t‖ / α) ^ n ≤ C := by
      rw [div_pow, div_le_iff₀ (pow_pos hα₀ n)]
      simpa only [zpow_natCast] using hpow (n : ℤ)
    exact hn.not_ge hle
  · obtain ⟨n, hn⟩ :=
      ((tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div htpos).2 hgt)).eventually_gt_atTop C).exists
    have h := hpow (-(n : ℤ))
    rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast] at h
    have hle : (α / ‖t‖) ^ n ≤ C := calc
      (α / ‖t‖) ^ n = α ^ n * (‖t‖ ^ n)⁻¹ := by rw [div_pow, div_eq_mul_inv]
      _ ≤ α ^ n * (C * (α ^ n)⁻¹) := mul_le_mul_of_nonneg_left h (pow_nonneg hα₀.le n)
      _ = C := by field_simp
    exact hn.not_ge hle

/-- In particular, evaluation at `t` is not Lipschitz for the `α`-gauge whenever `α ≠ ‖t‖`. -/
theorem not_lipschitzWith_localizedEvalAt_of_ne {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    (t : K) (ht₀ : (p : ℝ)⁻¹ < ‖t‖) (ht₁ : ‖t‖ < 1) (hne : α ≠ ‖t‖) :
    letI := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
    ¬ ∃ L : NNReal, LipschitzWith L (localizedEvalAt (A := A) t ht₀ ht₁) := by
  let := Huber.awayNormedCommRing (T : AnnularRing p) A T_mem_nonZeroDivisors hα₀ hα₁
  rintro ⟨L, hL⟩
  refine not_exists_bound_localizedEvalAt_of_ne (A := A) hα₀ hα₁ t ht₀ ht₁ hne ⟨(L : ℝ), fun x ↦ ?_⟩
  have := hL.dist_le_mul x 0
  simpa only [map_zero, dist_zero_right] using this

end LocalizedEvalAt

end TauCeti.AnnularRing
