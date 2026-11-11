/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Cumulant.Free
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# The free law of large numbers

For freely independent elements with identical moments, the averages converge in moments to
their common mean. Their cumulants of order `k ≥ 1` are exactly `N^(1-k)` times the cumulants
of one summand. The moment–cumulant formula then gives the limit without positivity, a trace,
selfadjointness, or a topology on the algebra.

For free elements with equal first and second moments, the centered second moment is exactly
the variance divided by `N`. For selfadjoint elements in a star-ordered algebra this also proves
convergence in the state's GNS seminorm. This is
not a claim of operator-norm convergence, and the state need not be faithful or tracial.
The GNS seminorm is Mathlib's `PositiveLinearMap.PreGNS`, with its existing squared-norm
formula; no new representation or completion is constructed here.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 11–12
  (multilinearity and additivity of free cumulants).
-/

public section

open Finset Filter
open scoped Topology

namespace TauCeti

section Algebraic

variable {R A α : Type*} [Field R] [CharZero R] [Ring A] [Algebra R A] [LinearOrder α]
  {φ : A →ₗ[R] R} {a : ℕ → A}

/-- The cumulant of order `#s` of an average of free elements with identical moments is
`N^(1-#s)` times the corresponding cumulant of one summand. The set of positions is nonempty,
and the number of summands is positive. -/
theorem IsFreelyIndependentElements.freeCumulant_inv_natCast_smul_sum
    (h : IsFreelyIndependentElements φ a) (hφ : φ 1 = 1)
    (hm : ∀ j k, φ (a j ^ k) = φ (a 0 ^ k)) {s : Finset α} (hs : s.Nonempty)
    {N : ℕ} (hN : N ≠ 0) :
    freeCumulant φ (fun _ => (N : R)⁻¹ • ∑ j ∈ range N, a j) s =
      (N : R)⁻¹ ^ (#s - 1) * freeCumulant φ (fun _ => a 0) s := by
  classical
  rw [freeCumulant_smul φ (fun _ => (N : R)⁻¹) (fun _ => ∑ j ∈ range N, a j),
    h.freeCumulant_sum hφ (range N) hs]
  simp only [freeCumulant_const_eq_of_apply_pow_eq φ (hm _) s, prod_const,
    sum_const, card_range, nsmul_eq_mul]
  have hn : (N : R) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hk : #s - 1 + 1 = #s := Nat.sub_add_cancel hs.card_pos
  rw [← hk, pow_succ]
  field_simp
  simp [mul_comm]

/-- The exact second-moment error of a free average with equal first and second moments around
its common mean. No positivity, selfadjointness, or trace is needed for this algebraic identity. -/
theorem IsFreelyIndependentElements.apply_average_sub_mean_sq
    (h : IsFreelyIndependentElements φ a) (hφ : φ 1 = 1)
    (hm₁ : ∀ j, φ (a j) = φ (a 0)) (hm₂ : ∀ j, φ (a j ^ 2) = φ (a 0 ^ 2))
    {N : ℕ} (hN : N ≠ 0) :
    φ (((N : R)⁻¹ • ∑ j ∈ range N, a j - algebraMap R A (φ (a 0))) ^ 2) =
      (φ (a 0 ^ 2) - φ (a 0) ^ 2) / N := by
  have hmean : φ ((N : R)⁻¹ • ∑ j ∈ range N, a j) = φ (a 0) := by
    simp [map_sum, hm₁, hN]
  have hc : freeCumulant φ (fun _ : ℕ => (N : R)⁻¹ • ∑ j ∈ range N, a j) {0, 1} =
      (N : R)⁻¹ * freeCumulant φ (fun _ : ℕ => a 0) {0, 1} := by
    rw [freeCumulant_smul φ (fun _ => (N : R)⁻¹) (fun _ => ∑ j ∈ range N, a j),
      h.freeCumulant_sum hφ (range N) (by simp)]
    simp only [freeCumulant_pair φ _ (by omega : (0 : ℕ) < 1), ← sq, hm₁, hm₂,
      prod_const, card_pair (by omega : (0 : ℕ) ≠ 1), sum_const, card_range, nsmul_eq_mul]
    field_simp
  rw [freeCumulant_pair φ _ (by omega : (0 : ℕ) < 1),
    freeCumulant_pair φ _ (by omega : (0 : ℕ) < 1)] at hc
  simp only [← sq, hmean] at hc
  generalize hx : (N : R)⁻¹ • ∑ j ∈ range N, a j = x at hmean hc ⊢
  simp only [sq, sub_mul, mul_sub, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    mul_smul_comm, mul_one, one_mul, map_sub, map_smul, smul_eq_mul, hφ, hmean,
    div_eq_mul_inv] at hc ⊢
  linear_combination hc

end Algebraic

section Limits

variable {𝕜 A α : Type*} [Field 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜]
  [IsTopologicalRing 𝕜] [ContinuousSMul ℚ≥0 𝕜] [Ring A] [Algebra 𝕜 A] [LinearOrder α]
  {φ : A →ₗ[𝕜] 𝕜} {a : ℕ → A}

/-- Cumulants of free averages converge to those of the scalar common mean. -/
theorem IsFreelyIndependentElements.tendsto_freeCumulant_average
    (h : IsFreelyIndependentElements φ a) (hφ : φ 1 = 1)
    (hm : ∀ j k, φ (a j ^ k) = φ (a 0 ^ k)) (s : Finset α) :
    Tendsto (fun N : ℕ =>
      freeCumulant φ (fun _ => (N : 𝕜)⁻¹ • ∑ j ∈ range N, a j) s) atTop
      (𝓝 (freeCumulant φ (fun _ => algebraMap 𝕜 A (φ (a 0))) s)) := by
  classical
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp only [freeCumulant_empty]
    exact tendsto_const_nhds
  have he : (fun N : ℕ =>
      freeCumulant φ (fun _ => (N : 𝕜)⁻¹ • ∑ j ∈ range N, a j) s) =ᶠ[atTop]
      (fun N => (N : 𝕜)⁻¹ ^ (#s - 1) * freeCumulant φ (fun _ => a 0) s) := by
    filter_upwards [eventually_ne_atTop 0] with N hN
    exact h.freeCumulant_inv_natCast_smul_sum hφ hm hs hN
  rcases hs.exists_eq_singleton_or_nontrivial with ⟨i, rfl⟩ | hs'
  · simp only [card_singleton, Nat.sub_self, pow_zero, one_mul, freeCumulant_singleton] at he
    simpa [Algebra.algebraMap_eq_smul_one, hφ] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => φ (a 0)) atTop (𝓝 (φ (a 0)))).congr' he.symm
  · have hk : 0 < #s - 1 := by have := one_lt_card_iff_nontrivial.2 hs'; omega
    rw [freeCumulant_algebraMap φ hφ _ (one_lt_card_iff_nontrivial.2 hs')]
    simpa [zero_pow hk.ne'] using
      (((tendsto_inv_atTop_nhds_zero_nat (𝕜 := 𝕜)).pow (#s - 1)).mul_const
        (freeCumulant φ (fun _ => a 0) s)).congr' he.symm

/-- The free law of large numbers in moments: averages of freely independent elements with
identical moments converge to their common scalar mean. In particular this applies to
identically distributed selfadjoint elements, without a trace assumption. -/
theorem IsFreelyIndependentElements.tendsto_apply_average_pow
    (h : IsFreelyIndependentElements φ a) (hφ : φ 1 = 1)
    (hm : ∀ j k, φ (a j ^ k) = φ (a 0 ^ k)) (n : ℕ) :
    Tendsto (fun N : ℕ => φ (((N : 𝕜)⁻¹ • ∑ j ∈ range N, a j) ^ n)) atTop
      (𝓝 (φ (a 0) ^ n)) := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [pow_zero, hφ]
    exact tendsto_const_nhds
  have hlim := tendsto_finsetSum (univ : Finset (NoncrossingPartition (univ : Finset (Fin n))))
    fun π _ => tendsto_finsetProd π.1.parts fun B _ => h.tendsto_freeCumulant_average hφ hm B
  have hmc (x : A) : φ (x ^ n) =
      ∑ π : NoncrossingPartition (univ : Finset (Fin n)),
        ∏ B ∈ π.1.parts, freeCumulant φ (fun _ : Fin n => x) B := by
    simpa using apply_prod_ofFn_eq_sum_prod_freeCumulant φ hn (fun _ : Fin n => x)
  have hscalar : φ ((algebraMap 𝕜 A (φ (a 0))) ^ n) = φ (a 0) ^ n := by
    rw [← map_pow]
    simp [Algebra.algebraMap_eq_smul_one, hφ]
  simpa only [← hmc, hscalar] using hlim

end Limits

section GNS

open scoped ComplexOrder

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
  [SelfAdjointDecompose A] [Algebra ℂ A] [StarModule ℂ A]
  {φ : A →ₚ[ℂ] ℂ} {a : ℕ → A}

/-- The squared GNS seminorm of the error of a selfadjoint free average with equal first and
second moments is the variance of one summand divided by the number of summands.
Neither faithfulness nor traciality is needed. -/
theorem IsFreelyIndependentElements.norm_toPreGNS_average_sub_mean_sq
    (h : IsFreelyIndependentElements (φ : A →ₗ[ℂ] ℂ) a) (hφ : φ 1 = 1)
    (hm₁ : ∀ j, φ (a j) = φ (a 0)) (hm₂ : ∀ j, φ (a j ^ 2) = φ (a 0 ^ 2))
    (ha : ∀ j, IsSelfAdjoint (a j)) {N : ℕ} (hN : N ≠ 0) :
    ‖φ.toPreGNS ((N : ℂ)⁻¹ • ∑ j ∈ range N, a j - algebraMap ℂ A (φ (a 0)))‖ ^ 2 =
      (φ (a 0 ^ 2) - φ (a 0) ^ 2).re / N := by
  have hstar : star ((N : ℂ)⁻¹ • ∑ j ∈ range N, a j - algebraMap ℂ A (φ (a 0))) =
      (N : ℂ)⁻¹ • ∑ j ∈ range N, a j - algebraMap ℂ A (φ (a 0)) := by
    simp [Algebra.algebraMap_eq_smul_one, ← map_star φ, (ha _).star_eq]
  have hid := φ.preGNS_norm_sq
    (φ.toPreGNS ((N : ℂ)⁻¹ • ∑ j ∈ range N, a j - algebraMap ℂ A (φ (a 0))))
  have hc := h.apply_average_sub_mean_sq hφ hm₁ hm₂ hN
  simp only [LinearMap.coe_ofClass] at hc
  rw [φ.ofPreGNS_toPreGNS, hstar, ← sq, hc, ← Complex.ofReal_pow] at hid
  simpa only [Complex.ofReal_re, Complex.div_natCast_re] using congrArg Complex.re hid

/-- The free law of large numbers in the state's GNS seminorm for selfadjoint elements with
equal first and second moments. No operator-norm convergence or faithful-state assumption is
asserted. -/
theorem IsFreelyIndependentElements.tendsto_norm_toPreGNS_average_sub_mean
    (h : IsFreelyIndependentElements (φ : A →ₗ[ℂ] ℂ) a) (hφ : φ 1 = 1)
    (hm₁ : ∀ j, φ (a j) = φ (a 0)) (hm₂ : ∀ j, φ (a j ^ 2) = φ (a 0 ^ 2))
    (ha : ∀ j, IsSelfAdjoint (a j)) :
    Tendsto (fun N : ℕ =>
      ‖φ.toPreGNS ((N : ℂ)⁻¹ • ∑ j ∈ range N, a j - algebraMap ℂ A (φ (a 0)))‖)
      atTop (𝓝 0) := by
  have he : (fun N : ℕ =>
      ‖φ.toPreGNS ((N : ℂ)⁻¹ • ∑ j ∈ range N, a j - algebraMap ℂ A (φ (a 0)))‖ ^ 2)
      =ᶠ[atTop] (fun N => (φ (a 0 ^ 2) - φ (a 0) ^ 2).re / N) := by
    filter_upwards [eventually_ne_atTop 0] with N hN
    exact h.norm_toPreGNS_average_sub_mean_sq hφ hm₁ hm₂ ha hN
  have hsq := (tendsto_const_div_atTop_nhds_zero_nat
    (φ (a 0 ^ 2) - φ (a 0) ^ 2).re).congr' he.symm
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq

end GNS

end TauCeti
