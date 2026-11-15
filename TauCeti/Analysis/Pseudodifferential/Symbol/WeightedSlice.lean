/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Calculus.CoordinateDeriv.ParametricIntegral
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# The shifted frequency Laplacian `1 - Δ_ξ` and weighted position slices of uniform symbols

For a uniform symbol `b` (`TauCeti.Symbol.IsUniform`) without compact spatial support, the
unweighted position slices `y ↦ b(y, ξ)` need not be integrable. Integrating by parts `2(n + 1)`
times in frequency trades `(1 + ‖y - x‖²) ^ (n + 1)` against `(1 - Δ_ξ) ^ (n + 1)`. This file
builds the symbol-side ingredients:

* `TauCeti.Symbol.oneSubFrequencyLaplacian`: the shifted frequency Laplacian `1 - Δ_ξ` on
  `Symbol n V W m`, preserving uniform estimates and compact spatial support and commuting with
  spatial and frequency derivatives.
* `TauCeti.Symbol.weightedSlice`: the slice `z ↦ (1 + ‖z‖²) ^ (-(n + 1)) • b(x + z, ξ)`, whose
  Fourier transform decays rapidly in `η` uniformly in `x`
  (`TauCeti.Symbol.IsUniform.exists_norm_fourier_weightedSlice_le`), is jointly continuous, and
  differentiates under the integral in `(x, ξ)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* H. Kumano-go, *Pseudo-Differential Operators*, MIT Press, 1981, Chapter 2, §1–§2.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped ContDiff RealInnerProductSpace Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-! ### The shifted frequency Laplacian `1 - Δ_ξ` on symbols -/

section ShiftedFrequencyLaplacian

/-- The shifted frequency Laplacian `1 - Δ_ξ` on symbols of order `m`. In the quantization integral
at `x`, replacing `a` by `(1 - Δ_ξ) a` compensates dividing the input by `1 + ‖x - y‖²`. -/
def oneSubFrequencyLaplacian : Symbol n V W m →ₗ[ℂ] Symbol n V W m :=
  LinearMap.id - inclusion (by linarith) ∘ₗ frequencyLaplacian (m := m)

@[simp]
theorem coefficient_oneSubFrequencyLaplacian (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (oneSubFrequencyLaplacian a).coefficient p =
      a.coefficient p - (frequencyLaplacian a).coefficient p := by simp [oneSubFrequencyLaplacian]

theorem IsUniform.oneSubFrequencyLaplacian {a : Symbol n V W m} (ha : a.IsUniform) :
    (Symbol.oneSubFrequencyLaplacian a).IsUniform := by
  refine ha.sub (IsUniform.inclusion ?_ (by linarith))
  rw [frequencyLaplacian_eq_sum]
  exact IsUniform.sum fun j _ ↦ ((ha.frequencyDeriv j).frequencyDeriv j).inclusion (by linarith)

theorem IsUniform.iterate_oneSubFrequencyLaplacian {a : Symbol n V W m} (ha : a.IsUniform)
    (N : ℕ) : ((Symbol.oneSubFrequencyLaplacian (m := m))^[N] a).IsUniform := by
  induction N with
  | zero => exact ha
  | succ N ih => rw [Function.iterate_succ_apply']; exact ih.oneSubFrequencyLaplacian

theorem HasCompactSpatialSupport.oneSubFrequencyLaplacian {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) :
    (Symbol.oneSubFrequencyLaplacian a).HasCompactSpatialSupport := by
  refine ha.sub (HasCompactSpatialSupport.inclusion ?_ (by linarith))
  rw [frequencyLaplacian_eq_sum]
  exact Finset.sum_induction _ HasCompactSpatialSupport
    (fun _ _ ↦ HasCompactSpatialSupport.add) hasCompactSpatialSupport_zero fun j _ ↦
      ((ha.frequencyDeriv j).frequencyDeriv j).inclusion (by linarith)

theorem HasCompactSpatialSupport.iterate_oneSubFrequencyLaplacian {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (N : ℕ) :
    ((Symbol.oneSubFrequencyLaplacian (m := m))^[N] a).HasCompactSpatialSupport := by
  induction N with
  | zero => exact ha
  | succ N ih => rw [Function.iterate_succ_apply']; exact ih.oneSubFrequencyLaplacian

theorem spatialDeriv_oneSubFrequencyLaplacian (j : Fin n) (a : Symbol n V W m) :
    spatialDeriv j (oneSubFrequencyLaplacian a) = oneSubFrequencyLaplacian (spatialDeriv j a) := by
  ext1; funext ⟨x, ξ⟩
  simp only [oneSubFrequencyLaplacian, LinearMap.sub_apply, LinearMap.id_coe, id_eq,
    LinearMap.comp_apply, map_sub, spatialDeriv_inclusion, frequencyLaplacian_eq_sum, map_sum,
    coefficient_sub, Pi.sub_apply, coefficient_inclusion, coefficient_sum, Finset.sum_apply]
  congr 1; refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [spatialDeriv_frequencyDeriv_comm, spatialDeriv_frequencyDeriv_comm]

theorem spatialDeriv_iterate_oneSubFrequencyLaplacian (N : ℕ) (j : Fin n) (a : Symbol n V W m) :
    spatialDeriv j ((oneSubFrequencyLaplacian (m := m))^[N] a) =
      (oneSubFrequencyLaplacian (m := m))^[N] (spatialDeriv j a) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', spatialDeriv_oneSubFrequencyLaplacian, ih,
      Function.iterate_succ_apply']

theorem frequencyDeriv_oneSubFrequencyLaplacian (j : Fin n) (a : Symbol n V W m) :
    frequencyDeriv j (oneSubFrequencyLaplacian a) =
      oneSubFrequencyLaplacian (frequencyDeriv j a) := by
  ext1; funext ⟨x, ξ⟩
  simp only [oneSubFrequencyLaplacian, LinearMap.sub_apply, LinearMap.id_coe, id_eq,
    LinearMap.comp_apply, map_sub, frequencyDeriv_inclusion, frequencyLaplacian_eq_sum, map_sum,
    coefficient_sub, Pi.sub_apply, coefficient_inclusion, coefficient_sum, Finset.sum_apply]
  congr 1; refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [frequencyDeriv_comm j l, frequencyDeriv_comm j l]

theorem frequencyDeriv_iterate_oneSubFrequencyLaplacian (N : ℕ) (j : Fin n) (a : Symbol n V W m) :
    frequencyDeriv j ((oneSubFrequencyLaplacian (m := m))^[N] a) =
      (oneSubFrequencyLaplacian (m := m - 1))^[N] (frequencyDeriv j a) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', frequencyDeriv_oneSubFrequencyLaplacian, ih,
      Function.iterate_succ_apply']

/-- The coefficient of `(1 - Δ_ξ) ^ N a` depends only on the coefficient of `a`, not on its symbol
order. -/
theorem coefficient_iterate_oneSubFrequencyLaplacian_congr {m₁ m₂ : ℝ} {a₁ : Symbol n V W m₁}
    {a₂ : Symbol n V W m₂} (h : a₁.coefficient = a₂.coefficient) (N : ℕ) :
    ((oneSubFrequencyLaplacian (m := m₁))^[N] a₁).coefficient =
      ((oneSubFrequencyLaplacian (m := m₂))^[N] a₂).coefficient := by
  induction N with
  | zero => exact h
  | succ N ih =>
    funext ⟨x, ξ⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      coefficient_oneSubFrequencyLaplacian, coefficient_oneSubFrequencyLaplacian,
      coefficient_frequencyLaplacian, coefficient_frequencyLaplacian, ih]

end ShiftedFrequencyLaplacian

/-! ### Weighted position slices of a uniform symbol -/

section WeightedSlice

private def displacementWeight (n : ℕ) (z : CoordinateSpace n) : ℝ :=
  (1 + ‖z‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ))

private lemma contDiff_displacementWeight : ContDiff ℝ ∞ (displacementWeight n) :=
  contDiff_one_add_norm_sq_rpow _

private lemma exists_norm_iteratedFDeriv_displacementWeight_le (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ z : CoordinateSpace n,
      ‖iteratedFDeriv ℝ k (displacementWeight n) z‖ ≤
        C * (1 + ‖z‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le (E := CoordinateSpace n)
    (-((n + 1 : ℕ) : ℝ)) k
  refine ⟨max C 0, le_max_right _ _, fun z ↦ (hC z).trans ?_⟩
  have hexp : -((n + 1 : ℕ) : ℝ) - k / 2 ≤ -((n : ℝ) + 1) / 2 := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) k]
  exact mul_le_mul (le_max_left _ _)
    (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖z‖]) hexp)
    (by positivity) (le_max_right _ _)

/-- The weighted position slice `z ↦ (1 + ‖z‖²) ^ (-(n + 1)) • b(x + z, ξ)` of `b` around `x`. -/
def weightedSlice (b : Symbol n V W m) (x ξ z : CoordinateSpace n) : V →L[ℂ] W :=
  displacementWeight n z • b.coefficient (x + z, ξ)

@[simp]
theorem weightedSlice_apply (b : Symbol n V W m) (x ξ z : CoordinateSpace n) :
    weightedSlice b x ξ z = ((1 + ‖z‖ ^ 2) ^ (-((n + 1 : ℕ) : ℝ))) • b.coefficient (x + z, ξ) :=
  (rfl)

theorem contDiff_weightedSlice (b : Symbol n V W m) (x ξ : CoordinateSpace n) :
    ContDiff ℝ ∞ (weightedSlice b x ξ) :=
  contDiff_displacementWeight.smul
    (b.contDiff_coefficient.comp ((contDiff_const.add contDiff_id).prodMk contDiff_const))

theorem weightedSlice_add (b₁ b₂ : Symbol n V W m) (x ξ : CoordinateSpace n) :
    weightedSlice (b₁ + b₂) x ξ = weightedSlice b₁ x ξ + weightedSlice b₂ x ξ :=
  funext fun _ ↦ by simp [smul_add]

theorem weightedSlice_smul (c : ℂ) (b : Symbol n V W m) (x ξ : CoordinateSpace n) :
    weightedSlice (c • b) x ξ = c • weightedSlice b x ξ :=
  funext fun z ↦ smul_comm (displacementWeight n z) c (b.coefficient (x + z, ξ))

theorem weightedSlice_congr {m₁ m₂ : ℝ} {b₁ : Symbol n V W m₁} {b₂ : Symbol n V W m₂}
    (h : b₁.coefficient = b₂.coefficient) (x ξ : CoordinateSpace n) :
    weightedSlice b₁ x ξ = weightedSlice b₂ x ξ := funext fun _ ↦ by simp [h]

private lemma IsUniform.exists_norm_iteratedFDeriv_slice_le {b : Symbol n V W m}
    (hb : b.IsUniform) (i : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ y ξ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ i (fun y ↦ b.coefficient (y, ξ)) y‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  choose C hC0 hC using fun r : Fin i → Fin n ↦ isUniform_iff.mp hb (List.ofFn r) []
  refine ⟨∑ r : Fin i → Fin n, C r, Finset.sum_nonneg fun r _ ↦ hC0 r, fun y ξ ↦ ?_⟩
  rw [Finset.sum_mul]
  refine (norm_iteratedFDeriv_le_sum_coordinateDeriv
    ((b.contDiff_coefficient_slice ξ).of_le (mod_cast le_top)) y).trans
    (Finset.sum_le_sum fun r _ ↦ ?_)
  simpa [mixedDeriv_def, coordinateDeriv_nil] using hC r y ξ

/-- Every `z`-derivative of `weightedSlice b x ξ` is bounded by `C ⟨ξ⟩ ^ m ⟨z⟩ ^ (-(n + 1))`,
uniformly in `x`, `ξ` and `z`. -/
theorem IsUniform.exists_norm_iteratedFDeriv_weightedSlice_le {b : Symbol n V W m}
    (hb : b.IsUniform) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x ξ z : CoordinateSpace n,
      ‖iteratedFDeriv ℝ k (weightedSlice b x ξ) z‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖z‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  choose A hA0 hA using fun i : ℕ ↦ exists_norm_iteratedFDeriv_displacementWeight_le (n := n) i
  choose B hB0 hB using fun i : ℕ ↦ hb.exists_norm_iteratedFDeriv_slice_le i
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A i * B (k - i),
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA0 i)) (hB0 _),
    fun x ξ z ↦ ?_⟩
  have hbsmooth : ContDiff ℝ ∞ fun z ↦ b.coefficient (x + z, ξ) :=
    (b.contDiff_coefficient_slice ξ).comp (contDiff_const.add contDiff_id)
  refine (norm_iteratedFDeriv_smul_le contDiff_displacementWeight hbsmooth z
    (mod_cast le_top)).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_add_left (f := fun y ↦ b.coefficient (y, ξ))]
  have := hA0 i
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (displacementWeight n) z‖ *
        ‖iteratedFDeriv ℝ (k - i) (fun y ↦ b.coefficient (y, ξ)) (x + z)‖
      ≤ (k.choose i : ℝ) * (A i * (1 + ‖z‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)) *
          (B (k - i) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hA i z) (Nat.cast_nonneg _))
          (hB (k - i) (x + z) ξ) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem IsUniform.integrable_iteratedFDeriv_weightedSlice {b : Symbol n V W m}
    (hb : b.IsUniform) (k : ℕ) (x ξ : CoordinateSpace n) :
    Integrable (iteratedFDeriv ℝ k (weightedSlice b x ξ)) := by
  obtain ⟨C, -, hC⟩ := hb.exists_norm_iteratedFDeriv_weightedSlice_le k
  have hc : Continuous (iteratedFDeriv ℝ k (weightedSlice b x ξ)) :=
    (contDiff_weightedSlice b x ξ).continuous_iteratedFDeriv (mod_cast le_top)
  exact (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
    (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))).mono' hc.aestronglyMeasurable (.of_forall (hC x ξ))

theorem IsUniform.integrable_weightedSlice {b : Symbol n V W m} (hb : b.IsUniform)
    (x ξ : CoordinateSpace n) : Integrable (weightedSlice b x ξ) :=
  (hb.integrable_iteratedFDeriv_weightedSlice 0 x ξ).norm.mono'
    (contDiff_weightedSlice b x ξ).continuous.aestronglyMeasurable
    (.of_forall fun z ↦ by rw [norm_iteratedFDeriv_zero])

private lemma IsUniform.exists_integral_norm_iteratedFDeriv_weightedSlice_le {b : Symbol n V W m}
    (hb : b.IsUniform) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x ξ : CoordinateSpace n,
      ∫ z, ‖iteratedFDeriv ℝ k (weightedSlice b x ξ) z‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC0, hC⟩ := hb.exists_norm_iteratedFDeriv_weightedSlice_le k
  set I := ∫ z : CoordinateSpace n, (1 + ‖z‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  refine ⟨C * I, mul_nonneg hC0 (integral_nonneg fun _ ↦ by positivity), fun x ξ ↦ ?_⟩
  refine (integral_mono (hb.integrable_iteratedFDeriv_weightedSlice k x ξ).norm
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul _) (hC x ξ)).trans_eq ?_
  rw [integral_const_mul]; ring

/-- **Rapid decay of the Fourier transform of the weighted position slice.** For a uniform symbol
`b` of order `m`, `(1 + ‖η‖) ^ N ‖𝓕 (weightedSlice b x ξ) η‖ ≤ C ⟨ξ⟩ ^ m` uniformly in `x, ξ, η`. -/
theorem IsUniform.exists_one_add_norm_pow_mul_norm_fourier_weightedSlice_le
    {b : Symbol n V W m} (hb : b.IsUniform) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x ξ η : CoordinateSpace n,
      (1 + ‖η‖) ^ N * ‖𝓕 (weightedSlice b x ξ) η‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := hb.exists_integral_norm_iteratedFDeriv_weightedSlice_le 0
  obtain ⟨C₁, hC₁0, hC₁⟩ := hb.exists_integral_norm_iteratedFDeriv_weightedSlice_le N
  refine ⟨2 ^ N * (C₀ + C₁), by positivity, fun x ξ η ↦ ?_⟩
  rcases le_total ‖η‖ 1 with hη | hη
  · have h2 : (1 + ‖η‖) ^ N ≤ 2 ^ N := by gcongr; linarith
    have h0 : ‖𝓕 (weightedSlice b x ξ) η‖ ≤ (C₀ + C₁) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
      ((Real.norm_fourier_le_integral_norm _ _).trans
        (by simpa [norm_iteratedFDeriv_zero] using hC₀ x ξ)).trans (by gcongr; linarith)
    exact (mul_le_mul h2 h0 (norm_nonneg _) (by positivity)).trans_eq (by ring)
  · have hN : (2 * π * ‖η‖) ^ N * ‖𝓕 (weightedSlice b x ξ) η‖ ≤
        (C₀ + C₁) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
      ((pow_mul_norm_fourier_le_integral_norm_iteratedFDeriv
        ((contDiff_weightedSlice b x ξ).of_le (mod_cast le_top))
        (fun i _ ↦ hb.integrable_iteratedFDeriv_weightedSlice i x ξ) η).trans (hC₁ x ξ)).trans
        (by gcongr; linarith)
    calc (1 + ‖η‖) ^ N * ‖𝓕 (weightedSlice b x ξ) η‖
        ≤ (2 * ‖η‖) ^ N * ‖𝓕 (weightedSlice b x ξ) η‖ := by gcongr; linarith
      _ = 2 ^ N * (‖η‖ ^ N * ‖𝓕 (weightedSlice b x ξ) η‖) := by ring
      _ ≤ 2 ^ N * ((2 * π * ‖η‖) ^ N * ‖𝓕 (weightedSlice b x ξ) η‖) := by
          gcongr; nlinarith [Real.two_le_pi]
      _ ≤ 2 ^ N * ((C₀ + C₁) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by gcongr
      _ = 2 ^ N * (C₀ + C₁) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by ring

/-- For every real `r`, `‖𝓕 (weightedSlice b x ξ) η‖ ≤ C ⟨ξ⟩ ^ m ⟨η⟩ ^ (-r)` uniformly. -/
theorem IsUniform.exists_norm_fourier_weightedSlice_le {b : Symbol n V W m}
    (hb : b.IsUniform) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ξ η : CoordinateSpace n,
      ‖𝓕 (weightedSlice b x ξ) η‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨C, hC0, hC⟩ := hb.exists_one_add_norm_pow_mul_norm_fourier_weightedSlice_le ⌈r⌉₊
  refine ⟨C, hC0, fun x ξ η ↦ ?_⟩
  have hw : (1 + ‖η‖ ^ 2) ^ (r / 2) ≤ (1 + ‖η‖) ^ ⌈r⌉₊ :=
    (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖η‖])
      (by linarith [Nat.le_ceil r])).trans (one_add_norm_sq_rpow_le_one_add_norm_pow η ⌈r⌉₊)
  rw [neg_div, Real.rpow_neg (by positivity), ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  calc ‖𝓕 (weightedSlice b x ξ) η‖ * (1 + ‖η‖ ^ 2) ^ (r / 2)
      ≤ ‖𝓕 (weightedSlice b x ξ) η‖ * (1 + ‖η‖) ^ ⌈r⌉₊ := by gcongr
    _ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by rw [mul_comm]; exact hC x ξ η

/-- The Fourier transform `(p, η) ↦ 𝓕 (weightedSlice b p.1 p.2) η` is jointly continuous. -/
theorem IsUniform.continuous_fourier_weightedSlice {b : Symbol n V W m} (hb : b.IsUniform) :
    Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      𝓕 (weightedSlice b q.1.1 q.1.2) q.2 := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  obtain ⟨C, _, hC⟩ := hb.exists_norm_iteratedFDeriv_weightedSlice_le 0
  set M := (2 : ℝ) ^ |m| * (1 + ‖q₀.1.2‖ ^ 2) ^ (m / 2)
  have heq (q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n) :
      𝓕 (weightedSlice b q.1.1 q.1.2) q.2 =
        ∫ z, (𝐞 (-⟪z, q.2⟫) : ℂ) • weightedSlice b q.1.1 q.1.2 z := by
    simp [Real.fourier_eq, Circle.smul_def]
  simp_rw [heq]
  have hcont_z (z : CoordinateSpace n) :
      Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
        (𝐞 (-⟪z, q.2⟫) : ℂ) • weightedSlice b q.1.1 q.1.2 z := by
    dsimp only [weightedSlice]
    exact (Real.continuous_fourierChar.comp
      (((continuous_const (y := z)).inner continuous_snd).neg)).subtype_val.smul
      ((continuous_const (y := displacementWeight n z)).smul
        (b.contDiff_coefficient.continuous.comp
          (((continuous_fst.comp continuous_fst).add (continuous_const (y := z))).prodMk
            (continuous_snd.comp continuous_fst))))
  refine continuousAt_of_dominated
    (bound := fun z ↦ C * M * (1 + ‖z‖ ^ 2) ^ (-((n : ℝ) + 1) / 2))
    (.of_forall fun q ↦ ((by fun_prop : Continuous fun z ↦ (𝐞 (-⟪z, q.2⟫) : ℂ)).smul
      (contDiff_weightedSlice b q.1.1 q.1.2).continuous).aestronglyMeasurable) ?_
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul _)
    (.of_forall fun z ↦ (hcont_z z).continuousAt)
  filter_upwards [(continuous_snd.comp continuous_fst).continuousAt.preimage_mem_nhds
    (Metric.closedBall_mem_nhds q₀.1.2 one_pos)] with q hq
  refine .of_forall fun z ↦ ?_
  rw [norm_smul, Circle.norm_coe, one_mul, ← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
  have hMq : (1 + ‖q.1.2‖ ^ 2) ^ (m / 2) ≤ M :=
    one_add_norm_sq_rpow_le_of_norm_sub_le_one
      (by simpa only [Set.mem_preimage, Function.comp_apply, Metric.mem_closedBall,
        dist_eq_norm] using hq) m
  exact (hC q.1.1 q.1.2 z).trans (by gcongr)

private lemma differentiableAt_fourierChar_smul_weightedSlice (b : Symbol n V W m)
    (η z : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 (-⟪z, η⟫) : ℂ) • weightedSlice b p.1 p.2 z) p :=
  (((b.contDiff_coefficient.comp
    ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)).differentiable (by simp) p).const_smul
    (displacementWeight n z)).const_smul (𝐞 (-⟪z, η⟫) : ℂ)

private lemma fderiv_fourierChar_smul_weightedSlice (b : Symbol n V W m) (η z : CoordinateSpace n)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
        (𝐞 (-⟪z, η⟫) : ℂ) • weightedSlice b p.1 p.2 z) p v =
      ∑ j, v.1 j • ((𝐞 (-⟪z, η⟫) : ℂ) • weightedSlice (spatialDeriv j b) p.1 p.2 z) +
        ∑ j, v.2 j • ((𝐞 (-⟪z, η⟫) : ℂ) • weightedSlice (frequencyDeriv j b) p.1 p.2 z) := by
  rw [fderiv_apply_eq_sum_coordinateDeriv (differentiableAt_fourierChar_smul_weightedSlice b η z p)]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ ↦ congrArg _ ?_
  · have hd : DifferentiableAt ℝ (fun x' ↦ b.coefficient (x' + z, p.2)) p.1 :=
      (differentiableAt_comp_add_right z).2
        ((b.contDiff_coefficient_slice p.2).differentiable (by simp) (p.1 + z))
    rw [coordinateDeriv_cons, coordinateDeriv_nil]; dsimp only [weightedSlice]
    rw [← Pi.smul_def, ← Pi.smul_def, fderiv_const_smul (hd.const_smul _), fderiv_const_smul hd,
      smul_apply, smul_apply, fderiv_comp_add_right (f := fun y ↦ b.coefficient (y, p.2)),
      fderiv_coefficient_single]
  · have hd : DifferentiableAt ℝ (fun ξ' ↦ b.coefficient (p.1 + z, ξ')) p.2 :=
      (b.contDiff_coefficient.comp (contDiff_prodMk_right (p.1 + z))).differentiable (by simp) p.2
    rw [coordinateDeriv_cons, coordinateDeriv_nil]; dsimp only [weightedSlice]
    rw [← Pi.smul_def, ← Pi.smul_def, fderiv_const_smul (hd.const_smul _), fderiv_const_smul hd,
      smul_apply, smul_apply, fderiv_coefficient_slice_single]

private lemma IsUniform.exists_sum_norm_deriv_weightedSlice_ball_le {b : Symbol n V W m}
    (hb : b.IsUniform) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    ∃ D, ∀ z : CoordinateSpace n, ∀ p ∈ Metric.ball p₀ 1,
      (∑ j, ‖weightedSlice (Symbol.spatialDeriv j b) p.1 p.2 z‖) +
          ∑ j, ‖weightedSlice (Symbol.frequencyDeriv j b) p.1 p.2 z‖ ≤
        D * (1 + ‖z‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  choose C₁ hC₁0 hC₁ using fun j : Fin n ↦
    (hb.spatialDeriv j).exists_norm_iteratedFDeriv_weightedSlice_le 0
  choose C₂ hC₂0 hC₂ using fun j : Fin n ↦
    (hb.frequencyDeriv j).exists_norm_iteratedFDeriv_weightedSlice_le 0
  set M₁ := (2 : ℝ) ^ |m| * (1 + ‖p₀.2‖ ^ 2) ^ (m / 2)
  set M₂ := (2 : ℝ) ^ |m - 1| * (1 + ‖p₀.2‖ ^ 2) ^ ((m - 1) / 2)
  refine ⟨(∑ j, C₁ j * M₁) + ∑ j, C₂ j * M₂, fun z p hp ↦ ?_⟩
  have hp₂ : ‖p.2 - p₀.2‖ ≤ 1 := by
    rw [← dist_eq_norm]
    exact (((le_max_right _ _).trans Prod.dist_eq.ge).trans (Metric.mem_ball.1 hp).le)
  have hMp₁ : (1 + ‖p.2‖ ^ 2) ^ (m / 2) ≤ M₁ := one_add_norm_sq_rpow_le_of_norm_sub_le_one hp₂ m
  have hMp₂ : (1 + ‖p.2‖ ^ 2) ^ ((m - 1) / 2) ≤ M₂ :=
    one_add_norm_sq_rpow_le_of_norm_sub_le_one hp₂ (m - 1)
  rw [add_mul, Finset.sum_mul, Finset.sum_mul]
  gcongr with j _ j _
  · have := hC₁0 j
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]; exact (hC₁ j p.1 p.2 z).trans (by gcongr)
  · have := hC₂0 j
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]; exact (hC₂ j p.1 p.2 z).trans (by gcongr)

/-- Differentiation of `p ↦ 𝓕 (weightedSlice b p.1 p.2) η` under the Fourier integral. -/
theorem IsUniform.differentiableAt_fourier_weightedSlice_and_fderiv {b : Symbol n V W m}
    (hb : b.IsUniform) (η : CoordinateSpace n) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (fun p ↦ 𝓕 (weightedSlice b p.1 p.2) η) p₀ ∧
      ∀ v, fderiv ℝ (fun p ↦ 𝓕 (weightedSlice b p.1 p.2) η) p₀ v =
        ∑ j, v.1 j • 𝓕 (weightedSlice (Symbol.spatialDeriv j b) p₀.1 p₀.2) η +
          ∑ j, v.2 j • 𝓕 (weightedSlice (Symbol.frequencyDeriv j b) p₀.1 p₀.2) η := by
  obtain ⟨D, hD⟩ := hb.exists_sum_norm_deriv_weightedSlice_ball_le p₀
  have hchar : Continuous fun z ↦ (𝐞 (-⟪z, η⟫) : ℂ) := by fun_prop
  have key := differentiableAt_integral_and_fderiv_apply_eq_sum
    (differentiableAt_fourierChar_smul_weightedSlice b η)
    (fderiv_fourierChar_smul_weightedSlice b η)
    (fun p ↦ (hb.integrable_weightedSlice p.1 p.2).norm.mono'
      (hchar.smul (contDiff_weightedSlice b p.1 p.2).continuous).aestronglyMeasurable
      (.of_forall fun z ↦ by simp [norm_smul]))
    (fun j p ↦ hchar.smul
      (contDiff_weightedSlice (Symbol.spatialDeriv j b) p.1 p.2).continuous)
    (fun j p ↦ hchar.smul
      (contDiff_weightedSlice (Symbol.frequencyDeriv j b) p.1 p.2).continuous)
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul D) p₀
    (fun z p hp ↦ by simpa only [norm_smul, Circle.norm_coe, one_mul] using hD z p hp)
  have hFour {m₁ : ℝ} (b' : Symbol n V W m₁) (p : CoordinateSpace n × CoordinateSpace n) :
      𝓕 (weightedSlice b' p.1 p.2) η = ∫ z, (𝐞 (-⟪z, η⟫) : ℂ) • weightedSlice b' p.1 p.2 z := by
    simp [Real.fourier_eq, Circle.smul_def]
  simpa only [hFour] using key

end WeightedSlice

end Symbol

end TauCeti
