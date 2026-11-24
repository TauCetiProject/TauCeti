/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import TauCeti.Analysis.Calculus.CoordinateDeriv.ParametricIntegral
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# The composition symbol for uniform symbols

For a symbol `b` of order `m` with estimates uniform in the position (`Symbol.IsUniform`),
integrating the oscillatory composition integral by parts `n + 1` times in `z = y - x` gives

`(a #_u b)(x, ξ) = ∫ (((1 - Δ_ξ)^(n+1) a)(x, ξ + 2πη)) ∘ 𝓕_z(⟨z⟩^(-2(n+1)) b(x + z, ξ))(η) dη`.

This file defines `TauCeti.Symbol.uniformSharp` (`a.uniformSharp b hb`), proves its position and
frequency Leibniz rules, shows `TauCeti.Symbol.IsUniform.uniformSharp` and
`TauCeti.Symbol.uniformSharp_eq_sharp`, and establishes bounded pointwise continuity in the right
factor (`TauCeti.Symbol.exists_bound_and_tendsto_coefficient_uniformSharp`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §2.
-/

public section

open MeasureTheory Real FourierTransform Filter Function
open scoped ContDiff FourierTransform RealInnerProductSpace SchwartzMap Topology

noncomputable section

namespace TauCeti.Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### Iterating `1 - Δ_ξ` on symbols -/

section OneSubFreqLaplacian

private def oneSubFreqLaplacian : Symbol n W U m' →ₗ[ℂ] Symbol n W U m' :=
  LinearMap.id - Symbol.inclusion (m' := m') (by linarith) ∘ₗ frequencyLaplacian (m := m')

private theorem spatialDeriv_iterate_oneSubFreqLaplacian (j : Fin n) (k : ℕ)
    (a : Symbol n W U m') :
    Symbol.spatialDeriv j (oneSubFreqLaplacian^[k] a) =
      oneSubFreqLaplacian^[k] (Symbol.spatialDeriv j a) :=
  Function.Commute.iterate_right (fun b ↦ by
    simp only [oneSubFreqLaplacian, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, spatialDeriv_inclusion, frequencyLaplacian_eq_sum, map_sum,
      spatialDeriv_frequencyDeriv_comm]) k a

private theorem frequencyDeriv_iterate_oneSubFreqLaplacian (j : Fin n) (k : ℕ)
    (a : Symbol n W U m') :
    Symbol.frequencyDeriv j (oneSubFreqLaplacian^[k] a) =
      oneSubFreqLaplacian^[k] (Symbol.frequencyDeriv j a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; ext1; funext ⟨x, ξ⟩
    simp only [oneSubFreqLaplacian, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, coefficient_sub, Pi.sub_apply, frequencyDeriv_inclusion, coefficient_inclusion,
      frequencyLaplacian_eq_sum, map_sum, Finset.sum_apply, coefficient_sum, frequencyDeriv_comm j]

private theorem isUniform_iterate_oneSubFreqLaplacian {a : Symbol n W U m'} (ha : a.IsUniform)
    (k : ℕ) : (oneSubFreqLaplacian^[k] a).IsUniform := by
  induction k with
  | zero => exact ha
  | succ k ih =>
    rw [Function.iterate_succ_apply', oneSubFreqLaplacian, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, frequencyLaplacian_eq_sum]
    exact ih.sub ((IsUniform.sum fun j _ ↦
      ((ih.frequencyDeriv j).frequencyDeriv j).inclusion (by linarith)).inclusion (by linarith))

private theorem coefficient_iterate_oneSubFreqLaplacian_congr {m₁ m₂ : ℝ}
    {a₁ : Symbol n W U m₁} {a₂ : Symbol n W U m₂} (h : a₁.coefficient = a₂.coefficient) (k : ℕ) :
    (oneSubFreqLaplacian^[k] a₁).coefficient = (oneSubFreqLaplacian^[k] a₂).coefficient := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have hstep {m : ℝ} (b : Symbol n W U m) :
        oneSubFreqLaplacian b = b - Symbol.inclusion (by linarith) (frequencyLaplacian b) := rfl
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hstep, hstep]
    funext ⟨x, ξ⟩; simp [coefficient_frequencyLaplacian, ih]

private theorem map_iterate_oneSubFreqLaplacian {V' U' : Type*}
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] [NormedAddCommGroup U'] [NormedSpace ℂ U']
    (Φ : (W →L[ℂ] U) →L[ℝ] (V' →L[ℂ] U')) (k : ℕ) (a : Symbol n W U m') :
    (oneSubFreqLaplacian^[k] a).map Φ = oneSubFreqLaplacian^[k] (a.map Φ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    ext1; funext ⟨x, ξ⟩; simp [oneSubFreqLaplacian, frequencyLaplacian_eq_sum, frequencyDeriv_map]

private theorem hasCompactSpatialSupport_iterate_oneSubFreqLaplacian {a : Symbol n W U m'}
    (ha : a.HasCompactSpatialSupport) (k : ℕ) :
    (oneSubFreqLaplacian^[k] a).HasCompactSpatialSupport := by
  induction k with
  | zero => exact ha
  | succ k ih =>
    rw [Function.iterate_succ_apply', oneSubFreqLaplacian, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, frequencyLaplacian_eq_sum]
    refine ih.sub (HasCompactSpatialSupport.inclusion ?_ (by linarith))
    classical
    refine Finset.induction_on Finset.univ (by simpa using hasCompactSpatialSupport_zero)
      fun j s hj hs ↦ ?_
    rw [Finset.sum_insert hj]
    exact (((ih.frequencyDeriv j).frequencyDeriv j).inclusion (by linarith)).add hs

private theorem quantizeSchwartzValue_iterate_smulLeftCLM_one_add_norm_sub_sq
    {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℂ G₂]
    (k : ℕ) (c : Symbol n G₁ G₂ m') (v : 𝓢(CoordinateSpace n, G₁)) (x : CoordinateSpace n) :
    quantizeSchwartzValue c.coefficient
        ((SchwartzMap.smulLeftCLM G₁ (fun y ↦ (1 : ℝ) + ‖x - y‖ ^ 2))^[k] v) x =
      quantizeSchwartzValue (oneSubFreqLaplacian^[k] c).coefficient v x := by
  have h2 : (fun y : CoordinateSpace n ↦ ‖x - y‖ ^ 2).HasTemperateGrowth := by
    simpa using hasTemperateGrowth_norm_sub_pow x 1
  have h12 : (fun y : CoordinateSpace n ↦ (1 : ℝ) + ‖x - y‖ ^ 2).HasTemperateGrowth :=
    (by fun_prop : (fun _ : CoordinateSpace n ↦ (1 : ℝ)).HasTemperateGrowth).add h2
  induction k generalizing c v with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply']
    set d := oneSubFreqLaplacian^[k] c
    have hsplit : SchwartzMap.smulLeftCLM G₁ (fun y ↦ (1 : ℝ) + ‖x - y‖ ^ 2) v =
        v + SchwartzMap.smulLeftCLM G₁ (fun y ↦ ‖x - y‖ ^ 2) v := by
      ext y; rw [SchwartzMap.smulLeftCLM_apply_apply h12, add_apply,
        SchwartzMap.smulLeftCLM_apply_apply h2, add_smul, one_smul]
    obtain ⟨C, -, hC⟩ := d.exists_bound_coefficient_slice x
    have hd : d.coefficient = (oneSubFreqLaplacian d +
        Symbol.inclusion (by linarith) (frequencyLaplacian d)).coefficient := by
      ext p; simp [oneSubFreqLaplacian]
    rw [hsplit,
      quantizeSchwartzValue_add_right (d.continuous_coefficient_slice x).aestronglyMeasurable hC,
      d.quantizeSchwartzValue_smulLeftCLM_norm_sub_sq, hd, coefficient_add,
      quantizeSchwartzValue_coefficient_add,
      coefficient_inclusion (by linarith) (frequencyLaplacian d), add_neg_cancel_right]

end OneSubFreqLaplacian

/-! ### Quantitative decay and regularity of the weighted Fourier slice -/

section WeightedSlice

private def spatialWeight (n : ℕ) (z : CoordinateSpace n) : ℝ := (1 + ‖z‖ ^ 2) ^ (-((n : ℝ) + 1))

private theorem spatialWeight_nonneg (z : CoordinateSpace n) : 0 ≤ spatialWeight n z := by
  unfold spatialWeight; positivity

private theorem contDiff_spatialWeight : ContDiff ℝ ∞ (spatialWeight n) :=
  contDiff_one_add_norm_sq_rpow (-((n : ℝ) + 1))

private theorem integrable_spatialWeight : Integrable (spatialWeight n) :=
  (integrable_rpow_neg_one_add_norm_sq (E := CoordinateSpace n) (r := 2 * ((n : ℝ) + 1))
    (by rw [finrank_euclideanSpace_fin]; linarith)).congr
    (.of_forall fun z ↦ by unfold spatialWeight; ring_nf)

private theorem exists_norm_iteratedFDeriv_spatialWeight_le (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ z : CoordinateSpace n,
      ‖iteratedFDeriv ℝ k (spatialWeight n) z‖ ≤ C * spatialWeight n z := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le (E := CoordinateSpace n)
    (-((n : ℝ) + 1)) k
  exact ⟨max C 0, le_max_right _ _, fun z ↦ (hC z).trans (mul_le_mul (le_max_left _ _)
    (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖z‖])
      (by linarith [Nat.cast_nonneg (α := ℝ) k])) (by positivity) (le_max_right _ _))⟩

/-- Uniform symbols have spatial Fréchet derivatives bounded uniformly in `x` at each order `k`. -/
theorem IsUniform.exists_norm_iteratedFDeriv_slice_le {b : Symbol n V W m} (hb : b.IsUniform)
    (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ k (fun y ↦ b.coefficient (y, ξ)) x‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  choose A hA0 hA using isUniform_iff.1 hb
  refine ⟨∑ r : Fin k → Fin n, A (List.ofFn r) [], Finset.sum_nonneg fun _ _ ↦ hA0 _ _,
    fun x ξ ↦ (norm_iteratedFDeriv_le_sum_coordinateDeriv
      (contDiff_infty.1 (b.contDiff_coefficient_slice ξ) k) x).trans ?_⟩
  exact (Finset.sum_le_sum fun r _ ↦ by
    simpa [mixedDeriv_def, coordinateDeriv_nil] using hA (List.ofFn r) [] x ξ).trans_eq
    (Finset.sum_mul _ _ _).symm

private def weightedSlice (b : Symbol n V W m) (x ξ η : CoordinateSpace n) : V →L[ℂ] W :=
  𝓕 (fun z ↦ spatialWeight n z • b.coefficient (x + z, ξ)) η

private theorem exists_norm_weightedSlice_le_of_bound (r : ℝ) :
    ∃ (M : ℕ) (K : ℝ), 0 ≤ K ∧ ∀ {s : ℝ} {c : Symbol n V W s} {x ξ : CoordinateSpace n} {B : ℝ},
      0 ≤ B → (∀ k ≤ M, ∀ y, ‖iteratedFDeriv ℝ k (fun y ↦ c.coefficient (y, ξ)) y‖ ≤ B) →
      ∀ (η : CoordinateSpace n), ‖weightedSlice c x ξ η‖ ≤ K * B * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  set M : ℕ := ⌈max r 0⌉₊
  choose Cw hCw0 hCw using fun i : ℕ ↦ exists_norm_iteratedFDeriv_spatialWeight_le (n := n) i
  set S : ℕ → ℝ := fun k ↦ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cw i
  have hS0 (k : ℕ) : 0 ≤ S k := Finset.sum_nonneg fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (hCw0 i)
  set A : ℝ := ∑ k ∈ Finset.range (M + 1), S k
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ ↦ hS0 k
  have hI0 : 0 ≤ ∫ z, spatialWeight n z := integral_nonneg fun z ↦ spatialWeight_nonneg z
  refine ⟨M, 2 ^ M * (A * ∫ z, spatialWeight n z), by positivity,
    fun {s} {c} {x ξ} {B} hB0 hB η ↦ ?_⟩
  have hg : ContDiff ℝ M fun z ↦ c.coefficient (x + z, ξ) :=
    ((c.contDiff_coefficient_slice ξ).comp (contDiff_const.add contDiff_id)).of_le (mod_cast le_top)
  set f : CoordinateSpace n → V →L[ℂ] W := fun z ↦ spatialWeight n z • c.coefficient (x + z, ξ)
  have hf : ContDiff ℝ M f := (contDiff_spatialWeight.of_le (mod_cast le_top)).smul hg
  have hf_le (k : ℕ) (hk : k ≤ M) (z : CoordinateSpace n) :
      ‖iteratedFDeriv ℝ k f z‖ ≤ (A * B) * spatialWeight n z := by
    have hSk : S k ≤ A :=
      Finset.single_le_sum (fun q _ ↦ hS0 q) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
    refine ((norm_iteratedFDeriv_smul_le (contDiff_spatialWeight.of_le (mod_cast le_top)) hg z
      (mod_cast hk)).trans ((Finset.sum_le_sum (g := fun i ↦
        (k.choose i : ℝ) * (Cw i * spatialWeight n z) * B) fun i _ ↦ ?_).trans_eq ?_)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSk hB0) (spatialWeight_nonneg z))
    · rw [iteratedFDeriv_comp_add_left (f := fun y ↦ c.coefficient (y, ξ))]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hCw i z) (Nat.cast_nonneg _))
        (hB (k - i) ((Nat.sub_le k i).trans hk) (x + z)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hCw0 i) (spatialWeight_nonneg z)))
    · simp only [S, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hint (k : ℕ) (hk : k ≤ M) : Integrable (iteratedFDeriv ℝ k f) :=
    (integrable_spatialWeight.const_mul (A * B)).mono'
      (hf.continuous_iteratedFDeriv (mod_cast hk)).aestronglyMeasurable (.of_forall (hf_le k hk))
  have hint_le (k : ℕ) (hk : k ≤ M) :
      ∫ z, ‖iteratedFDeriv ℝ k f z‖ ≤ (A * ∫ z, spatialWeight n z) * B :=
    (integral_mono (hint k hk).norm (integrable_spatialWeight.const_mul (A * B))
      (hf_le k hk)).trans_eq (by rw [integral_const_mul]; ring)
  have hpow : (1 + ‖η‖) ^ M * ‖𝓕 f η‖ ≤ 2 ^ M * (A * ∫ z, spatialWeight n z) * B := by
    rcases le_total ‖η‖ 1 with hη | hη
    · exact (mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖η‖ ≤ 2) M)
        ((norm_fourier_le_integral_norm f η).trans
          (by simpa [norm_iteratedFDeriv_zero] using hint_le 0 (Nat.zero_le M)))
        (norm_nonneg _) (by positivity)).trans_eq (by ring)
    · have hM := (pow_mul_norm_fourier_le_integral_norm_iteratedFDeriv
        (fun k hk ↦ hf.differentiable_iteratedFDeriv (mod_cast hk)) hint η).trans (hint_le M le_rfl)
      calc (1 + ‖η‖) ^ M * ‖𝓕 f η‖ ≤ (2 * ‖η‖) ^ M * ‖𝓕 f η‖ := by gcongr; linarith
        _ = 2 ^ M * (‖η‖ ^ M * ‖𝓕 f η‖) := by ring
        _ ≤ 2 ^ M * ((2 * π * ‖η‖) ^ M * ‖𝓕 f η‖) := by gcongr; nlinarith [Real.two_le_pi]
        _ ≤ 2 ^ M * ((A * ∫ z, spatialWeight n z) * B) := by gcongr
        _ = 2 ^ M * (A * ∫ z, spatialWeight n z) * B := by ring
  have hw : (1 + ‖η‖ ^ 2) ^ (r / 2) ≤ (1 + ‖η‖) ^ M :=
    (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖η‖])
      (by linarith [(le_max_left r 0).trans (Nat.le_ceil _)])).trans
      (one_add_norm_sq_rpow_le_one_add_norm_pow η M)
  rw [neg_div, Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact (mul_comm ‖weightedSlice c x ξ η‖ _ ▸ mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans
    hpow

private theorem integrable_spatialWeight_smul_slice {b : Symbol n V W m} (hb : b.IsUniform)
    (x ξ : CoordinateSpace n) :
    Integrable fun z ↦ spatialWeight n z • b.coefficient (x + z, ξ) := by
  obtain ⟨Cb, -, hCb⟩ := hb.exists_bound_coefficient
  refine (integrable_spatialWeight.const_mul (Cb * (1 + ‖ξ‖ ^ 2) ^ (m / 2))).mono'
    (contDiff_spatialWeight.continuous.smul ((b.contDiff_coefficient_slice ξ).continuous.comp
      (continuous_const.add continuous_id))).aestronglyMeasurable (.of_forall fun z ↦ ?_)
  rw [norm_smul, Real.norm_of_nonneg (spatialWeight_nonneg z), mul_comm]
  exact mul_le_mul_of_nonneg_right (hCb (x + z) ξ) (spatialWeight_nonneg z)

private theorem exists_norm_fourierChar_spatialWeight_smul_le_of_dist_lt_one {s : ℝ}
    {c : Symbol n V W s} (hc : c.IsUniform) (ξ₀ : CoordinateSpace n) :
    ∃ C, 0 ≤ C ∧ ∀ x ξ η z, dist ξ ξ₀ < 1 →
      ‖(𝐞 (-⟪z, η⟫) : ℂ) • (spatialWeight n z • c.coefficient (x + z, ξ))‖ ≤
        C * spatialWeight n z := by
  obtain ⟨Cc, hCc0, hCc⟩ := hc.exists_bound_coefficient
  refine ⟨Cc * (2 ^ |s| * (1 + ‖ξ₀‖ ^ 2) ^ (s / 2)), by positivity, fun x ξ η z hξ ↦ ?_⟩
  have hw := one_add_norm_sq_rpow_le_of_norm_sub_le_one (dist_eq_norm ξ ξ₀ ▸ hξ.le) s
  rw [norm_smul, Circle.norm_coe, one_mul, norm_smul, Real.norm_of_nonneg (spatialWeight_nonneg z),
    mul_comm]
  exact mul_le_mul_of_nonneg_right ((hCc (x + z) ξ).trans (by gcongr)) (spatialWeight_nonneg z)

private theorem exists_norm_weightedSlice_le {b : Symbol n V W m} (hb : b.IsUniform) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ξ η, ‖weightedSlice b x ξ η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨M, K, hK0, hK⟩ := exists_norm_weightedSlice_le_of_bound (n := n) (V := V) (W := W) r
  choose Cd hCd0 hCd using hb.exists_norm_iteratedFDeriv_slice_le
  set Cb : ℝ := ∑ k ∈ Finset.range (M + 1), Cd k
  have hCb0 : 0 ≤ Cb := Finset.sum_nonneg fun k _ ↦ hCd0 k
  refine ⟨K * Cb, mul_nonneg hK0 hCb0, fun x ξ η ↦
    (hK (B := Cb * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (mul_nonneg hCb0 (by positivity))
      (fun k hk y ↦ (hCd k y ξ).trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun q _ ↦ hCd0 q) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
        (by positivity))) η).trans_eq (by ring)⟩

private theorem integrable_weightedSlice {b : Symbol n V W m} (hb : b.IsUniform)
    (x ξ : CoordinateSpace n) : Integrable (weightedSlice b x ξ) := by
  obtain ⟨C, -, hC⟩ := exists_norm_weightedSlice_le hb ((n : ℝ) + 1)
  have hcont : Continuous (weightedSlice b x ξ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (integrable_spatialWeight_smul_slice hb x ξ)
  exact (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
    (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))).mono' hcont.aestronglyMeasurable (.of_forall (hC x ξ))

private theorem continuous_weightedSlice {b : Symbol n V W m} (hb : b.IsUniform) :
    Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      weightedSlice b q.1.1 q.1.2 q.2 := by
  rw [continuous_iff_continuousAt]; intro q₀
  obtain ⟨B, -, hB⟩ := exists_norm_fourierChar_spatialWeight_smul_le_of_dist_lt_one hb q₀.1.2
  have hjoint : Continuous
      fun r : ((CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n) × CoordinateSpace n ↦
        (𝐞 (-⟪r.2, r.1.2⟫) : ℂ) • (spatialWeight n r.2 • b.coefficient (r.1.1.1 + r.2, r.1.1.2)) :=
    (Real.continuous_fourierChar.comp
      (((innerSL ℝ).continuous₂.comp₂ continuous_snd
        (continuous_snd.comp continuous_fst)).neg)).subtypeVal.smul
      ((contDiff_spatialWeight.continuous.comp continuous_snd).smul
        (b.contDiff_coefficient.continuous.comp
          (((continuous_fst.comp (continuous_fst.comp continuous_fst)).add continuous_snd).prodMk
            (continuous_snd.comp (continuous_fst.comp continuous_fst)))))
  have hdom : ∀ᶠ q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n in 𝓝 q₀,
      ∀ᵐ z ∂volume, ‖(𝐞 (-⟪z, q.2⟫) : ℂ) •
        (spatialWeight n z • b.coefficient (q.1.1 + z, q.1.2))‖ ≤ B * spatialWeight n z := by
    filter_upwards [Metric.ball_mem_nhds q₀ one_pos] with q hq
    have hq' : dist q q₀ < 1 := hq
    rw [Prod.dist_eq, max_lt_iff, Prod.dist_eq, max_lt_iff] at hq'
    exact .of_forall fun z ↦ hB q.1.1 q.1.2 q.2 z hq'.1.2
  exact (continuousAt_of_dominated (bound := fun z ↦ B * spatialWeight n z)
    (.of_forall fun q ↦ (hjoint.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    hdom (integrable_spatialWeight.const_mul B)
    (.of_forall fun z ↦ (hjoint.comp (continuous_id.prodMk continuous_const)).continuousAt)).congr
    (.of_forall fun q ↦ by simp [weightedSlice, Real.fourier_eq, Circle.smul_def])

private def fourierCharSpatialWeightSlice {s : ℝ} (c : Symbol n V W s) (η : CoordinateSpace n)
    (p : CoordinateSpace n × CoordinateSpace n) (z : CoordinateSpace n) : V →L[ℂ] W :=
  (𝐞 (-⟪z, η⟫) : ℂ) • (spatialWeight n z • c.coefficient (p.1 + z, p.2))

private theorem differentiableAt_fourierCharSpatialWeightSlice_and_fderiv_apply
    (b : Symbol n V W m) (η z : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (fourierCharSpatialWeightSlice b η · z) p ∧
      ∀ v, fderiv ℝ (fourierCharSpatialWeightSlice b η · z) p v =
        ∑ j, v.1 j • fourierCharSpatialWeightSlice (Symbol.spatialDeriv j b) η p z +
          ∑ j, v.2 j • fourierCharSpatialWeightSlice (Symbol.frequencyDeriv j b) η p z := by
  set c : ℂ := (𝐞 (-⟪z, η⟫) : ℂ)
  have hdiff : DifferentiableAt ℝ (fourierCharSpatialWeightSlice b η · z) p :=
    (((b.contDiff_coefficient.differentiable (by simp) _).comp p
      ((differentiableAt_fst.add_const z).prodMk differentiableAt_snd)).const_smul
        (spatialWeight n z)).const_smul c
  refine ⟨hdiff, fun v ↦ ?_⟩
  rw [fderiv_apply_eq_sum_coordinateDeriv hdiff]; congr 1
  · refine Finset.sum_congr rfl fun j _ ↦ congrArg (v.1 j • ·) ?_
    have h1 : HasFDerivAt (fun x ↦ b.coefficient (x + z, p.2))
        ((fderiv ℝ (fun y ↦ b.coefficient (y, p.2)) (p.1 + z)).comp
          (ContinuousLinearMap.id ℝ _)) p.1 :=
      HasFDerivAt.comp (g := fun y ↦ b.coefficient (y, p.2)) (f := fun x ↦ x + z) p.1
        (((b.contDiff_coefficient_slice p.2).differentiable (by simp) (p.1 + z)).hasFDerivAt)
        ((hasFDerivAt_id p.1).add_const z)
    have hfun : (fun x ↦ fourierCharSpatialWeightSlice b η (x, p.2) z) =
        fun x ↦ c • (spatialWeight n z • b.coefficient (x + z, p.2)) := rfl
    rw [coordinateDeriv_cons, coordinateDeriv_nil, hfun,
      ((h1.fun_const_smul (spatialWeight n z)).fun_const_smul c).fderiv]
    simp [fourierCharSpatialWeightSlice, c, fderiv_coefficient_single]
  · refine Finset.sum_congr rfl fun j _ ↦ congrArg (v.2 j • ·) ?_
    have h1 : HasFDerivAt (fun ξ ↦ b.coefficient (p.1 + z, ξ))
        (fderiv ℝ (fun ξ ↦ b.coefficient (p.1 + z, ξ)) p.2) p.2 :=
      ((b.contDiff_coefficient.comp (contDiff_prodMk_right (p.1 + z))).differentiable
        (by simp) p.2).hasFDerivAt
    have hfun : (fun ξ ↦ fourierCharSpatialWeightSlice b η (p.1, ξ) z) =
        fun ξ ↦ c • (spatialWeight n z • b.coefficient (p.1 + z, ξ)) := rfl
    rw [coordinateDeriv_cons, coordinateDeriv_nil, hfun,
      ((h1.fun_const_smul (spatialWeight n z)).fun_const_smul c).fderiv]
    simp [fourierCharSpatialWeightSlice, c, fderiv_coefficient_slice_single]

private theorem differentiableAt_weightedSlice_and_fderiv_apply {b : Symbol n V W m}
    (hb : b.IsUniform) (η : CoordinateSpace n) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (fun p ↦ weightedSlice b p.1 p.2 η) p₀ ∧
      ∀ v, fderiv ℝ (fun p ↦ weightedSlice b p.1 p.2 η) p₀ v =
        ∑ j, v.1 j • weightedSlice (Symbol.spatialDeriv j b) p₀.1 p₀.2 η +
        ∑ j, v.2 j • weightedSlice (Symbol.frequencyDeriv j b) p₀.1 p₀.2 η := by
  have hFeq {s : ℝ} (c : Symbol n V W s) (p : CoordinateSpace n × CoordinateSpace n) :
      (∫ z, fourierCharSpatialWeightSlice c η p z) = weightedSlice c p.1 p.2 η := by
    simp [fourierCharSpatialWeightSlice, weightedSlice, Real.fourier_eq, Circle.smul_def]
  have hFc {s : ℝ} (c : Symbol n V W s) (p : CoordinateSpace n × CoordinateSpace n) :
      Continuous (fourierCharSpatialWeightSlice c η p) :=
    (Real.continuous_fourierChar.comp (((innerSL ℝ).flip η).continuous.neg)).subtypeVal.smul
      (contDiff_spatialWeight.continuous.smul
        ((c.contDiff_coefficient_slice p.2).continuous.comp (continuous_const.add continuous_id)))
  choose Cx _ hCx using fun j ↦
    exists_norm_fourierChar_spatialWeight_smul_le_of_dist_lt_one (hb.spatialDeriv j) p₀.2
  choose Cξ _ hCξ using fun j ↦
    exists_norm_fourierChar_spatialWeight_smul_le_of_dist_lt_one (hb.frequencyDeriv j) p₀.2
  have key := differentiableAt_integral_and_fderiv_apply_eq_sum
    (F := fourierCharSpatialWeightSlice b η)
    (A := fun j ↦ fourierCharSpatialWeightSlice (Symbol.spatialDeriv j b) η)
    (B := fun j ↦ fourierCharSpatialWeightSlice (Symbol.frequencyDeriv j b) η)
    (fun z p ↦ (differentiableAt_fourierCharSpatialWeightSlice_and_fderiv_apply b η z p).1)
    (fun z p ↦ (differentiableAt_fourierCharSpatialWeightSlice_and_fderiv_apply b η z p).2)
    (fun p ↦ ((Real.fourierIntegral_convergent_iff η).2
      (integrable_spatialWeight_smul_slice hb p.1 p.2)).congr
        (.of_forall fun _ ↦ Circle.smul_def _ _))
    (fun _ p ↦ hFc _ p) (fun _ p ↦ hFc _ p)
    (integrable_spatialWeight.const_mul (∑ j, Cx j + ∑ j, Cξ j)) p₀ fun z p hp ↦ by
      have hp' : dist p p₀ < 1 := hp
      rw [Prod.dist_eq, max_lt_iff] at hp'
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]
      exact add_le_add (Finset.sum_le_sum fun j _ ↦ hCx j p.1 p.2 η z hp'.2)
        (Finset.sum_le_sum fun j _ ↦ hCξ j p.1 p.2 η z hp'.2)
  simpa only [hFeq] using key

end WeightedSlice

/-! ### The integrand and coefficient of `uniformSharp` -/

section Integrand

variable (a : Symbol n W U m') (b : Symbol n V W m)

private def uniformIntegrand (p : CoordinateSpace n × CoordinateSpace n) (η : CoordinateSpace n) :
    V →L[ℂ] U :=
  ((oneSubFreqLaplacian^[n + 1] a).coefficient (p.1, p.2 + (2 * π) • η)).comp
    (weightedSlice b p.1 p.2 η)

private def uniformCompCoeff (p : CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] U :=
  ∫ η, uniformIntegrand a b p η

variable {a b}

private theorem norm_comp_shift_two_pi_le {A : CoordinateSpace n → W →L[ℂ] U}
    {Ca : ℝ} (hCa : ∀ ζ, ‖A ζ‖ ≤ Ca * (1 + ‖ζ‖ ^ 2) ^ (m' / 2))
    {g : V →L[ℂ] W} {Cw r : ℝ} (hCw0 : 0 ≤ Cw) {ξ η : CoordinateSpace n}
    (hg : ‖g‖ ≤ Cw * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-(|m'| + r) / 2)) :
    ‖(A (ξ + (2 * π) • η)).comp g‖ ≤ Ca * 2 ^ (|m'| / 2) * (2 * π) ^ |m'| * Cw *
      (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  have hpeetre := one_add_norm_add_sq_rpow_le_mul m' ξ ((2 * π) • η)
  have hscale := one_add_norm_smul_sq_rpow_le (by linarith [Real.two_le_pi] : 1 ≤ 2 * π) |m'| η
  rw [abs_abs] at hscale
  have hCa0 : 0 ≤ Ca := (norm_nonneg (A 0)).trans (by simpa using hCa 0)
  have hξ : (1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) =
      (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by rw [← Real.rpow_add (by positivity)]; ring_nf
  have hη : (1 + ‖η‖ ^ 2) ^ (|m'| / 2) * (1 + ‖η‖ ^ 2) ^ (-(|m'| + r) / 2) =
      (1 + ‖η‖ ^ 2) ^ (-r / 2) := by rw [← Real.rpow_add (by positivity)]; ring_nf
  calc ‖(A (ξ + (2 * π) • η)).comp g‖
      ≤ (Ca * (1 + ‖ξ + (2 * π) • η‖ ^ 2) ^ (m' / 2)) *
          (Cw * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-(|m'| + r) / 2)) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hCa _) hg (norm_nonneg _) (by positivity))
    _ ≤ (Ca * (2 ^ (|m'| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m' / 2) *
            ((2 * π) ^ |m'| * (1 + ‖η‖ ^ 2) ^ (|m'| / 2)))) *
          (Cw * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-(|m'| + r) / 2)) := by
        gcongr; exact hpeetre.trans (by gcongr)
    _ = Ca * 2 ^ (|m'| / 2) * (2 * π) ^ |m'| * Cw *
          ((1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) *
          ((1 + ‖η‖ ^ 2) ^ (|m'| / 2) * (1 + ‖η‖ ^ 2) ^ (-(|m'| + r) / 2)) := by ring
    _ = _ := by rw [hξ, hη]

private theorem continuous_uniformIntegrand (hb : b.IsUniform) :
    Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      uniformIntegrand a b q.1 q.2 :=
  ((ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ).continuous₂.comp₂
    ((oneSubFreqLaplacian^[n + 1] a).contDiff_coefficient.continuous.comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).add (continuous_snd.const_smul (2 * π)))))
    (continuous_weightedSlice hb)

private theorem exists_norm_uniformIntegrand_le_of_bound {K : Set (CoordinateSpace n)}
    {Ca : ℝ} (hCa0 : 0 ≤ Ca)
    (hCa : ∀ x ∈ K, ∀ ξ,
      ‖(oneSubFreqLaplacian^[n + 1] a).coefficient (x, ξ)‖ ≤ Ca * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    (hb : b.IsUniform) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ η, ‖uniformIntegrand a b (x, ξ) η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_norm_weightedSlice_le hb (|m'| + r)
  exact ⟨Ca * 2 ^ (|m'| / 2) * (2 * π) ^ |m'| * Cb, by positivity,
    fun x hx ξ η ↦ norm_comp_shift_two_pi_le (hCa x hx) hCb0 (hCb x ξ η)⟩

private theorem integrable_uniformIntegrand (a : Symbol n W U m') (hb : b.IsUniform)
    (p : CoordinateSpace n × CoordinateSpace n) : Integrable (uniformIntegrand a b p) := by
  obtain ⟨Ca, hCa0, hCa⟩ := (oneSubFreqLaplacian^[n + 1] a).exists_bound_coefficient
    {p.1} isCompact_singleton
  obtain ⟨C, -, hC⟩ := exists_norm_uniformIntegrand_le_of_bound hCa0 hCa hb ((n : ℝ) + 1)
  exact (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
    (C * (1 + ‖p.2‖ ^ 2) ^ ((m' + m) / 2))).mono'
    ((continuous_uniformIntegrand (a := a) hb).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (.of_forall fun η ↦ hC p.1 rfl p.2 η)

private theorem exists_norm_uniformIntegrand_le_of_mem_ball (a : Symbol n W U m')
    (hb : b.IsUniform) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    ∃ C, 0 ≤ C ∧ ∀ η, ∀ p ∈ Metric.ball p₀ 1,
      ‖uniformIntegrand a b p η‖ ≤ C * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  obtain ⟨Ca, hCa0, hCa⟩ := (oneSubFreqLaplacian^[n + 1] a).exists_bound_coefficient
    (Metric.closedBall p₀.1 1) (isCompact_closedBall p₀.1 1)
  obtain ⟨C, hC0, hC⟩ := exists_norm_uniformIntegrand_le_of_bound hCa0 hCa hb ((n : ℝ) + 1)
  refine ⟨C * (2 ^ |m' + m| * (1 + ‖p₀.2‖ ^ 2) ^ ((m' + m) / 2)), by positivity, fun η p hp ↦ ?_⟩
  have hp' : dist p p₀ < 1 := hp
  rw [Prod.dist_eq, max_lt_iff] at hp'
  have hw := one_add_norm_sq_rpow_le_of_norm_sub_le_one (dist_eq_norm p.2 p₀.2 ▸ hp'.2.le) (m' + m)
  exact (hC p.1 (Metric.mem_closedBall.2 hp'.1.le) p.2 η).trans (by gcongr)

private theorem continuous_uniformCompCoeff (a : Symbol n W U m') (hb : b.IsUniform) :
    Continuous (uniformCompCoeff a b) := by
  rw [continuous_iff_continuousAt]; intro p₀
  obtain ⟨C, -, hC⟩ := exists_norm_uniformIntegrand_le_of_mem_ball a hb p₀
  exact continuousAt_of_dominated (bound := fun η ↦ C * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2))
    (.of_forall fun p ↦ (integrable_uniformIntegrand a hb p).aestronglyMeasurable)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds p₀ one_pos)
      fun p hp ↦ .of_forall fun η ↦ hC η p hp)
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul C)
    (.of_forall fun η ↦ ((continuous_uniformIntegrand (a := a) hb).comp
      (continuous_id.prodMk continuous_const)).continuousAt)

private theorem differentiableAt_uniformIntegrand_and_fderiv_apply (a : Symbol n W U m')
    (hb : b.IsUniform) (η : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (fun q ↦ uniformIntegrand a b q η) p ∧
      ∀ v, fderiv ℝ (fun q ↦ uniformIntegrand a b q η) p v =
        ∑ j, v.1 j • (uniformIntegrand (Symbol.spatialDeriv j a) b p η +
          uniformIntegrand a (Symbol.spatialDeriv j b) p η) +
        ∑ j, v.2 j • (uniformIntegrand (Symbol.frequencyDeriv j a) b p η +
          uniformIntegrand a (Symbol.frequencyDeriv j b) p η) := by
  set a' := oneSubFreqLaplacian^[n + 1] a
  set c := (2 * π) • η
  set Φ := (ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ
  have hAd : DifferentiableAt ℝ (fun q : CoordinateSpace n × CoordinateSpace n ↦
      a'.coefficient (q.1, q.2 + c)) p :=
    (a'.contDiff_coefficient.differentiable (by simp) _).comp p
      (differentiableAt_fst.prodMk (differentiableAt_snd.add_const c))
  have hAf (v : CoordinateSpace n × CoordinateSpace n) :
      fderiv ℝ (fun q : CoordinateSpace n × CoordinateSpace n ↦ a'.coefficient (q.1, q.2 + c)) p v =
        ∑ j, v.1 j • (Symbol.spatialDeriv j a').coefficient (p.1, p.2 + c) +
          ∑ j, v.2 j • (Symbol.frequencyDeriv j a').coefficient (p.1, p.2 + c) := by
    rw [fderiv_apply_eq_sum_coordinateDeriv hAd]; congr 1
    · exact Finset.sum_congr rfl fun j _ ↦ by dsimp only; rw [← coefficient_spatialDeriv]
    · refine Finset.sum_congr rfl fun j _ ↦ congrArg (v.2 j • ·) ?_
      have h1 : HasFDerivAt (fun ζ ↦ a'.coefficient (p.1, ζ + c))
          ((fderiv ℝ (fun ζ ↦ a'.coefficient (p.1, ζ)) (p.2 + c)).comp
            (ContinuousLinearMap.id ℝ _)) p.2 :=
        HasFDerivAt.comp (g := fun ζ ↦ a'.coefficient (p.1, ζ)) (f := fun ζ ↦ ζ + c) p.2
          (((a'.contDiff_coefficient.comp (contDiff_prodMk_right p.1)).differentiable (by simp)
            (p.2 + c)).hasFDerivAt) ((hasFDerivAt_id p.2).add_const c)
      dsimp only; rw [coordinateDeriv_cons, coordinateDeriv_nil, h1.fderiv]
      simp [fderiv_coefficient_slice_single]
  have hB := differentiableAt_weightedSlice_and_fderiv_apply hb η p
  have h := Φ.hasFDerivAt_of_bilinear hAd.hasFDerivAt hB.1.hasFDerivAt
  have hΦ : (fun q ↦ uniformIntegrand a b q η) =
      fun q ↦ Φ (a'.coefficient (q.1, q.2 + c)) (weightedSlice b q.1 q.2 η) := rfl
  rw [hΦ]
  refine ⟨h.differentiableAt, fun v ↦ ?_⟩
  rw [h.fderiv, add_apply, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, hAf v, hB.2 v]
  simp only [Φ, ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    ContinuousLinearMap.compL_apply, map_add, map_sum, map_smul, add_apply, sum_apply,
    smul_apply, uniformIntegrand, a', c, spatialDeriv_iterate_oneSubFreqLaplacian,
    frequencyDeriv_iterate_oneSubFreqLaplacian, smul_add, Finset.sum_add_distrib]
  abel

private theorem differentiableAt_uniformCompCoeff_and_fderiv_apply (a : Symbol n W U m')
    (hb : b.IsUniform) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (uniformCompCoeff a b) p₀ ∧
      ∀ v, fderiv ℝ (uniformCompCoeff a b) p₀ v =
        ∑ j, v.1 j • (uniformCompCoeff (Symbol.spatialDeriv j a) b p₀ +
          uniformCompCoeff a (Symbol.spatialDeriv j b) p₀) +
        ∑ j, v.2 j • (uniformCompCoeff (Symbol.frequencyDeriv j a) b p₀ +
          uniformCompCoeff a (Symbol.frequencyDeriv j b) p₀) := by
  choose C₁ _ hC₁ using fun j ↦
    exists_norm_uniformIntegrand_le_of_mem_ball (Symbol.spatialDeriv j a) hb p₀
  choose C₂ _ hC₂ using fun j ↦ exists_norm_uniformIntegrand_le_of_mem_ball a (hb.spatialDeriv j) p₀
  choose C₃ _ hC₃ using fun j ↦
    exists_norm_uniformIntegrand_le_of_mem_ball (Symbol.frequencyDeriv j a) hb p₀
  choose C₄ _ hC₄ using fun j ↦
    exists_norm_uniformIntegrand_le_of_mem_ball a (hb.frequencyDeriv j) p₀
  have hcont {m₁ m₂ : ℝ} (a' : Symbol n W U m₁) {b' : Symbol n V W m₂} (hb' : b'.IsUniform)
      (p : CoordinateSpace n × CoordinateSpace n) : Continuous (uniformIntegrand a' b' p) :=
    (continuous_uniformIntegrand (a := a') hb').comp (continuous_const.prodMk continuous_id)
  have key := differentiableAt_integral_and_fderiv_apply_eq_sum (F := uniformIntegrand a b)
    (A := fun j p η ↦ uniformIntegrand (Symbol.spatialDeriv j a) b p η +
      uniformIntegrand a (Symbol.spatialDeriv j b) p η)
    (B := fun j p η ↦ uniformIntegrand (Symbol.frequencyDeriv j a) b p η +
      uniformIntegrand a (Symbol.frequencyDeriv j b) p η)
    (fun η p ↦ (differentiableAt_uniformIntegrand_and_fderiv_apply a hb η p).1)
    (fun η p v ↦ (differentiableAt_uniformIntegrand_and_fderiv_apply a hb η p).2 v)
    (integrable_uniformIntegrand a hb)
    (fun j p ↦ (hcont (Symbol.spatialDeriv j a) hb p).add (hcont a (hb.spatialDeriv j) p))
    (fun j p ↦ (hcont (Symbol.frequencyDeriv j a) hb p).add (hcont a (hb.frequencyDeriv j) p))
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
      (∑ j, (C₁ j + C₂ j) + ∑ j, (C₃ j + C₄ j))) p₀ fun η p hp ↦ by
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]
      exact add_le_add
        (Finset.sum_le_sum fun j _ ↦ (norm_add_le _ _).trans
          ((add_le_add (hC₁ j η p hp) (hC₂ j η p hp)).trans_eq (by ring)))
        (Finset.sum_le_sum fun j _ ↦ (norm_add_le _ _).trans
          ((add_le_add (hC₃ j η p hp) (hC₄ j η p hp)).trans_eq (by ring)))
  refine ⟨key.1, fun v ↦ (key.2 v).trans ?_⟩
  congr 1
  · exact Finset.sum_congr rfl fun j _ ↦ congrArg (v.1 j • ·)
      (integral_add (integrable_uniformIntegrand (Symbol.spatialDeriv j a) hb p₀)
        (integrable_uniformIntegrand a (hb.spatialDeriv j) p₀))
  · exact Finset.sum_congr rfl fun j _ ↦ congrArg (v.2 j • ·)
      (integral_add (integrable_uniformIntegrand (Symbol.frequencyDeriv j a) hb p₀)
        (integrable_uniformIntegrand a (hb.frequencyDeriv j) p₀))

private theorem coordinateDeriv_fst_uniformCompCoeff (a : Symbol n W U m') (hb : b.IsUniform)
    (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun y ↦ uniformCompCoeff a b (y, ξ)) x =
      uniformCompCoeff (Symbol.spatialDeriv j a) b (x, ξ) +
        uniformCompCoeff a (Symbol.spatialDeriv j b) (x, ξ) := by
  obtain ⟨hd, hf⟩ := differentiableAt_uniformCompCoeff_and_fderiv_apply a hb (x, ξ)
  rw [coordinateDeriv_fst_eq_fderiv (p := (x, ξ)) hd, hf]; simp [Finset.sum_add_distrib]

private theorem coordinateDeriv_snd_uniformCompCoeff (a : Symbol n W U m') (hb : b.IsUniform)
    (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun ζ ↦ uniformCompCoeff a b (x, ζ)) ξ =
      uniformCompCoeff (Symbol.frequencyDeriv j a) b (x, ξ) +
        uniformCompCoeff a (Symbol.frequencyDeriv j b) (x, ξ) := by
  obtain ⟨hd, hf⟩ := differentiableAt_uniformCompCoeff_and_fderiv_apply a hb (x, ξ)
  rw [coordinateDeriv_snd_eq_fderiv (p := (x, ξ)) hd, hf]; simp [Finset.sum_add_distrib]

private theorem contDiff_uniformCompCoeff (a : Symbol n W U m') (hb : b.IsUniform) :
    ContDiff ℝ ∞ (uniformCompCoeff a b) := by
  refine contDiff_infty.2 fun k ↦ ?_
  induction k generalizing m m' a b with
  | zero => exact contDiff_zero.2 (continuous_uniformCompCoeff a hb)
  | succ k ih =>
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_fderiv_apply.2
      ⟨fun p ↦ (differentiableAt_uniformCompCoeff_and_fderiv_apply a hb p).1, by simp, fun v ↦ ?_⟩
    simp only [fun p ↦ (differentiableAt_uniformCompCoeff_and_fderiv_apply a hb p).2 v]
    exact (ContDiff.sum fun j _ ↦ ((ih (Symbol.spatialDeriv j a) hb).add
        (ih a (hb.spatialDeriv j))).const_smul _).add
      (ContDiff.sum fun j _ ↦ ((ih (Symbol.frequencyDeriv j a) hb).add
        (ih a (hb.frequencyDeriv j))).const_smul _)

private theorem exists_bound_uniformCompCoeff (P : ∀ {m' : ℝ}, Symbol n W U m' → Prop)
    (hPspatial : ∀ {m' : ℝ} {a : Symbol n W U m'}, P a → ∀ j, P (Symbol.spatialDeriv j a))
    (hPfrequency : ∀ {m' : ℝ} {a : Symbol n W U m'}, P a → ∀ j, P (Symbol.frequencyDeriv j a))
    {K : Set (CoordinateSpace n)}
    (hP : ∀ {m' : ℝ} {a : Symbol n W U m'}, P a → ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖(oneSubFreqLaplacian^[n + 1] a).coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    (a : Symbol n W U m') (ha : P a) (hb : b.IsUniform) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (uniformCompCoeff a b) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - β.length) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_mixedDeriv_le_of_leibniz (ι := Unit) 0 P hPspatial hPfrequency
    (fun b ↦ (b ()).IsUniform) (fun hb j ↦ hb.spatialDeriv j) (fun hb j ↦ hb.frequencyDeriv j)
    (fun a b _ _ ↦ uniformCompCoeff a (b ())) (fun a _ hb _ ↦ contDiff_uniformCompCoeff a hb)
    (fun a _ hb j _ ↦ coordinateDeriv_fst_uniformCompCoeff a hb j)
    (fun a _ hb j _ ↦ coordinateDeriv_snd_uniformCompCoeff a hb j)
    (fun {m₂ m₁} a' ha' {b'} hb' ↦ by
      obtain ⟨Ca, hCa0, hCa⟩ := hP ha'
      obtain ⟨C, hC0, hC⟩ := exists_norm_uniformIntegrand_le_of_bound hCa0 hCa hb' ((n : ℝ) + 1)
      set I : ℝ := ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
      refine ⟨C * I, mul_nonneg hC0 (integral_nonneg fun _ ↦ by positivity), fun _ x hx ξ ↦ ?_⟩
      simpa only [sub_zero, uniformCompCoeff] using (norm_integral_le_of_norm_le
        (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
          (C * (1 + ‖ξ‖ ^ 2) ^ ((m₁ + m₂) / 2)))
        (.of_forall fun η ↦ hC x hx ξ η)).trans_eq (by rw [integral_const_mul]; ring))
    a ha (b := fun _ ↦ b) hb α β
  exact ⟨C, hC0, by simpa only [sub_zero] using hC ()⟩

end Integrand

/-! ### The uniform composition symbol -/

section UniformSharp

variable (a : Symbol n W U m') (b : Symbol n V W m)

/-- The **uniform composition symbol** `a.uniformSharp b hb` of a symbol `a` of order `m'` and a
uniform symbol `b` of order `m`, a symbol of order `m' + m`:
`(a #_u b)(x, ξ) = ∫ (((1 - Δ_ξ)^(n+1) a)(x, ξ + 2πη)) ∘ 𝓕_z(⟨z⟩^(-2(n+1)) • b(x + z, ξ))(η) dη`. -/
def uniformSharp (hb : b.IsUniform) : Symbol n V U (m' + m) where
  coefficient := uniformCompCoeff a b
  contDiff_coefficient := contDiff_uniformCompCoeff a hb
  exists_bound K hK α β := exists_bound_uniformCompCoeff (fun _ ↦ True) (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun {_} a _ ↦ (oneSubFreqLaplacian^[n + 1] a).exists_bound_coefficient K hK)
    a trivial hb α β

variable {a b}

@[simp]
theorem coefficient_uniformSharp (hb : b.IsUniform) (x ξ : CoordinateSpace n) :
    (a.uniformSharp b hb).coefficient (x, ξ) =
      ∫ η, (((LinearMap.id (R := ℂ) (M := Symbol n W U m') -
        Symbol.inclusion (n := n) (V := W) (W := U) (m := m' - 2) (m' := m') (by linarith) ∘ₗ
          frequencyLaplacian (n := n) (V := W) (W := U) (m := m'))^[n + 1] a).coefficient
            (x, ξ + (2 * π) • η)).comp
            (𝓕 (fun z : CoordinateSpace n ↦
              ((1 + ‖z‖ ^ 2) ^ (-((n : ℝ) + 1)) : ℝ) • b.coefficient (x + z, ξ)) η) :=
  (rfl)

/-- The coefficient of `uniformSharp` depends on `a` and `b` only through their coefficients. -/
theorem coefficient_uniformSharp_congr {m₁ m₂ k₁ k₂ : ℝ}
    {a₁ : Symbol n W U m₁} {a₂ : Symbol n W U m₂} {b₁ : Symbol n V W k₁} {b₂ : Symbol n V W k₂}
    (hb₁ : b₁.IsUniform) (hb₂ : b₂.IsUniform)
    (ha : a₁.coefficient = a₂.coefficient) (hb : b₁.coefficient = b₂.coefficient) :
    (a₁.uniformSharp b₁ hb₁).coefficient = (a₂.uniformSharp b₂ hb₂).coefficient := by
  funext p
  simp only [uniformSharp, uniformCompCoeff, uniformIntegrand, weightedSlice,
    coefficient_iterate_oneSubFreqLaplacian_congr ha (n + 1), hb]

/-- **Leibniz rule in the position** for the uniform composition symbol. -/
theorem spatialDeriv_uniformSharp (hb : b.IsUniform) (j : Fin n) :
    Symbol.spatialDeriv j (a.uniformSharp b hb) =
      (Symbol.spatialDeriv j a).uniformSharp b hb +
        a.uniformSharp (Symbol.spatialDeriv j b) (hb.spatialDeriv j) := by
  ext1; funext ⟨x, ξ⟩
  rw [coefficient_spatialDeriv, coefficient_add, Pi.add_apply]
  exact coordinateDeriv_fst_uniformCompCoeff a hb j x ξ

/-- **Leibniz rule in the frequency** for the uniform composition symbol. -/
theorem coefficient_frequencyDeriv_uniformSharp (hb : b.IsUniform) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    (Symbol.frequencyDeriv j (a.uniformSharp b hb)).coefficient (x, ξ) =
      ((Symbol.frequencyDeriv j a).uniformSharp b hb).coefficient (x, ξ) +
        (a.uniformSharp (Symbol.frequencyDeriv j b) (hb.frequencyDeriv j)).coefficient (x, ξ) := by
  rw [coefficient_frequencyDeriv]; exact coordinateDeriv_snd_uniformCompCoeff a hb j x ξ

/-- **Uniform composition preserves uniform estimates.** -/
theorem IsUniform.uniformSharp (ha : a.IsUniform) (hb : b.IsUniform) :
    (a.uniformSharp b hb).IsUniform := isUniform_iff.2 fun α β ↦ by
  obtain ⟨C, hC0, hC⟩ := exists_bound_uniformCompCoeff IsUniform
    (fun ha j ↦ ha.spatialDeriv j) (fun ha j ↦ ha.frequencyDeriv j) (K := Set.univ)
    (fun ha ↦ (isUniform_iterate_oneSubFreqLaplacian ha (n + 1)).exists_bound_coefficient.imp
      fun _ hC ↦ ⟨hC.1, fun x _ ξ ↦ hC.2 x ξ⟩) a ha hb α β
  exact ⟨C, hC0, fun x ξ ↦ hC x (Set.mem_univ x) ξ⟩

/-- If the left factor `a` has compact spatial support, then so does `a.uniformSharp b hb`. -/
theorem HasCompactSpatialSupport.uniformSharp_left (ha : a.HasCompactSpatialSupport)
    (hb : b.IsUniform) : (a.uniformSharp b hb).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp
    (hasCompactSpatialSupport_iterate_oneSubFreqLaplacian ha (n + 1))
  refine hasCompactSpatialSupport_iff.2 ⟨K, hK, fun x hx ξ ↦ ?_⟩
  exact integral_eq_zero_of_ae (.of_forall fun η ↦ by
    rw [uniformIntegrand, hKa x hx]; exact ContinuousLinearMap.zero_comp _)

theorem add_uniformSharp (a₁ a₂ : Symbol n W U m') (hb : b.IsUniform) :
    (a₁ + a₂).uniformSharp b hb = a₁.uniformSharp b hb + a₂.uniformSharp b hb := by
  ext1; funext p
  have hadd : oneSubFreqLaplacian^[n + 1] (a₁ + a₂) =
      oneSubFreqLaplacian^[n + 1] a₁ + oneSubFreqLaplacian^[n + 1] a₂ := by
    simpa only [pow_apply_eq_iterate] using (oneSubFreqLaplacian ^ (n + 1)).map_add a₁ a₂
  simp only [coefficient_add, Pi.add_apply, uniformSharp, uniformCompCoeff,
    ← integral_add (integrable_uniformIntegrand a₁ hb p) (integrable_uniformIntegrand a₂ hb p)]
  exact integral_congr_ae (.of_forall fun η ↦ by
    rw [uniformIntegrand, hadd]; simp [uniformIntegrand, ContinuousLinearMap.add_comp])

theorem uniformSharp_add (a : Symbol n W U m') {b₁ b₂ : Symbol n V W m}
    (hb₁ : b₁.IsUniform) (hb₂ : b₂.IsUniform) :
    a.uniformSharp (b₁ + b₂) (hb₁.add hb₂) = a.uniformSharp b₁ hb₁ + a.uniformSharp b₂ hb₂ := by
  ext1; funext ⟨x, ξ⟩
  have hw (η : CoordinateSpace n) :
      weightedSlice (b₁ + b₂) x ξ η = weightedSlice b₁ x ξ η + weightedSlice b₂ x ξ η := by
    have hi {c : Symbol n V W m} (hc : c.IsUniform) := ((Real.fourierIntegral_convergent_iff η).2
      (integrable_spatialWeight_smul_slice hc x ξ)).congr (.of_forall fun _ ↦ Circle.smul_def _ _)
    simp only [weightedSlice, Real.fourier_eq, coefficient_add, Pi.add_apply, Circle.smul_def,
      smul_add]
    exact integral_add (hi hb₁) (hi hb₂)
  simp only [coefficient_add, Pi.add_apply, uniformSharp, uniformCompCoeff,
    ← integral_add (integrable_uniformIntegrand a hb₁ (x, ξ))
      (integrable_uniformIntegrand a hb₂ (x, ξ))]
  exact integral_congr_ae (.of_forall fun η ↦ by
    simp [uniformIntegrand, hw, ContinuousLinearMap.comp_add])

@[simp]
theorem smul_uniformSharp (c : ℂ) (a : Symbol n W U m') (hb : b.IsUniform) :
    (c • a).uniformSharp b hb = c • a.uniformSharp b hb := by
  ext1; funext p
  have hsmul : oneSubFreqLaplacian^[n + 1] (c • a) = c • oneSubFreqLaplacian^[n + 1] a := by
    simpa only [pow_apply_eq_iterate] using (oneSubFreqLaplacian ^ (n + 1)).map_smul c a
  simp only [coefficient_smul, Pi.smul_apply, uniformSharp, uniformCompCoeff, ← integral_smul]
  exact integral_congr_ae (.of_forall fun η ↦ by
    rw [uniformIntegrand, hsmul]; simp [uniformIntegrand])

@[simp]
theorem uniformSharp_smul (a : Symbol n W U m') (hb : b.IsUniform) (c : ℂ) :
    a.uniformSharp (c • b) (hb.smul c) = c • a.uniformSharp b hb := by
  ext1; funext ⟨x, ξ⟩
  have hw (η : CoordinateSpace n) : weightedSlice (c • b) x ξ η = c • weightedSlice b x ξ η := by
    simp only [weightedSlice, Real.fourier_eq, coefficient_smul, Pi.smul_apply,
      smul_comm (spatialWeight n _) c, smul_comm (𝐞 _) c, integral_smul]
  simp only [coefficient_smul, Pi.smul_apply, uniformSharp, uniformCompCoeff, ← integral_smul]
  exact integral_congr_ae (.of_forall fun η ↦ by simp [uniformIntegrand, hw])

/-- The constant identity symbol `1` is a left identity for `uniformSharp`: `1 #_u b = b` up to the
order identification `0 + m = m`. -/
@[simp]
theorem const_id_uniformSharp [CompleteSpace W] {b : Symbol n V W m} (hb : b.IsUniform) :
    (const (ContinuousLinearMap.id ℂ W)).uniformSharp b hb =
      Symbol.inclusion (zero_add m).ge b := by
  ext1; funext ⟨x, ξ⟩; rw [coefficient_inclusion]
  have h1 : oneSubFreqLaplacian (const (ContinuousLinearMap.id ℂ W) : Symbol n W W 0) =
      const (ContinuousLinearMap.id ℂ W) := by
    ext1; funext ⟨y, η⟩
    simp [oneSubFreqLaplacian, frequencyLaplacian_eq_sum, coordinateDeriv_const]
  have hconst : (oneSubFreqLaplacian^[n + 1] (const (ContinuousLinearMap.id ℂ W) :
      Symbol n W W 0)).coefficient = fun _ ↦ ContinuousLinearMap.id ℂ W := by
    rw [Function.iterate_fixed h1 (n + 1)]; exact funext (coefficient_const _)
  set g := fun z ↦ spatialWeight n z • b.coefficient (x + z, ξ)
  have hg_cont : Continuous g := contDiff_spatialWeight.continuous.smul
    ((b.contDiff_coefficient_slice ξ).continuous.comp (continuous_const.add continuous_id))
  have hinv : 𝓕⁻ (𝓕 g) 0 = g 0 := congrFun (hg_cont.fourierInv_fourier_eq
    (integrable_spatialWeight_smul_slice hb x ξ) (integrable_weightedSlice hb x ξ)) 0
  calc ((const (ContinuousLinearMap.id ℂ W)).uniformSharp b hb).coefficient (x, ξ)
      = 𝓕⁻ (𝓕 g) 0 := by
        rw [Real.fourierInv_eq]; exact integral_congr_ae (.of_forall fun η ↦ by
          dsimp only [uniformSharp, uniformCompCoeff]
          rw [uniformIntegrand, hconst]; simp [weightedSlice, g])
    _ = b.coefficient (x, ξ) := by rw [hinv]; simp [g, spatialWeight]

end UniformSharp

/-! ### Agreement with `Symbol.sharp` and bounded pointwise convergence -/

section Agreement

private theorem coordinateDeriv_coefficient_add_left (a : Symbol n W U m') (β : List (Fin n))
    (y ξ₀ ζ : CoordinateSpace n) :
    coordinateDeriv β (fun η ↦ a.coefficient (y, ξ₀ + η)) ζ =
      coordinateDeriv β (fun η ↦ a.coefficient (y, η)) (ξ₀ + ζ) := by
  have hf : ContDiff ℝ β.length fun η ↦ a.coefficient (y, η) :=
    (a.contDiff_coefficient.comp (contDiff_prodMk_right y)).of_le (mod_cast le_top)
  have hfc : ContDiff ℝ β.length fun η ↦ a.coefficient (y, ξ₀ + η) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [coordinateDeriv_eq_iteratedFDeriv β hfc,
    iteratedFDeriv_comp_add_left (f := fun η ↦ a.coefficient (y, η)),
    ← coordinateDeriv_eq_iteratedFDeriv β hf]

private def shiftFreq (ξ₀ : CoordinateSpace n) (a : Symbol n W U m') : Symbol n W U m' where
  coefficient p := a.coefficient (p.1, ξ₀ + p.2)
  contDiff_coefficient := a.contDiff_coefficient.comp (contDiff_fst.prodMk
    (contDiff_const.add contDiff_snd))
  exists_bound K hK α β := by
    obtain ⟨C, hC0, hC⟩ := a.exists_bound K hK α β
    set r : ℝ := m' - β.length
    refine ⟨C * 2 ^ (|r| / 2) * (1 + ‖ξ₀‖ ^ 2) ^ (|r| / 2), by positivity, fun x hx ζ ↦ ?_⟩
    have hmd : mixedDeriv α β (fun p : CoordinateSpace n × CoordinateSpace n ↦
        a.coefficient (p.1, ξ₀ + p.2)) x ζ = mixedDeriv α β a.coefficient x (ξ₀ + ζ) := by
      simp only [mixedDeriv_def, coordinateDeriv_coefficient_add_left a β _ ξ₀ ζ]
    have hp := add_comm ξ₀ ζ ▸ one_add_norm_add_sq_rpow_le_mul r ζ ξ₀
    exact hmd ▸ (hC x hx (ξ₀ + ζ)).trans ((mul_le_mul_of_nonneg_left hp hC0).trans_eq (by ring))

private theorem coefficient_iterate_oneSubFreqLaplacian_shiftFreq (ξ₀ : CoordinateSpace n)
    (k : ℕ) (a : Symbol n W U m') (x ζ : CoordinateSpace n) :
    (oneSubFreqLaplacian^[k] (shiftFreq ξ₀ a)).coefficient (x, ζ) =
      (oneSubFreqLaplacian^[k] a).coefficient (x, ξ₀ + ζ) := by
  have hfreq (j : Fin n) {s : ℝ} (d : Symbol n W U s) :
      Symbol.frequencyDeriv j (shiftFreq ξ₀ d) = shiftFreq ξ₀ (Symbol.frequencyDeriv j d) := by
    ext1; funext ⟨y, η⟩; simpa [shiftFreq] using coordinateDeriv_coefficient_add_left d [j] y ξ₀ η
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    have h1 : oneSubFreqLaplacian (shiftFreq ξ₀ a) = shiftFreq ξ₀ (oneSubFreqLaplacian a) := by
      ext1; funext ⟨y, η⟩
      simp only [oneSubFreqLaplacian, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        coefficient_sub, Pi.sub_apply, coefficient_inclusion, frequencyLaplacian_eq_sum,
        coefficient_sum, Finset.sum_apply, hfreq]
      simp [shiftFreq]
    rw [Function.iterate_succ_apply, h1, ih, Function.iterate_succ_apply]

private theorem iterate_smulLeftCLM_one_add_norm_sub_sq_cancel {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] (x : CoordinateSpace n)
    (f : 𝓢(CoordinateSpace n, F)) :
    (SchwartzMap.smulLeftCLM F (fun y ↦ (1 : ℝ) + ‖x - y‖ ^ 2))^[n + 1]
      (SchwartzMap.smulLeftCLM F (fun y ↦ (1 + ‖x - y‖ ^ 2) ^ (-((n : ℝ) + 1))) f) = f := by
  have htg_neg : (fun y : CoordinateSpace n ↦
      (1 + ‖x - y‖ ^ 2) ^ (-((n : ℝ) + 1))).HasTemperateGrowth :=
    (hasTemperateGrowth_one_add_norm_sq_rpow _ _).comp (by fun_prop)
  have htg_pos : (fun y : CoordinateSpace n ↦ (1 : ℝ) + ‖x - y‖ ^ 2).HasTemperateGrowth :=
    (by fun_prop : (fun _ : CoordinateSpace n ↦ (1 : ℝ)).HasTemperateGrowth).add
      (by simpa using hasTemperateGrowth_norm_sub_pow x 1)
  ext y
  have hpow (k : ℕ) (v : 𝓢(CoordinateSpace n, F)) :
      ((SchwartzMap.smulLeftCLM F (fun y ↦ (1 : ℝ) + ‖x - y‖ ^ 2))^[k] v) y =
        (1 + ‖x - y‖ ^ 2) ^ k • v y := by
    induction k generalizing v with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', SchwartzMap.smulLeftCLM_apply_apply htg_pos, ih,
        smul_smul, ← pow_succ']
  rw [hpow (n + 1), SchwartzMap.smulLeftCLM_apply_apply htg_neg, smul_smul,
    ← Real.rpow_natCast (1 + ‖x - y‖ ^ 2) (n + 1), ← Real.rpow_add (by positivity)]
  push_cast; rw [add_neg_cancel, Real.rpow_zero, one_smul]

/-- **Compatibility with `Symbol.sharp`.** When the right factor `b` has compact spatial support,
`a.uniformSharp b hb.isUniform` has the same coefficient as `a.sharp b hb`. -/
theorem coefficient_uniformSharp_eq_sharp {a : Symbol n W U m'} {b : Symbol n V W m}
    (hb : b.HasCompactSpatialSupport) :
    (a.uniformSharp b hb.isUniform).coefficient = (a.sharp b hb).coefficient := by
  funext ⟨x, ξ⟩
  set Φ : (W →L[ℂ] U) →L[ℝ] ((V →L[ℂ] W) →L[ℂ] (V →L[ℂ] U)) :=
    (ContinuousLinearMap.compL ℂ V W U).restrictScalars ℝ
  set c : Symbol n (V →L[ℂ] W) (V →L[ℂ] U) m' := (shiftFreq ξ a).map Φ
  set f : 𝓢(CoordinateSpace n, V →L[ℂ] W) := hb.sliceSchwartz ξ
  have htg_neg : (fun y : CoordinateSpace n ↦
      (1 + ‖x - y‖ ^ 2) ^ (-((n : ℝ) + 1))).HasTemperateGrowth :=
    (hasTemperateGrowth_one_add_norm_sq_rpow _ _).comp (by fun_prop)
  set fx : 𝓢(CoordinateSpace n, V →L[ℂ] W) :=
    SchwartzMap.smulLeftCLM (V →L[ℂ] W) (fun y ↦ (1 + ‖x - y‖ ^ 2) ^ (-((n : ℝ) + 1))) f
  have hsharp : (a.sharp b hb).coefficient (x, ξ) = quantizeSchwartzValue c.coefficient f x := by
    rw [coefficient_sharp, quantizeSchwartzValue_def]
    exact integral_congr_ae (.of_forall fun η ↦ by
      simp [c, Φ, shiftFreq, f, hb.fourier_sliceSchwartz, Circle.smul_def])
  have hc_iter (η : CoordinateSpace n) :
      (oneSubFreqLaplacian^[n + 1] c).coefficient (x, (2 * π) • η) =
        Φ ((oneSubFreqLaplacian^[n + 1] a).coefficient (x, ξ + (2 * π) • η)) := by
    rw [← map_iterate_oneSubFreqLaplacian, coefficient_map,
      coefficient_iterate_oneSubFreqLaplacian_shiftFreq]
  have hphase (η : CoordinateSpace n) : (𝐞 ⟪η, x⟫ : ℂ) • 𝓕 fx η = weightedSlice b x ξ η := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    simp only [weightedSlice, Real.fourier_eq, Circle.smul_def]
    rw [← integral_add_left_eq_self (fun y ↦ (𝐞 (-⟪y, η⟫) : ℂ) • fx y) x, ← integral_smul]
    refine integral_congr_ae (.of_forall fun z ↦ ?_)
    have hchar : (𝐞 ⟪η, x⟫ : ℂ) * (𝐞 (-⟪x + z, η⟫) : ℂ) = (𝐞 (-⟪z, η⟫) : ℂ) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, inner_add_left, real_inner_comm x η]
      congr 2; ring
    have hnorm : ‖x - (x + z)‖ = ‖z‖ := by simp
    dsimp only
    rw [SchwartzMap.smulLeftCLM_apply_apply htg_neg f (x + z), hb.coe_sliceSchwartz,
      hnorm, smul_smul, hchar]; rfl
  rw [hsharp, ← iterate_smulLeftCLM_one_add_norm_sub_sq_cancel x f,
    quantizeSchwartzValue_iterate_smulLeftCLM_one_add_norm_sub_sq, quantizeSchwartzValue_def]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  dsimp only [uniformSharp, uniformCompCoeff]
  rw [Circle.smul_def, hc_iter η, ← map_smul, hphase η]; simp [Φ, uniformIntegrand]

/-- **Compatibility with `Symbol.sharp`.** When `b` has compact spatial support, `a.uniformSharp b
hb.isUniform` equals `a.sharp b hb`. -/
@[simp]
theorem uniformSharp_eq_sharp {a : Symbol n W U m'} {b : Symbol n V W m}
    (hb : b.HasCompactSpatialSupport) :
    a.uniformSharp b hb.isUniform = a.sharp b hb :=
  Symbol.ext (coefficient_uniformSharp_eq_sharp hb)

private theorem tendsto_weightedSlice {b : Symbol n V W m} {bseq : ℕ → Symbol n V W m} {C₀ : ℝ}
    (hC₀ : ∀ N y ξ, ‖(bseq N).coefficient (y, ξ)‖ ≤ C₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (htend : ∀ y ξ,
      Tendsto (fun N ↦ (bseq N).coefficient (y, ξ)) atTop (𝓝 (b.coefficient (y, ξ))))
    (x ξ η : CoordinateSpace n) :
    Tendsto (fun N ↦ weightedSlice (bseq N) x ξ η) atTop (𝓝 (weightedSlice b x ξ η)) := by
  simp only [weightedSlice, Real.fourier_eq]
  refine tendsto_integral_of_dominated_convergence
    (fun z ↦ (C₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) * spatialWeight n z)
    (fun N ↦ ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (contDiff_spatialWeight.continuous.smul
        (((bseq N).contDiff_coefficient_slice ξ).continuous.comp
          (continuous_const.add continuous_id)))).aestronglyMeasurable)
    (integrable_spatialWeight.const_mul _) (fun N ↦ .of_forall fun z ↦ ?_)
    (.of_forall fun z ↦ ((htend (x + z) ξ).const_smul (spatialWeight n z)).const_smul _)
  rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul, norm_smul,
    Real.norm_of_nonneg (spatialWeight_nonneg z), mul_comm]
  exact mul_le_mul_of_nonneg_right (hC₀ N (x + z) ξ) (spatialWeight_nonneg z)

/-- **Bounded pointwise convergence of `uniformSharp` in the right factor.** -/
theorem exists_bound_and_tendsto_coefficient_uniformSharp (a : Symbol n W U m')
    {b : Symbol n V W m} (hb : b.IsUniform) {bseq : ℕ → Symbol n V W m}
    (hbseq : ∀ N, (bseq N).IsUniform)
    (hderiv : ∀ k : ℕ, ∃ C, 0 ≤ C ∧ ∀ N y ξ,
      ‖iteratedFDeriv ℝ k (fun y ↦ (bseq N).coefficient (y, ξ)) y‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (htend : ∀ y ξ,
      Tendsto (fun N ↦ (bseq N).coefficient (y, ξ)) atTop (𝓝 (b.coefficient (y, ξ))))
    (x : CoordinateSpace n) :
    (∃ K, 0 ≤ K ∧ ∀ N ξ,
      ‖(a.uniformSharp (bseq N) (hbseq N)).coefficient (x, ξ)‖ ≤
        K * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2)) ∧
    ∀ ξ, Tendsto (fun N ↦ (a.uniformSharp (bseq N) (hbseq N)).coefficient (x, ξ))
      atTop (𝓝 ((a.uniformSharp b hb).coefficient (x, ξ))) := by
  choose Cd hCd0 hCd using hderiv
  obtain ⟨Ca, -, hCa⟩ := (oneSubFreqLaplacian^[n + 1] a).exists_bound_coefficient_slice x
  obtain ⟨M, Kw, hKw0, hKw⟩ :=
    exists_norm_weightedSlice_le_of_bound (n := n) (V := V) (W := W) (|m'| + ((n : ℝ) + 1))
  set Cb : ℝ := ∑ k ∈ Finset.range (M + 1), Cd k
  have hCb0 : 0 ≤ Cb := Finset.sum_nonneg fun k _ ↦ hCd0 k
  have hw_le (N : ℕ) (ξ η : CoordinateSpace n) : ‖weightedSlice (bseq N) x ξ η‖ ≤
      (Kw * Cb) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-(|m'| + ((n : ℝ) + 1)) / 2) :=
    (hKw (B := Cb * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (mul_nonneg hCb0 (by positivity))
      (fun k hk y ↦ (hCd k N y ξ).trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun q _ ↦ hCd0 q) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
        (by positivity))) η).trans_eq (by ring)
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (by simpa using hCa 0)
  set C : ℝ := Ca * 2 ^ (|m'| / 2) * (2 * π) ^ |m'| * (Kw * Cb)
  have hInt (N : ℕ) (ξ η : CoordinateSpace n) : ‖uniformIntegrand a (bseq N) (x, ξ) η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) :=
    norm_comp_shift_two_pi_le hCa (mul_nonneg hKw0 hCb0) (hw_le N ξ η)
  set I : ℝ := ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  refine ⟨⟨C * I, mul_nonneg (by positivity) (integral_nonneg fun _ ↦ by positivity),
    fun N ξ ↦ (norm_integral_le_of_norm_le
      (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
        (C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2)))
      (.of_forall (hInt N ξ))).trans_eq (by rw [integral_const_mul]; ring)⟩, fun ξ ↦ ?_⟩
  simp only [uniformSharp, uniformCompCoeff]
  exact tendsto_integral_of_dominated_convergence
    (fun η ↦ (C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2)) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2))
    (fun N ↦ (integrable_uniformIntegrand a (hbseq N) (x, ξ)).aestronglyMeasurable)
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul _)
    (fun N ↦ .of_forall (hInt N ξ)) (.of_forall fun η ↦
      (((ContinuousLinearMap.compL ℂ V W U)
        ((oneSubFreqLaplacian^[n + 1] a).coefficient (x, ξ + (2 * π) • η))).continuous.tendsto
          _).comp (tendsto_weightedSlice
            (fun N y ζ ↦ by simpa [norm_iteratedFDeriv_zero] using hCd 0 N y ζ) htend x ξ η))

end Agreement

end TauCeti.Symbol
