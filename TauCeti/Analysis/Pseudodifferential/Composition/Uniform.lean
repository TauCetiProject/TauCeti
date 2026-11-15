/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
public import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import TauCeti.Analysis.Calculus.CoordinateDeriv.ParametricIntegral
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Pseudodifferential.OutputSupport
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# The composition symbol for uniform symbols

For a symbol `b` of order `m` whose estimates hold uniformly in the position (`Symbol.IsUniform`)
without compact spatial support, the slice `y ↦ b(y, ξ)` need not be integrable, so the ordinary
integral `∫ exp(2πi ⟪η, x⟫) a(x, ξ + 2πη) ∘ b̂(η, ξ) dη` of
`TauCeti.Analysis.Pseudodifferential.Composition.Basic` cannot be formed directly. Integrating the
oscillatory composition integral by parts `n + 1` times in the spatial displacement `z = y - x`
against `1 = (1 + ‖z‖²) ^ (n + 1) (1 + ‖z‖²) ^ (-(n + 1))` replaces `a` by
`(1 - Δ_ξ) ^ (n + 1) a` and inserts the integrable Japanese bracket weight `(1 + ‖z‖²) ^ (-(n + 1))`
in front of `b(x + z, ξ)`, absorbing the outer phase `exp(2πi ⟪η, x⟫)` by `y = x + z`:

`(a #_u b)(x, ξ) = ∫ (((1 - Δ_ξ)^(n+1) a)(x, ξ + 2πη)) ∘ 𝓕_z(⟨z⟩^(-2(n+1)) b(x + z, ξ))(η) dη`.

This file constructs `TauCeti.Symbol.uniformSharp` (`a.uniformSharp b hb`, written `a #_u b` below)
from this convergent integral, proves its Leibniz rules and bilinearity, shows that it agrees with
`a.sharp b hb` whenever `b` has compact spatial support (`TauCeti.Symbol.uniformSharp_eq_sharp`),
proves that it preserves `Symbol.IsUniform` when `a` is also uniform
(`TauCeti.Symbol.IsUniform.uniformSharp`), and establishes the operator composition law
`Op(a #_u b) u = Op(a) (Op(b) u)` on Schwartz space
(`TauCeti.Symbol.quantizeSchwartzValue_uniformSharp`,
`TauCeti.Symbol.quantizeUniformCLM_uniformSharp`) by dyadic spatial truncation, together with
associativity (`TauCeti.Symbol.uniformSharp_assoc`) and composition with frequency multipliers and
Bessel potentials.

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

/-- The linear operator `1 - Δ_ξ` on symbols of order `m'`, keeping the order `m'` via the symbol
inclusion `S^{m' - 2} ↪ S^{m'}`. -/
private def oneSubFreqLaplacian : Symbol n W U m' →ₗ[ℂ] Symbol n W U m' :=
  LinearMap.id - Symbol.inclusion (m' := m') (by linarith) ∘ₗ frequencyLaplacian (m := m')

private theorem spatialDeriv_iterate_oneSubFreqLaplacian (j : Fin n) (k : ℕ)
    (a : Symbol n W U m') :
    Symbol.spatialDeriv j (oneSubFreqLaplacian^[k] a) =
      oneSubFreqLaplacian^[k] (Symbol.spatialDeriv j a) := by
  refine Function.Commute.iterate_right (fun b ↦ ?_) k a
  simp only [oneSubFreqLaplacian, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    map_sub, spatialDeriv_inclusion, frequencyLaplacian_eq_sum, map_sum,
    spatialDeriv_frequencyDeriv_comm]

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

private theorem iterate_oneSubFreqLaplacian_add (k : ℕ) (a₁ a₂ : Symbol n W U m') :
    oneSubFreqLaplacian^[k] (a₁ + a₂) =
      oneSubFreqLaplacian^[k] a₁ + oneSubFreqLaplacian^[k] a₂ := by
  simpa only [pow_apply_eq_iterate] using (oneSubFreqLaplacian ^ k).map_add a₁ a₂

private theorem iterate_oneSubFreqLaplacian_smul (k : ℕ) (c : ℂ) (a : Symbol n W U m') :
    oneSubFreqLaplacian^[k] (c • a) = c • oneSubFreqLaplacian^[k] a := by
  simpa only [pow_apply_eq_iterate] using (oneSubFreqLaplacian ^ k).map_smul c a

private theorem isUniform_iterate_oneSubFreqLaplacian {a : Symbol n W U m'} (ha : a.IsUniform)
    (k : ℕ) : (oneSubFreqLaplacian^[k] a).IsUniform := by
  induction k with
  | zero => exact ha
  | succ k ih =>
    set b := oneSubFreqLaplacian^[k] a
    have hlap : (Symbol.inclusion (m' := m') (by linarith) (frequencyLaplacian b)).IsUniform := by
      rw [frequencyLaplacian_eq_sum]
      exact (IsUniform.sum fun j _ ↦
        ((ih.frequencyDeriv j).frequencyDeriv j).inclusion (by linarith)).inclusion (by linarith)
    have hsub : oneSubFreqLaplacian b =
        b + (-1 : ℂ) • Symbol.inclusion (m' := m') (by linarith) (frequencyLaplacian b) := by
      rw [oneSubFreqLaplacian, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        sub_eq_add_neg, neg_one_smul]
    rw [Function.iterate_succ_apply', hsub]; exact ih.add (hlap.smul (-1))

private theorem coefficient_iterate_oneSubFreqLaplacian_congr {m₁ m₂ : ℝ}
    {a₁ : Symbol n W U m₁} {a₂ : Symbol n W U m₂} (h : a₁.coefficient = a₂.coefficient) (k : ℕ) :
    (oneSubFreqLaplacian^[k] a₁).coefficient = (oneSubFreqLaplacian^[k] a₂).coefficient := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have hstep {m : ℝ} (b : Symbol n W U m) :
        oneSubFreqLaplacian b = b - Symbol.inclusion (by linarith) (frequencyLaplacian b) := rfl
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hstep, hstep]
    funext ⟨x, ξ⟩
    simp only [coefficient_sub, Pi.sub_apply, coefficient_inclusion,
      coefficient_frequencyLaplacian, ih]

private theorem map_iterate_oneSubFreqLaplacian {V' U' : Type*}
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] [NormedAddCommGroup U'] [NormedSpace ℂ U']
    (Φ : (W →L[ℂ] U) →L[ℝ] (V' →L[ℂ] U')) (k : ℕ) (a : Symbol n W U m') :
    (oneSubFreqLaplacian^[k] a).map Φ = oneSubFreqLaplacian^[k] (a.map Φ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    ext1; funext ⟨x, ξ⟩
    simp only [oneSubFreqLaplacian, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      coefficient_map, coefficient_sub, Pi.sub_apply, coefficient_inclusion,
      frequencyLaplacian_eq_sum, coefficient_sum, Finset.sum_apply, frequencyDeriv_map, map_sub,
      map_sum]

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

/-- Multiplying a Schwartz input by `1 + ‖x - y‖²` and evaluating the quantization at `x`
replaces the symbol `c` by `(1 - Δ_ξ) c`. -/
private theorem quantizeSchwartzValue_smulLeftCLM_one_add_norm_sub_sq
    {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℂ G₂]
    (c : Symbol n G₁ G₂ m') (v : 𝓢(CoordinateSpace n, G₁)) (x : CoordinateSpace n) :
    quantizeSchwartzValue c.coefficient
        (SchwartzMap.smulLeftCLM G₁ (fun y ↦ (1 : ℝ) + ‖x - y‖ ^ 2) v) x =
      quantizeSchwartzValue (oneSubFreqLaplacian c).coefficient v x := by
  have h1 : (fun _ : CoordinateSpace n ↦ (1 : ℝ)).HasTemperateGrowth := by fun_prop
  have h2 : (fun y : CoordinateSpace n ↦ ‖x - y‖ ^ 2).HasTemperateGrowth := by
    simpa using hasTemperateGrowth_norm_sub_pow x 1
  have h12 : (fun y : CoordinateSpace n ↦ (1 : ℝ) + ‖x - y‖ ^ 2).HasTemperateGrowth := h1.add h2
  have hsplit : SchwartzMap.smulLeftCLM G₁ (fun y ↦ (1 : ℝ) + ‖x - y‖ ^ 2) v =
      v + SchwartzMap.smulLeftCLM G₁ (fun y ↦ ‖x - y‖ ^ 2) v := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply h12, add_apply,
      SchwartzMap.smulLeftCLM_apply_apply h2, add_smul, one_smul]
  obtain ⟨C, -, hC⟩ := c.exists_bound_coefficient_slice x
  have hc : c.coefficient = (oneSubFreqLaplacian c +
      Symbol.inclusion (by linarith) (frequencyLaplacian c)).coefficient := by
    ext p; simp [oneSubFreqLaplacian]
  rw [hsplit,
    quantizeSchwartzValue_add_right (c.continuous_coefficient_slice x).aestronglyMeasurable hC,
    c.quantizeSchwartzValue_smulLeftCLM_norm_sub_sq, hc, coefficient_add,
    quantizeSchwartzValue_coefficient_add,
    coefficient_inclusion (by linarith) (frequencyLaplacian c), add_neg_cancel_right]

private theorem quantizeSchwartzValue_iterate_smulLeftCLM_one_add_norm_sub_sq
    {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℂ G₂]
    (k : ℕ) (c : Symbol n G₁ G₂ m') (v : 𝓢(CoordinateSpace n, G₁)) (x : CoordinateSpace n) :
    quantizeSchwartzValue c.coefficient
        ((SchwartzMap.smulLeftCLM G₁ (fun y ↦ (1 : ℝ) + ‖x - y‖ ^ 2))^[k] v) x =
      quantizeSchwartzValue (oneSubFreqLaplacian^[k] c).coefficient v x := by
  induction k generalizing c v with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih,
      quantizeSchwartzValue_smulLeftCLM_one_add_norm_sub_sq, Function.iterate_succ_apply']

end OneSubFreqLaplacian

/-! ### Quantitative decay and regularity of the weighted Fourier slice -/

section WeightedSlice

/-- The integrable spatial weight `z ↦ (1 + ‖z‖²) ^ (-(n + 1))` used in the oscillatory-integral
regularization of uniform symbol composition. -/
private def spatialWeight (n : ℕ) (z : CoordinateSpace n) : ℝ :=
  (1 + ‖z‖ ^ 2) ^ (-((n : ℝ) + 1))

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
  refine ⟨max C 0, le_max_right _ _, fun z ↦ (hC z).trans ?_⟩
  have hexp : (1 + ‖z‖ ^ 2) ^ (-((n : ℝ) + 1) - (k : ℝ) / 2) ≤ spatialWeight n z :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖z‖])
      (by linarith [Nat.cast_nonneg (α := ℝ) k])
  exact mul_le_mul (le_max_left _ _) hexp (by positivity) (le_max_right _ _)

private theorem exists_norm_iteratedFDeriv_spatialWeight_smul_le (M : ℕ) :
    ∃ A, 0 ≤ A ∧ ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
      {g : CoordinateSpace n → F}, ContDiff ℝ M g → ∀ {B : ℝ}, 0 ≤ B →
      (∀ k ≤ M, ∀ z, ‖iteratedFDeriv ℝ k g z‖ ≤ B) → ∀ k ≤ M, ∀ z,
      ‖iteratedFDeriv ℝ k (fun z ↦ spatialWeight n z • g z) z‖ ≤
        (A * B) * spatialWeight n z := by
  choose Cw hCw0 hCw using fun i : ℕ ↦ exists_norm_iteratedFDeriv_spatialWeight_le (n := n) i
  set S : ℕ → ℝ := fun k ↦ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cw i
  have hS0 (k : ℕ) : 0 ≤ S k := Finset.sum_nonneg fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (hCw0 i)
  refine ⟨∑ k ∈ Finset.range (M + 1), S k, Finset.sum_nonneg fun k _ ↦ hS0 k,
    fun {F} _ _ {g} hg {B} hB0 hB k hk z ↦ ?_⟩
  have hSk : S k ≤ ∑ q ∈ Finset.range (M + 1), S q :=
    Finset.single_le_sum (fun q _ ↦ hS0 q) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  refine (norm_iteratedFDeriv_smul_le (contDiff_spatialWeight.of_le (mod_cast le_top)) hg z
    (mod_cast hk)).trans ?_
  calc ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (spatialWeight n) z‖ *
          ‖iteratedFDeriv ℝ (k - i) g z‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (Cw i * spatialWeight n z) * B :=
        Finset.sum_le_sum fun i _ ↦
          mul_le_mul (mul_le_mul_of_nonneg_left (hCw i z) (Nat.cast_nonneg _))
            (hB (k - i) ((Nat.sub_le k i).trans hk) z) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hCw0 i) (spatialWeight_nonneg z)))
    _ = (S k * B) * spatialWeight n z := by
        simp only [S, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ ≤ ((∑ q ∈ Finset.range (M + 1), S q) * B) * spatialWeight n z :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSk hB0) (spatialWeight_nonneg z)

/-- **Quantitative rapid decay of a weighted Fourier transform.** For every `r : ℝ`, there are
`M : ℕ` and `K ≥ 0` depending only on `n` and `r` such that for any `C^M` function `g` on `ℝⁿ`
whose derivatives of order `≤ M` are bounded by `B ≥ 0`,
`‖𝓕 (z ↦ spatialWeight n z • g z) η‖ ≤ K * B * (1 + ‖η‖²) ^ (-r / 2)`. -/
private theorem exists_norm_fourier_spatialWeight_smul_le (r : ℝ) :
    ∃ (M : ℕ) (K : ℝ), 0 ≤ K ∧ ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
      {g : CoordinateSpace n → F}, ContDiff ℝ M g → ∀ {B : ℝ}, 0 ≤ B →
      (∀ k ≤ M, ∀ z, ‖iteratedFDeriv ℝ k g z‖ ≤ B) → ∀ (η : CoordinateSpace n),
      ‖𝓕 (fun z ↦ spatialWeight n z • g z) η‖ ≤ K * B * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  set M : ℕ := ⌈max r 0⌉₊
  obtain ⟨A, hA0, hA⟩ := exists_norm_iteratedFDeriv_spatialWeight_smul_le (n := n) M
  have hI0 : 0 ≤ ∫ z, spatialWeight n z := integral_nonneg fun z ↦ spatialWeight_nonneg z
  refine ⟨M, 2 ^ M * (A * ∫ z, spatialWeight n z), by positivity,
    fun {F} _ _ {g} hg {B} hB0 hB η ↦ ?_⟩
  set f : CoordinateSpace n → F := fun z ↦ spatialWeight n z • g z
  have hf : ContDiff ℝ M f := (contDiff_spatialWeight.of_le (mod_cast le_top)).smul hg
  have hint (k : ℕ) (hk : k ≤ M) : Integrable (iteratedFDeriv ℝ k f) :=
    (integrable_spatialWeight.const_mul (A * B)).mono'
      (hf.continuous_iteratedFDeriv (mod_cast hk)).aestronglyMeasurable
      (.of_forall (hA hg hB0 hB k hk))
  have hint_le (k : ℕ) (hk : k ≤ M) :
      ∫ z, ‖iteratedFDeriv ℝ k f z‖ ≤ (A * ∫ z, spatialWeight n z) * B :=
    (integral_mono (hint k hk).norm (integrable_spatialWeight.const_mul (A * B))
      (hA hg hB0 hB k hk)).trans_eq (by rw [integral_const_mul]; ring)
  have hpow : (1 + ‖η‖) ^ M * ‖𝓕 f η‖ ≤ 2 ^ M * (A * ∫ z, spatialWeight n z) * B := by
    rcases le_total ‖η‖ 1 with hη | hη
    · have h0 : ‖𝓕 f η‖ ≤ (A * ∫ z, spatialWeight n z) * B :=
        (norm_fourier_le_integral_norm f η).trans
          (by simpa [norm_iteratedFDeriv_zero] using hint_le 0 (Nat.zero_le M))
      have hη2 : (1 + ‖η‖) ^ M ≤ 2 ^ M := pow_le_pow_left₀ (by positivity) (by linarith) M
      exact (mul_le_mul hη2 h0 (norm_nonneg _) (by positivity)).trans_eq (by ring)
    · have hM := (pow_mul_norm_fourier_le_integral_norm_iteratedFDeriv hf hint η).trans
        (hint_le M le_rfl)
      calc (1 + ‖η‖) ^ M * ‖𝓕 f η‖ ≤ (2 * ‖η‖) ^ M * ‖𝓕 f η‖ := by gcongr; linarith
        _ = 2 ^ M * (‖η‖ ^ M * ‖𝓕 f η‖) := by ring
        _ ≤ 2 ^ M * ((2 * π * ‖η‖) ^ M * ‖𝓕 f η‖) := by gcongr; nlinarith [Real.two_le_pi]
        _ ≤ 2 ^ M * ((A * ∫ z, spatialWeight n z) * B) := by gcongr
        _ = 2 ^ M * (A * ∫ z, spatialWeight n z) * B := by ring
  have hw : (1 + ‖η‖ ^ 2) ^ (r / 2) ≤ (1 + ‖η‖) ^ M := by
    have hrmax : r ≤ M := (le_max_left r 0).trans (Nat.le_ceil _)
    exact (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖η‖]) (by linarith)).trans
      (one_add_norm_sq_rpow_le_one_add_norm_pow η M)
  rw [neg_div, Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖𝓕 f η‖ * (1 + ‖η‖ ^ 2) ^ (r / 2) ≤ (1 + ‖η‖) ^ M * ‖𝓕 f η‖ := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ ≤ 2 ^ M * (A * ∫ z, spatialWeight n z) * B := hpow

/-- The weighted Fourier slice `𝓕_z((1 + ‖z‖²) ^ (-(n + 1)) • b(x + z, ξ))(η)` of a symbol `b`. -/
private def weightedSlice (b : Symbol n V W m) (x ξ η : CoordinateSpace n) : V →L[ℂ] W :=
  𝓕 (fun z ↦ spatialWeight n z • b.coefficient (x + z, ξ)) η

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

private theorem exists_norm_iteratedFDeriv_add_slice_le {b : Symbol n V W m}
    (hb : b.IsUniform) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ k ≤ N, ∀ x ξ z,
      ‖iteratedFDeriv ℝ k (fun z ↦ b.coefficient (x + z, ξ)) z‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  choose A hA0 hA using isUniform_iff.1 hb
  set S : ℕ → ℝ := fun k ↦ ∑ r : Fin k → Fin n, A (List.ofFn r) []
  have hS0 (k : ℕ) : 0 ≤ S k := Finset.sum_nonneg fun r _ ↦ hA0 _ _
  refine ⟨∑ k ∈ Finset.range (N + 1), S k, Finset.sum_nonneg fun k _ ↦ hS0 k,
    fun k hk x ξ z ↦ ?_⟩
  rw [iteratedFDeriv_comp_add_left (f := fun y ↦ b.coefficient (y, ξ))]
  have hle : S k ≤ ∑ q ∈ Finset.range (N + 1), S q :=
    Finset.single_le_sum (fun q _ ↦ hS0 q) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  refine (norm_iteratedFDeriv_le_sum_coordinateDeriv
    (contDiff_infty.1 (b.contDiff_coefficient_slice ξ) k) (x + z)).trans ?_
  calc ∑ r : Fin k → Fin n, ‖coordinateDeriv (List.ofFn r) (fun y ↦ b.coefficient (y, ξ)) (x + z)‖
      ≤ ∑ r : Fin k → Fin n, A (List.ofFn r) [] * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
        Finset.sum_le_sum fun r _ ↦ by
          simpa [mixedDeriv_def, coordinateDeriv_nil] using hA (List.ofFn r) [] (x + z) ξ
    _ = S k * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by rw [Finset.sum_mul]
    _ ≤ (∑ q ∈ Finset.range (N + 1), S q) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
        mul_le_mul_of_nonneg_right hle (by positivity)

private theorem exists_norm_weightedSlice_le {b : Symbol n V W m} (hb : b.IsUniform) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ξ η, ‖weightedSlice b x ξ η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨M, K, hK0, hK⟩ := exists_norm_fourier_spatialWeight_smul_le (n := n) r
  obtain ⟨Cb, hCb0, hCb⟩ := exists_norm_iteratedFDeriv_add_slice_le hb M
  refine ⟨K * Cb, mul_nonneg hK0 hCb0, fun x ξ η ↦ ?_⟩
  have hg : ContDiff ℝ M fun z ↦ b.coefficient (x + z, ξ) :=
    ((b.contDiff_coefficient_slice ξ).comp (contDiff_const.add contDiff_id)).of_le (mod_cast le_top)
  exact (hK hg (mul_nonneg hCb0 (by positivity)) (fun k hk z ↦ hCb k hk x ξ z) η).trans_eq (by ring)

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
  rw [continuous_iff_continuousAt]
  intro q₀
  obtain ⟨B, -, hB⟩ := exists_norm_fourierChar_spatialWeight_smul_le_of_dist_lt_one hb q₀.1.2
  have hcont_q (q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n) :
      Continuous fun z ↦
        (𝐞 (-⟪z, q.2⟫) : ℂ) • (spatialWeight n z • b.coefficient (q.1.1 + z, q.1.2)) :=
    (Real.continuous_fourierChar.comp (((innerSL ℝ).flip q.2).continuous.neg)).subtype_val.smul
      (contDiff_spatialWeight.continuous.smul (b.contDiff_coefficient.continuous.comp
        ((continuous_const.add continuous_id).prodMk continuous_const)))
  have hdom : ∀ᶠ q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n in 𝓝 q₀,
      ∀ᵐ z ∂volume, ‖(𝐞 (-⟪z, q.2⟫) : ℂ) •
        (spatialWeight n z • b.coefficient (q.1.1 + z, q.1.2))‖ ≤ B * spatialWeight n z := by
    filter_upwards [Metric.ball_mem_nhds q₀ one_pos] with q hq
    have hq' : dist q q₀ < 1 := hq
    rw [Prod.dist_eq, max_lt_iff, Prod.dist_eq, max_lt_iff] at hq'
    exact .of_forall fun z ↦ hB q.1.1 q.1.2 q.2 z hq'.1.2
  have hcont_z : ∀ᵐ z ∂volume, ContinuousAt
      (fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
        (𝐞 (-⟪z, q.2⟫) : ℂ) • (spatialWeight n z • b.coefficient (q.1.1 + z, q.1.2))) q₀ :=
    .of_forall fun z ↦ by
      have hc : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
          (𝐞 (-⟪z, q.2⟫) : ℂ) • (spatialWeight n z • b.coefficient (q.1.1 + z, q.1.2)) :=
        (Real.continuous_fourierChar.comp
          (((innerSL ℝ z).continuous.comp continuous_snd).neg)).subtype_val.smul
          ((b.contDiff_coefficient.continuous.comp
            (((continuous_fst.comp continuous_fst).add (continuous_const (y := z))).prodMk
              (continuous_snd.comp continuous_fst))).const_smul (spatialWeight n z))
      exact hc.continuousAt
  exact (continuousAt_of_dominated (bound := fun z ↦ B * spatialWeight n z)
    (.of_forall fun q ↦ (hcont_q q).aestronglyMeasurable) hdom
    (integrable_spatialWeight.const_mul B) hcont_z).congr
    (.of_forall fun q ↦ by simp [weightedSlice, Real.fourier_eq, Circle.smul_def])

private theorem differentiableAt_fourierChar_spatialWeight_smul_and_fderiv
    (b : Symbol n V W m) (η z : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ
        (fun q : CoordinateSpace n × CoordinateSpace n ↦
          (𝐞 (-⟪z, η⟫) : ℂ) • (spatialWeight n z • b.coefficient (q.1 + z, q.2))) p ∧
      ∀ v, fderiv ℝ
        (fun q : CoordinateSpace n × CoordinateSpace n ↦
          (𝐞 (-⟪z, η⟫) : ℂ) • (spatialWeight n z • b.coefficient (q.1 + z, q.2))) p v =
        ∑ j, v.1 j • ((𝐞 (-⟪z, η⟫) : ℂ) •
          (spatialWeight n z • (Symbol.spatialDeriv j b).coefficient (p.1 + z, p.2))) +
        ∑ j, v.2 j • ((𝐞 (-⟪z, η⟫) : ℂ) •
          (spatialWeight n z • (Symbol.frequencyDeriv j b).coefficient (p.1 + z, p.2))) := by
  set c : ℂ := (𝐞 (-⟪z, η⟫) : ℂ)
  have hdiff : DifferentiableAt ℝ (fun q : CoordinateSpace n × CoordinateSpace n ↦
      c • (spatialWeight n z • b.coefficient (q.1 + z, q.2))) p :=
    (((b.contDiff_coefficient.differentiable (by simp) _).comp p
      ((differentiableAt_fst.add_const z).prodMk differentiableAt_snd)).const_smul
        (spatialWeight n z)).const_smul c
  refine ⟨hdiff, fun v ↦ ?_⟩
  rw [fderiv_apply_eq_sum_coordinateDeriv hdiff]
  congr 1
  · refine Finset.sum_congr rfl fun j _ ↦ congrArg (v.1 j • ·) ?_
    have h1 : HasFDerivAt (fun x ↦ b.coefficient (x + z, p.2))
        ((fderiv ℝ (fun y ↦ b.coefficient (y, p.2)) (p.1 + z)).comp
          (ContinuousLinearMap.id ℝ _)) p.1 :=
      HasFDerivAt.comp (g := fun y ↦ b.coefficient (y, p.2)) (f := fun x ↦ x + z) p.1
        (((b.contDiff_coefficient_slice p.2).differentiable (by simp) (p.1 + z)).hasFDerivAt)
        ((hasFDerivAt_id p.1).add_const z)
    dsimp only
    rw [coordinateDeriv_cons, coordinateDeriv_nil,
      ((h1.fun_const_smul (spatialWeight n z)).fun_const_smul c).fderiv]
    simp [fderiv_coefficient_single]
  · refine Finset.sum_congr rfl fun j _ ↦ congrArg (v.2 j • ·) ?_
    have h1 : HasFDerivAt (fun ξ ↦ b.coefficient (p.1 + z, ξ))
        (fderiv ℝ (fun ξ ↦ b.coefficient (p.1 + z, ξ)) p.2) p.2 :=
      ((b.contDiff_coefficient.comp (contDiff_prodMk_right (p.1 + z))).differentiable (by simp)
        p.2).hasFDerivAt
    dsimp only
    rw [coordinateDeriv_cons, coordinateDeriv_nil,
      ((h1.fun_const_smul (spatialWeight n z)).fun_const_smul c).fderiv]
    simp [fderiv_coefficient_slice_single]

/-- Differentiation of `weightedSlice` under the `z`-integral. -/
private theorem differentiableAt_weightedSlice_and_fderiv_apply {b : Symbol n V W m}
    (hb : b.IsUniform) (η : CoordinateSpace n) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (fun p ↦ weightedSlice b p.1 p.2 η) p₀ ∧
      ∀ v, fderiv ℝ (fun p ↦ weightedSlice b p.1 p.2 η) p₀ v =
        ∑ j, v.1 j • weightedSlice (Symbol.spatialDeriv j b) p₀.1 p₀.2 η +
        ∑ j, v.2 j • weightedSlice (Symbol.frequencyDeriv j b) p₀.1 p₀.2 η := by
  set F : ∀ {s : ℝ}, Symbol n V W s → CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →
      V →L[ℂ] W :=
    fun c p z ↦ (𝐞 (-⟪z, η⟫) : ℂ) • (spatialWeight n z • c.coefficient (p.1 + z, p.2))
  have hFeq {s : ℝ} (c : Symbol n V W s) (p : CoordinateSpace n × CoordinateSpace n) :
      (∫ z, F c p z) = weightedSlice c p.1 p.2 η := by
    simp [F, weightedSlice, Real.fourier_eq, Circle.smul_def]
  have hFc {s : ℝ} (c : Symbol n V W s) (p : CoordinateSpace n × CoordinateSpace n) :
      Continuous (F c p) :=
    (Real.continuous_fourierChar.comp (((innerSL ℝ).flip η).continuous.neg)).subtype_val.smul
      (contDiff_spatialWeight.continuous.smul
        ((c.contDiff_coefficient_slice p.2).continuous.comp (continuous_const.add continuous_id)))
  choose Cx _ hCx using fun j ↦
    exists_norm_fourierChar_spatialWeight_smul_le_of_dist_lt_one (hb.spatialDeriv j) p₀.2
  choose Cξ _ hCξ using fun j ↦
    exists_norm_fourierChar_spatialWeight_smul_le_of_dist_lt_one (hb.frequencyDeriv j) p₀.2
  have key := differentiableAt_integral_and_fderiv_apply_eq_sum
    (F := F b) (A := fun j ↦ F (Symbol.spatialDeriv j b))
    (B := fun j ↦ F (Symbol.frequencyDeriv j b))
    (fun z p ↦ (differentiableAt_fourierChar_spatialWeight_smul_and_fderiv b η z p).1)
    (fun z p ↦ (differentiableAt_fourierChar_spatialWeight_smul_and_fderiv b η z p).2)
    (fun p ↦ ((Real.fourierIntegral_convergent_iff η).2
      (integrable_spatialWeight_smul_slice hb p.1 p.2)).congr
        (.of_forall fun _ ↦ Circle.smul_def _ _))
    (fun j p ↦ hFc _ p) (fun j p ↦ hFc _ p)
    (integrable_spatialWeight.const_mul (∑ j, Cx j + ∑ j, Cξ j)) p₀ fun z p hp ↦ by
      have hp' : dist p p₀ < 1 := hp
      rw [Prod.dist_eq, max_lt_iff] at hp'
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]
      exact add_le_add (Finset.sum_le_sum fun j _ ↦ hCx j p.1 p.2 η z hp'.2)
        (Finset.sum_le_sum fun j _ ↦ hCξ j p.1 p.2 η z hp'.2)
  simp only [hFeq] at key
  exact key

end WeightedSlice

/-! ### The integrand and coefficient of `uniformSharp` -/

section Integrand

variable (a : Symbol n W U m') (b : Symbol n V W m)

/-- The integrand `(((1 - Δ_ξ) ^ (n + 1) a)(x, ξ + 2πη)) ∘ weightedSlice b x ξ η` of the uniform
composition symbol. -/
private def uniformIntegrand (p : CoordinateSpace n × CoordinateSpace n) (η : CoordinateSpace n) :
    V →L[ℂ] U :=
  ((oneSubFreqLaplacian^[n + 1] a).coefficient (p.1, p.2 + (2 * π) • η)).comp
    (weightedSlice b p.1 p.2 η)

/-- The coefficient `∫ uniformIntegrand a b (x, ξ) η dη` of `a.uniformSharp b hb`. -/
private def uniformCompCoeff (p : CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] U :=
  ∫ η, uniformIntegrand a b p η

variable {a b}

/-- Pointwise Peetre bound on `(A(x, ξ + 2πη)).comp (W η)` when `‖A(x, ζ)‖ ≤ Ca ⟨ζ⟩ ^ m'` and
`‖W η‖ ≤ Cw ⟨ξ⟩ ^ m ⟨η⟩ ^ (-(|m'| + r))`. -/
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

private theorem exists_norm_uniformIntegrand_le (a : Symbol n W U m') (hb : b.IsUniform)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ η, ‖uniformIntegrand a b (x, ξ) η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨Ca, hCa0, hCa⟩ := (oneSubFreqLaplacian^[n + 1] a).exists_bound_coefficient K hK
  exact exists_norm_uniformIntegrand_le_of_bound hCa0 hCa hb r

private theorem integrable_uniformIntegrand (a : Symbol n W U m') (hb : b.IsUniform)
    (p : CoordinateSpace n × CoordinateSpace n) : Integrable (uniformIntegrand a b p) := by
  obtain ⟨C, -, hC⟩ := exists_norm_uniformIntegrand_le a hb (isCompact_singleton (x := p.1))
    ((n : ℝ) + 1)
  exact (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
    (C * (1 + ‖p.2‖ ^ 2) ^ ((m' + m) / 2))).mono'
    ((continuous_uniformIntegrand (a := a) hb).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (.of_forall fun η ↦ hC p.1 rfl p.2 η)

private theorem exists_norm_uniformIntegrand_le_of_mem_ball (a : Symbol n W U m')
    (hb : b.IsUniform) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    ∃ C, 0 ≤ C ∧ ∀ η, ∀ p ∈ Metric.ball p₀ 1,
      ‖uniformIntegrand a b p η‖ ≤ C * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_uniformIntegrand_le a hb (isCompact_closedBall p₀.1 1)
    ((n : ℝ) + 1)
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
    rw [fderiv_apply_eq_sum_coordinateDeriv hAd]
    congr 1
    · exact Finset.sum_congr rfl fun j _ ↦ by dsimp only; rw [← coefficient_spatialDeriv]
    · refine Finset.sum_congr rfl fun j _ ↦ congrArg (v.2 j • ·) ?_
      have h1 : HasFDerivAt (fun ζ ↦ a'.coefficient (p.1, ζ + c))
          ((fderiv ℝ (fun ζ ↦ a'.coefficient (p.1, ζ)) (p.2 + c)).comp
            (ContinuousLinearMap.id ℝ _)) p.2 :=
        HasFDerivAt.comp (g := fun ζ ↦ a'.coefficient (p.1, ζ)) (f := fun ζ ↦ ζ + c) p.2
          (((a'.contDiff_coefficient.comp (contDiff_prodMk_right p.1)).differentiable (by simp)
            (p.2 + c)).hasFDerivAt) ((hasFDerivAt_id p.2).add_const c)
      dsimp only
      rw [coordinateDeriv_cons, coordinateDeriv_nil, h1.fderiv]
      simp [fderiv_coefficient_slice_single]
  have hB := differentiableAt_weightedSlice_and_fderiv_apply hb η p
  have h := Φ.hasFDerivAt_of_bilinear hAd.hasFDerivAt hB.1.hasFDerivAt
  have hbi : (fun q ↦ uniformIntegrand a b q η) =
      fun q ↦ Φ (a'.coefficient (q.1, q.2 + c)) (weightedSlice b q.1 q.2 η) := rfl
  rw [hbi]
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
  have key := differentiableAt_integral_and_fderiv_apply_eq_sum
    (F := uniformIntegrand a b)
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

private theorem exists_norm_uniformCompCoeff_le {K : Set (CoordinateSpace n)}
    {Ca : ℝ} (hCa0 : 0 ≤ Ca)
    (hCa : ∀ x ∈ K, ∀ ξ,
      ‖(oneSubFreqLaplacian^[n + 1] a).coefficient (x, ξ)‖ ≤ Ca * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    (hb : b.IsUniform) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖uniformCompCoeff a b (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_uniformIntegrand_le_of_bound hCa0 hCa hb ((n : ℝ) + 1)
  set I : ℝ := ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  refine ⟨C * I, mul_nonneg hC0 (integral_nonneg fun _ ↦ by positivity), fun x hx ξ ↦ ?_⟩
  exact (norm_integral_le_of_norm_le
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
      (C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2)))
    (.of_forall fun η ↦ hC x hx ξ η)).trans_eq (by rw [integral_const_mul]; ring)

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
  simpa only [sub_zero] using exists_norm_mixedDeriv_le_of_leibniz 0 P hPspatial hPfrequency
    IsUniform (fun hb j ↦ hb.spatialDeriv j) (fun hb j ↦ hb.frequencyDeriv j)
    (fun a b _ ↦ uniformCompCoeff a b) (fun a _ hb ↦ contDiff_uniformCompCoeff a hb)
    (fun a _ hb ↦ coordinateDeriv_fst_uniformCompCoeff a hb)
    (fun a _ hb ↦ coordinateDeriv_snd_uniformCompCoeff a hb)
    (fun _ ha _ hb ↦ by
      obtain ⟨Ca, hCa0, hCa⟩ := hP ha
      simpa only [sub_zero] using exists_norm_uniformCompCoeff_le hCa0 hCa hb)
    a ha hb α β

end Integrand

/-! ### The uniform composition symbol -/

section UniformSharp

variable (a : Symbol n W U m') (b : Symbol n V W m)

/-- The **uniform composition symbol** `a.uniformSharp b hb` of a symbol `a` of order `m'` and a
uniform symbol `b` of order `m`, a symbol of order `m' + m`:

`(a #_u b)(x, ξ) = ∫ (((1 - Δ_ξ)^(n+1) a)(x, ξ + 2πη)) ∘ 𝓕_z(⟨z⟩^(-2(n+1)) • b(x + z, ξ))(η) dη`.

When `b` has compact spatial support, integrating by parts `n + 1` times in `z` identifies
`a.uniformSharp b hb.isUniform` with `a.sharp b hb` (`Symbol.uniformSharp_eq_sharp`). When `a` also
satisfies uniform estimates, so does `a.uniformSharp b hb` (`Symbol.IsUniform.uniformSharp`), and
`Op(a #_u b) = Op(a) ∘ Op(b)` on Schwartz space (`Symbol.quantizeUniformCLM_uniformSharp`). -/
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

private theorem coefficient_uniformSharp_eq_uniformCompCoeff (hb : b.IsUniform) :
    (a.uniformSharp b hb).coefficient = uniformCompCoeff a b :=
  (rfl)

private theorem uniformCompCoeff_congr {m₁ m₂ k₁ k₂ : ℝ}
    {a₁ : Symbol n W U m₁} {a₂ : Symbol n W U m₂}
    {b₁ : Symbol n V W k₁} {b₂ : Symbol n V W k₂}
    (ha : a₁.coefficient = a₂.coefficient) (hb : b₁.coefficient = b₂.coefficient) :
    uniformCompCoeff a₁ b₁ = uniformCompCoeff a₂ b₂ := by
  funext p
  simp only [uniformCompCoeff, uniformIntegrand, weightedSlice,
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
  rw [coefficient_frequencyDeriv]
  exact coordinateDeriv_snd_uniformCompCoeff a hb j x ξ

/-- **Uniform composition preserves uniform estimates.** If both `a` and `b` satisfy uniform symbol
estimates in all positions, then so does their composition symbol `a.uniformSharp b hb`. -/
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
  rw [coefficient_uniformSharp_eq_uniformCompCoeff, uniformCompCoeff]
  exact integral_eq_zero_of_ae (.of_forall fun η ↦ by
    rw [uniformIntegrand, hKa x hx]; exact ContinuousLinearMap.zero_comp _)

/-! ### Bilinearity, inclusions, and the smoothing ideal -/

theorem add_uniformSharp (a₁ a₂ : Symbol n W U m') (hb : b.IsUniform) :
    (a₁ + a₂).uniformSharp b hb = a₁.uniformSharp b hb + a₂.uniformSharp b hb := by
  ext1; funext p
  simp only [coefficient_add, Pi.add_apply, coefficient_uniformSharp_eq_uniformCompCoeff,
    uniformCompCoeff, ← integral_add (integrable_uniformIntegrand a₁ hb p)
      (integrable_uniformIntegrand a₂ hb p)]
  exact integral_congr_ae (.of_forall fun η ↦ by
    rw [uniformIntegrand, iterate_oneSubFreqLaplacian_add]
    simp [uniformIntegrand, ContinuousLinearMap.add_comp])

theorem uniformSharp_add (a : Symbol n W U m') {b₁ b₂ : Symbol n V W m}
    (hb₁ : b₁.IsUniform) (hb₂ : b₂.IsUniform) :
    a.uniformSharp (b₁ + b₂) (hb₁.add hb₂) = a.uniformSharp b₁ hb₁ + a.uniformSharp b₂ hb₂ := by
  ext1; funext ⟨x, ξ⟩
  have hw (η : CoordinateSpace n) :
      weightedSlice (b₁ + b₂) x ξ η = weightedSlice b₁ x ξ η + weightedSlice b₂ x ξ η := by
    have hi {c : Symbol n V W m} (hc : c.IsUniform) := ((Real.fourierIntegral_convergent_iff η).2
      (integrable_spatialWeight_smul_slice hc x ξ)).congr (.of_forall fun _ ↦ Circle.smul_def _ _)
    simp only [weightedSlice, Real.fourier_eq, coefficient_add, Pi.add_apply, Circle.smul_def]
    simp only [smul_add]; exact integral_add (hi hb₁) (hi hb₂)
  simp only [coefficient_add, Pi.add_apply, coefficient_uniformSharp_eq_uniformCompCoeff,
    uniformCompCoeff, ← integral_add (integrable_uniformIntegrand a hb₁ (x, ξ))
      (integrable_uniformIntegrand a hb₂ (x, ξ))]
  exact integral_congr_ae (.of_forall fun η ↦ by
    simp [uniformIntegrand, hw, ContinuousLinearMap.comp_add])

@[simp]
theorem smul_uniformSharp (c : ℂ) (a : Symbol n W U m') (hb : b.IsUniform) :
    (c • a).uniformSharp b hb = c • a.uniformSharp b hb := by
  ext1; funext p
  simp only [coefficient_smul, Pi.smul_apply, coefficient_uniformSharp_eq_uniformCompCoeff,
    uniformCompCoeff, ← integral_smul]
  exact integral_congr_ae (.of_forall fun η ↦ by
    rw [uniformIntegrand, iterate_oneSubFreqLaplacian_smul]; simp [uniformIntegrand])

@[simp]
theorem uniformSharp_smul (a : Symbol n W U m') (hb : b.IsUniform) (c : ℂ) :
    a.uniformSharp (c • b) (hb.smul c) = c • a.uniformSharp b hb := by
  ext1; funext ⟨x, ξ⟩
  have hw (η : CoordinateSpace n) : weightedSlice (c • b) x ξ η = c • weightedSlice b x ξ η := by
    simp only [weightedSlice, Real.fourier_eq, coefficient_smul, Pi.smul_apply,
      smul_comm (spatialWeight n _) c, smul_comm (𝐞 _) c, integral_smul]
  simp only [coefficient_smul, Pi.smul_apply, coefficient_uniformSharp_eq_uniformCompCoeff,
    uniformCompCoeff, ← integral_smul]
  exact integral_congr_ae (.of_forall fun η ↦ by simp [uniformIntegrand, hw])

@[simp]
theorem zero_uniformSharp (hb : b.IsUniform) : (0 : Symbol n W U m').uniformSharp b hb = 0 := by
  simpa using smul_uniformSharp (0 : ℂ) (0 : Symbol n W U m') hb

@[simp]
theorem uniformSharp_zero (a : Symbol n W U m')
    (h : (0 : Symbol n V W m).IsUniform := hasCompactSpatialSupport_zero.isUniform) :
    a.uniformSharp (0 : Symbol n V W m) h = 0 := by
  simpa using uniformSharp_smul a h 0

@[simp]
theorem neg_uniformSharp (a : Symbol n W U m') (hb : b.IsUniform) :
    (-a).uniformSharp b hb = -a.uniformSharp b hb := by
  simpa using smul_uniformSharp (-1 : ℂ) a hb

@[simp]
theorem uniformSharp_neg (a : Symbol n W U m') (hb : b.IsUniform) (hnb : (-b).IsUniform) :
    a.uniformSharp (-b) hnb = -a.uniformSharp b hb := by
  have heq : -b = (-1 : ℂ) • b := (neg_one_smul ℂ b).symm
  simpa [← heq] using uniformSharp_smul a hb (-1)

theorem sub_uniformSharp (a₁ a₂ : Symbol n W U m') (hb : b.IsUniform) :
    (a₁ - a₂).uniformSharp b hb = a₁.uniformSharp b hb - a₂.uniformSharp b hb := by
  rw [sub_eq_add_neg, add_uniformSharp, neg_uniformSharp, ← sub_eq_add_neg]

theorem uniformSharp_sub (a : Symbol n W U m') {b₁ b₂ : Symbol n V W m}
    (hb₁ : b₁.IsUniform) (hb₂ : b₂.IsUniform) (hb₁₂ : (b₁ - b₂).IsUniform) :
    a.uniformSharp (b₁ - b₂) hb₁₂ = a.uniformSharp b₁ hb₁ - a.uniformSharp b₂ hb₂ := by
  have hnb₂ : (-b₂).IsUniform := by simpa using hb₂.smul (-1)
  have h1 : a.uniformSharp (b₁ - b₂) hb₁₂ = a.uniformSharp (b₁ + -b₂) (hb₁.add hnb₂) := by
    simp only [sub_eq_add_neg]
  rw [h1, uniformSharp_add a hb₁ hnb₂, uniformSharp_neg a hb₂ hnb₂, ← sub_eq_add_neg]

theorem inclusion_uniformSharp {m'' : ℝ} (h : m' ≤ m'') (a : Symbol n W U m') (hb : b.IsUniform) :
    (Symbol.inclusion h a).uniformSharp b hb =
      Symbol.inclusion (by linarith) (a.uniformSharp b hb) := by
  ext1; rw [coefficient_inclusion]
  exact uniformCompCoeff_congr (b₁ := b) (coefficient_inclusion h a) rfl

theorem uniformSharp_inclusion {m'' : ℝ} (h : m ≤ m'') (a : Symbol n W U m') (hb : b.IsUniform) :
    a.uniformSharp (Symbol.inclusion h b) (hb.inclusion h) =
      Symbol.inclusion (by linarith) (a.uniformSharp b hb) := by
  ext1; rw [coefficient_inclusion]
  exact uniformCompCoeff_congr (a₁ := a) rfl (coefficient_inclusion h b)

/-- Smoothing symbols form a right ideal for `uniformSharp`. -/
theorem IsSmoothing.uniformSharp_right (ha : a.IsSmoothing) (b : Symbol n V W m)
    (hb : b.IsUniform) : (a.uniformSharp b hb).IsSmoothing := isSmoothing_iff.2 fun m'' ↦ by
  obtain ⟨a', ha'⟩ := isSmoothing_iff.1 ha (m'' - m)
  exact ⟨Symbol.inclusion (by linarith) (a'.uniformSharp b hb),
    (coefficient_inclusion _ _).trans (uniformCompCoeff_congr (b₁ := b) ha' rfl)⟩

/-- Smoothing symbols form a left ideal for `uniformSharp`: if `b` is uniform at every symbol
order, then `a.uniformSharp b hb` is smoothing. -/
theorem IsSmoothing.uniformSharp_left {b : Symbol n V W m} (hb : b.IsUniform)
    (hbs : ∀ m₁ : ℝ, ∃ b' : Symbol n V W m₁, b'.IsUniform ∧ b'.coefficient = b.coefficient)
    (a : Symbol n W U m') : (a.uniformSharp b hb).IsSmoothing := isSmoothing_iff.2 fun m'' ↦ by
  obtain ⟨b', hb'u, hb'⟩ := hbs (m'' - m')
  exact ⟨Symbol.inclusion (by linarith) (a.uniformSharp b' hb'u),
    (coefficient_inclusion _ _).trans (uniformCompCoeff_congr (a₁ := a) rfl hb')⟩

end UniformSharp

/-! ### Agreement with `Symbol.sharp` for compactly supported symbols -/

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

/-- Frequency-translated symbol `(y, ζ) ↦ a(y, ξ₀ + ζ)`. -/
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
    have hp : (1 + ‖ξ₀ + ζ‖ ^ 2) ^ (r / 2) ≤
        2 ^ (|r| / 2) * (1 + ‖ζ‖ ^ 2) ^ (r / 2) * (1 + ‖ξ₀‖ ^ 2) ^ (|r| / 2) := by
      rw [add_comm ξ₀ ζ]; exact one_add_norm_add_sq_rpow_le_mul r ζ ξ₀
    rw [hmd]
    exact (hC x hx (ξ₀ + ζ)).trans ((mul_le_mul_of_nonneg_left hp hC0).trans_eq (by ring))

private theorem frequencyDeriv_shiftFreq (ξ₀ : CoordinateSpace n) (j : Fin n)
    (a : Symbol n W U m') :
    Symbol.frequencyDeriv j (shiftFreq ξ₀ a) = shiftFreq ξ₀ (Symbol.frequencyDeriv j a) := by
  ext1; funext ⟨y, ζ⟩
  simpa [shiftFreq] using coordinateDeriv_coefficient_add_left a [j] y ξ₀ ζ

private theorem coefficient_iterate_oneSubFreqLaplacian_shiftFreq (ξ₀ : CoordinateSpace n)
    (k : ℕ) (a : Symbol n W U m') (x ζ : CoordinateSpace n) :
    (oneSubFreqLaplacian^[k] (shiftFreq ξ₀ a)).coefficient (x, ζ) =
      (oneSubFreqLaplacian^[k] a).coefficient (x, ξ₀ + ζ) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    have h1 : oneSubFreqLaplacian (shiftFreq ξ₀ a) = shiftFreq ξ₀ (oneSubFreqLaplacian a) := by
      ext1; funext ⟨y, η⟩
      simp only [oneSubFreqLaplacian, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        coefficient_sub, Pi.sub_apply, coefficient_inclusion, frequencyLaplacian_eq_sum,
        coefficient_sum, Finset.sum_apply, frequencyDeriv_shiftFreq]
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
the oscillatory-integral regularization in `a.uniformSharp b hb.isUniform` gives the exact same
coefficient as `a.sharp b hb`. -/
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
    rw [SchwartzMap.smulLeftCLM_apply_apply htg_neg f (x + z), hb.coe_sliceSchwartz, hnorm,
      smul_smul, hchar]; rfl
  rw [hsharp, ← iterate_smulLeftCLM_one_add_norm_sub_sq_cancel x f,
    quantizeSchwartzValue_iterate_smulLeftCLM_one_add_norm_sub_sq, quantizeSchwartzValue_def,
    coefficient_uniformSharp_eq_uniformCompCoeff, uniformCompCoeff]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  dsimp only; rw [Circle.smul_def, hc_iter η, ← map_smul, hphase η]; simp [Φ, uniformIntegrand]

/-- **Compatibility with `Symbol.sharp`.** When `b` has compact spatial support, `a.uniformSharp b
hb.isUniform` is equal to `a.sharp b hb` as a symbol of order `m' + m`. -/
@[simp]
theorem uniformSharp_eq_sharp {a : Symbol n W U m'} {b : Symbol n V W m}
    (hb : b.HasCompactSpatialSupport) :
    a.uniformSharp b hb.isUniform = a.sharp b hb :=
  Symbol.ext (coefficient_uniformSharp_eq_sharp hb)

end Agreement

/-! ### Left identity -/

section LeftIdentity

/-- The constant identity symbol `1` is a left identity for `uniformSharp`: `1 #_u b = b` up to the
order identification `0 + m = m`. -/
@[simp]
theorem const_id_uniformSharp [CompleteSpace W] {b : Symbol n V W m} (hb : b.IsUniform) :
    (const (ContinuousLinearMap.id ℂ W)).uniformSharp b hb =
      Symbol.inclusion (zero_add m).ge b := by
  ext1; funext ⟨x, ξ⟩
  rw [coefficient_inclusion]
  have hconst : (oneSubFreqLaplacian^[n + 1] (const (ContinuousLinearMap.id ℂ W) :
      Symbol n W W 0)).coefficient = fun _ ↦ ContinuousLinearMap.id ℂ W := by
    have h1 : oneSubFreqLaplacian (const (ContinuousLinearMap.id ℂ W) : Symbol n W W 0) =
        const (ContinuousLinearMap.id ℂ W) := by
      ext1; funext ⟨y, η⟩
      simp [oneSubFreqLaplacian, frequencyLaplacian_eq_sum, coordinateDeriv_const]
    rw [Function.iterate_fixed h1 (n + 1)]
    exact funext (coefficient_const _)
  set g : CoordinateSpace n → V →L[ℂ] W := fun z ↦ spatialWeight n z • b.coefficient (x + z, ξ)
  have hg_cont : Continuous g := contDiff_spatialWeight.continuous.smul
    ((b.contDiff_coefficient_slice ξ).continuous.comp (continuous_const.add continuous_id))
  have hinv : 𝓕⁻ (𝓕 g) 0 = g 0 := congrFun (hg_cont.fourierInv_fourier_eq
    (integrable_spatialWeight_smul_slice hb x ξ) (integrable_weightedSlice hb x ξ)) 0
  calc ((const (ContinuousLinearMap.id ℂ W)).uniformSharp b hb).coefficient (x, ξ)
      = 𝓕⁻ (𝓕 g) 0 := by
        rw [coefficient_uniformSharp_eq_uniformCompCoeff, uniformCompCoeff, Real.fourierInv_eq]
        exact integral_congr_ae (.of_forall fun η ↦ by
          rw [uniformIntegrand, hconst]; simp [weightedSlice, g])
    _ = b.coefficient (x, ξ) := by rw [hinv]; simp [g, spatialWeight]

end LeftIdentity

/-! ### Operator composition on Schwartz space via dyadic spatial truncation -/

section Operator

/-- Dyadic spatial truncation `b_N(y, ξ) = φ(2^{-N} y) • b(y, ξ)` of a symbol `b` by a bump `φ`
equal to `1` near `0`. -/
private def spatialTrunc (φ : ContDiffBump (0 : CoordinateSpace n)) (N : ℕ)
    (b : Symbol n V W m) : Symbol n V W (0 + m) :=
  (ofSpatial (fun y ↦ (φ (((2 : ℝ) ^ N)⁻¹ • y) : ℂ) • ContinuousLinearMap.id ℂ W)
    ((Complex.ofRealCLM.contDiff.comp (φ.contDiff.comp
      (contDiff_id.const_smul ((2 : ℝ) ^ N)⁻¹))).smul contDiff_const)).comp b

private theorem coefficient_spatialTrunc (φ : ContDiffBump (0 : CoordinateSpace n)) (N : ℕ)
    (b : Symbol n V W m) (y ξ : CoordinateSpace n) :
    (spatialTrunc φ N b).coefficient (y, ξ) =
      (φ (((2 : ℝ) ^ N)⁻¹ • y) : ℂ) • b.coefficient (y, ξ) := by
  simp [spatialTrunc]

private theorem hasCompactSpatialSupport_spatialTrunc (φ : ContDiffBump (0 : CoordinateSpace n))
    (N : ℕ) (b : Symbol n V W m) : (spatialTrunc φ N b).HasCompactSpatialSupport := by
  have hφ : HasCompactSupport fun y : CoordinateSpace n ↦ φ (((2 : ℝ) ^ N)⁻¹ • y) :=
    φ.hasCompactSupport.comp_smul (inv_ne_zero (pow_ne_zero N two_ne_zero))
  refine ((hasCompactSpatialSupport_ofSpatial_iff _).2 ?_).comp_right b
  exact HasCompactSupport.intro hφ.isCompact fun y hy ↦ by
    simp [image_eq_zero_of_notMem_tsupport hy]

private theorem exists_norm_iteratedFDeriv_bump_le (φ : ContDiffBump (0 : CoordinateSpace n))
    (k : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖iteratedFDeriv ℝ k (fun y ↦ (φ y : ℝ)) y‖ ≤ B := by
  obtain ⟨B, hB⟩ := φ.hasCompactSupport.isCompact.exists_bound_of_continuousOn
    ((φ.contDiff.of_le (mod_cast le_top)).continuous_iteratedFDeriv le_rfl).continuousOn
  refine ⟨max B 0, le_max_right _ _, fun y ↦ ?_⟩
  by_cases hy : y ∈ tsupport φ
  · exact (hB y hy).trans (le_max_left _ _)
  · rw [Function.notMem_support.1 fun h ↦ hy (support_iteratedFDeriv_subset k h), norm_zero]
    exact le_max_right _ _

private theorem exists_norm_weightedSlice_spatialTrunc_le
    (φ : ContDiffBump (0 : CoordinateSpace n)) {b : Symbol n V W m} (hb : b.IsUniform) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (N : ℕ) x ξ η,
      ‖weightedSlice (spatialTrunc φ N b) x ξ η‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨M, K, hK0, hK⟩ := exists_norm_fourier_spatialWeight_smul_le (n := n) r
  obtain ⟨Cb, hCb0, hCb⟩ := exists_norm_iteratedFDeriv_add_slice_le hb M
  choose Bφ hBφ0 hBφ using exists_norm_iteratedFDeriv_bump_le φ
  set S : ℕ → ℝ := fun k ↦ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Bφ i
  have hS0 (k : ℕ) : 0 ≤ S k := Finset.sum_nonneg fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (hBφ0 i)
  set A : ℝ := ∑ k ∈ Finset.range (M + 1), S k
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ ↦ hS0 k
  refine ⟨K * (A * Cb), by positivity, fun N x ξ η ↦ ?_⟩
  set s : ℝ := ((2 : ℝ) ^ N)⁻¹
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  have hf : ContDiff ℝ M fun z ↦ φ (s • (x + z)) :=
    (φ.contDiff.of_le (mod_cast le_top)).comp ((contDiff_const.add contDiff_id).const_smul s)
  have hg : ContDiff ℝ M fun z ↦ b.coefficient (x + z, ξ) :=
    ((b.contDiff_coefficient_slice ξ).comp (contDiff_const.add contDiff_id)).of_le (mod_cast le_top)
  have hcut : (fun z ↦ (spatialTrunc φ N b).coefficient (x + z, ξ)) =
      fun z ↦ φ (s • (x + z)) • b.coefficient (x + z, ξ) := by
    funext z; rw [coefficient_spatialTrunc]
    exact Complex.coe_smul (φ (s • (x + z))) (b.coefficient (x + z, ξ))
  have htrunc_deriv (k : ℕ) (hk : k ≤ M) (z : CoordinateSpace n) :
      ‖iteratedFDeriv ℝ k (fun z ↦ (spatialTrunc φ N b).coefficient (x + z, ξ)) z‖ ≤
        (A * Cb) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
    rw [hcut]
    have hf_bound (i : ℕ) : ‖iteratedFDeriv ℝ i (fun z ↦ φ (s • (x + z))) z‖ ≤ Bφ i := by
      rw [iteratedFDeriv_comp_add_left (f := fun y ↦ φ (s • y)),
        norm_iteratedFDeriv_comp_const_smul (fun y ↦ (φ y : ℝ)) s (x + z) i,
        Real.norm_of_nonneg hs0]
      exact (mul_le_mul (pow_le_pow_left₀ hs0 hs1 i) (hBφ i _) (norm_nonneg _)
        (by positivity)).trans_eq (by rw [one_pow, one_mul])
    have hSk : S k ≤ A := Finset.single_le_sum (fun q _ ↦ hS0 q)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
    refine (norm_iteratedFDeriv_smul_le hf hg z (mod_cast hk)).trans ?_
    calc ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z ↦ φ (s • (x + z))) z‖ *
            ‖iteratedFDeriv ℝ (k - i) (fun z ↦ b.coefficient (x + z, ξ)) z‖
        ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Bφ i * (Cb * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :=
          Finset.sum_le_sum fun i _ ↦
            mul_le_mul (mul_le_mul_of_nonneg_left (hf_bound i) (Nat.cast_nonneg _))
              (hCb (k - i) ((Nat.sub_le k i).trans hk) x ξ z) (norm_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) (hBφ0 i))
      _ = S k * Cb * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
          simp only [S, Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ ≤ (A * Cb) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSk hCb0) (by positivity)
  have hg' : ContDiff ℝ M fun z ↦ (spatialTrunc φ N b).coefficient (x + z, ξ) := by
    rw [hcut]; exact hf.smul hg
  simpa only [weightedSlice, zero_add, mul_assoc] using hK hg' (by positivity) htrunc_deriv η

private theorem exists_norm_uniformIntegrand_spatialTrunc_le
    (φ : ContDiffBump (0 : CoordinateSpace n)) (a : Symbol n W U m') {b : Symbol n V W m}
    (hb : b.IsUniform) (x : CoordinateSpace n) :
    ∃ C, 0 ≤ C ∧ ∀ N ξ η, ‖uniformIntegrand a (spatialTrunc φ N b) (x, ξ) η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  obtain ⟨Ca, hCa0, hCa⟩ := (oneSubFreqLaplacian^[n + 1] a).exists_bound_coefficient_slice x
  obtain ⟨Cw, hCw0, hCw⟩ := exists_norm_weightedSlice_spatialTrunc_le φ hb (|m'| + ((n : ℝ) + 1))
  refine ⟨Ca * 2 ^ (|m'| / 2) * (2 * π) ^ |m'| * Cw, by positivity, fun N ξ η ↦ ?_⟩
  simpa only [uniformIntegrand, zero_add] using
    norm_comp_shift_two_pi_le (m := m) hCa hCw0 (hCw N x ξ η)

private theorem tendsto_weightedSlice_spatialTrunc (φ : ContDiffBump (0 : CoordinateSpace n))
    {b : Symbol n V W m} (hb : b.IsUniform) (x ξ η : CoordinateSpace n) :
    Tendsto (fun N ↦ weightedSlice (spatialTrunc φ N b) x ξ η)
      atTop (𝓝 (weightedSlice b x ξ η)) := by
  obtain ⟨Cb, -, hCb⟩ := hb.exists_bound_coefficient
  simp only [weightedSlice, Real.fourier_eq]
  refine tendsto_integral_of_dominated_convergence
    (fun z ↦ (Cb * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) * spatialWeight n z)
    (fun N ↦ ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (contDiff_spatialWeight.continuous.smul
        (((spatialTrunc φ N b).contDiff_coefficient_slice ξ).continuous.comp
          (continuous_const.add continuous_id)))).aestronglyMeasurable)
    (integrable_spatialWeight.const_mul _) (fun N ↦ .of_forall fun z ↦ ?_)
    (.of_forall fun z ↦ ?_)
  · rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul, norm_smul,
      Real.norm_of_nonneg (spatialWeight_nonneg z), coefficient_spatialTrunc, norm_smul,
      Complex.norm_real, Real.norm_of_nonneg φ.nonneg, mul_comm]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul φ.le_one (hCb (x + z) ξ) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
      (spatialWeight_nonneg z)
  · have h0 : Tendsto (fun N : ℕ ↦ ((2 : ℝ) ^ N)⁻¹ • (x + z)) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ)))).smul_const (x + z)
    have hφc : Continuous fun y : CoordinateSpace n ↦ φ y := φ.continuous
    have hφ1 : Tendsto (fun N : ℕ ↦ (φ (((2 : ℝ) ^ N)⁻¹ • (x + z)) : ℂ)) atTop (𝓝 1) := by
      have h := (Complex.continuous_ofReal.tendsto (φ 0)).comp ((hφc.tendsto 0).comp h0)
      simp only [Function.comp_def,
        φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le), Complex.ofReal_one] at h
      exact h
    simpa [coefficient_spatialTrunc] using
      ((hφ1.smul_const (b.coefficient (x + z, ξ))).const_smul (spatialWeight n z)).const_smul
        (𝐞 (-⟪z, η⟫))

private theorem tendsto_coefficient_sharp_spatialTrunc
    (φ : ContDiffBump (0 : CoordinateSpace n)) (a : Symbol n W U m') {b : Symbol n V W m}
    (hb : b.IsUniform) (x ξ : CoordinateSpace n) :
    Tendsto (fun N ↦ (a.sharp (spatialTrunc φ N b)
        (hasCompactSpatialSupport_spatialTrunc φ N b)).coefficient (x, ξ))
      atTop (𝓝 ((a.uniformSharp b hb).coefficient (x, ξ))) := by
  have heq (N : ℕ) : (a.sharp (spatialTrunc φ N b)
      (hasCompactSpatialSupport_spatialTrunc φ N b)).coefficient (x, ξ) =
        uniformCompCoeff a (spatialTrunc φ N b) (x, ξ) := by
    rw [← coefficient_uniformSharp_eq_sharp, coefficient_uniformSharp_eq_uniformCompCoeff]
  simp only [heq, coefficient_uniformSharp_eq_uniformCompCoeff, uniformCompCoeff]
  obtain ⟨C, -, hC⟩ := exists_norm_uniformIntegrand_spatialTrunc_le φ a hb x
  refine tendsto_integral_of_dominated_convergence
    (fun η ↦ (C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2)) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2))
    (fun N ↦ (integrable_uniformIntegrand a (hasCompactSpatialSupport_spatialTrunc φ N b).isUniform
      (x, ξ)).aestronglyMeasurable)
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul _)
    (fun N ↦ .of_forall (hC N ξ)) (.of_forall fun η ↦ ?_)
  exact (((ContinuousLinearMap.compL ℂ V W U)
    ((oneSubFreqLaplacian^[n + 1] a).coefficient (x, ξ + (2 * π) • η))).continuous.tendsto _).comp
    (tendsto_weightedSlice_spatialTrunc φ hb x ξ η)

private theorem quantizeSchwartzValue_sharp_spatialTrunc_eq [CompleteSpace W] [CompleteSpace U]
    (φ : ContDiffBump (0 : CoordinateSpace n)) (N : ℕ) (a : Symbol n W U m')
    {b : Symbol n V W m} (hb : b.IsUniform) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.sharp (spatialTrunc φ N b)
        (hasCompactSpatialSupport_spatialTrunc φ N b)).coefficient u x =
      quantizeSchwartzValue a.coefficient
        (SchwartzMap.smulLeftCLM W (fun y ↦ (φ (((2 : ℝ) ^ N)⁻¹ • y) : ℂ))
          (quantizeUniformCLM b hb u)) x := by
  rw [quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue]
  congr 1; ext y
  have h0 : ((2 : ℝ) ^ N)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero N two_ne_zero)
  have htgR : (fun y : CoordinateSpace n ↦ φ (((2 : ℝ) ^ N)⁻¹ • y)).HasTemperateGrowth :=
    (φ.hasCompactSupport.comp_smul h0).hasTemperateGrowth
      (φ.contDiff.comp (contDiff_id.const_smul ((2 : ℝ) ^ N)⁻¹))
  have htgC : (fun y : CoordinateSpace n ↦ (φ (((2 : ℝ) ^ N)⁻¹ • y) : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp htgR
  rw [HasCompactSupport.toSchwartzMap_toFun, SchwartzMap.smulLeftCLM_apply_apply htgC,
    quantizeUniformCLM_apply, quantizeSchwartzValue_def, quantizeSchwartzValue_def, ← integral_smul]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  dsimp only
  rw [coefficient_spatialTrunc, smul_apply, smul_comm (𝐞 ⟪ζ, y⟫)]

/-- **Composition of quantizations for uniform symbols.** For any symbol `a` of order `m'` and any
uniform symbol `b` of order `m`, the quantization of `a.uniformSharp b hb` on a Schwartz function
`u` equals the quantization of `a` applied to the Schwartz function `quantizeUniformCLM b hb u`. -/
theorem quantizeSchwartzValue_uniformSharp [CompleteSpace W] [CompleteSpace U]
    (a : Symbol n W U m') {b : Symbol n V W m} (hb : b.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.uniformSharp b hb).coefficient u x =
      quantizeSchwartzValue a.coefficient (quantizeUniformCLM b hb u) x := by
  let φ : ContDiffBump (0 : CoordinateSpace n) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  set cN : ℕ → Symbol n V U (m' + (0 + m)) := fun N ↦
    a.sharp (spatialTrunc φ N b) (hasCompactSpatialSupport_spatialTrunc φ N b)
  obtain ⟨Ca_x, -, hCa_x⟩ := a.exists_bound_coefficient_slice x
  have hRHS_tendsto :
      Tendsto (fun N ↦ quantizeSchwartzValue (cN N).coefficient u x) atTop
        (𝓝 (quantizeSchwartzValue a.coefficient (quantizeUniformCLM b hb u) x)) := by
    simp only [cN, quantizeSchwartzValue_sharp_spatialTrunc_eq φ _ a hb u x]
    exact ((continuous_quantizeSchwartzValue_input (a.continuous_coefficient_slice x)
      hCa_x).tendsto _).comp (SchwartzMap.tendsto_smulLeftCLM_contDiffBump_two_pow φ
        (quantizeUniformCLM b hb u))
  obtain ⟨C, -, hC⟩ := exists_norm_uniformIntegrand_spatialTrunc_le φ a hb x
  set K_x : ℝ := C * ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hcN_bound (N : ℕ) (ξ : CoordinateSpace n) :
      ‖(cN N).coefficient (x, ξ)‖ ≤ K_x * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
    have heq : (cN N).coefficient (x, ξ) = uniformCompCoeff a (spatialTrunc φ N b) (x, ξ) := by
      simp only [cN]
      rw [← coefficient_uniformSharp_eq_sharp, coefficient_uniformSharp_eq_uniformCompCoeff]
    rw [heq, uniformCompCoeff]
    exact (norm_integral_le_of_norm_le
      (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
        (C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2)))
      (.of_forall (hC N ξ))).trans_eq (by rw [integral_const_mul]; ring)
  have hLHS_tendsto :
      Tendsto (fun N ↦ quantizeSchwartzValue (cN N).coefficient u x) atTop
        (𝓝 (quantizeSchwartzValue (a.uniformSharp b hb).coefficient u x)) := by
    simp only [quantizeSchwartzValue_def]
    refine tendsto_integral_of_dominated_convergence
      (fun ζ ↦ K_x * ((1 + ‖(2 * π) • ζ‖ ^ 2) ^ ((m' + m) / 2) * ‖𝓕 u ζ‖))
      (fun N ↦ ((Real.continuous_fourierChar.comp (by fun_prop)).smul
        (((cN N).continuous_coefficient_slice x |>.comp (by fun_prop)).clm_apply
          (𝓕 u).continuous)).aestronglyMeasurable)
      (((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) (m' + m)).const_mul K_x)
      (fun N ↦ .of_forall fun ζ ↦ ?_) (.of_forall fun ζ ↦ ?_)
    · rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
      exact ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hcN_bound N _) (norm_nonneg _))).trans_eq (by ring)
    · exact (((ContinuousLinearMap.apply ℂ U (𝓕 u ζ)).continuous.tendsto _).comp
        (tendsto_coefficient_sharp_spatialTrunc φ a hb x ((2 * π) • ζ))).const_smul (𝐞 ⟪ζ, x⟫)
  exact tendsto_nhds_unique hLHS_tendsto hRHS_tendsto

/-- **Composition of uniform pseudodifferential operators on Schwartz space.** When both `a` and `b`
satisfy uniform estimates, `Op(a #_u b) = Op(a) ∘ Op(b)` as continuous linear maps on Schwartz
space. -/
theorem quantizeUniformCLM_uniformSharp [CompleteSpace W] [CompleteSpace U]
    {a : Symbol n W U m'} {b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) :
    quantizeUniformCLM (a.uniformSharp b hb) (ha.uniformSharp hb) =
      (quantizeUniformCLM a ha).comp (quantizeUniformCLM b hb) := by
  ext u x
  rw [quantizeUniformCLM_apply, ContinuousLinearMap.comp_apply, quantizeUniformCLM_apply]
  exact quantizeSchwartzValue_uniformSharp a hb u x

/-- **Uniqueness of the uniform composition symbol.** Any symbol `c`, of any order, whose
quantization agrees with `Op(a) ∘ Op(b)` on compactly supported Schwartz functions has the
coefficient of `a.uniformSharp b hb`. -/
theorem coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq
    [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]
    (a : Symbol n W U m') {b : Symbol n V W m} (hb : b.IsUniform)
    {m'' : ℝ} {c : Symbol n V U m''}
    (h : ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u → ∀ x,
      quantizeSchwartzValue c.coefficient u x =
        quantizeSchwartzValue a.coefficient (quantizeUniformCLM b hb u) x) :
    c.coefficient = (a.uniformSharp b hb).coefficient :=
  coefficient_eq_of_forall_quantizeSchwartzValue_eq fun u hu ↦ funext fun x ↦
    (h u hu x).trans (quantizeSchwartzValue_uniformSharp a hb u x).symm

end Operator

/-! ### Associativity and composition with frequency multipliers -/

section Algebra

/-- **Associativity of uniform symbol composition.** For any symbol `a` and uniform symbols `b` and
`c`, `(a #_u b) #_u c = a #_u (b #_u c)` up to the identification of orders
`(m'' + m') + m = m'' + (m' + m)`. -/
theorem uniformSharp_assoc {U' : Type*} [NormedAddCommGroup U'] [NormedSpace ℂ U']
    [CompleteSpace V] [CompleteSpace W] [CompleteSpace U] [CompleteSpace U'] {m'' : ℝ}
    (a : Symbol n U U' m'') {b : Symbol n W U m'} {c : Symbol n V W m}
    (hb : b.IsUniform) (hc : c.IsUniform) :
    (a.uniformSharp b hb).uniformSharp c hc =
      Symbol.inclusion (add_assoc m'' m' m).ge
        (a.uniformSharp (b.uniformSharp c hc) (hb.uniformSharp hc)) := by
  ext1; rw [coefficient_inclusion]
  refine coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq a (hb.uniformSharp hc)
    fun u _ x ↦ ?_
  rw [quantizeSchwartzValue_uniformSharp (a.uniformSharp b hb) hc,
    quantizeSchwartzValue_uniformSharp a hb, quantizeUniformCLM_uniformSharp hb hc]; rfl

/-- **Exact composition with a frequency multiplier on the right.** In the left quantization,
composing any symbol `a` on the right with a frequency-only symbol `ofFrequency g hg hgbound` gives
the pointwise product `a.comp (ofFrequency g hg hgbound)`, with no lower-order remainder. -/
theorem uniformSharp_ofFrequency [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]
    (a : Symbol n W U m') {g : CoordinateSpace n → V →L[ℂ] W} (hg : ContDiff ℝ ∞ g)
    (hgbound : ∀ k : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2))
    (hb : (ofFrequency g hg hgbound).IsUniform := isUniform_ofFrequency hg hgbound) :
    a.uniformSharp (ofFrequency g hg hgbound) hb = a.comp (ofFrequency g hg hgbound) := by
  ext1
  refine (coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq a hb fun u _ x ↦ ?_).symm
  have hgu : quantizeUniformCLM (ofFrequency g hg hgbound) hb u = quantizeFrequencyCLM g u := by
    ext y; rw [quantizeUniformCLM_apply]; exact quantizeSchwartzValue_ofFrequency hg hgbound u y
  rw [hgu, quantizeSchwartzValue_quantizeFrequencyCLM
    (Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow hg hgbound)]
  exact quantizeSchwartzValue_congr_left
    (fun ξ ↦ by simp only [coefficient_comp, coefficient_ofFrequency]) u

/-- **Exact composition with the Bessel potential on the right.** Composing any symbol `a` on the
right with `besselPotential s` in `uniformSharp` equals `a.comp (besselPotential s)`. -/
@[simp]
theorem uniformSharp_besselPotential [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m') (s : ℝ)
    (hs : (besselPotential s : Symbol n V V s).IsUniform := isUniform_besselPotential s) :
    a.uniformSharp (besselPotential s) hs = a.comp (besselPotential s) := by
  ext1
  refine (coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq a hs fun u _ x ↦ ?_).symm
  have hg : (fun ζ : CoordinateSpace n ↦
      (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow (CoordinateSpace n) (s / 2))
  have hbu : quantizeUniformCLM (besselPotential s : Symbol n V V s) hs u =
      SchwartzMap.fourierMultiplierCLM V
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u := by
    ext y; rw [quantizeUniformCLM_apply]; exact quantizeSchwartzValue_besselPotential s u y
  rw [hbu, quantizeSchwartzValue_fourierMultiplierCLM hg]
  exact quantizeSchwartzValue_congr_left (fun ξ ↦ by
    simp only [coefficient_comp, coefficient_besselPotential, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_id]) u

/-- Composing any symbol `a` on the right with `const T` gives `a.comp (const T)`. -/
theorem uniformSharp_const [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]
    (a : Symbol n W U m') (T : V →L[ℂ] W) :
    a.uniformSharp (const T) (isUniform_const T) = a.comp (const T) := by
  ext1
  refine (coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq a (isUniform_const T)
    fun u _ x ↦ ?_).symm
  have hf (ζ : CoordinateSpace n) : 𝓕 (u.postcompCLM T) ζ = T (𝓕 u ζ) := by
    simp only [SchwartzMap.fourier_coe, Real.fourier_eq, SchwartzMap.postcompCLM_apply,
      Circle.smul_def, ← map_smul]
    exact T.integral_comp_comm (((Real.fourierIntegral_convergent_iff ζ).2 u.integrable).congr
      (.of_forall fun _ ↦ Circle.smul_def _ _))
  rw [quantizeUniformCLM_const T, quantizeSchwartzValue_def, quantizeSchwartzValue_def]
  exact integral_congr_ae (.of_forall fun ζ ↦ by
    dsimp only; rw [hf ζ, coefficient_comp, coefficient_const, ContinuousLinearMap.comp_apply])

/-- The constant identity symbol `1` is a right identity for `uniformSharp` up to `m' + 0 = m'`. -/
@[simp]
theorem uniformSharp_const_id [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m') :
    a.uniformSharp (const (ContinuousLinearMap.id ℂ V)) (isUniform_const _) =
      Symbol.inclusion (add_zero m').ge a := by
  rw [uniformSharp_const, comp_const_id]

/-- **Composition with a frequency multiplier on the left** for a uniform symbol `a`:
`c(D) (Op(a) u) = Op(c #_u a) u`, where `c #_u a` is uniform of order `m' + m`. -/
theorem quantizeSchwartzValue_ofFrequency_uniformSharp [CompleteSpace W] [CompleteSpace U]
    {a : Symbol n V W m} (ha : a.IsUniform) {c : CoordinateSpace n → W →L[ℂ] U}
    (hc : ContDiff ℝ ∞ c)
    (hcbound : ∀ k : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k c ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' - k) / 2))
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue ((ofFrequency c hc hcbound).uniformSharp a ha).coefficient u x =
      quantizeFrequencyCLM c (quantizeUniformCLM a ha u) x := by
  rw [quantizeSchwartzValue_uniformSharp _ ha, quantizeSchwartzValue_ofFrequency]

/-- **Composition with Mathlib's Bessel multiplier on the left** for a uniform symbol `a`:
`J^s (Op(a) u) = Op((besselPotential s) #_u a) u`. -/
theorem quantizeSchwartzValue_besselPotential_uniformSharp [CompleteSpace W]
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue ((besselPotential s : Symbol n W W s).uniformSharp a ha).coefficient u x =
      SchwartzMap.fourierMultiplierCLM W
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))
        (quantizeUniformCLM a ha u) x := by
  rw [quantizeSchwartzValue_uniformSharp _ ha, quantizeSchwartzValue_besselPotential]

end Algebra

end TauCeti.Symbol
