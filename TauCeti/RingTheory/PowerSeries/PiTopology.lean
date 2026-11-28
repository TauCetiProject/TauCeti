/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import TauCeti.RingTheory.PowerSeries.CoeffProd
public import TauCeti.RingTheory.PowerSeries.Rescale
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.FieldSimp

/-!
# Infinite products and the `(X)`-adic topology on power series

If all but finitely many factors agree with `1` to each prescribed degree, their product
converges coefficientwise. Each coefficient is computed from any finite cutoff containing all
factors that can affect it. Over a discrete commutative ring, the coefficientwise topology on
`R⟦X⟧` coincides with the `(X)`-adic topology. We also record coefficientwise convergence
through quotients by constant-term-`1` series and the exponential limit
`(1 + C (c / N) * X) ^ N → exp (c X)`.

## Main results

* `PowerSeries.WithPiTopology.hasProd_of_X_pow_dvd_sub_one`: convergence and finite-cutoff
  coefficients for products whose factors approach `1` modulo increasing powers of `X`.
* `PowerSeries.WithPiTopology.isAdic_span_X`: over a discrete commutative ring, the
  coefficientwise topology on `R⟦X⟧` is `(X)`-adic.
* `PowerSeries.tendsto_coeff_of_mul_eq`: coefficientwise convergence passes through
  `F i * B i = A i` when `B i` and `B₀` have constant coefficient `1`.
* `PowerSeries.tendsto_coeff_one_add_div_pow`: coefficients of `(1 + C (c / N) * X) ^ N`
  converge to those of `rescale c (exp 𝕜)`.
* `PowerSeries.coeff_succ_one_add_mul_rescale_exp`: `(m + 1)`-th coefficient formula for
  `(1 + c₁ * X * ∑ f (k + 1) X ^ k) * rescale (c₁ * c₂) (exp 𝕜)`.
-/

public section

open Finset

namespace PowerSeries.WithPiTopology

open scoped PowerSeries.WithPiTopology Topology

variable {R ι : Type*} [CommRing R] [TopologicalSpace R]

/-- **Infinite products through finite cutoffs.** If, for each `n`, every factor `g i` with
`i ∉ F n` is congruent to `1` modulo `X ^ (n + 1)`, then the product of all the `g i` converges
in the coefficientwise topology, and its `n`-th coefficient is that of `∏ i ∈ F n, g i`. -/
theorem hasProd_of_X_pow_dvd_sub_one {g : ι → R⟦X⟧} (F : ℕ → Finset ι)
    (hF : ∀ n i, i ∉ F n → X ^ (n + 1) ∣ g i - 1) :
    HasProd g (mk fun n ↦ coeff n (∏ i ∈ F n, g i)) := by
  classical
  rw [HasProd, tendsto_iff_coeff_tendsto]
  refine fun n ↦ tendsto_atTop_of_eventually_const (i₀ := F n) fun s hs ↦ ?_
  rw [coeff_mk]; exact coeff_prod_eq_coeff_prod_of_X_pow_dvd_sub_one hs fun i hi ↦
    hF n i (mem_sdiff.1 hi).2

/-- **The coefficientwise topology over a discrete ring is `(X)`-adic.** -/
theorem isAdic_span_X [DiscreteTopology R] : IsAdic (Ideal.span {(X : R⟦X⟧)}) := by
  rw [isAdic_iff]; refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
  · rw [show ((Ideal.span {(X : R⟦X⟧)} ^ n : Ideal R⟦X⟧) : Set R⟦X⟧) =
        ⋂ d ∈ Finset.range n, (coeff (R := R) d) ⁻¹' {0} by
      ext f; simp [Ideal.span_singleton_pow, Ideal.mem_span_singleton, X_pow_dvd_iff]]
    exact isOpen_biInter_finset fun d _ ↦ (isOpen_discrete _).preimage (continuous_coeff R d)
  · let f : ℕ → Set R⟦X⟧ := fun n ↦ ((Ideal.span {(X : R⟦X⟧)} ^ n : Ideal R⟦X⟧) : Set R⟦X⟧)
    have hf_anti : Antitone f := fun _ _ h ↦ Ideal.pow_le_pow_right h
    have hle : (⨅ n, Filter.principal (f n)) ≤ 𝓝 (0 : R⟦X⟧) := by
      rw [← Filter.tendsto_id', tendsto_iff_coeff_tendsto]; intro d
      rw [map_zero, nhds_discrete, Filter.tendsto_pure]
      refine Filter.mem_iInf_of_mem (d + 1) (Filter.mem_principal.mpr fun g hg ↦ ?_)
      rw [SetLike.mem_coe, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
        X_pow_dvd_iff] at hg
      exact hg d (Nat.lt_succ_self d)
    have hdir : Directed (· ≥ ·) (fun n ↦ Filter.principal (f n)) := fun i j ↦
      ⟨max i j, Filter.principal_mono.mpr (hf_anti (le_max_left _ _)),
        Filter.principal_mono.mpr (hf_anti (le_max_right _ _))⟩
    simpa only [Filter.mem_principal] using (Filter.mem_iInf_of_directed hdir s).mp (hle hs)

end PowerSeries.WithPiTopology

namespace PowerSeries

open Filter
open scoped Nat Topology

/-- Coefficientwise convergence passes through `F i * B i = A i` when `B i` and `B₀` have
constant coefficient `1`. -/
theorem tendsto_coeff_of_mul_eq {R ι : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    {l : Filter ι} {F A B : ι → R⟦X⟧} {L A₀ B₀ : R⟦X⟧}
    (hmul : ∀ i, F i * B i = A i) (hmul₀ : L * B₀ = A₀)
    (hB_const : ∀ i, constantCoeff (B i) = 1) (hB₀_const : constantCoeff B₀ = 1)
    (hA : ∀ k, Tendsto (fun i ↦ coeff k (A i)) l (𝓝 (coeff k A₀)))
    (hB : ∀ k, Tendsto (fun i ↦ coeff k (B i)) l (𝓝 (coeff k B₀)))
    (k : ℕ) : Tendsto (fun i ↦ coeff k (F i)) l (𝓝 (coeff k L)) := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hsolve (P Q : R⟦X⟧) (hQ : constantCoeff Q = 1) :
        coeff k P = coeff k (P * Q) - ∑ i ∈ Finset.range k, coeff i P * coeff (k - i) Q := by
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ coeff i P * coeff j Q)
        k, Finset.sum_range_succ, Nat.sub_self, coeff_zero_eq_constantCoeff, hQ, mul_one,
        add_sub_cancel_left]
    simp_rw [fun i ↦ hsolve (F i) (B i) (hB_const i), hmul, hsolve L B₀ hB₀_const, hmul₀]
    exact (hA k).sub (tendsto_finsetSum _ fun i hi ↦
      (ih i (Finset.mem_range.mp hi)).mul (hB (k - i)))

/-- Coefficientwise convergence of `(1 + C (c / N) * X) ^ N` to `rescale c (exp 𝕜)`. -/
theorem tendsto_coeff_one_add_div_pow {𝕜 : Type*} [Field 𝕜] [Algebra ℚ 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] [ContinuousSMul ℚ≥0 𝕜] (c : 𝕜) (k : ℕ) :
    Tendsto (fun N : ℕ ↦ coeff k ((1 + C (c / N) * X) ^ N))
      atTop (𝓝 (coeff k (rescale c (exp 𝕜)))) := by
  have : CharZero 𝕜 := charZero_of_inj_zero fun n hn ↦
    Nat.cast_eq_zero.mp ((algebraMap ℚ 𝕜).injective (by simpa using hn))
  have hcoeff : ∀ᶠ N : ℕ in atTop, coeff k ((1 + C (c / N) * X) ^ N) =
      (c ^ k / (k ! : 𝕜)) * ∏ i ∈ Finset.range k, (1 - (i : 𝕜) * (N : 𝕜)⁻¹) := by
    filter_upwards [eventually_ge_atTop (max k 1)] with N hN
    have hkN : k ≤ N := (le_max_left k 1).trans hN; have hN0 : (N : 𝕜) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega)
    have hk0 : (k ! : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hpow : (1 + C (c / N) * X) ^ N =
        ∑ i ∈ Finset.range (N + 1), C ((N.choose i : 𝕜) * (c / N) ^ i) * X ^ i := by
      rw [add_comm 1 _, add_pow]; refine Finset.sum_congr rfl fun i _ ↦ ?_; rw [one_pow, mul_one,
        mul_pow, ← map_natCast C, ← map_pow, mul_right_comm, ← map_mul, mul_comm ((c / ↑N) ^ i)]
    have hdesc : (k ! : 𝕜) * (N.choose k : 𝕜) = ∏ i ∈ Finset.range k, ((N : 𝕜) - i) := by
      have h := congrArg ((↑) : ℕ → 𝕜) (Nat.descFactorial_eq_factorial_mul_choose N k)
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_mul, Nat.cast_prod] at h; exact h.symm.trans
        (Finset.prod_congr rfl fun i hi ↦ Nat.cast_sub ((Finset.mem_range.mp hi).le.trans hkN))
    have hprod : ∏ i ∈ Finset.range k, (1 - (i : 𝕜) * (N : 𝕜)⁻¹) =
        (∏ i ∈ Finset.range k, ((N : 𝕜) - i)) / (N : 𝕜) ^ k := by
      rw [show (N : 𝕜) ^ k = ∏ _ ∈ Finset.range k, (N : 𝕜) by simp, ← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun i _ ↦ by field_simp
    rw [hpow, map_sum]; simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq,
      Finset.mem_range, Nat.lt_succ_iff.mpr hkN, ↓reduceIte, hprod, ← hdesc, div_pow]; field_simp
  have h1 : Tendsto (fun N : ℕ ↦ ∏ i ∈ Finset.range k, (1 - (i : 𝕜) * (N : 𝕜)⁻¹)) atTop (𝓝 1) := by
    simpa using tendsto_finsetProd (Finset.range k) fun i _ ↦
      (tendsto_const_nhds (x := (1 : 𝕜))).sub
        ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := 𝕜)).const_mul (i : 𝕜))
  simpa only [mul_one, coeff_rescale, coeff_exp, map_div₀, map_one, map_natCast, mul_one_div] using
    (h1.const_mul (c ^ k / (k ! : 𝕜))).congr' (EventuallyEq.symm hcoeff)

/-- Coefficient formula for `(1 + c₁ * X * ∑ f (k + 1) X ^ k) * rescale (c₁ * c₂) (exp 𝕜)`
in degree `m + 1`. -/
theorem coeff_succ_one_add_mul_rescale_exp {𝕜 : Type*} [Field 𝕜] [Algebra ℚ 𝕜]
    (c₁ c₂ : 𝕜) (f : ℕ → 𝕜) (m : ℕ) :
    coeff (m + 1) (mk (fun k ↦ if k = 0 then 1 else c₁ * f k) * rescale (c₁ * c₂) (exp 𝕜)) =
      c₁ * (coeff m ((mk fun k ↦ f (k + 1)) * rescale (c₁ * c₂) (exp 𝕜)) +
        c₁ ^ m * c₂ ^ (m + 1) / ((m + 1)! : 𝕜)) := by
  let E := rescale (c₁ * c₂) (exp 𝕜)
  rw [show mk (fun k ↦ if k = 0 then 1 else c₁ * f k) * E =
      E + C c₁ * X * ((mk fun k ↦ f (k + 1)) * E) by
    rw [show mk (fun k ↦ if k = 0 then 1 else c₁ * f k) = 1 + C c₁ * X * mk fun k ↦ f (k + 1) by
      ext (_ | k) <;> [simp; (rw [map_add, mul_assoc, coeff_C_mul, coeff_succ_X_mul]; simp)]]; ring]
  rw [map_add, mul_assoc, coeff_C_mul, coeff_succ_X_mul, coeff_rescale, coeff_exp, map_div₀,
    map_one, map_natCast, mul_pow, pow_succ' c₁ m]; ring

end PowerSeries
