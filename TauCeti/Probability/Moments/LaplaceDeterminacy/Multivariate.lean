/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Log.ERealExp
public import TauCeti.Probability.Moments.CompactDeterminacy
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Probability.IdentDistrib

/-!
# Finite-dimensional Laplace determinacy, including infinite coordinates

A finite measure on `ι → ℝ≥0∞`, for finite `ι`, is determined by its Laplace transform
at nonnegative integer vectors. Infinite coordinates are allowed: the exponential at minus
infinity is zero, and a zero coefficient ignores its coordinate. In particular the all-zero
test recovers total mass, even when some coordinates are infinite.

This is the finite-dimensional uniqueness input for identifying laws of random measures from
Laplace functionals: apply it to finite families of evaluations. It also gives a criterion for
equality in distribution of extended nonnegative random vectors on different sample spaces.

The proof uses Mathlib's `EReal.exp` and the coordinate substitution `yᵢ = exp(-xᵢ)`.
The transformed measures are carried by the compact cube `[0,1]^ι`, where the existing
`TauCeti.Measure.ext_of_forall_integral_monomial_eq_of_support` applies. Thus neither moments
of the original coordinates nor almost-sure finiteness assumptions are required.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapters 2 and 13 (Laplace-functional determination).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.Measure

variable {ι : Type*} [Fintype ι]

/-- A finite law of an extended nonnegative vector is determined by the mixed moments of
its coordinatewise negative exponential. This includes infinite coordinates and the empty
index type; the zero exponent vector tests total mass. -/
theorem ext_of_forall_lintegral_prod_exp_neg_pow_eq
    {μ ν : Measure (ι → ℝ≥0∞)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ι → ℕ,
      ∫⁻ x, ∏ i, EReal.exp (-(x i : EReal)) ^ n i ∂μ =
        ∫⁻ x, ∏ i, EReal.exp (-(x i : EReal)) ^ n i ∂ν) :
    μ = ν := by
  classical
  let f : (ι → ℝ≥0∞) → (ι → ℝ) := fun x i ↦ (EReal.exp (-(x i : EReal))).toReal
  have hb (x : ℝ≥0∞) : EReal.exp (-(x : EReal)) ≤ 1 := by
    exact EReal.exp_le_one_iff.2 (EReal.neg_le_zero.2 (EReal.coe_ennreal_nonneg x))
  have hf : Measurable f := by
    fun_prop
  have hinj : Function.Injective f := by
    intro x y hxy
    ext i
    have he := ENNReal.toReal_eq_toReal_iff'
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hb (x i)))
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hb (y i)))
    have hi := he.1 (congrFun hxy i)
    exact EReal.coe_ennreal_injective (neg_injective (EReal.exp_strictMono.injective hi))
  refine hf.measurableEmbedding hinj |>.map_injective ?_
  let K : Set (ι → ℝ) := univ.pi fun _ ↦ Icc 0 1
  have hK : IsCompact K := isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hmem (x : ι → ℝ≥0∞) : f x ∈ K := by
    simp only [K, mem_univ_pi, mem_Icc]
    exact fun i ↦ ⟨ENNReal.toReal_nonneg,
      by simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hb (x i))⟩
  have hsupport (ρ : Measure (ι → ℝ≥0∞)) : ρ.map f Kᶜ = 0 := by
    rw [Measure.map_apply hf hK.measurableSet.compl]
    have hpre : f ⁻¹' Kᶜ = ∅ := by
      ext x
      simp [hmem x]
    rw [hpre, measure_empty]
  refine TauCeti.Measure.ext_of_forall_integral_monomial_eq_of_support hK
    (hsupport μ) (hsupport ν) fun n ↦ ?_
  have hmoment (ρ : Measure (ι → ℝ≥0∞)) :
      ∫ y, ∏ i, y i ^ n i ∂ρ.map f =
        (∫⁻ x, ∏ i, EReal.exp (-(x i : EReal)) ^ n i ∂ρ).toReal := by
    rw [integral_map hf.aemeasurable
      ((by fun_prop : Continuous fun y : ι → ℝ ↦ ∏ i, y i ^ n i).aestronglyMeasurable)]
    have heq (x : ι → ℝ≥0∞) :
        ∏ i, f x i ^ n i = (∏ i, EReal.exp (-(x i : EReal)) ^ n i).toReal := by
      simp [f, ENNReal.toReal_prod]
    simp_rw [heq]
    refine integral_toReal (Measurable.aemeasurable (by fun_prop)) (ae_of_all _ fun x ↦ ?_)
    exact (Finset.prod_le_one fun i _ ↦ pow_le_one₀ zero_le (hb (x i))).trans_lt
      ENNReal.one_lt_top
  rw [hmoment, hmoment, h n]

/-- **Finite-dimensional Laplace determinacy.** Values at nonnegative integer vectors
identify finite measures on extended nonnegative vectors. The summand is `nᵢ · (-xᵢ)` in
`EReal`, so a zero coefficient contributes zero even at an infinite coordinate. -/
theorem ext_of_forall_lintegral_exp_sum_eq
    {μ ν : Measure (ι → ℝ≥0∞)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ι → ℕ,
      ∫⁻ x, EReal.exp (∑ i, (n i : EReal) * -(x i : EReal)) ∂μ =
        ∫⁻ x, EReal.exp (∑ i, (n i : EReal) * -(x i : EReal)) ∂ν) :
    μ = ν := by
  classical
  have hexp (n : ι → ℕ) (x : ι → ℝ≥0∞) :
      EReal.exp (∑ i, (n i : EReal) * -(x i : EReal)) =
        ∏ i, EReal.exp (-(x i : EReal)) ^ n i := by
    simp only [EReal.exp_sum, EReal.exp_nmul]
  apply ext_of_forall_lintegral_prod_exp_neg_pow_eq
  simpa only [hexp] using h

end TauCeti.Measure

namespace TauCeti.Probability

variable {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure Q]
  {X : Ω → ι → ℝ≥0∞} {Y : Ω' → ι → ℝ≥0∞}

/-- Two a.e. measurable extended nonnegative random vectors have the same distribution
exactly when their Laplace transforms agree at every nonnegative integer vector.
No common sample space or almost-sure finiteness hypothesis is needed. -/
theorem identDistrib_iff_forall_lintegral_exp_sum_eq
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q) :
    ProbabilityTheory.IdentDistrib X Y P Q ↔ ∀ n : ι → ℕ,
      ∫⁻ ω, EReal.exp (∑ i, (n i : EReal) * -(X ω i : EReal)) ∂P =
        ∫⁻ ω, EReal.exp (∑ i, (n i : EReal) * -(Y ω i : EReal)) ∂Q := by
  have hm (n : ι → ℕ) :
      Measurable fun x : ι → ℝ≥0∞ ↦ EReal.exp (∑ i, (n i : EReal) * -(x i : EReal)) := by
    fun_prop
  constructor
  · intro h n
    exact (h.comp (hm n)).lintegral_eq
  · intro h
    refine ⟨hX, hY, Measure.ext_of_forall_lintegral_exp_sum_eq fun n ↦ ?_⟩
    rw [lintegral_map' (hm n).aemeasurable hX, lintegral_map' (hm n).aemeasurable hY]
    exact h n

end TauCeti.Probability
