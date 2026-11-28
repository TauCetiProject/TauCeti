/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Finite.Basic
import Mathlib.Probability.Moments.SubGaussian

/-!
# Hoeffding's inequality for counting in finite products

The uniform measure on a finite product is the product of the factor uniform measures. It is
a probability measure when every factor is nonempty. Applying
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` to each coordinate and
`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` to their sum bounds the
cardinality of its upper tail by an exponential fraction of the product cardinality.
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*}

/-- For real functions `X i` on finite sets, with `X i` taking values in `[a i, b i]`,
the number of tuples at which the sum of the functions exceeds the sum of their uniform means by
at least `t ≥ 0` is at most the product cardinality times
`exp (-2 t² / ∑ i, (b i - a i)²)`. -/
theorem ncard_setOf_sum_sub_mean_ge_le_card_mul_exp [∀ i, Fintype (Ω i)]
    (X : ∀ i, Ω i → ℝ) {a b : ι → ℝ} (hX : ∀ i x, X i x ∈ Set.Icc (a i) (b i))
    {t : ℝ} (ht : 0 ≤ t) :
    ({x : ∀ i, Ω i |
        t ≤ ∑ i, (X i (x i) - (∑ y, X i y) / Fintype.card (Ω i))}.ncard : ℝ) ≤
      Nat.card (∀ i, Ω i) * Real.exp (-2 * t ^ 2 / ∑ i, (b i - a i) ^ 2) := by
  classical
  rcases isEmpty_or_nonempty (∀ i, Ω i) with h | h
  · have hs : {x : ∀ i, Ω i |
        t ≤ ∑ i, (X i (x i) - (∑ y, X i y) / Fintype.card (Ω i))} = ∅ :=
      Set.eq_empty_of_isEmpty _
    rw [hs]
    simp
  have (i : ι) : Nonempty (Ω i) := ⟨Classical.choice h i⟩
  let (i : ι) : MeasurableSpace (Ω i) := ⊤
  let (i : ι) : MeasurableSingletonClass (Ω i) := ⟨fun _ ↦ trivial⟩
  rw [Nat.card_eq_fintype_card]
  let μ (i : ι) : Measure (Ω i) := uniformOn Set.univ
  have hmeas (i : ι) : Measurable (X i) := measurable_of_countable _
  let Y (i : ι) (y : Ω i) := X i y - (∑ z, X i z) / Fintype.card (Ω i)
  have hindep : iIndepFun (fun i (x : ∀ i, Ω i) ↦ Y i (x i)) (Measure.pi μ) :=
    iIndepFun_pi fun i ↦ (measurable_of_countable (Y i)).aemeasurable
  have hsub (i : ι) :
      HasSubgaussianMGF (fun x : ∀ i, Ω i ↦ Y i (x i))
        ((‖b i - a i‖₊ / 2) ^ 2) (Measure.pi μ) := by
    have hx : AEMeasurable (fun x : ∀ i, Ω i ↦ X i (x i)) (Measure.pi μ) :=
      ((hmeas i).comp (measurable_pi_apply i)).aemeasurable
    have hmean : ∫ x : ∀ i, Ω i, X i (x i) ∂Measure.pi μ =
        (∑ y, X i y) / Fintype.card (Ω i) := by
      rw [integral_comp_eval (hmeas i).aestronglyMeasurable]
      simp [μ, integral_uniformOn_univ, div_eq_inv_mul]
    simpa only [Y, hmean] using hasSubgaussianMGF_of_mem_Icc hx (ae_of_all _ fun x ↦ hX i (x i))
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    hindep (s := univ) (fun i _ ↦ hsub i) ht
  rw [← uniformOn_univ_pi] at htail
  let s := {x : ∀ i, Ω i | t ≤ ∑ i, Y i (x i)}
  have hmass : (uniformOn Set.univ : Measure (∀ i, Ω i)).real s =
      (s.ncard : ℝ) / Fintype.card (∀ i, Ω i) := by
    rw [← s.toFinite.coe_toFinset, uniformOn_univ_real_finset, Set.ncard_coe_finset]
  have hcard : (0 : ℝ) < Fintype.card (∀ i, Ω i) := Nat.cast_pos.2 Fintype.card_pos
  rw [hmass, div_le_iff₀ hcard] at htail
  have hvariance : (2 * ∑ i, ((((‖b i - a i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) =
      (∑ i, (b i - a i) ^ 2) / 2 := by
    rw [div_eq_mul_inv, sum_mul, mul_sum]
    congr 1
    ext i
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnNorm,
      Real.norm_eq_abs, div_pow, sq_abs]
    ring
  simp only [NNReal.coe_sum] at htail
  rw [hvariance, div_div_eq_mul_div] at htail
  have hexp : -t ^ 2 * 2 / (∑ i, (b i - a i) ^ 2) =
      -2 * t ^ 2 / (∑ i, (b i - a i) ^ 2) := by ring
  rwa [hexp, mul_comm (Real.exp _)] at htail

end TauCeti.Probability
