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

Uniform counting on a product of finite sets is the product of the uniform laws. Applying
Mathlib's Hoeffding inequality to functions of the individual coordinates bounds the cardinality
of an upper tail of their sum by an exponential fraction of the cardinality of the product.
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*}

/-- The uniform measure on a finite dependent product is the product of the uniform measures on
its factors. Each factor can carry any measurable structure with measurable singletons. -/
theorem uniformOn_univ_pi [∀ i, Finite (Ω i)] [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSingletonClass (Ω i)] :
    uniformOn (Set.univ : Set (∀ i, Ω i)) =
      Measure.pi (fun i ↦ uniformOn (Set.univ : Set (Ω i))) := by
  classical
  let (i : ι) : Fintype (Ω i) := Fintype.ofFinite _
  apply Measure.ext_of_singleton
  intro x
  have (i : ι) : Nonempty (Ω i) := ⟨x i⟩
  simp only [Measure.pi_singleton, uniformOn_univ, Measure.count_singleton, Fintype.card_pi,
    Nat.cast_prod, one_div]
  symm
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [← prod_mul_distrib]
  exact prod_eq_one fun i _ ↦
    ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero (α := Ω i))
      (ENNReal.natCast_ne_top _)

/-- For real functions `X i` on finite nonempty sets, with `X i` taking values in `[a i, b i]`,
the number of tuples at which the sum of the functions exceeds the sum of their uniform means by
at least `t ≥ 0` is at most the product cardinality times
`exp (-2 t² / ∑ i, (b i - a i)²)`. -/
theorem ncard_setOf_sum_sub_mean_ge_le_exp [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (X : ∀ i, Ω i → ℝ) {a b : ι → ℝ} (hX : ∀ i x, X i x ∈ Set.Icc (a i) (b i))
    {t : ℝ} (ht : 0 ≤ t) :
    ({x : ∀ i, Ω i |
        t ≤ ∑ i, (X i (x i) - (∑ y, X i y) / Fintype.card (Ω i))}.ncard : ℝ) ≤
      Nat.card (∀ i, Ω i) * Real.exp (-2 * t ^ 2 / ∑ i, (b i - a i) ^ 2) := by
  classical
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
      calc
        _ = ∫ y, X i y ∂(Measure.pi μ).map (Function.eval i) :=
          (integral_map (measurable_pi_apply i).aemeasurable (hmeas i).aestronglyMeasurable).symm
        _ = _ := by
          rw [(measurePreserving_eval μ i).map_eq]
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
