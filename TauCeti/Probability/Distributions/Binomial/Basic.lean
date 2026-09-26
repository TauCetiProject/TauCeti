/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Probability.GeneratingFunction
import TauCeti.Probability.Distributions.Bernoulli.Basic

/-!
# Elementary theory of the binomial distribution

This file develops the moments, transforms, convolution law, and independent-sum
characterization of Mathlib's binomial measure.  The native law remains
`ProbabilityTheory.binomial n p` on `ℕ`; real-valued moments and transforms use its cast pushforward
`Bin(ℝ, n, p)`. Its variance is `n * p * (1 - p)`.

## Main results

* `TauCeti.Probability.pgf_binomial` computes the probability-generating function on the native
  carrier;
* `TauCeti.Probability.variance_id_map_cast_binomial` computes the variance of the cast law;
* `TauCeti.Probability.mgf_id_map_cast_binomial` and
  `TauCeti.Probability.cgf_id_map_cast_binomial` compute its moment and cumulant generating
  functions;
* `TauCeti.Probability.charFun_map_cast_binomial` computes its characteristic function;
* `TauCeti.Probability.binomial_conv_binomial` proves additivity of the native binomial laws;
* `TauCeti.Probability.iIndepFun.hasLaw_sum_bernoulli` identifies a finite sum of independent
  Bernoulli variables with a binomial law.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 3.
* `TauCetiRoadmap/StandardDistributions/README.md`, Layer 1, "Bernoulli and binomial".
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The probability-generating function of a binomial distribution. -/
@[simp]
theorem pgf_binomial (n : ℕ) (p : unitInterval) (t : ℝ) :
    pgf id (binomial n p) t = (1 - (p : ℝ) + (p : ℝ) * t) ^ n := by
  -- `add_pow` attaches the binomial weights to its first summand.
  have hbase : 1 - (p : ℝ) + (p : ℝ) * t = (p : ℝ) * t + (1 - (p : ℝ)) := add_comm _ _
  rw [pgf_def, integral_binomial, ← Nat.range_succ_eq_Iic, hbase, add_pow]
  simp only [smul_eq_mul, id_eq]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The moment generating function of the real-valued binomial law. -/
theorem mgf_id_map_cast_binomial (n : ℕ) (p : unitInterval) (t : ℝ) :
    mgf id Bin(ℝ, n, p) t = (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ n := by
  rw [mgf_id_map_natCast, pgf_binomial]

/-- The cumulant generating function of the real-valued binomial law. -/
theorem cgf_id_map_cast_binomial (n : ℕ) (p : unitInterval) (t : ℝ) :
    cgf id Bin(ℝ, n, p) t =
      Real.log ((1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ n) := by
  rw [cgf, mgf_id_map_cast_binomial]

private theorem charFun_map_cast_binomial_aux (n : ℕ) (p : unitInterval) (t : ℝ) :
    charFun Bin(ℝ, n, p) t =
      ∑ k ∈ Finset.Iic n, (n.choose k : ℂ) * (p : ℂ) ^ k * (1 - p : ℂ) ^ (n - k) *
        Complex.exp (((k : ℝ) * t) * Complex.I) := by
  rw [charFun_apply, integral_map_cast_binomial]
  simp only [Real.inner_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Complex.real_smul]
  push_cast
  ring

/-- The characteristic function of the real-valued binomial law. -/
theorem charFun_map_cast_binomial (n : ℕ) (p : unitInterval) (t : ℝ) :
    charFun Bin(ℝ, n, p) t =
      (1 - (p : ℂ) + (p : ℂ) * Complex.exp (Complex.I * t)) ^ n := by
  rw [charFun_map_cast_binomial_aux, ← n.range_succ_eq_Iic]
  calc
    _ = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) *
        ((p : ℂ) * Complex.exp (Complex.I * t)) ^ k * (1 - p : ℂ) ^ (n - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hexp : Complex.exp (((k : ℝ) * t) * Complex.I) =
          Complex.exp (Complex.I * t) ^ k := by
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [hexp, mul_pow]
      ring
    _ = ((p : ℂ) * Complex.exp (Complex.I * t) + (1 - p : ℂ)) ^ n := by
      simpa only [Nat.cast_choose, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
        (add_pow ((p : ℂ) * Complex.exp (Complex.I * t)) (1 - p : ℂ) n).symm
    _ = (1 - (p : ℂ) + (p : ℂ) * Complex.exp (Complex.I * t)) ^ n := by ring

private theorem map_cast_binomial_conv_real (n m : ℕ) (p : unitInterval) :
    Bin(ℝ, n, p) ∗ Bin(ℝ, m, p) = Bin(ℝ, n + m, p) := by
  apply Measure.ext_of_charFun
  ext t
  simp only [charFun_conv, charFun_map_cast_binomial, ← pow_add]

/-- The convolution of two native binomial laws with the same success probability is binomial,
with the numbers of trials added. -/
theorem binomial_conv_binomial (n m : ℕ) (p : unitInterval) :
    Bin(n, p) ∗ Bin(m, p) = Bin(n + m, p) := by
  apply (MeasurableEmbedding.natCast (α := ℝ)).map_injective
  rw [← Nat.coe_castAddMonoidHom, Measure.map_conv_addMonoidHom _ (by fun_prop)]
  exact map_cast_binomial_conv_real n m p

/-- A finite sum of independent Bernoulli variables with common success probability `p` has the
native binomial law, with as many trials as the index type has elements. -/
theorem iIndepFun.hasLaw_sum_bernoulli {ι : Type*} [Fintype ι] {p : unitInterval} {X : ι → Ω → ℕ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) Ber((1 : ℕ), 0, p) P) :
    HasLaw (fun ω ↦ ∑ i, X i ω) Bin(Fintype.card ι, p) P := by
  -- `Bin(ℝ, n, p)` is *notation* for `Bin(n, p).map (Nat.cast : ℕ → ℝ)`, not a wrapper
  -- definition, so the `map_eq` field of `hnatCast` is a syntactic identity rather than an
  -- unfolding; stating it as a standalone lemma is a syntactic tautology.
  have hcast (i : ι) :
      HasLaw (fun ω ↦ (X i ω : ℝ)) Bin(ℝ, 1, p) P := by
    have hnatCast : HasLaw (Nat.cast : ℕ → ℝ) Bin(ℝ, 1, p) Bin(1, p) :=
      ⟨Measurable.of_discrete.aemeasurable, rfl⟩
    have hi := hX i
    rw [← binomial_one_eq_bernoulliMeasure] at hi
    simpa [Function.comp_def] using hnatCast.comp hi
  have hindepCast : iIndepFun (fun i ω ↦ (X i ω : ℝ)) P := by
    simpa [Function.comp_def] using
      hindep.comp (fun _ ↦ (Nat.cast : ℕ → ℝ)) (fun _ ↦ Measurable.of_discrete)
  let _ : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hsumCast :
      P.map (fun ω ↦ ∑ i, (X i ω : ℝ)) = Bin(ℝ, Fintype.card ι, p) := by
    apply Measure.ext_of_charFun
    ext t
    calc
      charFun (P.map (fun ω ↦ ∑ i, (X i ω : ℝ))) t =
          (∏ i, charFun (P.map (fun ω ↦ (X i ω : ℝ)))) t := by
        exact congrFun (hindepCast.charFun_map_fun_sum_eq_prod fun i ↦ (hcast i).aemeasurable) t
      _ = ∏ _i : ι,
          (1 - (p : ℂ) + (p : ℂ) * Complex.exp (Complex.I * t)) := by
        rw [Fintype.prod_apply]
        apply Finset.prod_congr rfl
        intro i hi
        rw [(hcast i).map_eq, charFun_map_cast_binomial]
        simp
      _ = (1 - (p : ℂ) + (p : ℂ) * Complex.exp (Complex.I * t)) ^ Fintype.card ι := by simp
      _ = charFun Bin(ℝ, Fintype.card ι, p) t :=
        (charFun_map_cast_binomial (Fintype.card ι) p t).symm
  refine ⟨Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦ (hX i).aemeasurable, ?_⟩
  apply (MeasurableEmbedding.natCast (α := ℝ)).map_injective
  rw [AEMeasurable.map_map_of_aemeasurable Measurable.of_discrete.aemeasurable
    (Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦ (hX i).aemeasurable)]
  have hcomp : (Nat.cast : ℕ → ℝ) ∘ (fun ω ↦ ∑ i, X i ω) =
      fun ω ↦ ∑ i, (X i ω : ℝ) := by
    funext ω
    simp
  rw [hcomp]
  exact hsumCast

/-! ### Variance -/

/-- The variance of the real-valued binomial measure itself. -/
theorem variance_id_map_cast_binomial (n : ℕ) (p : unitInterval) :
    Var[id; Bin(ℝ, n, p)] = (p : ℝ) * (1 - p) * n := by
  let μ : Fin n → Measure ℕ := fun _ ↦ Ber((1 : ℕ), 0, p)
  have hcoord (i : Fin n) : HasLaw (fun ω : Fin n → ℕ ↦ ω i) (μ i) (Measure.pi μ) :=
    (measurePreserving_eval μ i).hasLaw
  have hsum : HasLaw (fun ω : Fin n → ℕ ↦ ∑ i, ω i) Bin(n, p) (Measure.pi μ) := by
    simpa only [Fintype.card_fin, id_eq] using
      iIndepFun.hasLaw_sum_bernoulli
        (iIndepFun_pi (μ := μ) (fun _ ↦ aemeasurable_id)) hcoord
  have hcast : HasLaw (Nat.cast : ℕ → ℝ) Bin(ℝ, n, p) Bin(n, p) :=
    ⟨Measurable.of_discrete.aemeasurable, rfl⟩
  have hsumCast : HasLaw (∑ i : Fin n, fun ω : Fin n → ℕ ↦ (ω i : ℝ))
      Bin(ℝ, n, p) (Measure.pi μ) := by
    simpa only [Function.comp_def, Nat.cast_sum, Finset.sum_fn] using hcast.comp hsum
  have hber : HasLaw (Nat.cast : ℕ → ℝ) Ber((1 : ℝ), 0, p) Ber((1 : ℕ), 0, p) :=
    ⟨Measurable.of_discrete.aemeasurable, by simp [map_bernoulliMeasure]⟩
  have hmem : MemLp (Nat.cast : ℕ → ℝ) 2 Ber((1 : ℕ), 0, p) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 (integrable_bernoulliMeasure _ _ _ _)
  rw [← hsumCast.variance_eq, variance_sum_pi (fun _ ↦ hmem)]
  simp [variance_of_hasLaw_bernoulliMeasure hber, mul_comm]

/-- The variance of a real-valued binomial random variable with parameters `n` and `p` is
`p(1-p)n`. -/
theorem variance_of_hasLaw_binomial {n : ℕ} {p : unitInterval} {X : Ω → ℝ}
    (hX : HasLaw X Bin(ℝ, n, p) P) : Var[X; P] = p * (1 - p) * n := by
  rw [hX.variance_eq, variance_id_map_cast_binomial]

end Probability

end TauCeti
