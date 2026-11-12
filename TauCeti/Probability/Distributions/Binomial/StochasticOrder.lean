/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Binomial.Basic
public import TauCeti.Probability.StochasticOrder
import TauCeti.Probability.Distributions.PoissonBinomial.Count
import TauCeti.Probability.Distributions.Uniform.Basic

/-!
# Stochastic comparison of binomial laws

Increasing either the number of trials or the success probability increases a binomial law
in first-order stochastic order. We express this through reversed cdf inequalities for the
real cast laws, inequalities between their interior quantiles, and almost-sure order under
their common-uniform quantile coupling. Zero trials and success probabilities zero and one
are included.

The success-probability comparison uses the same independent uniform trials at both
thresholds. The trial-count comparison adds independent Bernoulli trials, using the native
binomial convolution identity. The resulting joint comparison allows both parameters to vary.

## References

* M. Shaked and J. G. Shanthikumar, *Stochastic Orders*, Springer, 2007, Chapter 1.
* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace TauCeti.Probability

/-- Increasing the success probability decreases the cdf of a real-cast binomial law.
This includes success probabilities zero and one. -/
theorem cdf_map_cast_binomial_le_of_le_prob (n : ℕ) {p q : I} (hpq : p ≤ q) (x : ℝ) :
    cdf Bin(ℝ, n, q) x ≤ cdf Bin(ℝ, n, p) x := by
  classical
  let P := Measure.pi fun _ : Fin n ↦ uniformMeasure 0 1
  have hmass (r : I) : (uniformMeasure 0 1).real (Iic (r : ℝ)) = r := by
    rw [← cdf_eq_real, cdf_uniformMeasure zero_lt_one]
    split_ifs with hzero hone
    · exact (le_antisymm hzero r.property.1).symm
    · exact (le_antisymm r.property.2 hone).symm
    · simp
  have hlaw (r : I) :
      HasLaw (fun z : Fin n → ℝ ↦ (Finset.univ.filter fun i ↦ z i ≤ r).card)
        Bin(n, r) P := by
    simpa only [P, poissonBinomialMeasure_const, Fintype.card_fin, hmass,
      Subtype.coe_eta, mem_Iic] using
      (hasLaw_card_filter_mem_pi (fun _ : Fin n ↦ uniformMeasure 0 1)
        (s := fun _ ↦ Iic (r : ℝ)) (fun _ ↦ measurableSet_Iic))
  have hcast (r : I) : HasLaw (Nat.cast : ℕ → ℝ) Bin(ℝ, n, r) Bin(n, r) :=
    hasLaw_map (by fun_prop)
  apply ((hcast p).comp (hlaw p)).cdf_le_of_ae_le ((hcast q).comp (hlaw q)) _ x
  exact ae_of_all _ fun z ↦ Nat.cast_le.mpr <| Finset.card_le_card <|
    Finset.monotone_filter_right _ fun _ _ hi ↦ hi.trans hpq

/-- Adding trials decreases the cdf of a real-cast binomial law while keeping the success
probability fixed. -/
theorem cdf_map_cast_binomial_le_of_le_trials {n m : ℕ} (hnm : n ≤ m) (p : I) (x : ℝ) :
    cdf Bin(ℝ, m, p) x ≤ cdf Bin(ℝ, n, p) x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  let P := (binomial n p).prod (binomial k p)
  have hfst : HasLaw Prod.fst Bin(n, p) P := measurePreserving_fst.hasLaw
  have hsnd : HasLaw Prod.snd Bin(k, p) P := measurePreserving_snd.hasLaw
  have hindep : IndepFun Prod.fst Prod.snd P :=
    (indepFun_iff_hasLaw_prodMk_prod hfst hsnd).2 HasLaw.id
  have hsum : HasLaw (fun z : ℕ × ℕ ↦ z.1 + z.2) Bin(n + k, p) P := by
    simpa only [binomial_conv_binomial] using hindep.hasLaw_fun_add hfst hsnd
  have hcast (j : ℕ) : HasLaw (Nat.cast : ℕ → ℝ) Bin(ℝ, j, p) Bin(j, p) :=
    hasLaw_map (by fun_prop)
  apply ((hcast n).comp hfst).cdf_le_of_ae_le ((hcast (n + k)).comp hsum) _ x
  exact ae_of_all _ fun z ↦ Nat.cast_le.mpr (Nat.le_add_right z.1 z.2)

/-- Increasing both binomial parameters decreases the cdf, including the zero-trial and
deterministic-probability boundaries. -/
theorem cdf_map_cast_binomial_le {n m : ℕ} {p q : I} (hnm : n ≤ m) (hpq : p ≤ q)
    (x : ℝ) : cdf Bin(ℝ, m, q) x ≤ cdf Bin(ℝ, n, p) x :=
  (cdf_map_cast_binomial_le_of_le_prob m hpq x).trans
    (cdf_map_cast_binomial_le_of_le_trials hnm p x)

/-- Every interior binomial quantile increases with the number of trials and the success
probability, including deterministic laws. -/
theorem quantile_map_cast_binomial_le {n m : ℕ} {p q : I} (hnm : n ≤ m) (hpq : p ≤ q)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Bin(ℝ, n, p).quantile u ≤ Bin(ℝ, m, q).quantile u :=
  (Measure.cdf_le_iff_quantile_le _ _).1 (cdf_map_cast_binomial_le hnm hpq) u hu0 hu1

/-- The common-uniform quantile coupling of binomial laws is almost surely ordered when
both parameters increase. Its marginals are given by `Measure.isCoupling_quantileCoupling`. -/
theorem ae_fst_le_snd_quantileCoupling_map_cast_binomial {n m : ℕ} {p q : I} (hnm : n ≤ m)
    (hpq : p ≤ q) :
    ∀ᵐ z ∂Bin(ℝ, n, p).quantileCoupling Bin(ℝ, m, q), z.1 ≤ z.2 :=
  Measure.ae_fst_le_snd_quantileCoupling _ _ (cdf_map_cast_binomial_le hnm hpq)

end TauCeti.Probability
