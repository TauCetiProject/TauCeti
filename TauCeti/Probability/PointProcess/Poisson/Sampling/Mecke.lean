/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Lebesgue.Dirac
public import TauCeti.Probability.Distributions.Poisson.SizeBias
public import TauCeti.Probability.Independence.RandomPrefix
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Mecke's identity for Poisson sampling

A Poisson number of independent locations satisfies Mecke's insertion identity: selecting
an occurrence in the sampled configuration is equivalent to inserting one fresh independent
location and multiplying by the mean count. Multiplicities are retained, and neither the
location space nor its probability law needs to be atomless.

The finite-product identities apply even to sigma-finite location measures. For probability
location laws, `ProbabilityTheory.IndepFun.mecke_poissonMeasure_sample` transfers the identity
to any realization with an independent Poisson count and iid locations. No configuration
carrier or canonical sample space is imposed on the caller. The passage from fixed sample
size to Poisson size uses `TauCeti.Probability.withDensity_natCast_poissonMeasure`.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Theorem 4.1 (the finite-intensity independent-sampling proof).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X] (Q : Measure X)
  {g : X × Measure X → ℝ≥0∞}

/-- The Campbell formula for `n + 1` independent locations: distinguish one of the
occurrences and integrate the remaining `n` locations independently. Coincident locations
are counted separately. -/
theorem lintegral_finsetSum_dirac_pi_succ [SigmaFinite Q] (hg : Measurable g) (n : ℕ) :
    (∫⁻ x : Fin (n + 1) → X, ∫⁻ y, g (y, ∑ i, Measure.dirac (x i))
      ∂(∑ i, Measure.dirac (x i)) ∂Measure.pi (fun _ ↦ Q)) =
      (n + 1 : ℝ≥0∞) * ∫⁻ y, ∫⁻ x : Fin n → X,
        g (y, Measure.dirac y + ∑ i, Measure.dirac (x i))
          ∂Measure.pi (fun _ ↦ Q) ∂Q := by
  have hi (i : Fin (n + 1)) :
      (∫⁻ x : Fin (n + 1) → X, g (x i, ∑ j, Measure.dirac (x j))
        ∂Measure.pi (fun _ ↦ Q)) =
        ∫⁻ y, ∫⁻ x : Fin n → X,
          g (y, Measure.dirac y + ∑ j, Measure.dirac (x j))
            ∂Measure.pi (fun _ ↦ Q) ∂Q := by
    let h : X × (Fin n → X) → ℝ≥0∞ :=
      fun p ↦ g (p.1, Measure.dirac p.1 + ∑ j, Measure.dirac (p.2 j))
    have hh : Measurable h := hg.comp (by fun_prop)
    rw [← lintegral_prod _ hh.aemeasurable,
      ← (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ Q) i).lintegral_comp hh]
    apply lintegral_congr
    intro x
    have hsplit : Measure.dirac (x i) +
        ∑ j, Measure.dirac (Fin.removeNth i x j) = ∑ j, Measure.dirac (x j) := by
      simpa only [Fin.removeNth_apply] using
        (Fin.sum_univ_succAbove (fun j ↦ Measure.dirac (x j)) i).symm
    simp only [h, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv_symm_apply, hsplit]
  simp_rw [lintegral_finsetSum_dirac (f := fun y ↦ g (y, _)) _ _
    (hg.comp (measurable_id.prodMk measurable_const))]
  rw [lintegral_finsetSum Finset.univ
    (f := fun (i : Fin (n + 1)) (x : Fin (n + 1) → X) ↦
      g (x i, ∑ j, Measure.dirac (x j)))
    (fun i _ ↦ hg.comp (by fun_prop))]
  simp_rw [hi]
  simp

/-- Mecke's identity for a Poisson mixture of independent finite samples. The left side
selects an occurrence of the sample, whereas the right side inserts an independent location.
The identity includes zero rate and extended-valued tests. For a probability location law
this is the usual sampling formula; sigma-finite location measures give the same
product-integral identity. -/
theorem lintegral_finsetSum_dirac_poissonMeasure_pi [SigmaFinite Q]
    (r : ℝ≥0) (hg : Measurable g) :
    (∫⁻ n : ℕ, ∫⁻ x : Fin n → X, ∫⁻ y, g (y, ∑ i, Measure.dirac (x i))
      ∂(∑ i, Measure.dirac (x i)) ∂Measure.pi (fun _ ↦ Q) ∂poissonMeasure r) =
      (r : ℝ≥0∞) * ∫⁻ y, ∫⁻ n : ℕ, ∫⁻ x : Fin n → X,
        g (y, Measure.dirac y + ∑ i, Measure.dirac (x i))
          ∂Measure.pi (fun _ ↦ Q) ∂poissonMeasure r ∂Q := by
  let f : ℕ → ℝ≥0∞ := fun n ↦ ∫⁻ y, ∫⁻ x : Fin n → X,
    g (y, Measure.dirac y + ∑ i, Measure.dirac (x i))
      ∂Measure.pi (fun _ ↦ Q) ∂Q
  let h : ℕ → ℝ≥0∞ := fun n ↦ f (n - 1)
  have hcount (n : ℕ) :
      (∫⁻ x : Fin n → X, ∫⁻ y, g (y, ∑ i, Measure.dirac (x i))
        ∂(∑ i, Measure.dirac (x i)) ∂Measure.pi (fun _ ↦ Q)) = n * h n := by
    cases n with
    | zero => simp
    | succ n => simpa [h, f] using lintegral_finsetSum_dirac_pi_succ Q hg n
  simp_rw [hcount]
  have hd := lintegral_withDensity_eq_lintegral_mul (poissonMeasure r)
    (f := fun n : ℕ ↦ (n : ℝ≥0∞)) Measurable.of_discrete
    (g := h) Measurable.of_discrete
  simp only [Pi.mul_apply] at hd
  rw [← hd, TauCeti.Probability.withDensity_natCast_poissonMeasure, lintegral_smul_measure,
    lintegral_map (by fun_prop) (by fun_prop)]
  simp only [h, Nat.succ_sub_one]
  congr 1
  apply lintegral_lintegral_swap
  apply Measurable.aemeasurable
  apply measurable_from_prod_countable_right
  intro n
  simp only [Function.uncurry]
  apply Measurable.lintegral_prod_right (ν := Measure.pi (fun _ : Fin n ↦ Q))
    (f := fun (y : X) (x : Fin n → X) ↦
      g (y, Measure.dirac y + ∑ i, Measure.dirac (x i)))
  apply hg.comp
  fun_prop

end MeasureTheory.Measure

namespace ProbabilityTheory

/-- An independent Poisson number of iid locations satisfies Mecke's insertion identity
on any probability realization. The empirical measure counts occurrences with multiplicity. -/
theorem IndepFun.mecke_poissonMeasure_sample {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω} [IsProbabilityMeasure P]
    {Q : Measure X} [IsProbabilityMeasure Q] {N : Ω → ℕ} {Z : ℕ → Ω → X}
    (hNZ : IndepFun N (fun ω i ↦ Z i ω) P) (hind : iIndepFun Z P)
    (hZ : ∀ i, HasLaw (Z i) Q P) {r : ℝ≥0} (hN : HasLaw N (poissonMeasure r) P)
    {g : X × Measure X → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ ω, ∫⁻ y, g (y, ∑ i : Fin (N ω), Measure.dirac (Z i ω))
      ∂(∑ i : Fin (N ω), Measure.dirac (Z i ω)) ∂P) =
      (r : ℝ≥0∞) * ∫⁻ y, ∫⁻ ω,
        g (y, Measure.dirac y + ∑ i : Fin (N ω), Measure.dirac (Z i ω)) ∂P ∂Q := by
  have hleft (n : ℕ) : Measurable (fun x : Fin n → X ↦
      ∫⁻ y, g (y, ∑ i, Measure.dirac (x i)) ∂(∑ i, Measure.dirac (x i))) := by
    simp_rw [lintegral_finsetSum_dirac (f := fun y ↦ g (y, _)) _ _
      (hg.comp (measurable_id.prodMk measurable_const))]
    exact Finset.measurable_sum _ fun i _ ↦ hg.comp (by fun_prop)
  rw [hNZ.lintegral_random_prefix hind hZ hN hleft,
    Q.lintegral_finsetSum_dirac_poissonMeasure_pi r hg]
  congr 1
  apply lintegral_congr
  intro y
  exact (hNZ.lintegral_random_prefix hind hZ hN
    (fun n ↦ hg.comp (by fun_prop))).symm

end ProbabilityTheory
