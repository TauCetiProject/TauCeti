/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.GaltonWatson.Kernel
public import TauCeti.Probability.Moments.ConvolutionPower

/-!
# The Galton–Watson process: generating functions and moments

A Galton–Watson process with offspring law `ν` is a process `Z : ℕ → Ω → ℕ` whose path has the
law of the Markov chain with kernel `MeasureTheory.Measure.gwKernel ν` started from one
individual (`MeasureTheory.Measure.IsGaltonWatson`). No sample space is imposed: the coordinate
process on path space is one (`MeasureTheory.Measure.isGaltonWatson_coord`), and every statement
below depends only on the law of the process.

Write `f` for the generating function of `ν`, `m` for its mean and `σ²` for its variance. This
file computes the generating function and the first two moments of a generation:

* on `[-1, 1]`, `E[s ^ Z n] = f^[n] s`, the `n`-fold iterate of `f`;
* `E[Z n] = m ^ n`, as a lower integral in `[0, ∞]` for every offspring law, with `0 ^ 0 = 1`;
* if `ν` has a second moment, `Var (Z n) = σ² (m ^ (n - 1) + m ^ n + ⋯ + m ^ (2 n - 2))`.

The same identities hold for the kernel itself, from an arbitrary number `j` of individuals: the
descendants after `n` generations have generating function `(f^[n] s) ^ j`, mean `j m ^ n` and
variance `j σ² (m ^ (n - 1) + ⋯ + m ^ (2 n - 2))`; the statements about a process are read off
from these at `j = 1`. These are the moment inputs of the martingale `Z n / m ^ n` and of its
convergence in `L²` in the supercritical case, and the generating function at `0` is the
probability of extinction by generation `n`.

## Main definitions

* `MeasureTheory.Measure.IsGaltonWatson ν Z μ`: `Z` is a Galton–Watson process with offspring
  law `ν` started from one individual.

## Main results

* `MeasureTheory.Measure.pgf_gwKernel_pow_apply`,
  `MeasureTheory.Measure.IsGaltonWatson.pgf_eq_iterate`: the generating function of generation
  `n` is the `n`-fold iterate of the offspring generating function.
* `MeasureTheory.Measure.lintegral_gwKernel_pow_apply`,
  `MeasureTheory.Measure.IsGaltonWatson.lintegral_eq_pow`: the mean of generation `n` is `m ^ n`
  in `[0, ∞]`; `MeasureTheory.Measure.IsGaltonWatson.integral_eq_pow` is the real form.
* `MeasureTheory.Measure.variance_gwKernel_pow_apply`,
  `MeasureTheory.Measure.IsGaltonWatson.variance_eq`: the variance of generation `n`.

## References

* R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press (2016),
  Propositions 5.2 and 5.5.
* R. Durrett, *Probability: Theory and Examples*, fifth edition, Cambridge University Press
  (2019), Section 4.3.4 and Example 4.4.9.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability Finset
open scoped ENNReal

namespace MeasureTheory.Measure

variable {ν : Measure ℕ}

/-! ### The descendants of `j` individuals after `n` generations -/

section Kernel

variable [IsProbabilityMeasure ν]

/-- On `[-1, 1]`, the generating function of the descendants of `j` individuals after `n`
generations is `(f^[n] s) ^ j`, where `f` is the offspring generating function. -/
theorem pgf_gwKernel_pow_apply (n j : ℕ) {s : ℝ} (hs : |s| ≤ 1) :
    pgf id ((ν.gwKernel ^ n) j) s = (pgf id ν)^[n] s ^ j := by
  induction n generalizing s with
  | zero => simp [Kernel.one_def, Kernel.id_apply, pgf_dirac]
  | succ n ih =>
    have hf : |pgf id ν s| ≤ 1 := by simpa using abs_pgf_le (μ := ν) id hs
    rw [Function.iterate_succ_apply, ← ih hf, Nat.add_comm n 1, Kernel.pow_add, pow_one, pgf_def,
      Kernel.integral_comp (integrable_pow_of_abs_le_one measurable_id.aemeasurable hs), pgf_def]
    congr 1 with i
    rw [id_eq, ← pgf_gwKernel i hs, pgf_def]

/-- The mean number of offspring of `j` individuals is `j` times the offspring mean, in `[0, ∞]`. -/
theorem lintegral_gwKernel_apply (j : ℕ) :
    ∫⁻ k, (k : ℝ≥0∞) ∂ν.gwKernel j = j * ν.offspringMean := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hx (x : ℕ) : ∫⁻ y, ((x + y : ℕ) : ℝ≥0∞) ∂ν = x + ν.offspringMean := by
      simp only [Nat.cast_add]
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        offspringMean_def]
    rw [gwKernel_apply, lintegral_convolutionPower_succ _ _ _ (measurable_of_countable _)]
    simp only [hx]
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
      ← gwKernel_apply, ih, Nat.cast_succ, add_mul, one_mul]

/-- The mean number of descendants of `j` individuals after `n` generations is `j m ^ n`, in
`[0, ∞]`, for every offspring law; here `0 ^ 0 = 1`. -/
theorem lintegral_gwKernel_pow_apply (n j : ℕ) :
    ∫⁻ k, (k : ℝ≥0∞) ∂(ν.gwKernel ^ n) j = j * ν.offspringMean ^ n := by
  induction n with
  | zero => simp [Kernel.one_def, Kernel.id_apply]
  | succ n ih =>
    rw [Nat.add_comm n 1, Kernel.pow_add, pow_one,
      Kernel.lintegral_comp _ _ _ (measurable_of_countable _)]
    simp only [lintegral_gwKernel_apply]
    rw [lintegral_mul_const _ (measurable_of_countable _), ih]
    ring

/-- The mean number of descendants of `j` individuals after `n` generations, as a real integral,
is `j m ^ n`. No integrability is needed: if the offspring mean is infinite, both sides are the
junk value `0` as soon as `j ≠ 0` and `n ≠ 0`. -/
theorem integral_gwKernel_pow_apply (n j : ℕ) :
    ∫ k, (k : ℝ) ∂(ν.gwKernel ^ n) j = j * (∫ k, (k : ℝ) ∂ν) ^ n := by
  -- both real integrals are the real parts of the corresponding lower integrals
  have htoReal (ρ : Measure ℕ) : ∫ k, (k : ℝ) ∂ρ = (∫⁻ k, (k : ℝ≥0∞) ∂ρ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun k => Nat.cast_nonneg k)
      (measurable_of_countable _).aestronglyMeasurable]
    simp
  rw [htoReal, htoReal, lintegral_gwKernel_pow_apply, ← offspringMean_def, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_natCast]

variable (hν : MemLp (fun k : ℕ => (k : ℝ)) 2 ν)
include hν

/-- The offspring of `j` individuals have a second moment when `ν` does. -/
theorem memLp_gwKernel_apply (j : ℕ) : MemLp (fun k : ℕ => (k : ℝ)) 2 (ν.gwKernel j) := by
  simpa using
    memLp_addMonoidHom_convolutionPower (Nat.castAddMonoidHom ℝ) (measurable_of_countable _) hν j

/-- The second moment of the offspring of `j` individuals is `j σ² + (j m) ^ 2`. -/
private theorem integral_sq_gwKernel_apply (j : ℕ) :
    ∫ k, (k : ℝ) ^ 2 ∂ν.gwKernel j =
      j * Var[fun k : ℕ => (k : ℝ); ν] + (j * ∫ k, (k : ℝ) ∂ν) ^ 2 := by
  have hvar := variance_addMonoidHom_convolutionPower (Nat.castAddMonoidHom ℝ)
    (measurable_of_countable _) hν j
  have hmean := integral_gwKernel_pow_apply (ν := ν) 1 j
  simp only [Nat.coe_castAddMonoidHom, pow_one] at hvar hmean
  rw [← gwKernel_apply, variance_eq_sub (memLp_gwKernel_apply hν j)] at hvar
  simp only [Pi.pow_apply] at hvar
  rw [← hmean]
  linarith

/-- The descendants of `j` individuals after `n` generations have a second moment when `ν`
does. -/
theorem memLp_gwKernel_pow_apply (n j : ℕ) :
    MemLp (fun k : ℕ => (k : ℝ)) 2 ((ν.gwKernel ^ n) j) := by
  induction n with
  | zero => simp [Kernel.one_def, Kernel.id_apply, memLp_dirac]
  | succ n ih =>
    have hsm (ρ : Measure ℕ) : AEStronglyMeasurable (fun k : ℕ => (k : ℝ)) ρ :=
      (measurable_of_countable _).aestronglyMeasurable
    rw [Nat.add_comm n 1, Kernel.pow_add, pow_one, memLp_two_iff_integrable_sq (hsm _),
      integrable_comp_iff (measurable_of_countable _).aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun i =>
      (memLp_two_iff_integrable_sq (hsm _)).1 (memLp_gwKernel_apply hν i), ?_⟩
    have hint := ih.integrable one_le_two
    have hsq := (memLp_two_iff_integrable_sq (hsm _)).1 ih
    simp only [norm_pow, Real.norm_natCast, integral_sq_gwKernel_apply hν, mul_pow]
    exact (hint.mul_const _).add (hsq.mul_const _)

/-- The variance of the descendants of `j` individuals after `n` generations is
`j σ² (m ^ (n - 1) + m ^ n + ⋯ + m ^ (2 n - 2))`, where `σ²` and `m` are the variance and the
mean of `ν`. -/
theorem variance_gwKernel_pow_apply (n j : ℕ) :
    Var[fun k : ℕ => (k : ℝ); (ν.gwKernel ^ n) j] =
      j * Var[fun k : ℕ => (k : ℝ); ν] *
        ∑ i ∈ range n, (∫ k, (k : ℝ) ∂ν) ^ (n - 1 + i) := by
  set m := ∫ k, (k : ℝ) ∂ν
  set σ2 := Var[fun k : ℕ => (k : ℝ); ν]
  -- by induction, from `Var (n + 1) = σ² E (n) + m ² Var (n)`, which conditions on generation `n`
  induction n with
  | zero => simp [Kernel.one_def, Kernel.id_apply, variance_dirac]
  | succ n ih =>
    have hL := memLp_gwKernel_pow_apply hν n j
    have hsq : Integrable (fun k : ℕ => (k : ℝ) ^ 2) ((ν.gwKernel ^ n) j) :=
      (memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).1 hL
    have hint := hL.integrable one_le_two
    -- the second moment after `n + 1` generations, by conditioning on generation `n`
    have h2 : ∫ k, (k : ℝ) ^ 2 ∂(ν.gwKernel ^ (n + 1)) j =
        σ2 * ∫ k, (k : ℝ) ∂(ν.gwKernel ^ n) j + m ^ 2 * ∫ k, (k : ℝ) ^ 2 ∂(ν.gwKernel ^ n) j := by
      have hL' := memLp_gwKernel_pow_apply hν (n + 1) j
      rw [Nat.add_comm n 1, Kernel.pow_add, pow_one] at hL' ⊢
      rw [Kernel.integral_comp ((memLp_two_iff_integrable_sq
        (measurable_of_countable _).aestronglyMeasurable).1 hL')]
      simp only [integral_sq_gwKernel_apply hν, mul_pow]
      rw [integral_add (hint.mul_const _) (hsq.mul_const _), integral_mul_const,
        integral_mul_const]
      ring
    rw [variance_eq_sub (memLp_gwKernel_pow_apply hν (n + 1) j)]
    rw [variance_eq_sub hL] at ih
    simp only [Pi.pow_apply] at ih ⊢
    rw [integral_gwKernel_pow_apply] at ih
    rw [h2, integral_gwKernel_pow_apply, integral_gwKernel_pow_apply]
    -- the identity `m ^ n + m ^ 2 (m ^ (n - 1) + ⋯ + m ^ (2 n - 2)) = m ^ n + ⋯ + m ^ (2 n)`
    have hsum : m ^ n + m ^ 2 * ∑ i ∈ range n, m ^ (n - 1 + i) =
        ∑ i ∈ range (n + 1), m ^ (n + 1 - 1 + i) := by
      rcases n with _ | n
      · simp
      rw [Finset.sum_range_succ' _ (n + 1), mul_sum, add_comm (m ^ (n + 1))]
      simp only [Nat.add_sub_cancel, add_zero, ← pow_add]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      omega
    rw [← hsum]
    linear_combination m ^ 2 * ih

end Kernel

/-! ### Galton–Watson processes -/

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {Z : ℕ → Ω → ℕ} {μ : Measure Ω}

/-- `Z` is a **Galton–Watson process** with offspring law `ν`, started from one individual: the
path `ω ↦ (Z n ω)ₙ` has the law of the Markov chain with kernel `ν.gwKernel` started at `1`. Each
`Z n` is then the size of generation `n`. -/
def IsGaltonWatson (ν : Measure ℕ) [IsProbabilityMeasure ν] (Z : ℕ → Ω → ℕ) (μ : Measure Ω) :
    Prop :=
  HasLaw (fun ω n => Z n ω) (markovChainLaw (dirac 1) ν.gwKernel) μ

variable [IsProbabilityMeasure ν]

/-- Unfolding of `IsGaltonWatson`: the path of `Z` has the law of the chain with kernel
`ν.gwKernel` started at `1`. -/
theorem isGaltonWatson_iff :
    IsGaltonWatson ν Z μ ↔ HasLaw (fun ω n => Z n ω) (markovChainLaw (dirac 1) ν.gwKernel) μ :=
  Iff.rfl

/-- The coordinate process on path space, under the path law of the chain started at `1`, is a
Galton–Watson process. -/
theorem isGaltonWatson_coord :
    IsGaltonWatson ν (fun n x => x n) (markovChainLaw (dirac 1) ν.gwKernel) :=
  HasLaw.id

/-- The underlying measure of a Galton–Watson process is a probability measure. -/
theorem IsGaltonWatson.isProbabilityMeasure (h : IsGaltonWatson ν Z μ) : IsProbabilityMeasure μ :=
  HasLaw.isProbabilityMeasure h

/-- Generation `n` of a Galton–Watson process has the law `(ν.gwKernel ^ n) 1` of the descendants
of one individual after `n` generations. -/
theorem IsGaltonWatson.hasLaw (h : IsGaltonWatson ν Z μ) (n : ℕ) :
    HasLaw (Z n) ((ν.gwKernel ^ n) 1) μ := by
  have h' := HasLaw.eval_markovChainLaw (dirac 1) ν.gwKernel (isGaltonWatson_iff.1 h) n
  rwa [dirac_bind (Kernel.measurable _)] at h'

/-- On `[-1, 1]`, the generating function of generation `n` of a Galton–Watson process is the
`n`-fold iterate of the offspring generating function. -/
theorem IsGaltonWatson.pgf_eq_iterate (h : IsGaltonWatson ν Z μ) (n : ℕ) {s : ℝ}
    (hs : |s| ≤ 1) : pgf (Z n) μ s = (pgf id ν)^[n] s := by
  rw [HasLaw.pgf_eq (h.hasLaw n), pgf_gwKernel_pow_apply n 1 hs, pow_one]

/-- The mean of generation `n` of a Galton–Watson process is `m ^ n`, in `[0, ∞]`, for every
offspring law; here `0 ^ 0 = 1`. -/
theorem IsGaltonWatson.lintegral_eq_pow (h : IsGaltonWatson ν Z μ) (n : ℕ) :
    ∫⁻ ω, (Z n ω : ℝ≥0∞) ∂μ = ν.offspringMean ^ n := by
  rw [(h.hasLaw n).lintegral_comp (measurable_of_countable _).aemeasurable,
    lintegral_gwKernel_pow_apply, Nat.cast_one, one_mul]

/-- The mean of generation `n` of a Galton–Watson process, as a real integral, is `m ^ n`. No
integrability is needed: for an offspring law of infinite mean both sides are the junk value `0`
as soon as `n ≠ 0`. -/
theorem IsGaltonWatson.integral_eq_pow (h : IsGaltonWatson ν Z μ) (n : ℕ) :
    ∫ ω, (Z n ω : ℝ) ∂μ = (∫ k, (k : ℝ) ∂ν) ^ n := by
  have hlaw := (h.hasLaw n).integral_comp (f := fun k : ℕ => (k : ℝ))
    (measurable_of_countable _).aestronglyMeasurable
  rw [Function.comp_def] at hlaw
  rw [hlaw, integral_gwKernel_pow_apply, Nat.cast_one, one_mul]

/-- The generations of a Galton–Watson process have second moments when `ν` does. -/
theorem IsGaltonWatson.memLp (h : IsGaltonWatson ν Z μ)
    (hν : MemLp (fun k : ℕ => (k : ℝ)) 2 ν) (n : ℕ) :
    MemLp (fun ω => (Z n ω : ℝ)) 2 μ :=
  (h.hasLaw n).memLp_comp (memLp_gwKernel_pow_apply hν n 1)

/-- The variance of generation `n` of a Galton–Watson process whose offspring law has a second
moment is `σ² (m ^ (n - 1) + m ^ n + ⋯ + m ^ (2 n - 2))`. -/
theorem IsGaltonWatson.variance_eq (h : IsGaltonWatson ν Z μ)
    (hν : MemLp (fun k : ℕ => (k : ℝ)) 2 ν) (n : ℕ) :
    Var[fun ω => (Z n ω : ℝ); μ] =
      Var[fun k : ℕ => (k : ℝ); ν] * ∑ i ∈ range n, (∫ k, (k : ℝ) ∂ν) ^ (n - 1 + i) := by
  have hmap := variance_map (X := fun k : ℕ => (k : ℝ)) (measurable_of_countable _).aemeasurable
    (h.hasLaw n).aemeasurable
  rw [(h.hasLaw n).map_eq, variance_gwKernel_pow_apply hν, Nat.cast_one, one_mul] at hmap
  rw [Function.comp_def] at hmap
  exact hmap.symm

end Process

end MeasureTheory.Measure
