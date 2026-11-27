/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.GeneratingFunction
public import TauCeti.Probability.Kernel.Composition.Power
public import TauCeti.Probability.Process.MarkovChain

/-!
# The generation kernel of a Galton–Watson process

An offspring law is a measure `ν` on `ℕ`: each individual of a generation independently has a
number of children with law `ν`, and these children form the next generation. This file defines
the mean `MeasureTheory.Measure.offspringMean ν` of an offspring law, taken in `[0, ∞]` as a lower
integral so that it exists for every law, and the transition kernel
`MeasureTheory.Measure.gwKernel ν` of the number of individuals, which sends a generation of `n`
individuals to the `n`-fold convolution power of `ν`. For a probability measure `ν` it is a Markov
kernel, the kernel of the Galton–Watson branching process.

The results are the branching property of the kernel, of all its powers and of the path law of the
chain, `0` being absorbing, and the generating function of one generation. Together with the shape
of the offspring generating function on `[0, 1]` (`TauCeti.Probability.convexOn_pgf`,
`TauCeti.Probability.tendsto_ofReal_deriv_pgf_nhdsLT_one`), they are the inputs of the analysis of
the moments and the extinction of the process.

## Main definitions

* `MeasureTheory.Measure.offspringMean ν`: the mean `∑ k, k ν {k}` in `[0, ∞]`.
* `MeasureTheory.Measure.gwKernel ν`: the kernel `n ↦ ν.convolutionPower n` on `ℕ`.

## Main results

* `MeasureTheory.Measure.gwKernel_one`: one individual has offspring with law `ν`.
* `MeasureTheory.Measure.gwKernel_add`, `MeasureTheory.Measure.gwKernel_pow_apply_add`: the
  branching property, `κ (j + k) = κ j ∗ κ k` for the kernel `κ` and all its powers.
* `MeasureTheory.Measure.gwKernel_pow_apply`: after `n` generations, `j` individuals have the
  descendants of `j` independent individuals.
* `MeasureTheory.Measure.gwKernel_pow_apply_zero`: the state `0` is absorbing.
* `MeasureTheory.Measure.markovChainLaw_conv_gwKernel`,
  `MeasureTheory.Measure.markovChainLaw_dirac_add_gwKernel`: the branching property of the path
  law, the chain started from `j + k` individuals being the sum of independent chains started from
  `j` and from `k`.
* `MeasureTheory.Measure.pgf_gwKernel`: on `[-1, 1]`, the generating function of the offspring
  of `n` individuals is `f s ^ n`, where `f` is the generating function of `ν`.

## References

* R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press (2016),
  Section 5.1.
* R. Durrett, *Probability: Theory and Examples*, fifth edition, Cambridge University Press
  (2019), Section 4.3.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability
open scoped ENNReal

namespace MeasureTheory.Measure

variable {ν : Measure ℕ}

/-- The mean of an offspring law `ν` on `ℕ`, the lower integral `∑ k, k ν {k}`, taken in `[0, ∞]`
so that it is defined for every law. -/
def offspringMean (ν : Measure ℕ) : ℝ≥0∞ :=
  ∫⁻ k, (k : ℝ≥0∞) ∂ν

theorem offspringMean_def (ν : Measure ℕ) : ν.offspringMean = ∫⁻ k, (k : ℝ≥0∞) ∂ν := (rfl)

/-- The mean of an offspring law is the sum of its masses weighted by the number of offspring. -/
theorem offspringMean_eq_tsum (ν : Measure ℕ) : ν.offspringMean = ∑' k : ℕ, k * ν {k} := by
  rw [offspringMean_def, lintegral_countable']

/-- The point mass at `n` has mean `n`. -/
@[simp]
theorem offspringMean_dirac (n : ℕ) : (dirac n).offspringMean = n := by
  rw [offspringMean_def, lintegral_dirac]

/-- When the number of offspring is integrable, the mean is its real integral. -/
theorem offspringMean_eq_ofReal_integral (h : Integrable (fun k : ℕ => (k : ℝ)) ν) :
    ν.offspringMean = ENNReal.ofReal (∫ k, (k : ℝ) ∂ν) := by
  rw [offspringMean_def, ofReal_integral_eq_lintegral_ofReal h
    (Filter.Eventually.of_forall fun k => Nat.cast_nonneg k)]
  simp

/-- The mean of an offspring law is finite exactly when the number of offspring is integrable. -/
theorem offspringMean_lt_top_iff : ν.offspringMean < ∞ ↔ Integrable (fun k : ℕ => (k : ℝ)) ν := by
  rw [offspringMean_def, Integrable, hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun k => Nat.cast_nonneg k)]
  simp [Measurable.aestronglyMeasurable (measurable_of_countable _)]

/-- The generation kernel of the Galton–Watson process with offspring law `ν`: from a generation
of `n` individuals, each of whom has offspring independently with law `ν`, the next generation has
the law of the `n`-fold convolution power of `ν`. -/
def gwKernel (ν : Measure ℕ) : Kernel ℕ ℕ :=
  Kernel.ofFunOfCountable fun n => ν.convolutionPower n

@[simp]
theorem gwKernel_apply (ν : Measure ℕ) (n : ℕ) : ν.gwKernel n = ν.convolutionPower n := (rfl)

instance [IsProbabilityMeasure ν] : IsMarkovKernel ν.gwKernel :=
  ⟨fun n => by rw [gwKernel_apply]; infer_instance⟩

instance [SFinite ν] (n : ℕ) : SFinite (ν.gwKernel n) := by
  rw [gwKernel_apply]; infer_instance

/-- If every individual has exactly `m` children, `n` individuals have `n * m` children. -/
theorem gwKernel_dirac (m n : ℕ) : (dirac m).gwKernel n = dirac (n * m) := by
  rw [gwKernel_apply, convolutionPower_dirac, smul_eq_mul]

/-- A single individual has offspring with law `ν`. -/
theorem gwKernel_one [SFinite ν] : ν.gwKernel 1 = ν := by
  rw [gwKernel_apply, convolutionPower_one]

/-- The branching property of one generation: the offspring of `j + k` individuals have the law of
the sum of independent offspring of `j` and of `k` individuals. -/
theorem gwKernel_add [SFinite ν] (j k : ℕ) : ν.gwKernel (j + k) = ν.gwKernel j ∗ ν.gwKernel k := by
  simp only [gwKernel_apply, convolutionPower_add]

/-- The branching property after `n` generations: the descendants in generation `n` of `j + k`
individuals have the law of the sum of independent descendants of `j` and of `k` individuals. -/
theorem gwKernel_pow_apply_add [SFinite ν] (n j k : ℕ) :
    (ν.gwKernel ^ n) (j + k) = (ν.gwKernel ^ n) j ∗ (ν.gwKernel ^ n) k := by
  induction n with
  | zero => simp [Kernel.one_def, Kernel.id_apply]
  | succ n ih =>
    simp only [Nat.add_comm n 1, Kernel.pow_add, pow_one, Kernel.comp_apply]
    rw [ih, bind_conv_bind (K := ν.gwKernel) gwKernel_add]

/-- The state `0` is absorbing: a population with no individuals stays extinct. -/
@[simp]
theorem gwKernel_pow_apply_zero (n : ℕ) : (ν.gwKernel ^ n) 0 = dirac 0 := by
  induction n with
  | zero => simp [Kernel.one_def, Kernel.id_apply]
  | succ n ih =>
    rw [Nat.add_comm n 1, Kernel.pow_add, pow_one, Kernel.comp_apply, ih,
      dirac_bind (Kernel.measurable _), gwKernel_apply, convolutionPower_zero]

/-- After `n` generations, the descendants of `j` individuals have the law of the sum of `j`
independent copies of the descendants of one individual. -/
theorem gwKernel_pow_apply [SFinite ν] (n j : ℕ) :
    (ν.gwKernel ^ n) j = ((ν.gwKernel ^ n) 1).convolutionPower j := by
  induction j with
  | zero => simp
  | succ j ih => rw [gwKernel_pow_apply_add, ih, convolutionPower_succ]

/-- On `[-1, 1]` the generating function of the offspring of `n` individuals is the `n`th power
of the offspring generating function `f`. -/
theorem pgf_gwKernel [IsFiniteMeasure ν] (n : ℕ) {t : ℝ} (ht : |t| ≤ 1) :
    pgf id (ν.gwKernel n) t = pgf id ν t ^ n := by
  rw [gwKernel_apply, pgf_convolutionPower_of_abs_le_one ν n ht]

/-- The branching property of the whole process: the sum of independent Galton–Watson chains
with initial laws `ρ` and `σ` is a Galton–Watson chain with initial law `ρ ∗ σ`. The convolution on
the right is taken in the path space `ℕ → ℕ`, so it is the law of the sum of the two paths under
the product of their laws. -/
theorem markovChainLaw_conv_gwKernel [IsProbabilityMeasure ν] (ρ σ : Measure ℕ)
    [IsFiniteMeasure ρ] [IsFiniteMeasure σ] :
    markovChainLaw (ρ ∗ σ) ν.gwKernel =
      markovChainLaw ρ ν.gwKernel ∗ markovChainLaw σ ν.gwKernel := by
  set P := markovChainLaw ρ ν.gwKernel
  set Q := markovChainLaw σ ν.gwKernel
  -- `P ∗ Q` starts from `ρ ∗ σ` and satisfies the Markov recursion: the joint law of a prefix and
  -- the next state, being additive in the path, is the convolution of those of `P` and `Q`, and
  -- the branching property lets the convolution pass through the last step
  symm
  refine eq_markovChainLaw (ρ ∗ σ) ν.gwKernel ?_ fun n => ?_
  · have h := map_conv_addMonoidHom (μ := P) (ν := Q) (Pi.evalAddMonoidHom (fun _ : ℕ => ℕ) 0)
      (measurable_pi_apply 0)
    have he : ⇑(Pi.evalAddMonoidHom (fun _ : ℕ => ℕ) 0) = fun x => x 0 := by
      ext; simp
    rw [he] at h
    rw [h, markovChainLaw_map_eval_zero, markovChainLaw_map_eval_zero]
  · let pre : (ℕ → ℕ) →+ (Fin (n + 1) → ℕ) :=
      AddMonoidHom.pi fun i : Fin (n + 1) => Pi.evalAddMonoidHom (fun _ : ℕ => ℕ) i.val
    let pair : (ℕ → ℕ) →+ (Fin (n + 1) → ℕ) × ℕ :=
      pre.prod (Pi.evalAddMonoidHom (fun _ : ℕ => ℕ) (n + 1))
    have hpre : Measurable pre := Measurable.of_eval fun i => measurable_pi_apply _
    have hpair : Measurable pair := hpre.prodMk (measurable_pi_apply _)
    have h1 := map_conv_addMonoidHom (μ := P) (ν := Q) pair hpair
    have h2 := map_conv_addMonoidHom (μ := P) (ν := Q) pre hpre
    have hP := markovChainLaw_map_prefix_succ_eq_compProd ρ ν.gwKernel n
    have hQ := markovChainLaw_map_prefix_succ_eq_compProd σ ν.gwKernel n
    have hK : ∀ u v : Fin (n + 1) → ℕ,
        (ν.gwKernel.comap (fun w : Fin (n + 1) → ℕ => w (Fin.last n))
          (measurable_pi_apply (Fin.last n))) (u + v) =
        (ν.gwKernel.comap (fun w : Fin (n + 1) → ℕ => w (Fin.last n))
          (measurable_pi_apply (Fin.last n))) u ∗
        (ν.gwKernel.comap (fun w : Fin (n + 1) → ℕ => w (Fin.last n))
          (measurable_pi_apply (Fin.last n))) v := fun u v => by
      simp only [Kernel.comap_apply, Pi.add_apply, gwKernel_add]
    have := compProd_conv_compProd hK (P.map pre) (Q.map pre)
    have hpre' : ⇑pre = fun x (i : Fin (n + 1)) => x i.val := by
      ext; simp [pre]
    have hpair' : ⇑pair = fun x => ((fun i : Fin (n + 1) => x i.val), x (n + 1)) := by
      ext <;> simp [pair, pre]
    rw [hpre'] at h2 this
    rw [hpair'] at h1
    rw [h1, hP, hQ, this, h2]

/-- The chain started from `j + k` individuals has the law of the sum of independent chains started
from `j` and from `k` individuals. -/
theorem markovChainLaw_dirac_add_gwKernel [IsProbabilityMeasure ν] (j k : ℕ) :
    markovChainLaw (dirac (j + k)) ν.gwKernel =
      markovChainLaw (dirac j) ν.gwKernel ∗ markovChainLaw (dirac k) ν.gwKernel := by
  rw [← markovChainLaw_conv_gwKernel, dirac_conv_dirac]

end MeasureTheory.Measure
