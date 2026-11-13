/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Finite
public import TauCeti.Probability.RandomMeasure.Superposition
public import TauCeti.MeasureTheory.Measure.Measurability
public import TauCeti.Probability.PointProcess.Poisson.Basic
import TauCeti.Probability.PointProcess.Poisson.LaplaceCharacterization

/-!
# Sampling with a sigma-finite Poisson intensity

`Measure.poissonLaw` superposes independent finite Poisson samples on a countable
measurable partition of a sigma-finite intensity. The resulting probability law has
the Poisson exponential formula and its mean measure is the specified intensity. By the
Laplace characterization, the identity random measure under this law is therefore a Poisson
random measure with the specified intensity, so Poisson random measures exist for every
sigma-finite intensity.
Infinite total intensity and infinite test integrals are allowed, and atomic
intensities retain multiplicities. No topology or nonempty location space is needed.

The finite samples use `Measure.finitePoissonLawOf`; countable
superposition uses its existing independent Laplace-functional identity.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Theorem 3.6 (finite samples on a countable partition).
-/

public section

noncomputable section

open ProbabilityTheory Set
open TauCeti.Probability
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X]

/-- The finite intensity on the `n`th piece of the disjointed spanning partition used
by `poissonLaw`. -/
def poissonPiece (Λ : Measure X) [SigmaFinite Λ] (n : ℕ) : Measure X :=
  Λ.restrict (disjointed (spanningSets Λ) n)

/-- Each sampling piece is the restriction to a disjointed spanning set. -/
theorem poissonPiece_def (Λ : Measure X) [SigmaFinite Λ] (n : ℕ) :
    Λ.poissonPiece n = Λ.restrict (disjointed (spanningSets Λ) n) := (rfl)

/-- Each sampling piece has finite intensity. -/
instance (Λ : Measure X) [SigmaFinite Λ] (n : ℕ) :
    IsFiniteMeasure (poissonPiece Λ n) := by
  apply isFiniteMeasure_restrict.mpr
  exact ne_top_of_le_ne_top (measure_spanningSets_lt_top Λ n).ne
    (measure_mono (disjointed_subset _ _))

/-- The sampling pieces recover the full intensity by countable superposition. -/
@[simp] theorem sum_poissonPiece (Λ : Measure X) [SigmaFinite Λ] :
    Measure.sum (poissonPiece Λ) = Λ := by
  simpa only [← poissonPiece_def] using sum_restrict_disjointed_spanningSets Λ Λ

private abbrev poissonPieceLaw (Λ : Measure X) [SigmaFinite Λ] (n : ℕ) :=
  (Λ.poissonPiece n).finitePoissonLawOf

/-- Sample independently on the finite pieces of a measurable partition of `Λ`, then
superpose the samples. The rate on each piece is its mass, including zero-mass pieces. -/
def poissonLaw (Λ : Measure X) [SigmaFinite Λ] : Measure (Measure X) :=
  (Measure.infinitePi (poissonPieceLaw Λ)).map Measure.sum

/-- The law is the pushforward of independent normalized finite samples by superposition. -/
theorem poissonLaw_def (Λ : Measure X) [SigmaFinite Λ] :
    Λ.poissonLaw =
      (Measure.infinitePi fun n : ℕ => (Λ.poissonPiece n).finitePoissonLawOf).map
        Measure.sum := (rfl)

/-- The countable sampling construction is a probability law. -/
instance (Λ : Measure X) [SigmaFinite Λ] : IsProbabilityMeasure Λ.poissonLaw := by
  unfold poissonLaw
  infer_instance

/-- Integrals against the sampling law are integrals of the superposition of independent
finite samples. This exposes the sampling representation without unfolding the law. -/
theorem lintegral_poissonLaw (Λ : Measure X) [SigmaFinite Λ]
    {g : Measure X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ξ, g ξ ∂Λ.poissonLaw =
      ∫⁻ ξ, g (Measure.sum ξ) ∂Measure.infinitePi
        (fun n : ℕ => (Λ.poissonPiece n).finitePoissonLawOf) := by
  rw [poissonLaw_def, lintegral_map hg measurable_sum]

/-- The sigma-finite sampling construction has the Poisson exponential formula.
An infinite exponent integral gives zero, not a real-valued integral's junk value. -/
theorem laplaceFunctional_poissonLaw (Λ : Measure X) [SigmaFinite Λ]
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    Λ.poissonLaw.laplaceFunctional id f =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞) ∂Λ) : ℝ≥0∞) := by
  have hL (n : ℕ) :
      (Measure.infinitePi (poissonPieceLaw Λ)).laplaceFunctional (fun ξ => ξ n) f =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞)
        ∂poissonPiece Λ n) : ℝ≥0∞) := by
    calc
      _ = (poissonPieceLaw Λ n).laplaceFunctional id f := by
        simpa only [laplaceFunctional_def, Function.comp_apply, id_eq] using
          (measurePreserving_eval_infinitePi (poissonPieceLaw Λ) n).lintegral_comp
            (measurable_expNeg_lintegral measurable_id hf)
      _ = _ := laplaceFunctional_finitePoissonLawOf _ hf
  have hsum := (iIndepFun_infinitePi (fun _ : ℕ => measurable_id)).laplaceFunctional_sum_eq_expNeg
    (fun n => measurable_pi_apply n) hf hL
  rw [sum_poissonPiece] at hsum
  rw [poissonLaw, laplaceFunctional_map _ measurable_sum measurable_id hf]
  exact hsum

/-- **Existence of Poisson random measures.** Under the sigma-finite sampling law, the identity
random measure is a Poisson random measure with intensity `Λ`. -/
theorem isPoissonRandomMeasure_poissonLaw (Λ : Measure X) [SigmaFinite Λ] :
    IsPoissonRandomMeasure Λ.poissonLaw id Λ :=
  isPoissonRandomMeasure_of_laplaceFunctional measurable_id fun _ hf ↦
    laplaceFunctional_poissonLaw Λ hf

/-- The mean random measure of the sigma-finite construction is exactly its intensity. -/
@[simp] theorem join_poissonLaw (Λ : Measure X) [SigmaFinite Λ] :
    Λ.poissonLaw.join = Λ := by
  ext s hs
  rw [join_apply hs, lintegral_poissonLaw Λ (measurable_coe hs)]
  simp only [Measure.sum_apply _ hs]
  rw [lintegral_tsum (f := fun n (ξ : ℕ → Measure X) => ξ n s)
    (fun n => ((measurable_coe hs).comp (measurable_pi_apply n)).aemeasurable)]
  have heval (n : ℕ) :
      (∫⁻ ξ : ℕ → Measure X, ξ n s ∂Measure.infinitePi
        (fun k : ℕ => (Λ.poissonPiece k).finitePoissonLawOf)) =
        poissonPiece Λ n s := by
    rw [(measurePreserving_eval_infinitePi (poissonPieceLaw Λ) n).lintegral_comp
      (measurable_coe hs), ← join_apply hs, join_finitePoissonLawOf]
  simp_rw [heval]
  rw [← Measure.sum_apply _ hs, sum_poissonPiece]

/-- Zero intensity produces the empty configuration, including on an empty location space. -/
@[simp] theorem poissonLaw_zero : (0 : Measure X).poissonLaw = Measure.dirac 0 := by
  rw [poissonLaw_def]
  simp only [poissonPiece_def, Measure.restrict_zero, finitePoissonLawOf_zero,
    infinitePi_dirac, Measure.map_dirac' measurable_sum]
  simp

end MeasureTheory.Measure
