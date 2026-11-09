/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Finite
public import TauCeti.Probability.RandomMeasure.Superposition
public import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Sampling with a sigma-finite Poisson intensity

`Measure.poissonLaw` superposes independent finite Poisson samples on a countable
measurable partition of a sigma-finite intensity. The resulting probability law has
the Poisson exponential formula and its mean measure is the specified intensity.
Infinite total intensity and infinite test integrals are allowed, and atomic
intensities retain multiplicities. No topology or nonempty location space is needed.

The finite samples use `TauCeti.Probability.finitePoissonLaw`; countable
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

private def poissonPiece (Λ : Measure X) [SigmaFinite Λ] (n : ℕ) : Measure X :=
  Λ.restrict (disjointed (spanningSets Λ) n)

private instance (Λ : Measure X) [SigmaFinite Λ] (n : ℕ) :
    IsFiniteMeasure (poissonPiece Λ n) := by
  apply isFiniteMeasure_restrict.mpr
  exact ne_top_of_le_ne_top (measure_spanningSets_lt_top Λ n).ne
    (measure_mono (disjointed_subset _ _))

/-- Sample independently on the finite pieces of a measurable partition of `Λ`, then
superpose the samples. The rate on each piece is its mass, including zero-mass pieces. -/
def poissonLaw (Λ : Measure X) [SigmaFinite Λ] : Measure (Measure X) :=
  (Measure.infinitePi fun n : ℕ =>
    finitePoissonLaw ((poissonPiece Λ n) univ).toNNReal
      (((poissonPiece Λ n) univ)⁻¹ • poissonPiece Λ n)).map Measure.sum

/-- The countable sampling construction is a probability law. -/
instance (Λ : Measure X) [SigmaFinite Λ] : IsProbabilityMeasure Λ.poissonLaw := by
  unfold poissonLaw
  infer_instance

/-- Integrals against the sampling law are integrals of the superposition of independent
finite samples. This exposes the sampling representation without unfolding the law. -/
theorem lintegral_poissonLaw (Λ : Measure X) [SigmaFinite Λ]
    {g : Measure X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ξ, g ξ ∂Λ.poissonLaw =
      ∫⁻ ξ, g (Measure.sum ξ) ∂Measure.infinitePi (fun n : ℕ =>
        finitePoissonLaw ((Λ.restrict (disjointed (spanningSets Λ) n)) univ).toNNReal
          (((Λ.restrict (disjointed (spanningSets Λ) n)) univ)⁻¹ •
            Λ.restrict (disjointed (spanningSets Λ) n))) := by
  rw [poissonLaw, lintegral_map hg measurable_sum]
  simp only [poissonPiece]

/-- The sigma-finite sampling construction has the Poisson exponential formula.
An infinite exponent integral gives zero, not a real-valued integral's junk value. -/
theorem laplaceFunctional_poissonLaw (Λ : Measure X) [SigmaFinite Λ]
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    Λ.poissonLaw.laplaceFunctional id f =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞) ∂Λ) : ℝ≥0∞) := by
  let Q (n : ℕ) := finitePoissonLaw ((poissonPiece Λ n) univ).toNNReal
    (((poissonPiece Λ n) univ)⁻¹ • poissonPiece Λ n)
  have hQ (n : ℕ) : IsProbabilityMeasure (Q n) := inferInstance
  have hL (n : ℕ) : (Measure.infinitePi Q).laplaceFunctional (fun ξ => ξ n) f =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞)
        ∂poissonPiece Λ n) : ℝ≥0∞) := by
    calc
      _ = (Q n).laplaceFunctional id f := by
        simpa only [laplaceFunctional_def, Function.comp_apply, id_eq] using
          (measurePreserving_eval_infinitePi Q n).lintegral_comp
            (measurable_expNeg_lintegral measurable_id hf)
      _ = _ := laplaceFunctional_finitePoissonLaw_normalize _ hf
  have hsum := (iIndepFun_infinitePi (fun _ : ℕ => measurable_id)).laplaceFunctional_sum_eq_expNeg
    (fun n => measurable_pi_apply n) hf hL
  unfold poissonPiece at hsum
  rw [sum_restrict_disjointed_spanningSets] at hsum
  rw [poissonLaw, laplaceFunctional_map _ measurable_sum measurable_id hf]
  exact hsum

/-- The mean random measure of the sigma-finite construction is exactly its intensity. -/
@[simp] theorem join_poissonLaw (Λ : Measure X) [SigmaFinite Λ] :
    Λ.poissonLaw.join = Λ := by
  let Q (n : ℕ) := finitePoissonLaw ((poissonPiece Λ n) univ).toNNReal
    (((poissonPiece Λ n) univ)⁻¹ • poissonPiece Λ n)
  have hQ (n : ℕ) : IsProbabilityMeasure (Q n) := inferInstance
  ext s hs
  rw [join_apply hs, lintegral_poissonLaw Λ (measurable_coe hs)]
  simp only [Measure.sum_apply _ hs]
  rw [lintegral_tsum (f := fun n (ξ : ℕ → Measure X) => ξ n s)
    (fun n => ((measurable_coe hs).comp (measurable_pi_apply n)).aemeasurable)]
  have heval (n : ℕ) : (∫⁻ ξ : ℕ → Measure X, ξ n s ∂Measure.infinitePi Q) =
      poissonPiece Λ n s := by
    rw [(measurePreserving_eval_infinitePi Q n).lintegral_comp (measurable_coe hs),
      ← join_apply hs, join_finitePoissonLaw_normalize]
  simp only [Q, poissonPiece] at heval
  simp_rw [heval]
  rw [← Measure.sum_apply _ hs, sum_restrict_disjointed_spanningSets]

/-- Zero intensity produces the empty configuration, including on an empty location space. -/
@[simp] theorem poissonLaw_zero : (0 : Measure X).poissonLaw = Measure.dirac 0 := by
  rw [poissonLaw]
  simp only [poissonPiece, Measure.restrict_zero, FunLike.coe_zero, Pi.zero_apply,
    ENNReal.toNNReal_zero, finitePoissonLaw_zero, infinitePi_dirac,
    Measure.map_dirac' measurable_sum]
  simp

end MeasureTheory.Measure
