/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Matrix
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.MeasureTheory.Measure.PiWithDensity

/-!
# Maximal rank of Gaussian matrices

A rectangular matrix of independent real Gaussian entries with nonzero variances has rank
equal to the smaller of its dimensions almost surely. The means and variances may vary across
entries, and either index type may be empty.

The product-law theorem and its random-variable corollary supply the full-rank input to
Gaussian Gram-matrix arguments. They use the joint density and the general almost-sure rank
theorem for absolutely continuous matrix laws; no independence of rows or columns is assumed
in that underlying theorem.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapter 3.
-/

public section

open MeasureTheory ProbabilityTheory

open scoped NNReal

namespace TauCeti.Probability

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Independent Gaussian entries with arbitrary means and nonzero variances give a rectangular
matrix of maximal rank almost surely. In particular this applies to standard Gaussian entries.
The nested products sample rows and then their entries. -/
theorem ae_rank_eq_min_pi_gaussianReal (a : Matrix m n ℝ) (v : Matrix m n ℝ≥0)
    (hv : ∀ i j, v i j ≠ 0) :
    ∀ᵐ A ∂Measure.pi (fun i => Measure.pi fun j => gaussianReal (a i j) (v i j)),
      (Matrix.of A).rank = min (Fintype.card m) (Fintype.card n) := by
  classical
  let f (i : m) (j : n) := gaussianPDF (a i j) (v i j)
  have hfactor (i : m) (j : n) :
      volume.withDensity (f i j) = gaussianReal (a i j) (v i j) :=
    (gaussianReal_of_var_ne_zero _ (hv i j)).symm
  let (i : m) (j : n) : IsProbabilityMeasure (volume.withDensity (f i j)) := by
    rw [hfactor]
    infer_instance
  have hrow (i : m) :
      (Measure.pi fun j => gaussianReal (a i j) (v i j)) =
        (volume : Measure (n → ℝ)).withDensity (fun x => ∏ j, f i j (x j)) := by
    simp_rw [← hfactor i]
    exact TauCeti.pi_withDensity _ fun j => measurable_gaussianPDF _ _
  let (i : m) : IsProbabilityMeasure
      ((volume : Measure (n → ℝ)).withDensity (fun x => ∏ j, f i j (x j))) := by
    rw [← hrow]
    infer_instance
  have hμ : (Measure.pi fun i => Measure.pi fun j => gaussianReal (a i j) (v i j)) ≪
      (volume : Measure (m → n → ℝ)) := by
    simp_rw [hrow]
    rw [TauCeti.pi_withDensity (fun _ : m => (volume : Measure (n → ℝ)))
      (f := fun i x => ∏ j, f i j (x j)) (fun i =>
      Finset.measurable_prod _ fun j _ =>
        (measurable_gaussianPDF (a i j) (v i j)).comp (measurable_pi_apply j))]
    exact withDensity_absolutelyContinuous _ _
  exact Measure.ae_rank_eq_min _ hμ

end TauCeti.Probability

namespace ProbabilityTheory

variable {Ω m n : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n]
    {P : Measure Ω} {X : m → n → Ω → ℝ} {a : Matrix m n ℝ} {v : Matrix m n ℝ≥0}

/-- A matrix of jointly independent Gaussian random variables with nonzero variances has
maximal rank almost surely. The independence hypothesis ranges over all entries, including
entries in different rows. -/
theorem iIndepFun.ae_rank_eq_min_gaussianReal
    (hindep : iIndepFun (fun ij : m × n => X ij.1 ij.2) P)
    (hX : ∀ i j, HasLaw (X i j) (gaussianReal (a i j) (v i j)) P)
    (hv : ∀ i j, v i j ≠ 0) :
    ∀ᵐ ω ∂P, (Matrix.of fun i j => X i j ω).rank =
      min (Fintype.card m) (Fintype.card n) := by
  let (i : m) (j : n) : SigmaFinite (gaussianReal (a i j) (v i j)) := inferInstance
  have hindepSigma := hindep.precomp (Equiv.sigmaEquivProd m n).injective
  have hflat := hindepSigma.hasLaw_pi (fun ij : Σ _ : m, n => hX ij.1 ij.2)
  have hmatrix := (TauCeti.measurePreserving_piCurry
    (fun i j => gaussianReal (a i j) (v i j))).hasLaw.comp hflat
  have hrank := TauCeti.Probability.ae_rank_eq_min_pi_gaussianReal a v hv
  rw [← hmatrix.map_eq] at hrank
  exact ae_of_ae_map hmatrix.aemeasurable hrank

end ProbabilityTheory
