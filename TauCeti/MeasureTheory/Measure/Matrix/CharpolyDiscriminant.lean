/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Discriminant
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus

/-!
# Almost everywhere nonzero characteristic discriminant

Along a real-linear family of real or complex matrices parametrized by a finite-dimensional real
normed space, the real part of the characteristic discriminant is a real polynomial in linear
coordinates (`Matrix.exists_eval_eq_re_charpoly_discr`). If it is nonzero at one parameter, the
polynomial is nonzero, so its zero locus is null for additive Haar measure. Hence the
characteristic discriminant is nonzero almost everywhere for every law absolutely continuous
with respect to an additive Haar measure on the parameters.

The discriminant argument is the one used in Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2.
-/

public section

noncomputable section

namespace MeasureTheory.Measure

variable {ι 𝕜 E : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- If the characteristic discriminant along a real-linear family of matrices has nonzero
real part at one parameter, then it is nonzero almost everywhere for every law absolutely
continuous with respect to an additive Haar measure on the parameters. -/
theorem ae_charpoly_discr_ne_zero_of_re_ne_zero {ν : Measure E} [ν.IsAddHaarMeasure]
    (μ : Measure E) (hμ : μ ≪ ν) (L : E →ₗ[ℝ] Matrix ι ι 𝕜) {x₀ : E}
    (hx₀ : RCLike.re (L x₀).charpoly.discr ≠ 0) :
    ∀ᵐ x ∂μ, (L x).charpoly.discr ≠ 0 := by
  let b := Module.finBasis ℝ E
  obtain ⟨q, hq⟩ := Matrix.exists_eval_eq_re_charpoly_discr (L ∘ₗ b.equivFun.symm.toLinearMap)
  have hqL (x : E) : MvPolynomial.eval (b.equivFun x) q = RCLike.re (L x).charpoly.discr := by
    rw [hq, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hq₀ : q ≠ 0 := by
    rintro rfl
    rw [← hqL, map_zero] at hx₀
    exact hx₀ rfl
  have hnonzero : ∀ᵐ y : _ ∂volume, MvPolynomial.eval y q ≠ 0 :=
    compl_mem_ae_iff.mpr (q.volume_setOfPred_eval_eq_zero hq₀)
  have hp := (ae_comp_linearMap_mem_iff (μ := ν) (ν := volume)
    (L := b.equivFun.toLinearMap) b.equivFun.surjective
    (s := {y | MvPolynomial.eval y q = 0}ᶜ)
    q.measurableSet_setOfPred_eval_eq_zero.compl).mpr hnonzero
  filter_upwards [hμ.ae_le hp] with x hx h
  refine hx ?_
  simp only [Set.mem_ofPred_eq, LinearEquiv.coe_toLinearMap]
  rw [hqL, h, map_zero]

end MeasureTheory.Measure
