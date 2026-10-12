/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# The volume of a parallelepiped and the Gram determinant

In a finite-dimensional real inner product space, the volume measure gives measure one to the
parallelepiped spanned by an orthonormal basis (`OrthonormalBasis.volume_parallelepiped`). For an
arbitrary family `v` of as many vectors as the dimension, the parallelepiped it spans has volume
`√(det G)`, where `G` is the Gram matrix `⟪vᵢ, vⱼ⟫` of `v`; both sides vanish when `v` is linearly
dependent. For a basis `b` this says that the volume measure is `√(det G)` times the additive Haar
measure `b.addHaar` normalized by `b`.

This converts integrals against a basis-normalized Haar measure, such as the coordinate measure
in which a Riemannian volume density is expressed, into integrals against the volume measure.

## Main results

* `TauCeti.volume_parallelepiped`: the parallelepiped spanned by `v` has volume `√(det G)`.
* `Module.Basis.volume_eq_smul_addHaar`: the volume measure is `√(det G) • b.addHaar`.

## References

* F. R. Gantmacher, *The Theory of Matrices*, Vol. 1, Chelsea, 1959, Chapter IX, §5 (the Gram
  determinant as the squared volume of a parallelepiped).
-/

public section

open MeasureTheory Module

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace TauCeti

/-- In a finite-dimensional real inner product space, the parallelepiped spanned by a family of
as many vectors as the dimension has volume the square root of the Gram determinant of the
family. -/
theorem volume_parallelepiped (v : ι → E) (hv : Fintype.card ι = finrank ℝ E) :
    volume (parallelepiped v) = ENNReal.ofReal √(Matrix.gram ℝ v).det := by
  let o : OrthonormalBasis ι ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (Fintype.equivFinOfCardEq hv).symm
  -- The linear map sending the orthonormal basis `o` to `v` carries one parallelepiped to the
  -- other, and its absolute determinant is the square root of the Gram determinant of `v`.
  let f : E →ₗ[ℝ] E := o.toBasis.constr ℝ v
  have hfo (i : ι) : f (o i) = v i := by simp [f]
  have hf : f ∘ o = v := funext hfo
  have hsq : f.normDet ^ 2 = (Matrix.gram ℝ v).det := by
    simpa [hfo] using f.normDet_sq_eq_det_gram o
  rw [← hf, ← image_parallelepiped, Measure.addHaar_image_linearMap, o.volume_parallelepiped,
    mul_one, ← f.normDet_eq_abs_det, hf, ← hsq, Real.sqrt_sq f.normDet_nonneg]

end TauCeti

namespace Module.Basis

/-- The volume measure of a finite-dimensional real inner product space is the additive Haar
measure normalized by a basis `b`, scaled by the square root of the Gram determinant of `b`. -/
theorem volume_eq_smul_addHaar (b : Basis ι ℝ E) :
    (volume : Measure E) = ENNReal.ofReal √(Matrix.gram ℝ b).det • b.addHaar := by
  rw [← TauCeti.volume_parallelepiped b (finrank_eq_card_basis b).symm, addHaar_def]
  exact Measure.addHaarMeasure_unique volume b.parallelepiped

end Module.Basis
