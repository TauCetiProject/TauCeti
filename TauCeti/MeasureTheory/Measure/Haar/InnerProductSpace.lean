/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Constructions.Pi

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

The volume of an `L²` product `PiLp 2 F` of finitely many finite-dimensional real inner product
spaces is the product of the volumes of the factors. Mathlib proves this for real factors, that is
for `EuclideanSpace ℝ ι`. The general form covers `EuclideanSpace ℂ ι`, whose volume is thereby
the product of the Lebesgue measures of its complex coordinates; this is how sets cut out by
conditions on single coordinates, such as polydiscs, are measured.

## Main results

* `TauCeti.volume_parallelepiped`: the parallelepiped spanned by `v` has volume `√(det G)`.
* `Module.Basis.volume_eq_smul_addHaar`: the volume measure is `√(det G) • b.addHaar`.
* `AffineIsometryEquiv.measurePreserving`: affine isometries preserve the volume measure, extending
  Mathlib's `LinearIsometryEquiv.measurePreserving` by a translation.
* `MeasureTheory.Measure.addHaar_setOf_fst_eq`: a hyperplane `{a} × E` of the Euclidean product
  `ℝ × E` is null for every additive Haar measure.
* `PiLp.volume_preserving_symm_measurableEquiv_toLp`: the volume of `PiLp 2 F` is the product of
  the volumes of the factors.

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

namespace AffineIsometryEquiv

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- Every affine isometry between finite-dimensional real inner product spaces preserves the
volume measure: it is a linear isometry followed by a translation. -/
theorem measurePreserving (f : E ≃ᵃⁱ[ℝ] F) : MeasurePreserving f := by
  have hf : ⇑f = fun x => f.linearIsometryEquiv x + f 0 := funext fun x => by
    simpa using f.map_vadd 0 x
  rw [hf]
  exact (measurePreserving_add_right volume (f 0)).comp f.linearIsometryEquiv.measurePreserving

end AffineIsometryEquiv

namespace MeasureTheory.Measure

/-- The hyperplane `{a} × E` of the Euclidean product `ℝ × E` is a null set for every additive
Haar measure. -/
theorem addHaar_setOf_fst_eq (μ : Measure (WithLp 2 (ℝ × E))) [μ.IsAddHaarMeasure] (a : ℝ) :
    μ {x | x.fst = a} = 0 := by
  let s : AffineSubspace ℝ (WithLp 2 (ℝ × E)) :=
    AffineSubspace.mk' (WithLp.toLp 2 (a, 0)) (LinearMap.ker (WithLp.fstL 2 ℝ ℝ E).toLinearMap)
  have hs : (s : Set (WithLp 2 (ℝ × E))) = {x | x.fst = a} := by
    ext x
    simp [s, sub_eq_zero]
  have hne : s ≠ ⊤ := by
    intro h
    have hmem : WithLp.toLp 2 (a + 1, (0 : E)) ∈ s := h ▸ AffineSubspace.mem_top ℝ _ _
    rw [← SetLike.mem_coe, hs] at hmem
    simp at hmem
  rw [← hs]
  exact addHaar_affineSubspace μ s hne

end MeasureTheory.Measure

namespace PiLp

variable {η : Type*} [Fintype η] (F : η → Type*) [∀ i, NormedAddCommGroup (F i)]
  [∀ i, InnerProductSpace ℝ (F i)] [∀ i, FiniteDimensional ℝ (F i)] [∀ i, MeasurableSpace (F i)]
  [∀ i, BorelSpace (F i)]

/-- **The volume of a Euclidean product is the product of the volumes.** For finitely many
finite-dimensional real inner product spaces `F i`, the measurable equivalence `ofLp` from the
`L²` product `PiLp 2 F` to the product `∀ i, F i` carries the volume of the inner product space
`PiLp 2 F` to the product of the volumes of the factors.

Mathlib's `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp` is the case of real factors.
For complex factors this identifies the volume of `EuclideanSpace ℂ ι`, as a real inner product
space, with the product of the Lebesgue measures of the coordinates. Since the map is a measurable
equivalence, `MeasurePreserving.symm` gives the direction of `toLp`. -/
theorem volume_preserving_symm_measurableEquiv_toLp :
    MeasurePreserving (MeasurableEquiv.toLp 2 (∀ i, F i)).symm := by
  let B i := stdOrthonormalBasis ℝ (F i)
  -- Read `PiLp 2 F` in the orthonormal basis `Pi.orthonormalBasis B` assembled from the bases
  -- `B i` of the factors, regroup its coordinates by factor, and read each group back in `F i`.
  have h := ((volume_preserving_pi fun i => (B i).measurePreserving_repr_symm).comp
    (volume_preserving_pi fun i => PiLp.volume_preserving_toLp (Fin (finrank ℝ (F i))))).comp
    ((TauCeti.measurePreserving_piCurry fun _ _ => (volume : Measure ℝ)).comp
      ((PiLp.volume_preserving_ofLp _).comp (Pi.orthonormalBasis B).measurePreserving_repr))
  -- The composite is `ofLp`, as one checks coordinate by coordinate.
  convert h using 1
  ext x i
  simp [Pi.orthonormalBasis, MeasurableEquiv.coe_piCurry]

end PiLp
