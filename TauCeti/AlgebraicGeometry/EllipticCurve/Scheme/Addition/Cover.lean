/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Chart
import TauCeti.LinearAlgebra.Unimodular

/-!
# The Bosma–Lenstra chart cover of `E ×_S E`

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its
projective model and let `S = Spec R`. The products `D₊(Xᵢ) ×_S D₊(Xⱼ)` of the standard affine
charts of `E` cover `E ×_S E`, and `D₊(Xᵢ) ×_S D₊(Xⱼ)` is the spectrum of
`ChartRing i ⊗[R] ChartRing j` (`WeierstrassCurve.chartPairι`). This ring carries two universal
points of the curve: `P`, coming from the first factor, with `i`-th coordinate `1`, and `Q`, coming
from the second factor, with `j`-th coordinate `1`.

The six coordinates of the two Bosma–Lenstra addition laws `addXYZ P Q` and `dblAddXYZ P Q`
generate the unit ideal of `ChartRing i ⊗[R] ChartRing j`
(`WeierstrassCurve.Projective.span_range_addXYZ_union_range_dblAddXYZ_eq_top`), so the loci where
one of them is a unit cover `D₊(Xᵢ) ×_S D₊(Xⱼ)`. On such a locus, the corresponding law is a triple
with a unit coordinate. This file assembles these loci, nine chart products with six loci each,
into a finite affine open cover of `E ×_S E`.

## Main definitions

* `WeierstrassCurve.chartPairLaw W i j`: the six coordinates of `addXYZ P Q` and `dblAddXYZ P Q` at
  the universal points `P` and `Q` of `ChartRing i ⊗[R] ChartRing j`.
* `WeierstrassCurve.additionCover W`: the affine open cover of `E ×_S E` by the spectra of the
  localizations of the rings `ChartRing i ⊗[R] ChartRing j` away from the coordinates
  `chartPairLaw W i j k`.

## Main results

* `WeierstrassCurve.span_range_chartPairLaw_eq_top`: the six law coordinates generate the unit
  ideal.
* `WeierstrassCurve.exists_mem_range_specMap_comp_chartPairι`: every point of `E ×_S E` lies on the
  locus, in some product of two charts, where some law coordinate is a unit.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, directory
`projects/ModularCurves/ModularCurves/EllipticCurve/`:
* from `AdditionChartRing.lean`: `biChartPointFst`, `biChartPointSnd`, `lawOneTriple` and
  `lawTwoTriple`, as `chartPairLaw`. The universal points of a product of two charts are the images
  of `WeierstrassCurve.Projective.chartPoint` in the tensor product of TauCeti's chart rings
  `ChartRing`, in place of the source's presented ring in four variables.
* from `AdditionChartSpec.lean`: `chartProductCover`, as
  `exists_mem_range_specMap_comp_chartPairι`.
* from `AdditionChartDomain.lean`: `span_lawOneTriple_union_lawTwoTriple_eq_top`, as
  `span_range_chartPairLaw_eq_top`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MvPolynomial TensorProduct
open Algebra.TensorProduct (includeLeft includeLeftRingHom includeRight)

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The six coordinates of the two Bosma–Lenstra addition laws `addXYZ P Q` (indexed by `inl`)
and `dblAddXYZ P Q` (indexed by `inr`) at the universal points `P = chartPoint i ⊗ 1` and
`Q = 1 ⊗ chartPoint j` of the product `ChartRing i ⊗[R] ChartRing j` of two charts. -/
noncomputable def chartPairLaw (i j : Fin 3) :
    Fin 3 ⊕ Fin 3 → W.toProjective.ChartRing i ⊗[R] W.toProjective.ChartRing j :=
  Sum.elim
    ((W.toProjective.baseChange _).addXYZ (includeLeft (S := R) ∘ W.toProjective.chartPoint i)
      (includeRight ∘ W.toProjective.chartPoint j))
    ((W.toProjective.baseChange _).dblAddXYZ (includeLeft (S := R) ∘ W.toProjective.chartPoint i)
      (includeRight ∘ W.toProjective.chartPoint j))

/-- The coordinates of `chartPairLaw` indexed by `inl` are those of `addXYZ P Q`. -/
@[simp]
theorem chartPairLaw_inl (i j k : Fin 3) :
    W.chartPairLaw i j (.inl k) =
      (W.toProjective.baseChange _).addXYZ (includeLeft (S := R) ∘ W.toProjective.chartPoint i)
        (includeRight ∘ W.toProjective.chartPoint j) k :=
  (rfl)

/-- The coordinates of `chartPairLaw` indexed by `inr` are those of `dblAddXYZ P Q`. -/
@[simp]
theorem chartPairLaw_inr (i j k : Fin 3) :
    W.chartPairLaw i j (.inr k) =
      (W.toProjective.baseChange _).dblAddXYZ (includeLeft (S := R) ∘ W.toProjective.chartPoint i)
        (includeRight ∘ W.toProjective.chartPoint j) k :=
  (rfl)

/-- On an elliptic curve, the six coordinates of the two addition laws at the universal points of
the product `ChartRing i ⊗[R] ChartRing j` of two charts generate the unit ideal. -/
theorem span_range_chartPairLaw_eq_top [W.IsElliptic] (i j : Fin 3) :
    Ideal.span (Set.range (W.chartPairLaw i j)) = ⊤ := by
  have : (W.toProjective.baseChange
      (W.toProjective.ChartRing i ⊗[R] W.toProjective.ChartRing j)).IsElliptic :=
    inferInstanceAs (W.map _).IsElliptic
  rw [chartPairLaw, Set.Sum.elim_range]
  exact Projective.span_range_addXYZ_union_range_dblAddXYZ_eq_top
    ((W.toProjective.equation_chartPoint i).baseChange _)
    ((W.toProjective.equation_chartPoint j).baseChange _)
    (TauCeti.Module.isUnimodular_of_isUnit_apply (i := i)
      (by simp [← Algebra.TensorProduct.one_def]))
    (TauCeti.Module.isUnimodular_of_isUnit_apply (i := j)
      (by simp [← Algebra.TensorProduct.one_def]))

/-- Every point of `E ×_S E` lies on the product `D₊(Xᵢ) ×_S D₊(Xⱼ)` of two charts, at a point
where some coordinate `chartPairLaw W i j k` of one of the two addition laws is a unit: it is in
the image of `Spec` of the localization of `ChartRing i ⊗[R] ChartRing j` away from that
coordinate. -/
theorem exists_mem_range_specMap_comp_chartPairι [W.IsElliptic]
    (x : ↑(pullback W.projModelOver W.projModelOver)) : ∃ a : (Fin 3 × Fin 3) × (Fin 3 ⊕ Fin 3),
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap _
        (Localization.Away (W.chartPairLaw a.1.1 a.1.2 a.2)))) ≫ W.chartPairι a.1.1 a.1.2) := by
  -- the charts `D₊(Xᵢ)` cover `projModel W`
  obtain ⟨i, hi⟩ := W.exists_mem_range_chartι (pullback.fst W.projModelOver W.projModelOver x)
  obtain ⟨j, hj⟩ := W.exists_mem_range_chartι (pullback.snd W.projModelOver W.projModelOver x)
  -- so `x` lies on the product of the charts `D₊(Xᵢ)` and `D₊(Xⱼ)`
  obtain ⟨y, rfl⟩ : x ∈ Set.range (W.chartPairι i j) := by
    rw [range_chartPairι]
    exact ⟨hi, hj⟩
  -- the law coordinates generate the unit ideal, so the localizations away from them cover
  -- `Spec (ChartRing i ⊗ ChartRing j)`
  obtain ⟨k, z, hz⟩ : ∃ k, y ∈ Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap _ (Localization.Away (W.chartPairLaw i j k))))) := by
    obtain ⟨z, hz⟩ := (Scheme.affineOpenCoverOfSpanRangeEqTop
      (R := .of (W.toProjective.ChartRing i ⊗[R] W.toProjective.ChartRing j)) (W.chartPairLaw i j)
      (W.span_range_chartPairLaw_eq_top i j)).covers y
    -- the maps of this cover are `Spec` of the localization maps
    exact ⟨_, z, Scheme.affineOpenCoverOfSpanRangeEqTop_f _ _ _ ▸ hz⟩
  exact ⟨((i, j), k), z, by rw [Scheme.Hom.comp_apply, hz]⟩

/-- The **Bosma–Lenstra chart cover** of `E ×_S E`, for `E = projModel W` and `S = Spec R`: the
affine open cover by the loci, in the products `D₊(Xᵢ) ×_S D₊(Xⱼ)` of two charts, where one of the
six coordinates `chartPairLaw W i j k` of the two addition laws is a unit. It has `54` pieces,
indexed by `((i, j), k)` in `(Fin 3 × Fin 3) × (Fin 3 ⊕ Fin 3)`; the piece indexed by `((i, j), k)`
is `Spec` of the localization of `ChartRing i ⊗[R] ChartRing j` away from `chartPairLaw W i j k`.
The definition is reducible, so its pieces and their maps to `E ×_S E` unfold by `simp`. -/
@[expose, reducible, simps f]
noncomputable def additionCover [W.IsElliptic] :
    (pullback W.projModelOver W.projModelOver).AffineOpenCover where
  I₀ := (Fin 3 × Fin 3) × (Fin 3 ⊕ Fin 3)
  X a := .of (Localization.Away (W.chartPairLaw a.1.1 a.1.2 a.2))
  f a := Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ W.chartPairι a.1.1 a.1.2
  idx x := (W.exists_mem_range_specMap_comp_chartPairι x).choose
  covers x := (W.exists_mem_range_specMap_comp_chartPairι x).choose_spec

end WeierstrassCurve
