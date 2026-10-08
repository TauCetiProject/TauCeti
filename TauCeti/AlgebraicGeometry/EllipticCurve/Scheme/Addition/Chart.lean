/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Cover
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Points
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.AdditionLaw.Equation

/-!
# The Bosma–Lenstra addition morphisms on the chart cover

Let `W` be a Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its
projective model and let `S = Spec R`. The pieces of the Bosma–Lenstra chart cover
`WeierstrassCurve.additionCover` of `E ×_S E` are the spectra of the localizations of
`ChartRing i ⊗[R] ChartRing j` away from the six coordinates `chartPairLaw W i j k` of the two
addition laws `addXYZ P Q` (for `k = inl _`) and `dblAddXYZ P Q` (for `k = inr _`) at the
universal points `P` and `Q` of `ChartRing i ⊗[R] ChartRing j`. On such a piece, the law selected
by `k` is a solution of the projective Weierstrass equation
(`WeierstrassCurve.Projective.Equation.addXYZ`, `WeierstrassCurve.Projective.Equation.dblAddXYZ`)
with a unit coordinate, so it gives a point of `E` (`WeierstrassCurve.projModelPoint`). This file
defines the addition morphisms on the pieces of the cover as these points, and shows that they lie
over `S`. No ellipticity is needed.

## Main definitions

* `WeierstrassCurve.additionOnPiece W i j k`: the morphism
  `Spec (Localization.Away (chartPairLaw W i j k)) ⟶ projModel W` given by the addition law
  selected by `k`.

## Main results

* `WeierstrassCurve.additionOnPiece_inl` and `WeierstrassCurve.additionOnPiece_inr`: on the piece
  indexed by `inl k` (resp. `inr k`), the addition morphism is the point `projModelPoint` with
  homogeneous coordinates `addXYZ P Q` (resp. `dblAddXYZ P Q`), read on the chart `D₊(Xₖ)`.
* `WeierstrassCurve.equation_chartPairLaw_comp_inl` and
  `WeierstrassCurve.equation_chartPairLaw_comp_inr`: the two laws at the universal points of a
  product of two charts are solutions of the Weierstrass equation.
* `WeierstrassCurve.exists_SpecMap_additionOnPiece`: for a homomorphism `φ` out of the ring of a
  piece of the cover, the composite of `Spec φ` with the addition morphism on that piece is the
  point whose homogeneous coordinates are the image under `φ` of the law.
* `WeierstrassCurve.additionOnPiece_projModelOver`: the addition morphisms lie over `Spec R`.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, directory
`projects/ModularCurves/ModularCurves/EllipticCurve/`:
* from `AdditionChartAway.lean`: `awayTriple`, `equation_awayTriple`, `addOnZPieceHom` and
  `addOnYPieceHom`, within `additionOnPiece`;
* from `AdditionChartMor.lean`: `addOnZPieceMor`, `addOnYPieceMor`, `addOnZPieceMor_projModelπ`
  and `addOnYPieceMor_projModelπ`, as `additionOnPiece` and `additionOnPiece_projModelOver`.

Here the two laws are indexed together by `Fin 3 ⊕ Fin 3`, as in `chartPairLaw`. The morphism on a
piece is the point `WeierstrassCurve.projModelPoint` of the law, which evaluates the homogeneous
coordinate ring, in place of the source's chart homomorphism `chartHomOfTriple` (file
`AdditionChartHom.lean`) out of a dehomogenised chart ring. The laws solve the equation over every
ring, so the source's hypotheses that `R` is a Jacobson ring, that the product of two charts is a
domain and that the discriminant is a unit are dropped.
-/

public section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The law `addXYZ P Q` at the universal points `P` and `Q` of `ChartRing i ⊗[R] ChartRing j`,
that is `chartPairLaw W i j ∘ inl`, is a solution of the Weierstrass equation over that ring. -/
theorem equation_chartPairLaw_comp_inl (i j : Fin 3) :
    (W.toProjective.baseChange _).Equation (W.chartPairLaw i j ∘ Sum.inl) := by
  simpa only [Function.comp_def, chartPairLaw_inl] using
    Projective.Equation.addXYZ ((W.toProjective.equation_chartPoint i).baseChange _)
      ((W.toProjective.equation_chartPoint j).baseChange _)

/-- The law `dblAddXYZ P Q` at the universal points `P` and `Q` of `ChartRing i ⊗[R] ChartRing j`,
that is `chartPairLaw W i j ∘ inr`, is a solution of the Weierstrass equation over that ring. -/
theorem equation_chartPairLaw_comp_inr (i j : Fin 3) :
    (W.toProjective.baseChange _).Equation (W.chartPairLaw i j ∘ Sum.inr) := by
  simpa only [Function.comp_def, chartPairLaw_inr] using
    Projective.Equation.dblAddXYZ ((W.toProjective.equation_chartPoint i).baseChange _)
      ((W.toProjective.equation_chartPoint j).baseChange _)

/-- The **Bosma–Lenstra addition morphism** on a piece of the chart cover `additionCover W` of
`E ×_S E`, for `E = projModel W` and `S = Spec R`. Let `P` and `Q` be the universal points of
`ChartRing i ⊗[R] ChartRing j`. For `k = inl m` (resp. `k = inr m`), the coordinate of index `m`
of the law `addXYZ P Q` (resp. `dblAddXYZ P Q`) is `chartPairLaw W i j k`, a unit in the
localization away from it, and `additionOnPiece W i j k` is the point of `E` with homogeneous
coordinates the image of that law, read on the chart `D₊(Xₘ)` (`additionOnPiece_inl`,
`additionOnPiece_inr`). It lies over `S` (`additionOnPiece_projModelOver`). -/
noncomputable def additionOnPiece (i j : Fin 3) : (k : Fin 3 ⊕ Fin 3) →
    Spec (.of (Localization.Away (W.chartPairLaw i j k))) ⟶ W.projModel
  -- the law, a solution over `ChartRing i ⊗[R] ChartRing j`, is mapped to the localization
  | .inl k => W.projModelPoint _
      ((W.equation_chartPairLaw_comp_inl i j).baseChange (IsScalarTower.toAlgHom R _ _))
      (IsLocalization.Away.algebraMap_isUnit (W.chartPairLaw i j (.inl k)))
  | .inr k => W.projModelPoint _
      ((W.equation_chartPairLaw_comp_inr i j).baseChange (IsScalarTower.toAlgHom R _ _))
      (IsLocalization.Away.algebraMap_isUnit (W.chartPairLaw i j (.inr k)))

/-- On the piece of `additionCover W` indexed by `inl k`, the addition morphism is the point of
`projModel W` whose homogeneous coordinates are the image of the law `addXYZ P Q` at the universal
points `P` and `Q`, that is of `chartPairLaw W i j ∘ inl`, read on the chart `D₊(Xₖ)`. -/
@[simp]
theorem additionOnPiece_inl (i j k : Fin 3) : W.additionOnPiece i j (.inl k) =
    W.projModelPoint (algebraMap R _) (P := algebraMap _ _ ∘ W.chartPairLaw i j ∘ Sum.inl)
      ((W.equation_chartPairLaw_comp_inl i j).baseChange (IsScalarTower.toAlgHom R _ _))
      (IsLocalization.Away.algebraMap_isUnit (W.chartPairLaw i j (.inl k))) :=
  (rfl)

/-- On the piece of `additionCover W` indexed by `inr k`, the addition morphism is the point of
`projModel W` whose homogeneous coordinates are the image of the law `dblAddXYZ P Q` at the
universal points `P` and `Q`, that is of `chartPairLaw W i j ∘ inr`, read on the chart `D₊(Xₖ)`. -/
@[simp]
theorem additionOnPiece_inr (i j k : Fin 3) : W.additionOnPiece i j (.inr k) =
    W.projModelPoint (algebraMap R _) (P := algebraMap _ _ ∘ W.chartPairLaw i j ∘ Sum.inr)
      ((W.equation_chartPairLaw_comp_inr i j).baseChange (IsScalarTower.toAlgHom R _ _))
      (IsLocalization.Away.algebraMap_isUnit (W.chartPairLaw i j (.inr k))) :=
  (rfl)

/-- Let `φ` be a homomorphism to `A` from `Localization.Away (chartPairLaw W i j k)`, the ring of
the piece of the chart cover indexed by `(i, j, k)`. The image under `φ` of the law selected by `k`
at the universal points, `addXYZ` for `k = inl m` and `dblAddXYZ` for `k = inr m`, is a solution
of the Weierstrass equation over `A` whose coordinate of index `m` is a unit, and the composite of
`Spec φ` with the addition morphism on the piece is the point of `projModel W` with these
homogeneous coordinates, read on the chart `D₊(Xₘ)`. -/
theorem exists_SpecMap_additionOnPiece {A : CommRingCat.{u}} {i j : Fin 3}
    (k : Fin 3 ⊕ Fin 3) (φ : CommRingCat.of (Localization.Away (W.chartPairLaw i j k)) ⟶ A) :
    ∃ hP hm, Spec.map φ ≫ W.additionOnPiece i j k =
      W.projModelPoint (CommRingCat.ofHom (algebraMap R _) ≫ φ).hom (i := k.elim id id)
        (P := fun m ↦ (CommRingCat.ofHom (algebraMap
          (W.toProjective.ChartRing i ⊗[R] W.toProjective.ChartRing j) _) ≫ φ).hom
            (W.chartPairLaw i j (k.map (fun _ ↦ m) (fun _ ↦ m)))) hP hm := by
  -- along `φ`, a point of `projModel W` over the localization is the point of the images
  have key {P : Fin 3 → Localization.Away (W.chartPairLaw i j k)} {hP} {m : Fin 3}
      (hm : IsUnit (P m)) : ∃ hP' hm', Spec.map φ ≫ W.projModelPoint (algebraMap R _) hP hm =
        W.projModelPoint (CommRingCat.ofHom (algebraMap R _) ≫ φ).hom (P := φ.hom ∘ P) hP' hm' :=
    ⟨_, _, SpecMap_projModelPoint φ.hom hm⟩
  cases k
  · rw [additionOnPiece_inl]
    exact key _
  · rw [additionOnPiece_inr]
    exact key _

/-- The addition morphism on each piece of `additionCover W` lies over `Spec R`: its composite
with the structure morphism of `projModel W` is `Spec` of the structure map
`R → Localization.Away (chartPairLaw W i j k)`. -/
@[reassoc (attr := simp)]
theorem additionOnPiece_projModelOver (i j : Fin 3) (k : Fin 3 ⊕ Fin 3) :
    W.additionOnPiece i j k ≫ W.projModelOver =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (W.chartPairLaw i j k)))) := by
  cases k <;> exact W.projModelPoint_projModelOver ..

end WeierstrassCurve
