/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.Hopf.InnerConjugation

/-!
# Inner conjugation in Hopf coordinates

An `R`-valued point `g` of an affine group acts on all algebra-valued points by inner
conjugation. This action is natural in the value algebra and is a group automorphism. Full
faithfulness of the functor of points therefore recovers a coordinate Hopf-algebra
automorphism.

The coordinate morphism is characterized both on arbitrary algebra-valued points and as an
algebra map. The latter is evaluation of the universal conjugation morphism at `g` in its first
factor:

```text
H --conj#--> H ⊗ H --(g ⊗ id)--> H.
```

## Main declarations

* `TauCeti.CommHopfAlgCat.innerConjugationIso`: the corresponding coordinate Hopf-algebra
  automorphism.
* `TauCeti.CommHopfAlgCat.innerConjugationIso_hom_toAlgHom`: its explicit coordinate formula.
* `TauCeti.CommHopfAlgCat.mapPointsFunctor_innerConjugationIso_hom`: its natural action on
  algebra-valued points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§3.5 and 10.20.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §8.
* The Tau Ceti contributors, prior formalization of inner conjugation,
  [TauCeti#5490](https://github.com/TauCetiProject/TauCeti/pull/5490),
  commit `8419e7ceed8e87e7a14be030b7a0dda52aea2d41`.
-/

public section

open CategoryTheory TauCeti TauCeti.CommHopfAlgCat TauCeti.HopfAlgebra WithConv

namespace TauCeti

universe u v

variable {R : Type u} [CommRing R]

namespace CommHopfAlgCat

variable (H : _root_.CommHopfAlgCat.{u} R)

/-- The coordinate Hopf-algebra automorphism representing conjugation by an `R`-valued point.

Contravariance means that its underlying coordinate map is the pullback of the pointwise inner
automorphism. -/
noncomputable def innerConjugationIso
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) : H ≅ H where
  hom := homOfPointsMap (HopfAlgebra.innerConjugationPointNatIso H g).hom
  inv := homOfPointsMap (HopfAlgebra.innerConjugationPointNatIso H g).inv
  hom_inv_id := by
    rw [← homOfPointsMap_comp, Iso.inv_hom_id, homOfPointsMap_id]
  inv_hom_id := by
    rw [← homOfPointsMap_comp, Iso.hom_inv_id, homOfPointsMap_id]

/-- Conjugation by the identity point is the identity coordinate Hopf-algebra automorphism. -/
@[simp]
theorem innerConjugationIso_one :
    innerConjugationIso H
        (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) =
      Iso.refl H := by
  apply Iso.ext
  dsimp only [innerConjugationIso]
  rw [HopfAlgebra.innerConjugationPointNatIso_one]
  exact homOfPointsMap_id H

/-- Coordinate pullback reverses the pointwise composition order: the coordinate automorphism for
conjugation by `g * h` is the composite for `g` followed by the one for `h`. -/
@[simp]
theorem innerConjugationIso_mul
    (g h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationIso H (g * h) =
      (innerConjugationIso H g).trans (innerConjugationIso H h) := by
  apply Iso.ext
  dsimp only [innerConjugationIso, Iso.trans_hom]
  have hmul := congrArg Iso.hom (HopfAlgebra.innerConjugationPointNatIso_mul H g h)
  simp only [Iso.trans_hom] at hmul
  rw [hmul, homOfPointsMap_comp]

/-- The coordinate automorphism for conjugation by an inverse point is the inverse coordinate
automorphism. -/
@[simp]
theorem innerConjugationIso_inv_point
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationIso H g⁻¹ = (innerConjugationIso H g).symm := by
  apply Iso.ext
  dsimp only [innerConjugationIso, Iso.symm_hom]
  rw [HopfAlgebra.innerConjugationPointNatIso_inv_point, Iso.symm_hom]

/-- The coordinate algebra map of inner conjugation is obtained from the universal conjugation
map by evaluating its conjugating variable at the given `R`-valued point. -/
theorem innerConjugationIso_hom_toAlgHom
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (innerConjugationIso H g).hom.hom.toAlgHom =
      (Algebra.TensorProduct.productMap
        ((Algebra.ofId R H).comp g.ofConv) (AlgHom.id R H)).comp
          (HopfAlgebra.conjugationAlgHom (R := R) (H := H)) := by
  apply AlgHom.ext
  intro x
  have hpoint :
      (mapPointsFunctor (innerConjugationIso H g).hom).app (CommAlgCat.of R H)
          (toConv (AlgHom.id R H)) =
        extendPoint H (CommAlgCat.of R H) g * toConv (AlgHom.id R H) *
          (extendPoint H (CommAlgCat.of R H) g)⁻¹ := by
    dsimp only [innerConjugationIso]
    rw [mapPointsFunctor_homOfPointsMap]
    exact HopfAlgebra.innerConjugationPointNatIso_hom_app_apply H g _ _
  have hx := congrArg (fun p : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R H) ↦
    p.ofConv x) hpoint
  rw [mapPointsFunctor_app_apply] at hx
  calc
    (innerConjugationIso H g).hom.hom.toAlgHom x =
        (extendPoint H (CommAlgCat.of R H) g * toConv (AlgHom.id R H) *
          (extendPoint H (CommAlgCat.of R H) g)⁻¹).ofConv x := by
      simpa only [AlgHom.comp_apply, AlgHom.id_apply, WithConv.toConv_ofConv] using hx
    _ = (Algebra.TensorProduct.productMap
          ((Algebra.ofId R H).comp g.ofConv) (AlgHom.id R H)).comp
            (HopfAlgebra.conjugationAlgHom (R := R) (H := H)) x := by
      rw [HopfAlgebra.extendPoint_apply]
      exact
        DFunLike.congr_fun
          (HopfAlgebra.productMap_comp_conjugationAlgHom (R := R) (H := H)
            (toConv ((Algebra.ofId R H).comp g.ofConv)) (toConv (AlgHom.id R H))).symm x

/-- The inverse coordinate algebra map is obtained from the universal conjugation map by
evaluating its conjugating variable at the inverse of the given `R`-valued point. -/
theorem innerConjugationIso_inv_toAlgHom
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (innerConjugationIso H g).inv.hom.toAlgHom =
      (Algebra.TensorProduct.productMap
        ((Algebra.ofId R H).comp (g⁻¹).ofConv) (AlgHom.id R H)).comp
          (HopfAlgebra.conjugationAlgHom (R := R) (H := H)) := by
  rw [← Iso.symm_hom, ← innerConjugationIso_inv_point, innerConjugationIso_hom_toAlgHom]

/-- The coordinate inner automorphism induces natural inner conjugation on points over
commutative value algebras in any universe. -/
@[simp]
theorem mapPointsFunctor_innerConjugationIso_hom
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    mapPointsFunctor.{u, u, v} (innerConjugationIso H g).hom =
      (HopfAlgebra.innerConjugationPointNatIso H g).hom := by
  -- `mapPointsFunctor_homOfPointsMap` only covers value universe `u`; prove the
  -- universe-`v` statement pointwise using the coordinate formula.
  apply HopfAlgebra.pointsFunctor_hom_ext
  intro A x
  rw [HopfAlgebra.innerConjugationPointNatIso_hom_app_apply]
  apply WithConv.ofConv_injective
  rw [mapPointsFunctor_app_apply]
  rw [innerConjugationIso_hom_toAlgHom]
  rw [← AlgHom.comp_assoc]
  have hprod :
      x.ofConv.comp (Algebra.TensorProduct.productMap
          ((Algebra.ofId R H).comp g.ofConv) (AlgHom.id R H)) =
        Algebra.TensorProduct.productMap (extendPoint H A g).ofConv x.ofConv := by
    rw [HopfAlgebra.extendPoint_apply]
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply,
      AlgHom.id_apply, Algebra.ofId_apply, map_mul]
    exact congrArg (fun c : A ↦ c * x.ofConv b) (x.ofConv.commutes (g.ofConv a))
  rw [hprod]
  exact (HopfAlgebra.productMap_comp_conjugationAlgHom (R := R) (H := H)
    (extendPoint H A g) x)

/-- The inverse coordinate inner automorphism induces the inverse natural inner conjugation
on points over commutative value algebras in any universe. -/
@[simp]
theorem mapPointsFunctor_innerConjugationIso_inv
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    mapPointsFunctor.{u, u, v} (innerConjugationIso H g).inv =
      (HopfAlgebra.innerConjugationPointNatIso H g).inv := by
  rw [← Iso.symm_hom, ← innerConjugationIso_inv_point,
    mapPointsFunctor_innerConjugationIso_hom,
    HopfAlgebra.innerConjugationPointNatIso_inv_point, Iso.symm_hom]

end CommHopfAlgCat

end TauCeti
