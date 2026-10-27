/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.InnerConjugation
public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation

/-!
# Inner conjugation in Hopf coordinates

An `R`-valued point `g` of an affine group acts on all algebra-valued points by inner
conjugation. This file packages `HopfAlgebra.pointConjugationBialgEquiv` as an isomorphism
in the category of commutative Hopf algebras and identifies its action on the functor of points.

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
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) : H ≅ H :=
  _root_.CommHopfAlgCat.isoMk (HopfAlgebra.pointConjugationBialgEquiv g)

/-- The coordinate algebra map of inner conjugation is the point-conjugation algebra map. -/
@[simp]
theorem innerConjugationIso_hom_toAlgHom
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (innerConjugationIso H g).hom.hom.toAlgHom =
      HopfAlgebra.pointConjugationAlgHom g := by
  simp only [innerConjugationIso, _root_.CommHopfAlgCat.isoMk_hom,
    _root_.CommHopfAlgCat.hom_ofHom, HopfAlgebra.pointConjugationBialgEquiv_toAlgHom]

/-- Conjugation by the identity point is the identity coordinate Hopf-algebra automorphism. -/
@[simp]
theorem innerConjugationIso_one :
    innerConjugationIso H
        (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) =
      Iso.refl H := by
  apply Iso.ext
  apply _root_.CommHopfAlgCat.hom_ext
  apply BialgHom.coe_toAlgHom_injective
  simp only [innerConjugationIso_hom_toAlgHom, HopfAlgebra.pointConjugationAlgHom_one,
    Iso.refl_hom, _root_.CommHopfAlgCat.hom_id]

/-- Coordinate pullback reverses the pointwise composition order: the coordinate automorphism for
conjugation by `g * h` is the composite for `g` followed by the one for `h`. -/
@[simp]
theorem innerConjugationIso_mul
    (g h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationIso H (g * h) =
      (innerConjugationIso H g).trans (innerConjugationIso H h) := by
  apply Iso.ext
  apply _root_.CommHopfAlgCat.hom_ext
  apply BialgHom.coe_toAlgHom_injective
  simp only [innerConjugationIso_hom_toAlgHom, HopfAlgebra.pointConjugationAlgHom_mul,
    Iso.trans_hom, _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom]

/-- The coordinate automorphism for conjugation by an inverse point is the inverse coordinate
automorphism. -/
@[simp]
theorem innerConjugationIso_inv_point
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationIso H g⁻¹ = (innerConjugationIso H g).symm := by
  apply Iso.ext
  apply (cancel_mono (innerConjugationIso H g).hom).mp
  rw [Iso.symm_hom, Iso.inv_hom_id]
  rw [← Iso.trans_hom, ← innerConjugationIso_mul, inv_mul_cancel,
    innerConjugationIso_one, Iso.refl_hom]

/-- The inverse coordinate algebra map is point conjugation by the inverse point. -/
theorem innerConjugationIso_inv_toAlgHom
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (innerConjugationIso H g).inv.hom.toAlgHom =
      HopfAlgebra.pointConjugationAlgHom g⁻¹ := by
  rw [← Iso.symm_hom, ← innerConjugationIso_inv_point, innerConjugationIso_hom_toAlgHom]

/-- The coordinate inner automorphism induces natural inner conjugation on points over
commutative value algebras in any universe. -/
@[simp]
theorem mapPointsFunctor_innerConjugationIso_hom
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    CommHopfAlgCat.Hom.mapPointsFunctor.{u, u, v} (innerConjugationIso H g).hom =
      (HopfAlgebra.innerConjugationPointNatIso H g).hom := by
  apply HopfAlgebra.pointsFunctor_hom_ext
  intro A x
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, innerConjugationIso_hom_toAlgHom,
    HopfAlgebra.comp_pointConjugationAlgHom, HopfAlgebra.innerConjugationPointNatIso_hom_app_apply]
  rw [HopfAlgebra.extendPoint_apply H A g, AlgHom.mapValue_apply]

/-- The inverse coordinate inner automorphism induces the inverse natural inner conjugation
on points over commutative value algebras in any universe. -/
@[simp]
theorem mapPointsFunctor_innerConjugationIso_inv
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    CommHopfAlgCat.Hom.mapPointsFunctor.{u, u, v} (innerConjugationIso H g).inv =
      (HopfAlgebra.innerConjugationPointNatIso H g).inv := by
  rw [← Iso.symm_hom, ← innerConjugationIso_inv_point,
    mapPointsFunctor_innerConjugationIso_hom,
    HopfAlgebra.innerConjugationPointNatIso_inv_point, Iso.symm_hom]

end CommHopfAlgCat

end TauCeti
