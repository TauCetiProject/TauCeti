/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.PointsFunctor

/-!
# Inner conjugation on the functor of points

An `R`-valued point of a Hopf algebra acts on its algebra-valued points by conjugation after
extension to the value algebra. This action is a group automorphism, natural in the value
algebra, and respects identity, multiplication, and inversion of the conjugating point.

## Main declarations

* `TauCeti.HopfAlgebra.innerConjugationPointIso`: inner conjugation on `A`-valued points.
* `TauCeti.HopfAlgebra.innerConjugationPointNatIso`: the natural automorphism of the functor
  of points, for an arbitrary semiring Hopf algebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§3.5 and 10.20.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §8.
* The Tau Ceti contributors, prior formalization of inner conjugation,
  [TauCeti#5490](https://github.com/TauCetiProject/TauCeti/pull/5490),
  commit `8419e7ceed8e87e7a14be030b7a0dda52aea2d41`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R]

namespace HopfAlgebra

variable (H : Type w) [Semiring H] [_root_.HopfAlgebra R H]

/-- Conjugation by the extension of an `R`-valued point, as an automorphism of `A`-valued points. -/
noncomputable def innerConjugationPointIso
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) :
    (HopfAlgebra.pointsFunctor (R := R) (H := H)).obj A ≅
      (HopfAlgebra.pointsFunctor (R := R) (H := H)).obj A :=
  MulEquiv.toGrpIso (MulAut.conj (extendPoint H A g))

-- Isolate the definitional reduction through `MulEquiv.toGrpIso`; the public application
-- theorems below depend only on these bridges and the named `MulAut.conj` equations.
private theorem innerConjugationPointIso_hom_apply_def
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (innerConjugationPointIso H g A).hom x = MulAut.conj (extendPoint H A g) x :=
  (rfl)

private theorem innerConjugationPointIso_inv_apply_def
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (innerConjugationPointIso H g A).inv x = (MulAut.conj (extendPoint H A g)).symm x :=
  (rfl)

/-- Inner conjugation acts by `x ↦ g * x * g⁻¹` after extending `g` to the value algebra. -/
@[simp]
theorem innerConjugationPointIso_hom_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (innerConjugationPointIso H g A).hom x =
      extendPoint H A g * x * (extendPoint H A g)⁻¹ := by
  rw [innerConjugationPointIso_hom_apply_def, MulAut.conj_apply]

/-- The inverse inner-conjugation map is conjugation by the inverse of the extended point. -/
@[simp]
theorem innerConjugationPointIso_inv_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (innerConjugationPointIso H g A).inv x =
      (extendPoint H A g)⁻¹ * x * extendPoint H A g := by
  rw [innerConjugationPointIso_inv_apply_def, MulAut.conj_symm_apply]

/-- Conjugation by an `R`-valued point, naturally on the full functor of points. -/
noncomputable def innerConjugationPointNatIso
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    HopfAlgebra.pointsFunctor.{u, w, v} (R := R) (H := H) ≅
      HopfAlgebra.pointsFunctor.{u, w, v} (R := R) (H := H) :=
  NatIso.ofComponents (innerConjugationPointIso H g) fun {A B} f ↦ by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    let x' : HopfAlgebra.points (R := R) (H := H) A := x
    -- `NatIso.ofComponents` stores this naturality square through the categorical wrappers for
    -- `GrpCat`; expose its pointwise form so the named point-map laws apply.
    change (innerConjugationPointIso H g B).hom (HopfAlgebra.mapPoints (H := H) f x') =
      HopfAlgebra.mapPoints (H := H) f ((innerConjugationPointIso H g A).hom x')
    rw [innerConjugationPointIso_hom_apply, innerConjugationPointIso_hom_apply]
    rw [HopfAlgebra.mapPoints_mul, HopfAlgebra.mapPoints_mul, HopfAlgebra.mapPoints_inv,
      HopfAlgebra.mapPoints_extendPoint]

/-- The forward component of the natural inner-conjugation isomorphism acts by conjugation. -/
@[simp]
theorem innerConjugationPointNatIso_hom_app_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (innerConjugationPointNatIso H g).hom.app A x =
      extendPoint H A g * x * (extendPoint H A g)⁻¹ := by
  rw [innerConjugationPointNatIso, NatIso.ofComponents_hom_app _ _]
  exact innerConjugationPointIso_hom_apply H g A x

/-- The inverse component of the natural inner-conjugation isomorphism acts by conjugation by
the inverse extended point. -/
@[simp]
theorem innerConjugationPointNatIso_inv_app_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (innerConjugationPointNatIso H g).inv.app A x =
      (extendPoint H A g)⁻¹ * x * extendPoint H A g := by
  rw [innerConjugationPointNatIso, NatIso.ofComponents_inv_app _ _]
  exact innerConjugationPointIso_inv_apply H g A x

private theorem pointNatIso_ext
    {e₁ e₂ : HopfAlgebra.pointsFunctor.{u, w, v} (R := R) (H := H) ≅
      HopfAlgebra.pointsFunctor.{u, w, v} (R := R) (H := H)}
    (h : ∀ (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A),
      e₁.hom.app A x = e₂.hom.app A x) : e₁ = e₂ := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  exact h A

/-- Conjugation by the identity point is the identity automorphism of the functor of points. -/
@[simp]
theorem innerConjugationPointNatIso_one :
    innerConjugationPointNatIso H
        (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) =
      Iso.refl _ := by
  apply pointNatIso_ext
  intro A x
  rw [innerConjugationPointNatIso_hom_app_apply]
  simp only [map_one, inv_one, one_mul, mul_one]
  -- The component of the identity natural isomorphism is the identity `GrpCat` morphism.
  change x = (𝟙 (HopfAlgebra.points (R := R) (H := H) A)) x
  exact (GrpCat.id_apply _ x).symm

/-- Conjugation by a product is successive conjugation, first by the second point and then by the
first. -/
@[simp]
theorem innerConjugationPointNatIso_mul
    (g h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationPointNatIso H (g * h) =
      (innerConjugationPointNatIso H h).trans (innerConjugationPointNatIso H g) := by
  apply pointNatIso_ext
  intro A x
  rw [innerConjugationPointNatIso_hom_app_apply]
  -- After extensionality, this is the residual application rule for the composite `GrpCat`
  -- morphism stored by `Iso.trans`; the following rewrites use the public component equations.
  change extendPoint H A (g * h) * x * (extendPoint H A (g * h))⁻¹ =
    (innerConjugationPointNatIso H g).hom.app A
      ((innerConjugationPointNatIso H h).hom.app A x)
  rw [innerConjugationPointNatIso_hom_app_apply,
    innerConjugationPointNatIso_hom_app_apply]
  simp only [map_mul, mul_inv_rev, mul_assoc]

/-- Conjugation by an inverse point is inverse to conjugation by the original point. -/
@[simp]
theorem innerConjugationPointNatIso_inv
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationPointNatIso H g⁻¹ = (innerConjugationPointNatIso H g).symm := by
  apply pointNatIso_ext
  intro A x
  rw [innerConjugationPointNatIso_hom_app_apply, Iso.symm_hom,
    innerConjugationPointNatIso_inv_app_apply, map_inv, inv_inv]

end HopfAlgebra

end TauCeti
