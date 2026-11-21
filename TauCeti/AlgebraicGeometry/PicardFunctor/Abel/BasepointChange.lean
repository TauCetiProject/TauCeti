/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.Abel.Fppf

/-!
# Changing the Abel–Jacobi base point in the fppf sheaf

For two sections `x₀` and `x₁` of a family of smooth curves, normalization at `x₁` translates
normalization at `x₀` by the negative of the class of `x₁ - x₀`. This comparison holds on every
test scheme, both in the relative Picard presheaf and in its degree-zero fppf sheaf. For an
effective divisor of degree `d`, the translation is multiplied by `d`.

## Main declarations

* `TauCeti.AlgebraicGeometry.abelJacobiMapToPicZeroFppf_app_change_basePoint`: the comparison
  in the degree-zero fppf sheaf;
* `TauCeti.AlgebraicGeometry.abelJacobiMapOfDegreeToPicZeroFppf_app_change_basePoint`: the
  degree-`d` comparison in that sheaf.

## References

* J. S. Milne, *Jacobian varieties*, in *Arithmetic Geometry* (G. Cornell, J. H. Silverman,
  eds.), Springer, 1986, Sections 2 and 5.
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) {x₀ x₁ : S ⟶ X}
  (hx₀ : x₀ ≫ f = 𝟙 S) (hx₁ : x₁ ≫ f = 𝟙 S)

section Proper

variable [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]

/-- For an effective divisor of degree `d`, changing the Abel–Jacobi base point subtracts
`d` times the class of `x₁ - x₀` in the degree-zero Picard fppf sheaf. -/
theorem abelJacobiMapOfDegreeToPicZeroFppf_app_change_basePoint (d : ℕ)
    {T : (Over S)ᵒᵖ} (D : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj T) :
    ConcreteCategory.hom (C := Type (u + 1))
      (X := ULift.{u + 1} ((relativeEffectiveCartierDegreeSubfunctor f d).obj T))
      (Y := ToType ((relativePicardDegreeZeroFppfSheaf f).obj.obj T))
      ((abelJacobiMapOfDegreeToPicZeroFppf f hx₁ d).app T) (ULift.up D) =
      ConcreteCategory.hom (C := Type (u + 1))
        (X := ULift.{u + 1} ((relativeEffectiveCartierDegreeSubfunctor f d).obj T))
        (Y := ToType ((relativePicardDegreeZeroFppfSheaf f).obj.obj T))
        ((abelJacobiMapOfDegreeToPicZeroFppf f hx₀ d).app T) (ULift.up D) -
        d • ConcreteCategory.hom (C := Type (u + 1))
          (X := ULift.{u + 1} (T.unop ⟶ Over.mk f))
          (Y := ToType ((relativePicardDegreeZeroFppfSheaf f).obj.obj T))
          ((abelJacobiMapToPicZeroFppf f hx₀).app T)
          (ULift.up (basePoint hx₁ T.unop)) := by
  let c (z : (relativePicardDegreeZeroSubfunctor f).obj T) :=
    relativePicardDegreeZeroFunctor.mk f z.val z.property
  let ψ := ((relativePicardDegreeZeroToFppfSheaf f).app T).hom.comp
    (relativePicardDegreeZeroAddPresheafAddEquiv f T).toAddMonoidHom
  have h : c ((abelJacobiMapOfDegreeToPicZero f hx₁ d).app T (ULift.up D)) =
      c ((abelJacobiMapOfDegreeToPicZero f hx₀ d).app T (ULift.up D)) /
        c ((abelJacobiMapToPicZero f hx₀).app T
          (ULift.up (basePoint hx₁ T.unop))) ^ d := by
    apply relativePicardDegreeZeroFunctorι_app_injective f T
    simp only [c, map_div, map_pow, relativePicardDegreeZeroFunctorι_app_mk]
    calc
      _ = (abelJacobiMapOfDegree f hx₁ d).app T (ULift.up D) :=
        abelJacobiMapOfDegreeToPicZero_app_apply_val f hx₁ d (ULift.up D)
      _ = _ := abelJacobiMapOfDegree_app_change_basePoint f hx₀ hx₁ d D
      _ = _ := congrArg₂ (fun a b ↦ a / b ^ d)
        (abelJacobiMapOfDegreeToPicZero_app_apply_val f hx₀ d (ULift.up D)).symm
        (abelJacobiMapToPicZero_app_apply_val f hx₀
          (ULift.up (basePoint hx₁ T.unop))).symm
  simp only [abelJacobiMapOfDegreeToPicZeroFppf_app_apply,
    abelJacobiMapToPicZeroFppf_app_apply]
  have h' := congrArg (fun z ↦ ψ (Additive.ofMul z)) h
  rw [ofMul_div, ofMul_pow, map_sub, map_nsmul] at h'
  exact h'

/-- In the degree-zero Picard fppf sheaf, changing the Abel–Jacobi base point subtracts the
class of `x₁ - x₀`. -/
theorem abelJacobiMapToPicZeroFppf_app_change_basePoint {T : (Over S)ᵒᵖ}
    (x : T.unop ⟶ Over.mk f) :
    ConcreteCategory.hom (C := Type (u + 1))
        (X := ULift.{u + 1} (T.unop ⟶ Over.mk f))
        (Y := ToType ((relativePicardDegreeZeroFppfSheaf f).obj.obj T))
        ((abelJacobiMapToPicZeroFppf f hx₁).app T) (ULift.up x) =
      ConcreteCategory.hom (C := Type (u + 1))
        (X := ULift.{u + 1} (T.unop ⟶ Over.mk f))
        (Y := ToType ((relativePicardDegreeZeroFppfSheaf f).obj.obj T))
        ((abelJacobiMapToPicZeroFppf f hx₀).app T) (ULift.up x) -
        ConcreteCategory.hom (C := Type (u + 1))
        (X := ULift.{u + 1} (T.unop ⟶ Over.mk f))
        (Y := ToType ((relativePicardDegreeZeroFppfSheaf f).obj.obj T))
        ((abelJacobiMapToPicZeroFppf f hx₀).app T) (ULift.up (basePoint hx₁ T.unop)) := by
  have h := abelJacobiMapOfDegreeToPicZeroFppf_app_change_basePoint f hx₀ hx₁ 1
    ((graphDivisorDegreeOne f).app T x)
  have hcomp {z : S ⟶ X} (hz : z ≫ f = 𝟙 S) :
      (abelJacobiMapOfDegreeToPicZeroFppf f hz 1).app T
          (ULift.up ((graphDivisorDegreeOne f).app T x)) =
        (abelJacobiMapToPicZeroFppf f hz).app T (ULift.up x) :=
    ConcreteCategory.congr_hom (C := Type (u + 1))
      (NatTrans.congr_app
        (whiskerRight_graphDivisorDegreeOne_comp_abelJacobiMapOfDegreeToPicZeroFppf_one f hz) T)
      (ULift.up x : (yoneda.obj (Over.mk f) ⋙ uliftFunctor.{u + 1}).obj T)
  simpa only [one_nsmul, hcomp] using h

end Proper

end

end TauCeti.AlgebraicGeometry
