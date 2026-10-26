/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.Abel.PicZero
public import TauCeti.AlgebraicGeometry.PicardFunctor.PicZero.Fppf

/-!
# Abel–Jacobi maps into the degree-zero Picard fppf sheaf

For a smooth proper geometrically connected family of curves `f : X ⟶ S` with a section
`x₀`, the normalized Abel map sends a relative effective Cartier divisor `D` of degree `d` to
the degree-zero class `𝒪(D - d • x₀)`. Composing this map with fppf sheafification gives the
canonical map from the divisor functor to the degree-zero relative Picard fppf sheaf.

In degree one, the graph construction gives the Abel–Jacobi map from the functor of points of
`X`. It sends the base-changed section `x₀` to zero. These maps are stated before
representability; when the degree-zero Picard sheaf is represented, they are the functor-of-points
maps induced by the corresponding morphisms of schemes.

## Main declarations

* `TauCeti.AlgebraicGeometry.abelJacobiMapOfDegreeToPicZeroFppf`: the normalized degree-`d` Abel
  map into the degree-zero Picard fppf sheaf;
* `TauCeti.AlgebraicGeometry.abelJacobiMapToPicZeroFppf`: the Abel–Jacobi map from the functor of
  points of `X` into that sheaf;
* `TauCeti.AlgebraicGeometry.abelJacobiMapToPicZeroFppf_app_basePoint`: the base point maps to
  zero.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Sections 9.3 and 9.5.
* J. S. Milne, *Jacobian varieties*, in *Arithmetic Geometry* (G. Cornell, J. H. Silverman,
  eds.), Springer, 1986, Sections 2 and 5.
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] [SmoothOfRelativeDimension 1 f]
  [GeometricallyConnected f]
variable {x₀ : S ⟶ X} (hx₀ : x₀ ≫ f = 𝟙 S)

/-- **The normalized Abel map into the degree-zero Picard fppf sheaf.** A relative effective
Cartier divisor `D` of degree `d` is sent to the fppf-local class of
`𝒪(D - d • x₀)`. -/
def abelJacobiMapOfDegreeToPicZeroFppf (d : ℕ) :
    (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor ⋙ uliftFunctor.{u + 1} ⟶
      (relativePicardDegreeZeroFppfSheaf f).obj ⋙ forget AddCommGrpCat :=
  abelJacobiMapOfDegreeToPicZero f hx₀ d ≫
    (relativePicardDegreeZeroSubfunctorIsoFunctor f).hom ≫
    relativePicardDegreeZeroToFppfSheafOfMul f

/-- The degree-`d` Abel map into the degree-zero Picard fppf sheaf is the sheafification image of
its degree-zero Picard class. -/
@[simp]
lemma abelJacobiMapOfDegreeToPicZeroFppf_app_apply (d : ℕ) {T : (Over S)ᵒᵖ}
    (D : ((relativeEffectiveCartierDegreeSubfunctor f d).toFunctor ⋙
      uliftFunctor.{u + 1}).obj T) :
    ConcreteCategory.hom (C := Type (u + 1))
        (X := uliftFunctor.{u + 1}.obj
          ((relativeEffectiveCartierDegreeSubfunctor f d).obj T))
        (Y := ToType ((relativePicardDegreeZeroFppfSheaf f).obj.obj T))
        ((abelJacobiMapOfDegreeToPicZeroFppf f hx₀ d).app T) D =
      (relativePicardDegreeZeroToFppfSheaf f).app T
        (relativePicardDegreeZeroAddPresheafAddEquiv f T
          (Additive.ofMul (relativePicardDegreeZeroFunctor.mk f
            ((abelJacobiMapOfDegreeToPicZero f hx₀ d).app T D).1
            ((abelJacobiMapOfDegreeToPicZero f hx₀ d).app T D).2))) :=
  by
    rw [abelJacobiMapOfDegreeToPicZeroFppf]
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
    rw [relativePicardDegreeZeroSubfunctorIsoFunctor_hom_app,
      relativePicardDegreeZeroToFppfSheafOfMul_app_apply]

/-- **The Abel–Jacobi map into the degree-zero Picard fppf sheaf.** It sends an `S`-point
`x : T ⟶ X` to the fppf-local class of `𝒪(Γₓ - x₀,T)`. -/
def abelJacobiMapToPicZeroFppf :
    yoneda.obj (Over.mk f) ⋙ uliftFunctor.{u + 1} ⟶
      (relativePicardDegreeZeroFppfSheaf f).obj ⋙ forget AddCommGrpCat :=
  Functor.whiskerRight (graphDivisorDegreeOne f) uliftFunctor.{u + 1} ≫
    abelJacobiMapOfDegreeToPicZeroFppf f hx₀ 1

/-- The Abel–Jacobi map into the degree-zero Picard fppf sheaf is the existing degree-zero
Abel–Jacobi class followed by the comparison with the group-valued functor and sheafification. -/
theorem abelJacobiMapToPicZeroFppf_eq :
    abelJacobiMapToPicZeroFppf f hx₀ =
      abelJacobiMapToPicZero f hx₀ ≫
        (relativePicardDegreeZeroSubfunctorIsoFunctor f).hom ≫
        relativePicardDegreeZeroToFppfSheafOfMul f := by
  rw [abelJacobiMapToPicZeroFppf, abelJacobiMapOfDegreeToPicZeroFppf,
    abelJacobiMapToPicZero_eq, Category.assoc]

/-- The value of the Abel–Jacobi map in the degree-zero Picard fppf sheaf is the sheafification
image of its existing degree-zero Picard class. -/
@[simp]
lemma abelJacobiMapToPicZeroFppf_app_apply {T : (Over S)ᵒᵖ}
    (x : (yoneda.obj (Over.mk f) ⋙ uliftFunctor.{u + 1}).obj T) :
    ConcreteCategory.hom (C := Type (u + 1))
        (X := uliftFunctor.{u + 1}.obj (T.unop ⟶ Over.mk f))
        (Y := ToType ((relativePicardDegreeZeroFppfSheaf f).obj.obj T))
        ((abelJacobiMapToPicZeroFppf f hx₀).app T) x =
      (relativePicardDegreeZeroToFppfSheaf f).app T
        (relativePicardDegreeZeroAddPresheafAddEquiv f T
          (Additive.ofMul (relativePicardDegreeZeroFunctor.mk f
            ((abelJacobiMapToPicZero f hx₀).app T x).1
            ((abelJacobiMapToPicZero f hx₀).app T x).2))) := by
  rw [abelJacobiMapToPicZeroFppf_eq]
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  rw [relativePicardDegreeZeroSubfunctorIsoFunctor_hom_app,
    relativePicardDegreeZeroToFppfSheafOfMul_app_apply]

/-- **The Abel–Jacobi map into the degree-zero Picard fppf sheaf sends the base point to zero.** -/
@[simp]
theorem abelJacobiMapToPicZeroFppf_app_basePoint (T : (Over S)ᵒᵖ) :
    ConcreteCategory.hom (C := Type (u + 1))
      (X := uliftFunctor.{u + 1}.obj (T.unop ⟶ Over.mk f))
      (Y := ToType ((relativePicardDegreeZeroFppfSheaf f).obj.obj T))
      ((abelJacobiMapToPicZeroFppf f hx₀).app T)
      (ULift.up (basePoint hx₀ T.unop)) = 0 := by
  rw [abelJacobiMapToPicZeroFppf]
  -- Expose the value of the composite natural transformation at the base point.
  change (abelJacobiMapOfDegreeToPicZeroFppf f hx₀ 1).app T
    ((Functor.whiskerRight (graphDivisorDegreeOne f) uliftFunctor.{u + 1}).app T
      (ULift.up (basePoint hx₀ T.unop))) = 0
  rw [abelJacobiMapOfDegreeToPicZeroFppf_app_apply]
  have h : relativePicardDegreeZeroFunctor.mk f
      ((abelJacobiMapOfDegreeToPicZero f hx₀ 1).app T
        ((Functor.whiskerRight (graphDivisorDegreeOne f) uliftFunctor.{u + 1}).app T
          (ULift.up (basePoint hx₀ T.unop)))).1
      ((abelJacobiMapOfDegreeToPicZero f hx₀ 1).app T
        ((Functor.whiskerRight (graphDivisorDegreeOne f) uliftFunctor.{u + 1}).app T
          (ULift.up (basePoint hx₀ T.unop)))).2 = 1 := by
    apply relativePicardDegreeZeroFunctorι_app_injective f T
    rw [relativePicardDegreeZeroFunctorι_app_mk, map_one]
    have hcomp := ConcreteCategory.congr_hom (C := Type (u + 1))
      (NatTrans.congr_app (abelJacobiMapToPicZero_eq f hx₀) T)
      (ULift.up (basePoint hx₀ T.unop) :
        (yoneda.obj (Over.mk f) ⋙ uliftFunctor.{u + 1}).obj T)
    calc
      ((abelJacobiMapOfDegreeToPicZero f hx₀ 1).app T
          ((Functor.whiskerRight (graphDivisorDegreeOne f) uliftFunctor.{u + 1}).app T
            (ULift.up (basePoint hx₀ T.unop)))).1 =
          ((abelJacobiMapToPicZero f hx₀).app T
            (ULift.up (basePoint hx₀ T.unop))).1 := (congrArg Subtype.val hcomp).symm
      _ = 1 := abelJacobiMapToPicZero_app_basePoint_val f hx₀ T
  rw [h, ofMul_one, map_zero, map_zero]
  rfl

end

end TauCeti.AlgebraicGeometry
