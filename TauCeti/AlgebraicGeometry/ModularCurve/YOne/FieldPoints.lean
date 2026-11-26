/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.YOne.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TateNormalForm

/-!
# The points of `Y₁(N)` with values in a field

Let `F` be a field and `N ≥ 1`. The modular curve `Y₁(N)` is cut out of the base
`Spec ℤ[A, B][Δ⁻¹]` of the universal Tate normal form `Y² + AXY + BY = X³ + BX²` by the conditions
that `N • (0, 0)` is the zero section and that no `k • (0, 0)`, `0 < k < N`, meets it
(`TauCeti.AlgebraicGeometry.UniversalTate.yOne`). This file reads these scheme-theoretic conditions
at the `F`-points: a morphism `Spec F ⟶ Y₁(N)` is the same as a pair `(a, b)` of elements of `F` for
which the Tate normal form `Y² + aXY + bY = X³ + bX²` is an elliptic curve on which `(0, 0)` has
exact order `N` (`TauCeti.AlgebraicGeometry.UniversalTate.yOnePointsEquiv`). The pair is the image
of `(A, B)` under the ring homomorphism `ℤ[A, B][Δ⁻¹] →+* F` of the composite
`Spec F ⟶ Y₁(N) ⟶ Spec ℤ[A, B][Δ⁻¹]`.

Base changing the universal Tate normal form along `Spec F ⟶ Spec ℤ[A, B][Δ⁻¹]` gives the elliptic
curve over `Spec F` of the Tate normal form with coefficients `(a, b)`, with the point `(0, 0)`.
Over a field, the scheme-theoretic multiple `n • (0, 0)` is the zero section exactly when it
meets it at the one point of `Spec F`, and exactly when `n • (0, 0) = 0` in the group of points of
the Weierstrass curve (`WeierstrassCurve.toEllipticCurveGeomPointsMulEquiv`).

Together with the classification of pointed curves by their Tate normal forms
(`TauCeti.PointedWeierstrassCurve.exactOrderQuotientEquivTateNormalForm`), this identifies, for
`N ≥ 4`, the `F`-points of `Y₁(N)` with the isomorphism classes of elliptic curves over `F` with a
point of exact order `N`.

## Main definitions

* `TauCeti.AlgebraicGeometry.UniversalTate.yOnePointsEquiv F N`: for `N ≥ 1`, the bijection from
  the morphisms `Spec F ⟶ Y₁(N)` to the pairs `(a, b)` whose Tate normal form is elliptic with
  `(0, 0)` of exact order `N`.

## Main results

* `TauCeti.AlgebraicGeometry.UniversalTate.exists_comp_yOneι_eq_SpecMap_iff`: a morphism
  `Spec F ⟶ Spec ℤ[A, B][Δ⁻¹]` factors through `Y₁(N)` exactly when the images of `A` and `B` are
  the coefficients of an elliptic Tate normal form on which `(0, 0)` has exact order `N`.
* `TauCeti.AlgebraicGeometry.UniversalTate.coe_yOnePointsEquiv_apply`,
  `TauCeti.AlgebraicGeometry.UniversalTate.yOnePointsEquiv_symm_comp_yOneι`: the bijection reads off
  the images of `A` and `B`, and the inverse of `(a, b)` lies over the classifying homomorphism
  `A ↦ a`, `B ↦ b`.

## References

* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237.
* D. Loeffler, *Modular curves*, lecture notes, §3.3.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj TauCeti.AlgebraicGeometry
  WeierstrassCurve WeierstrassCurve.UniversalTate

namespace TauCeti.AlgebraicGeometry.UniversalTate

variable {F : Type u} [Field F] [DecidableEq F]

-- Read exact order on the pulled-back universal section through the existing naive-order API.
private theorem exists_comp_yOneι_eq_SpecMap_iff_addOrderOf
    (φ : ULift.{u} UniversalTate.Ring →+* F) {W : WeierstrassCurve F} (hW : curveULift.map φ = W)
    (h : W.toAffine.Nonsingular 0 0) (N : ℕ) [NeZero N] :
    (∃ f : Spec (.of F) ⟶ yOne.{u} N, f ≫ yOneι N = Spec.map (CommRingCat.ofHom φ)) ↔
      addOrderOf (Affine.Point.some 0 0 h) = N := by
  subst hW
  let P := (curveULift.map φ).toEllipticCurveGeomPointsMulEquiv.symm (.ofAdd (.some 0 0 h))
  have hg := isPullback_toEllipticCurveGeomIso_hom_projModelBaseChange curveULift φ
  have h₀ := zero_toEllipticCurveGeomIso_hom_projModelBaseChange curveULift φ
  have hP : P.left ≫ ((toEllipticCurveGeomIso (curveULift.map φ)).hom ≫
      curveULift.projModelBaseChange φ ≫ (toEllipticCurveGeomIso curveULift).inv) =
      Spec.map (CommRingCat.ofHom φ) ≫ pointHom.left := by
    have key : ((curveULift.map φ).projModelPointsEquiv.symm (.some 0 0 h)).val ≫
        curveULift.projModelBaseChange φ = Spec.map (CommRingCat.ofHom φ) ≫ point := by
      rw [projModelPointsEquiv_symm_some_projModelBaseChange, point_def,
        SpecMap_projModelAffinePoint]
      simp only [map_zero]
    simp [P, reassoc_of% key]
  have hnaive : (curveULift.map φ).toEllipticCurveGeom.IsOfNaiveExactOrder P N ↔
      P ^ N = 1 ∧ ∀ k : ℕ, 0 < k → k < N →
        ∀ s, (P ^ k).left s ≠ (curveULift.map φ).toEllipticCurveGeom.zero s := by
    rw [EllipticCurveGeom.isOfNaiveExactOrder_iff_forall_lt]
    simp only [EllipticCurveGeom.isEmpty_equalizer_one_iff]
  rw [EllipticCurveGeom.exists_comp_yOneι_eq_iff_of_isPullback hg h₀ hP N, ← hnaive,
    EllipticCurveGeom.isOfNaiveExactOrder_iff_orderOf_eq]
  have hord : orderOf P = addOrderOf (Affine.Point.some 0 0 h) :=
    (curveULift.map φ).toEllipticCurveGeomPointsMulEquiv.symm.orderOf_eq _
  exact hord ▸ Iff.rfl

/-- **The `F`-points of `Y₁(N)`.** For a field `F` and `N ≥ 1`, the morphism
`Spec φ : Spec F ⟶ Spec ℤ[A, B][Δ⁻¹]` of a ring homomorphism `φ` factors through `Y₁(N)` exactly
when the images `a = φ(A)` and `b = φ(B)` are the coefficients of a Tate normal form
`Y² + aXY + bY = X³ + bX²` which is elliptic and on which `(0, 0)` has exact order `N`. -/
theorem exists_comp_yOneι_eq_SpecMap_iff (φ : ULift.{u} UniversalTate.Ring →+* F) (N : ℕ)
    [NeZero N] :
    (∃ f : Spec (.of F) ⟶ yOne.{u} N, f ≫ yOneι N = Spec.map (CommRingCat.ofHom φ)) ↔
      (φ curveULift.a₁, φ curveULift.a₃) ∈
        PointedWeierstrassCurve.tateNormalFormExactOrder F N := by
  have hb : φ curveULift.a₃ ≠ 0 := (isUnit_of_isUnit_tateNormalForm_Δ (a := φ curveULift.a₁)
    (by simpa using (curveULift.map φ).isUnit_Δ)).ne_zero
  have hW : (WeierstrassCurve.tateNormalForm (φ curveULift.a₁) (φ curveULift.a₃)).IsElliptic := by
    rw [← map_curveULift]
    infer_instance
  rw [exists_comp_yOneι_eq_SpecMap_iff_addOrderOf φ (map_curveULift φ)
    (nonsingular_tateNormalForm_zero (φ curveULift.a₁) hb) N]
  simp only [PointedWeierstrassCurve.mem_tateNormalFormExactOrder_iff,
    PointedWeierstrassCurve.tateNormalForm_def, PointedWeierstrassCurve.mem_exactOrder_iff]
  constructor
  · intro hn
    exact ⟨hb, hW, hn⟩
  · rintro ⟨_, _, hn⟩
    exact hn

variable {N : ℕ} [NeZero N]

-- The coefficients `(a, b)` of an `F`-point `f` of `Y₁(N)`: the images of `A` and `B` under the
-- ring homomorphism of `f ≫ yOneι N`.
private noncomputable def yOnePointsFun (f : Spec (.of F) ⟶ yOne.{u} N) :
    PointedWeierstrassCurve.tateNormalFormExactOrder F N :=
  ⟨((Spec.preimage (f ≫ yOneι N)).hom curveULift.a₁,
      (Spec.preimage (f ≫ yOneι N)).hom curveULift.a₃),
    (exists_comp_yOneι_eq_SpecMap_iff _ N).mp ⟨f, by simp⟩⟩

-- Equal coefficients give equal ring homomorphisms, and `yOneι N` is a monomorphism.
private theorem yOnePointsFun_injective :
    Function.Injective (yOnePointsFun (F := F) (N := N)) := by
  intro f f' h
  simp only [yOnePointsFun, Subtype.mk.injEq, Prod.mk.injEq] at h
  have := ringHom_ext_uLift h.1 h.2
  rwa [← CommRingCat.hom_ext_iff, Spec.preimage_inj, cancel_mono] at this

-- Retain the classifying factorization when choosing the inverse point.
private theorem exists_yOnePointsFun_preimage
    (p : PointedWeierstrassCurve.tateNormalFormExactOrder F N) :
    ∃ f : Spec (.of F) ⟶ yOne.{u} N, f ≫ yOneι N =
      Spec.map (CommRingCat.ofHom (liftULift
        (PointedWeierstrassCurve.isUnit_Δ_of_mem_tateNormalFormExactOrder p.property))) := by
  apply (exists_comp_yOneι_eq_SpecMap_iff _ N).mpr
  simp

-- The chosen factorization has the prescribed coefficients.
private theorem yOnePointsFun_choose_preimage
    (p : PointedWeierstrassCurve.tateNormalFormExactOrder F N) :
    yOnePointsFun (exists_yOnePointsFun_preimage p).choose = p := by
  apply Subtype.ext
  simp [yOnePointsFun, (exists_yOnePointsFun_preimage p).choose_spec]

variable (F N) in
/-- **The `F`-points of `Y₁(N)` are the Tate normal forms of level `N`.** For a field `F` and
`N ≥ 1`, a morphism `Spec F ⟶ Y₁(N)` is the same as a pair `(a, b)` for which the Tate normal form
`Y² + aXY + bY = X³ + bX²` is elliptic and `(0, 0)` has exact order `N`. The pair is the image of
`(A, B)` under the ring homomorphism of `Spec F ⟶ Y₁(N) ⟶ Spec ℤ[A, B][Δ⁻¹]`
(`coe_yOnePointsEquiv_apply`). -/
noncomputable def yOnePointsEquiv :
    (Spec (.of F) ⟶ yOne.{u} N) ≃ PointedWeierstrassCurve.tateNormalFormExactOrder F N :=
  { toFun := yOnePointsFun
    invFun := fun p ↦ (exists_yOnePointsFun_preimage p).choose
    left_inv := fun _ ↦ yOnePointsFun_injective (yOnePointsFun_choose_preimage _)
    right_inv := yOnePointsFun_choose_preimage }

/-- The pair `(a, b)` of an `F`-point `f` of `Y₁(N)` is the image of `(A, B)` under the ring
homomorphism `ℤ[A, B][Δ⁻¹] →+* F` of `f ≫ yOneι N : Spec F ⟶ Spec ℤ[A, B][Δ⁻¹]`. -/
@[simp]
theorem coe_yOnePointsEquiv_apply (f : Spec (.of F) ⟶ yOne.{u} N) :
    (yOnePointsEquiv F N f : F × F) = ((Spec.preimage (f ≫ yOneι N)).hom curveULift.a₁,
      (Spec.preimage (f ≫ yOneι N)).hom curveULift.a₃) :=
  (rfl)

/-- The `F`-point of `Y₁(N)` with coefficients `(a, b)` lies over the point of
`Spec ℤ[A, B][Δ⁻¹]` of the classifying homomorphism `A ↦ a`, `B ↦ b`. -/
theorem yOnePointsEquiv_symm_comp_yOneι
    (p : PointedWeierstrassCurve.tateNormalFormExactOrder F N) :
    (yOnePointsEquiv F N).symm p ≫ yOneι N = Spec.map (CommRingCat.ofHom (liftULift
      (PointedWeierstrassCurve.isUnit_Δ_of_mem_tateNormalFormExactOrder p.property))) :=
  (exists_yOnePointsFun_preimage p).choose_spec

end TauCeti.AlgebraicGeometry.UniversalTate
