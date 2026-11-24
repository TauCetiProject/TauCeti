/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.YOne.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TateNormalForm
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FieldPoints

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

-- Along `Spec φ`, for `φ : ℤ[A, B][Δ⁻¹] →+* F`, the multiple `n • (0, 0)` of the universal point is
-- the zero section, or meets it at a point of `Spec F`, exactly when `n • (0, 0) = 0` on the Tate
-- normal form `W` with coefficients `φ A` and `φ B`.
private theorem pointHom_pow_left_eq_zero_iff (φ : ULift.{u} UniversalTate.Ring →+* F)
    {W : WeierstrassCurve F} (hW : curveULift.map φ = W) (h : W.toAffine.Nonsingular 0 0)
    (n : ℕ) :
    (Spec.map (CommRingCat.ofHom φ) ≫ (pointHom ^ n).left =
        Spec.map (CommRingCat.ofHom φ) ≫ curveGeom.zero ↔ n • Affine.Point.some 0 0 h = 0) ∧
      ∀ s, ((pointHom ^ n).left (Spec.map (CommRingCat.ofHom φ) s) =
        curveGeom.zero (Spec.map (CommRingCat.ofHom φ) s) ↔ n • Affine.Point.some 0 0 h = 0) := by
  subst hW
  -- the point `(0, 0)` of the elliptic curve of `W` over `Spec F`, which is the pullback of the
  -- universal Tate normal form along `Spec φ`
  let P := (curveULift.map φ).toEllipticCurveGeomPointsMulEquiv.symm (.ofAdd (.some 0 0 h))
  have hg := isPullback_toEllipticCurveGeomIso_hom_projModelBaseChange curveULift φ
  have h₀ := zero_toEllipticCurveGeomIso_hom_projModelBaseChange curveULift φ
  have hP : P.left ≫ ((toEllipticCurveGeomIso (curveULift.map φ)).hom ≫
      curveULift.projModelBaseChange φ ≫ (toEllipticCurveGeomIso curveULift).inv) =
      Spec.map (CommRingCat.ofHom φ) ≫ pointHom.left := by
    have key : ((curveULift.map φ).projModelPointsEquiv.symm (.some 0 0 h)).val ≫
        curveULift.projModelBaseChange φ = Spec.map (CommRingCat.ofHom φ) ≫ point := by
      rw [projModelPointsEquiv_symm_some_projModelBaseChange, point_def,
        ← projModelAffinePoint_projModelBaseChange, projModelAffinePoint_def,
        projModelPoint_projModelBaseChange]
      refine (projModelPoint_eq_projModelPoint_iff_of_apply_eq ?_).mpr
        ⟨(RingHom.id_comp φ).symm, ?_⟩
      · rfl
      · simp
    simp [P, reassoc_of% key]
  have hPn : P ^ n = 1 ↔ n • Affine.Point.some 0 0 h = 0 := by
    rw [← map_pow, MulEquiv.map_eq_one_iff, ← ofAdd_nsmul, ofAdd_eq_one]
  refine ⟨(EllipticCurveGeom.pow_eq_one_iff_of_isPullback hg h₀ hP n).symm.trans hPn,
    fun s ↦ ?_⟩
  rw [← EllipticCurveGeom.pow_left_apply_eq_zero_iff_of_isPullback hg h₀ hP n s,
    ← EllipticCurveGeom.eq_one_iff_left_apply_eq_zero, hPn]

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
  have hP := pointHom_pow_left_eq_zero_iff φ (map_curveULift φ)
    (nonsingular_tateNormalForm_zero (φ curveULift.a₁) hb)
  simp only [exists_comp_yOneι_eq_iff, mem_exactOrderOpens_iff, ne_eq, (hP _).1, (hP _).2,
    forall_const, PointedWeierstrassCurve.mem_tateNormalFormExactOrder_iff,
    PointedWeierstrassCurve.tateNormalForm_def, PointedWeierstrassCurve.mem_exactOrder_iff]
  refine ⟨fun h ↦ ⟨hb, hW, ?_⟩, fun ⟨_, _, h⟩ ↦ ?_⟩
  · exact (addOrderOf_eq_iff (NeZero.pos N)).mpr ⟨h.1, fun k hk hk₀ ↦ h.2 k hk₀ hk⟩
  · obtain ⟨hN, hk⟩ := (addOrderOf_eq_iff (NeZero.pos N)).mp h
    exact ⟨hN, fun k hk₀ hkN ↦ hk k hkN hk₀⟩

-- The classifying homomorphism of the Tate normal form with coefficients `(a, b)`, read on
-- `ULift.{u} ℤ[A, B][Δ⁻¹]`, sends `A` to `a` and `B` to `b`.
omit [DecidableEq F] in
private theorem lift_comp_ringEquiv_apply {a b : F} (hΔ : IsUnit (tateNormalForm a b).Δ) :
    ((lift hΔ).comp (ULift.ringEquiv : ULift.{u} UniversalTate.Ring ≃+* _).toRingHom
      curveULift.a₁, (lift hΔ).comp (ULift.ringEquiv : ULift.{u} UniversalTate.Ring ≃+* _).toRingHom
      curveULift.a₃) = (a, b) := by
  simp [ULift.ringEquiv]

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

-- The classifying homomorphism of `(a, b)` factors through `Y₁(N)`.
private theorem yOnePointsFun_surjective :
    Function.Surjective (yOnePointsFun (F := F) (N := N)) := by
  intro p
  obtain ⟨hb, hX⟩ := PointedWeierstrassCurve.mem_tateNormalFormExactOrder_iff.mp p.property
  have hΔ : IsUnit (tateNormalForm p.val.1 p.val.2).Δ := by
    simpa using ((PointedWeierstrassCurve.mem_exactOrder_iff _).mp hX).1.isUnit
  have hφ : _ = p.val := lift_comp_ringEquiv_apply hΔ
  obtain ⟨f, hf⟩ := (exists_comp_yOneι_eq_SpecMap_iff _ N).mpr (hφ ▸ p.property)
  refine ⟨f, Subtype.ext ?_⟩
  simpa only [yOnePointsFun, hf, Spec.preimage_map, CommRingCat.hom_ofHom] using hφ

variable (F N) in
/-- **The `F`-points of `Y₁(N)` are the Tate normal forms of level `N`.** For a field `F` and
`N ≥ 1`, a morphism `Spec F ⟶ Y₁(N)` is the same as a pair `(a, b)` for which the Tate normal form
`Y² + aXY + bY = X³ + bX²` is elliptic and `(0, 0)` has exact order `N`. The pair is the image of
`(A, B)` under the ring homomorphism of `Spec F ⟶ Y₁(N) ⟶ Spec ℤ[A, B][Δ⁻¹]`
(`coe_yOnePointsEquiv_apply`). -/
noncomputable def yOnePointsEquiv :
    (Spec (.of F) ⟶ yOne.{u} N) ≃ PointedWeierstrassCurve.tateNormalFormExactOrder F N :=
  Equiv.ofBijective yOnePointsFun ⟨yOnePointsFun_injective, yOnePointsFun_surjective⟩

/-- The pair `(a, b)` of an `F`-point `f` of `Y₁(N)` is the image of `(A, B)` under the ring
homomorphism `ℤ[A, B][Δ⁻¹] →+* F` of `f ≫ yOneι N : Spec F ⟶ Spec ℤ[A, B][Δ⁻¹]`. -/
@[simp]
theorem coe_yOnePointsEquiv_apply (f : Spec (.of F) ⟶ yOne.{u} N) :
    (yOnePointsEquiv F N f : F × F) = ((Spec.preimage (f ≫ yOneι N)).hom curveULift.a₁,
      (Spec.preimage (f ≫ yOneι N)).hom curveULift.a₃) :=
  (rfl)

/-- The `F`-point of `Y₁(N)` with coefficients `(a, b)` lies over the point of
`Spec ℤ[A, B][Δ⁻¹]` of the classifying homomorphism `A ↦ a`, `B ↦ b`. -/
theorem yOnePointsEquiv_symm_comp_yOneι (p : PointedWeierstrassCurve.tateNormalFormExactOrder F N)
    (hΔ : IsUnit (tateNormalForm p.val.1 p.val.2).Δ) :
    (yOnePointsEquiv F N).symm p ≫ yOneι N = Spec.map (CommRingCat.ofHom
      ((lift hΔ).comp (ULift.ringEquiv : ULift.{u} UniversalTate.Ring ≃+* _).toRingHom)) := by
  have h := (congrArg Subtype.val ((yOnePointsEquiv F N).apply_symm_apply p)).trans
    (lift_comp_ringEquiv_apply hΔ).symm
  rw [coe_yOnePointsEquiv_apply, Prod.mk.injEq] at h
  rw [← Spec.map_preimage ((yOnePointsEquiv F N).symm p ≫ yOneι N)]
  congr 1
  ext1
  exact ringHom_ext_uLift h.1 h.2

end TauCeti.AlgebraicGeometry.UniversalTate
