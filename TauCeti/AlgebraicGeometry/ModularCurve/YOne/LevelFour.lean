/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.YOne.Basic

/-!
# Explicit presentation and smoothness of naive `Y₁(4)`

On an elliptic Tate normal form `Y² + AXY + BY = X³ + BX²` over an arbitrary commutative ring,
`4 • (0, 0) = 0` holds if and only if `A = 1`
(`WeierstrassCurve.tateNormalForm_projModelMulBy_four_eq_projModelZero_iff`), while `(0, 0)`,
`2 • (0, 0)` and `3 • (0, 0)` miss the zero section everywhere. Consequently the naive `Y₁(4)`
moduli scheme over `ℤ` (`UniversalTate.yOne 4`, representing the naive `[Γ₁(4)]` problem) is
isomorphic to `Spec ℤ[B, (B(1 - 16B))⁻¹]` (`UniversalTate.yOneFourIso`), and `EllObj.yOne B 4`
is smooth of relative dimension `1` over every base scheme `B` without any invertibility
assumption (`EllObj.smoothOfRelativeDimension_one_yOne_four_structureMap`). Where `4` (i.e. `2`) is
invertible on `B`, naive `[Γ₁(4)]` agrees with the Drinfeld moduli problem `[Γ₁(4)]`.

## Main definitions

* `TauCeti.AlgebraicGeometry.UniversalTate.yOneFourIso`: the isomorphism
  `UniversalTate.yOne 4 ≅ Spec ℤ[B, (B(1 - 16B))⁻¹]` identifying naive `Y₁(4)` over `ℤ`.

## Main results

* `TauCeti.AlgebraicGeometry.UniversalTate.exactOrderOpens_four`: the open exact-order locus for
  `N = 4` is the whole base, so naive `Y₁(4)` is a closed subscheme of `Spec ℤ[A, B][Δ⁻¹]`
  (`UniversalTate.isClosedImmersion_yOneι_four`) and affine (`UniversalTate.isAffine_yOne_four`).
* `TauCeti.AlgebraicGeometry.UniversalTate.yOneFourIso_hom_SpecMap` and
  `TauCeti.AlgebraicGeometry.UniversalTate.yOneFourIso_inv_yOneι`: `yOneFourIso` identifies
  `yOneι 4` with the spectrum of the specialization map `A = 1`.
* `TauCeti.AlgebraicGeometry.UniversalTate.smoothOfRelativeDimension_one_terminal_from_yOne_four`:
  naive `Y₁(4)` over `ℤ` is smooth of relative dimension `1` over `Spec ℤ`.
* `TauCeti.AlgebraicGeometry.EllObj.smoothOfRelativeDimension_one_yOne_four_structureMap`:
  naive `EllObj.yOne B 4` is smooth of relative dimension `1` over every base scheme `B`.

## References

* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237, Table 3 (`X₁(4)`).
* D. Loeffler, *Modular Curves*, lecture notes, §3.3.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry WeierstrassCurve MonObj

namespace TauCeti.AlgebraicGeometry

namespace UniversalTate

/-- On the universal Tate normal form, `(0, 0)`, `2 • (0, 0)` and `3 • (0, 0)` miss the zero
section at every point of the base, so `exactOrderOpens 4` is the whole base. -/
@[simp]
theorem exactOrderOpens_four : exactOrderOpens.{u} 4 = ⊤ := by
  rw [eq_top_iff]
  intro t _
  rw [mem_exactOrderOpens_iff]
  intro k hk0 hk4 heq
  rw [pointHom_pow_left] at heq
  have hzero : curveGeom.{u}.zero =
      WeierstrassCurve.UniversalTate.curveULift.projModelZero ≫
        (toEllipticCurveGeomIso WeierstrassCurve.UniversalTate.curveULift).inv := by
    simp [← zero_toEllipticCurveGeomIso_hom]
  rw [hzero, ← Category.assoc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at heq
  have heq' : (WeierstrassCurve.UniversalTate.point ≫
        WeierstrassCurve.UniversalTate.curveULift.projModelMulBy k) t =
      WeierstrassCurve.UniversalTate.curveULift.projModelZero t := by
    have h :=
      congrArg (toEllipticCurveGeomIso WeierstrassCurve.UniversalTate.curveULift.{u}).hom heq
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Iso.inv_hom_id] at h
    simpa using h
  interval_cases k <;> simp only [Nat.cast_one, Nat.cast_ofNat] at heq'
  · rw [projModelMulBy_one, Category.comp_id] at heq'
    exact WeierstrassCurve.UniversalTate.point_ne_projModelZero t heq'
  · exact WeierstrassCurve.UniversalTate.point_projModelMulBy_two_ne_projModelZero t heq'
  · exact WeierstrassCurve.UniversalTate.point_projModelMulBy_three_ne_projModelZero t heq'

/-- Over `ℤ`, the immersion from naive `Y₁(4)` into `Spec ℤ[A, B][Δ⁻¹]` is a closed
immersion: since `(0, 0)`, `2 • (0, 0)`, and `3 • (0, 0)` miss the zero section everywhere,
`yOne 4` is isomorphic over `Spec ℤ[A, B][Δ⁻¹]` to `torsionLocus 4`. -/
instance isClosedImmersion_yOneι_four : IsClosedImmersion (yOneι.{u} 4) := by
  have h₁ : ∃ f : yOne.{u} 4 ⟶ torsionLocus.{u} 4, f ≫ torsionLocusι 4 = yOneι 4 :=
    (exists_comp_torsionLocusι_eq_iff _ 4).mpr
      ((exists_comp_yOneι_eq_iff (yOneι.{u} 4) 4).mp ⟨𝟙 _, Category.id_comp _⟩).1
  have h₂ : ∃ g : torsionLocus.{u} 4 ⟶ yOne.{u} 4, g ≫ yOneι 4 = torsionLocusι 4 :=
    (exists_comp_yOneι_eq_iff (torsionLocusι.{u} 4) 4).mpr
      ⟨(exists_comp_torsionLocusι_eq_iff _ 4).mp ⟨𝟙 _, Category.id_comp _⟩, fun _ ↦ by simp⟩
  have : IsIso h₁.choose := ⟨h₂.choose,
    (cancel_mono (yOneι.{u} 4)).mp (by
      rw [Category.assoc, h₂.choose_spec, h₁.choose_spec, Category.id_comp]),
    (cancel_mono (torsionLocusι.{u} 4)).mp (by
      rw [Category.assoc, h₁.choose_spec, h₂.choose_spec, Category.id_comp])⟩
  rw [← h₁.choose_spec]
  infer_instance

/-- Naive `Y₁(4)` over `ℤ` is affine. -/
instance isAffine_yOne_four : IsAffine (yOne.{u} 4) :=
  isAffine_of_isAffineHom (yOneι.{u} 4)

-- Any morphism from an affine scheme `X` to `Spec ℤ[A, B][Δ⁻¹]` killing `4 • (0, 0)` factors
-- through `Spec ℤ[B, (B(1 - 16B))⁻¹]`.
private theorem exists_toSpec_of_isAffine {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of (ULift.{u} WeierstrassCurve.UniversalTate.Ring)))
    (hf : f ≫ (pointHom.{u} ^ 4).left = f ≫ curveGeom.zero) :
    ∃ hom : X ⟶ Spec (.of (ULift.{u} UniversalGammaOneFour.Ring)),
      hom ≫ Spec.map (CommRingCat.ofHom UniversalGammaOneFour.toUniversalTate.ulift) = f := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ f)
  have hN : Spec.map φ ≫ (pointHom.{u} ^ 4).left = Spec.map φ ≫ curveGeom.zero := by
    rw [hφ, Category.assoc, hf, Category.assoc]
  have ha₁ : φ.hom WeierstrassCurve.UniversalTate.curveULift.a₁ = 1 :=
    (specMap_comp_pointHom_pow_four_eq_zero_iff φ.hom).mp hN
  obtain ⟨hΔ', hφeq⟩ := WeierstrassCurve.UniversalTate.eq_liftULift φ.hom
  have hΔ : IsUnit (tateNormalForm 1 (φ.hom WeierstrassCurve.UniversalTate.curveULift.a₃)).Δ :=
    ha₁ ▸ hΔ'
  let ψ : CommRingCat.of (ULift.{u} UniversalGammaOneFour.Ring) ⟶ Γ(X, ⊤) :=
    CommRingCat.ofHom ((UniversalGammaOneFour.lift hΔ).comp ULift.ringEquiv.toRingHom)
  have hcomp : CommRingCat.ofHom UniversalGammaOneFour.toUniversalTate.ulift ≫ ψ = φ := by
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    rw [hφeq, WeierstrassCurve.UniversalTate.liftULift_congr hΔ' hΔ ha₁ rfl]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, RingHom.ulift_apply, ULift.ringEquiv,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ψ, CommRingCat.hom_ofHom,
      WeierstrassCurve.UniversalTate.liftULift_apply]
    exact RingHom.congr_fun (UniversalGammaOneFour.lift_comp_toUniversalTate hΔ) x.down
  refine ⟨X.isoSpec.hom ≫ Spec.map ψ, ?_⟩
  rw [Category.assoc, ← Spec.map_comp, hcomp, hφ, Iso.hom_inv_id_assoc]

private theorem exists_yOneFourToSpec :
    ∃ hom : yOne.{u} 4 ⟶ Spec (.of (ULift.{u} UniversalGammaOneFour.Ring)),
      hom ≫ Spec.map (CommRingCat.ofHom UniversalGammaOneFour.toUniversalTate.ulift) =
        yOneι.{u} 4 :=
  exists_toSpec_of_isAffine (yOneι.{u} 4)
    (((exists_comp_yOneι_eq_iff (yOneι.{u} 4) 4).mp ⟨𝟙 _, Category.id_comp _⟩).1)

private theorem exists_specToYOneFour :
    ∃ inv : Spec (.of (ULift.{u} UniversalGammaOneFour.Ring)) ⟶ yOne.{u} 4,
      inv ≫ yOneι 4 = Spec.map (CommRingCat.ofHom UniversalGammaOneFour.toUniversalTate.ulift) :=
  (exists_comp_yOneι_eq_iff _ 4).mpr
    ⟨(specMap_comp_pointHom_pow_four_eq_zero_iff _).mpr
        UniversalGammaOneFour.toUniversalTate_ulift_a₁,
      fun _ ↦ by simp⟩

/-- **Naive `Y₁(4)` over `ℤ` is `Spec ℤ[B, (B(1 - 16B))⁻¹]`** (agreeing with Drinfeld `Y₁(4)`
where `4` is invertible). -/
noncomputable def yOneFourIso :
    yOne.{u} 4 ≅ Spec (.of (ULift.{u} UniversalGammaOneFour.Ring)) where
  hom := exists_yOneFourToSpec.choose
  inv := exists_specToYOneFour.choose
  hom_inv_id := by
    refine (cancel_mono (yOneι.{u} 4)).mp ?_
    rw [Category.assoc, exists_specToYOneFour.choose_spec, exists_yOneFourToSpec.choose_spec,
      Category.id_comp]
  inv_hom_id := by
    obtain ⟨χ, hχ⟩ := Spec.map_surjective
      (exists_specToYOneFour.{u}.choose ≫ exists_yOneFourToSpec.choose)
    have hχj : Spec.map (CommRingCat.ofHom UniversalGammaOneFour.toUniversalTate.ulift ≫ χ) =
        Spec.map (CommRingCat.ofHom UniversalGammaOneFour.toUniversalTate.ulift) := by
      rw [Spec.map_comp, hχ, Category.assoc, exists_yOneFourToSpec.choose_spec,
        exists_specToYOneFour.choose_spec]
    have hχπ : χ.hom.comp UniversalGammaOneFour.toUniversalTate.ulift =
        UniversalGammaOneFour.toUniversalTate.ulift :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective hχj)
    have hparam : χ.hom (.up UniversalGammaOneFour.param) = .up UniversalGammaOneFour.param := by
      have h := RingHom.congr_fun hχπ WeierstrassCurve.UniversalTate.curveULift.a₃
      rwa [RingHom.comp_apply, UniversalGammaOneFour.toUniversalTate_ulift_a₃] at h
    have hχid : χ = 𝟙 _ := by
      refine CommRingCat.hom_ext ?_
      have h₀ : (ULift.ringEquiv.toRingHom.comp χ.hom).comp ULift.ringEquiv.symm.toRingHom =
          RingHom.id UniversalGammaOneFour.Ring := by
        ext
        exact congrArg ULift.down hparam
      ext x
      simpa [ULift.ringEquiv] using RingHom.congr_fun h₀ x.down
    rw [← hχ, hχid, Spec.map_id]

/-- Under `yOneFourIso.hom`, the specialization map `A = 1` recovers the closed immersion
`yOneι 4 : yOne 4 ⟶ Spec ℤ[A, B][Δ⁻¹]` of naive `Y₁(4)`. -/
@[reassoc (attr := simp)]
theorem yOneFourIso_hom_SpecMap :
    yOneFourIso.{u}.hom ≫
        Spec.map (CommRingCat.ofHom UniversalGammaOneFour.toUniversalTate.ulift) =
      yOneι.{u} 4 :=
  exists_yOneFourToSpec.choose_spec

/-- Under `yOneFourIso.inv`, the closed immersion `yOneι 4` is the spectrum of the specialization
map `A = 1`. -/
@[reassoc (attr := simp)]
theorem yOneFourIso_inv_yOneι :
    yOneFourIso.{u}.inv ≫ yOneι.{u} 4 =
      Spec.map (CommRingCat.ofHom UniversalGammaOneFour.toUniversalTate.ulift) :=
  exists_specToYOneFour.choose_spec

/-- Naive `Y₁(4)` over `ℤ` is smooth of relative dimension `1` over `Spec ℤ`. -/
instance smoothOfRelativeDimension_one_terminal_from_yOne_four :
    SmoothOfRelativeDimension 1 (terminal.from (yOne.{u} 4)) := by
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} 1) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [terminal.hom_ext (terminal.from (yOne.{u} 4))
    (yOneFourIso.{u}.hom ≫ terminal.from _)]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1)
    yOneFourIso.{u}.hom _).mpr inferInstance

end UniversalTate

namespace EllObj

/-- **Naive `Y₁(4)` is smooth of relative dimension `1` over every base scheme `B`** (and agrees
with Drinfeld `Y₁(4)` where `4` is invertible). -/
instance smoothOfRelativeDimension_one_yOne_four_structureMap (B : Scheme.{u}) :
    SmoothOfRelativeDimension 1 (yOne B 4).structureMap := by
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} 1) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hfst : SmoothOfRelativeDimension 1 (prod.fst : B ⨯ UniversalTate.yOne.{u} 4 ⟶ B) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasBinaryProduct' _ _).flip inferInstance
  rw [← yOneBaseIsoProd_hom_fst]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1)
    (yOneBaseIsoProd B 4).hom _).mpr hfst

end EllObj

end TauCeti.AlgebraicGeometry
