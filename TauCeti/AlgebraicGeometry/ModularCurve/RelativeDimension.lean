/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.YOne
import TauCeti.AlgebraicGeometry.ModularCurve.BaseChange
import TauCeti.AlgebraicGeometry.ModularCurve.Rigidifier.LevelThree
import TauCeti.AlgebraicGeometry.ModularCurve.Simultaneous.Projections
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.SourceDescent

/-!
# Smoothness of relative dimension one for fine modular curves

This file proves that every representable moduli problem over `Ell/B` whose relative-representing
morphisms are étale (and whose universal base is locally of finite presentation over `B`) has
base scheme smooth of relative dimension `1` over `B`
(`ModuliProblem.RelRepData.smoothOfRelativeDimension_one_of_representableBy`). In particular, for
`N ≥ 4` invertible on `B`, the fine modular curve `Y₁(N)` is smooth of relative dimension `1` over
`B` (`EllObj.smoothOfRelativeDimension_one_yOne_structureMap`).

The argument follows Katz and Mazur's rigidifier method:

1. **Explicit `Y₁(4)`** (`UniversalTate.yOneFourIso`): on the universal Tate normal form
   `Y² + AXY + BY = X³ + BX²`, the multiples `(0, 0)`, `2(0, 0)`, `3(0, 0)` already miss the zero
   section everywhere, so `Y₁(4)` is the closed `4`-torsion locus `4(0, 0) = 0`. By the doubling
   and four-torsion formulas on Tate normal form
   (`WeierstrassCurve.projModelAffinePoint_zero_projModelMulBy_four_eq_projModelZero_iff`), this
   locus is cut out scheme-theoretically by `A = 1`, where the discriminant becomes
   `B⁴(1 - 16B)`. Thus `UniversalTate.yOne 4` is isomorphic to
   `Spec ℤ[b, 1/(b(1 - 16b))]` (Kubert, Table 3), which is standard smooth of relative dimension
   `1` over `ℤ`. Identifying `(EllObj.yOne B N).base` with `B × UniversalTate.yOne N` over `B` for
   `N ≥ 4` (`EllObj.yOneBaseIso`) makes `(EllObj.yOne B 4).structureMap` smooth of relative
   dimension `1` over every base scheme `B`
   (`EllObj.smoothOfRelativeDimension_one_yOne_four_structureMap`).
2. **Comparison with a smooth rigidifier**
   (`ModuliProblem.RelRepData.smoothOfRelativeDimension_one_of_rigidifier`):
   if `𝒫` is represented by `U` and étale over `Ell/B`, and `𝒬` is an étale surjective rigidifier
   represented by `V` with `V.structureMap` smooth of relative dimension `1`, then the simultaneous
   problem `(𝒫, 𝒬)` is represented by `W = U_{𝒬_U}`, whose projections `a₁ : W ⟶ U` and
   `a₂ : W ⟶ V` are étale on bases with `a₁` surjective. Then
   `a₁.base ≫ U.structureMap = a₂.base ≫ V.structureMap` is smooth of relative dimension
   `0 + 1 = 1`, and source descent
   (`AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_surjective`) descends smoothness of
   relative dimension `1` along the étale surjection `a₁.base` to `U.structureMap`.
3. **Zariski cover of `B` by `B[1/2]` and `B[1/3]`**
   (`ModuliProblem.RelRepData.smoothOfRelativeDimension_one_of_representableBy`): any base scheme
   `B` is covered by the basic opens `D(2)` and `D(3)`, since `2` and `3` cannot both vanish in a
   residue field. Restricting `𝒫` along `D(2) ↪ B` and `D(3) ↪ B` via `ModuliProblem.baseChange`,
   we apply step 2 with `[Γ₁(4)]_naive` (represented by `EllObj.yOne D(2) 4`) on `D(2)` and with
   `[Γ(3)]_naive` (represented by `EllObj.universalLevelThree D(3)`, proved smooth of relative
   dimension `1` in `Rigidifier/LevelThree.lean`) on `D(3)`.

## Main definitions

* `WeierstrassCurve.UniversalTate.YOneFourRing`: the ring `ℤ[b, 1/(b(1 - 16b))]` classifying
  elliptic curves with a point of naive exact order `4`.
* `TauCeti.AlgebraicGeometry.UniversalTate.yOneFourIso`: the isomorphism
  `UniversalTate.yOne 4 ≅ Spec ℤ[b, 1/(b(1 - 16b))]`.
* `TauCeti.AlgebraicGeometry.EllObj.yOneIsoProdCurve` and
  `TauCeti.AlgebraicGeometry.EllObj.yOneBaseIso`: for `N ≥ 4`, the isomorphism
  `EllObj.yOne B N ≅ EllObj.prodCurve B (UniversalTate.yOneCurve N)` in `Ell/B` and the induced
  `B`-isomorphism `(EllObj.yOne B N).base ≅ B × UniversalTate.yOne N`.

## Main results

* `WeierstrassCurve.UniversalTate.isStandardSmoothOfRelativeDimension_one_yOneFourRing` and
  `EllObj.smoothOfRelativeDimension_one_yOne_four_structureMap`: `ℤ[b, 1/(b(1 - 16b))]` is standard
  smooth of relative dimension `1` over `ℤ`, and `EllObj.yOne B 4` is smooth of relative dimension
  `1` over `B`.
* `ModuliProblem.RelRepData.smoothOfRelativeDimension_one_of_representableBy`:
  every representable moduli problem over `Ell/B` which is étale over `Ell/B` and has universal
  base locally of finite presentation over `B` has universal base smooth of relative dimension `1`
  over `B`.
* `TauCeti.AlgebraicGeometry.EllObj.smoothOfRelativeDimension_one_yOne_structureMap`: for `N ≥ 4`
  invertible on `B`, `Y₁(N)` is smooth of relative dimension `1` over `B`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §§2.2, 4.3, and 4.7.
* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237, Table 3 (`Y₁(4)`).
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj

/-! ### The universal ring `ℤ[b, 1/(b(1 - 16b))]` of `Y₁(4)` -/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- At `a = 1`, the Tate normal form `Y² + XY + bY = X³ + bX²` has discriminant `b⁴(1 - 16b)`. -/
theorem tateNormalForm_one_Δ (b : R) : (tateNormalForm 1 b).Δ = b ^ 4 * (1 - 16 * b) := by
  rw [tateNormalForm_Δ]
  ring

/-- The Tate normal form `Y² + XY + bY = X³ + bX²` has unit discriminant if and only if
`b(1 - 16b)` is a unit. -/
theorem isUnit_tateNormalForm_one_Δ_iff {b : R} :
    IsUnit (tateNormalForm 1 b).Δ ↔ IsUnit (b * (1 - 16 * b)) := by
  rw [tateNormalForm_one_Δ, IsUnit.mul_iff, IsUnit.mul_iff, isUnit_pow_iff (by omega)]

namespace UniversalTate

/-- The polynomial ring `ℤ[b]` in one variable, parameterizing the `4`-torsion Tate normal form
`Y² + XY + bY = X³ + bX²`. -/
abbrev YOneFourPoly : Type :=
  MvPolynomial (Fin 1) ℤ

/-- The universal ring `ℤ[b, 1/(b(1 - 16b))]` of `Y₁(4)` (Kubert, Table 3): `ℤ[b]` localized away
from `b(1 - 16b)`. -/
abbrev YOneFourRing : Type :=
  Localization.Away (MvPolynomial.X 0 * (1 - 16 * MvPolynomial.X 0) : YOneFourPoly)

/-- The universal ring `ℤ[b, 1/(b(1 - 16b))]` of `Y₁(4)` is standard smooth of relative dimension
`1` over `ℤ`. -/
instance isStandardSmoothOfRelativeDimension_one_yOneFourRing :
    Algebra.IsStandardSmoothOfRelativeDimension 1 ℤ YOneFourRing := by
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 YOneFourPoly YOneFourRing :=
    .localization_away (MvPolynomial.X 0 * (1 - 16 * MvPolynomial.X 0) : YOneFourPoly)
  simpa using
    Algebra.IsStandardSmoothOfRelativeDimension.trans 1 0 ℤ YOneFourPoly YOneFourRing

/-- `Spec ℤ[b, 1/(b(1 - 16b))]` is smooth of relative dimension `1` over `Spec ℤ`, the terminal
scheme. -/
instance smoothOfRelativeDimension_one_terminal_from_yOneFour :
    SmoothOfRelativeDimension 1 (terminal.from (Spec (.of (ULift.{u} YOneFourRing)))) := by
  let f : ULift.{u} ℤ →+* ULift.{u} YOneFourRing :=
    ULift.ringEquiv.symm.toRingHom.comp ((algebraMap ℤ YOneFourRing).comp ULift.ringEquiv.toRingHom)
  have hf : f.IsStandardSmoothOfRelativeDimension 1 := by
    have h₁ := RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (ULift.ringEquiv : ULift.{u} YOneFourRing ≃+* YOneFourRing).symm
    have h₂ : (algebraMap ℤ YOneFourRing).IsStandardSmoothOfRelativeDimension 1 :=
      (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr inferInstance
    have h₃ := RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)
    dsimp only [f]
    simpa using h₁.comp (h₂.comp h₃)
  have : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom f)) :=
    HasRingHomProperty.Spec_iff.mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hf)
  have e := specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal
  rw [terminal.hom_ext (terminal.from _) (Spec.map (CommRingCat.ofHom f) ≫ e.hom)]
  have hcomp : SmoothOfRelativeDimension (1 + 0) (Spec.map (CommRingCat.ofHom f) ≫ e.hom) :=
    inferInstance
  simpa using hcomp

end UniversalTate

end WeierstrassCurve

/-! ### Explicit identification `Y₁(4) ≅ Spec ℤ[b, 1/(b(1 - 16b))]` -/

namespace TauCeti.AlgebraicGeometry.UniversalTate

open WeierstrassCurve WeierstrassCurve.UniversalTate

private theorem pointHom_pow_left_comp (n : ℕ) :
    (pointHom.{u} ^ n).left ≫ (toEllipticCurveGeomIso curveULift).hom =
      point.{u} ≫ curveULift.projModelMulBy n := by
  let x := pointHom.{u} ≫ (toEllipticCurveGeomOverIso curveULift).hom
  have hx : x.left = point.{u} := by simp [x]
  have h₂ := congrArg Over.Hom.left
    (GrpObj.zpow_comp pointHom.{u} (n : ℤ) (toEllipticCurveGeomOverIso curveULift).hom)
  rw [← zpow_natCast, ← toEllipticCurveGeomOverIso_hom_left, ← Over.comp_left, h₂,
    ← curveULift.comp_projModelMulBy, hx]

/-- On `Spec ℤ[A, B][Δ⁻¹]`, none of `(0, 0)`, `2(0, 0)`, `3(0, 0)` meets the zero section, so
`exactOrderOpens 4` is the whole base. -/
@[simp]
theorem exactOrderOpens_four : exactOrderOpens.{u} 4 = ⊤ := by
  refine eq_top_iff.mpr fun s _ ↦ ?_
  rw [mem_exactOrderOpens_iff]
  intro k hk0 hk4 hs
  have hs' : (point.{u} ≫ curveULift.projModelMulBy k) s = curveULift.projModelZero s := by
    rw [← pointHom_pow_left_comp, ← zero_toEllipticCurveGeomIso_hom,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hs]
  interval_cases k
  · have h1 := pointHom_pow_left_comp.{u} 1
    simp only [pow_one, pointHom_left, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Nat.cast_one] at h1
    rw [Nat.cast_one, ← h1] at hs'
    exact point_ne_projModelZero s hs'
  · exact point_projModelMulBy_two_ne_projModelZero s hs'
  · exact point_projModelMulBy_three_ne_projModelZero s hs'

/-- On the `4`-torsion locus of the universal Tate normal form, `yOneOpens 4` is the whole
scheme. -/
@[simp]
theorem yOneOpens_four : yOneOpens.{u} 4 = ⊤ := by
  ext z
  simp

/-- `Y₁(4)` is a closed subscheme of `Spec ℤ[A, B][Δ⁻¹]`. -/
instance isClosedImmersion_yOneι_four : IsClosedImmersion (yOneι.{u} 4) := by
  have : IsIso (yOneOpens.{u} 4).ι := by
    rw [yOneOpens_four, ← Scheme.topIso_hom]
    infer_instance
  rw [yOneι_def]
  infer_instance

/-- `Y₁(4)` over `Spec ℤ` is an affine scheme. -/
instance isAffine_yOne_four : IsAffine (yOne.{u} 4) :=
  isAffine_of_isAffineHom (yOneι.{u} 4)

private theorem projModelMulBy_projModelBaseChange {R : Type u} [CommRing R]
    (φ : ULift.{u} UniversalTate.Ring →+* R) (n : ℤ) :
    (curveULift.map φ).projModelMulBy n ≫ curveULift.projModelBaseChange φ =
      curveULift.projModelBaseChange φ ≫ curveULift.projModelMulBy n := by
  let W' : WeierstrassCurve R := curveULift.map φ
  have hsq := curveULift.isPullback_projModelBaseChange φ
  have hg : IsPullback ((toEllipticCurveGeomIso W').hom ≫ curveULift.projModelBaseChange φ)
      (toEllipticCurveGeom W').structureMap curveULift.projModelOver
      (Spec.map (CommRingCat.ofHom φ)) := by
    simpa using (IsPullback.of_horiz_isIso (fst := (toEllipticCurveGeomIso W').hom)
      (snd := (toEllipticCurveGeom W').structureMap) (f := W'.projModelOver) (g := 𝟙 _)
      ⟨by simp⟩).paste_horiz hsq
  have hg₀ : (toEllipticCurveGeom W').zero ≫
      ((toEllipticCurveGeomIso W').hom ≫ curveULift.projModelBaseChange φ) =
      Spec.map (CommRingCat.ofHom φ) ≫ curveULift.projModelZero := by
    rw [zero_toEllipticCurveGeomIso_hom_assoc, curveULift.projModelZero_projModelBaseChange]
  have h := curveULift.comp_projModelMulBy_of_isPullback hg hg₀ n
  rw [W'.projModelMulBy_eq, Category.assoc, Category.assoc, ← h]
  simp

-- A morphism `Spec φ : Spec R ⟶ Spec ℤ[A, B][Δ⁻¹]` factors through `Y₁(4)` iff `φ(A) = 1`.
private theorem exists_comp_yOneι_four_spec_iff {R : Type u} [CommRing R]
    (φ : ULift.{u} UniversalTate.Ring →+* R) :
    (∃ h : Spec (.of R) ⟶ yOne.{u} 4, h ≫ yOneι 4 = Spec.map (CommRingCat.ofHom φ)) ↔
      φ curveULift.a₁ = 1 := by
  rw [exists_comp_yOneι_eq_iff, exactOrderOpens_four]
  simp only [TopologicalSpace.Opens.mem_top, implies_true, and_true]
  rw [← cancel_mono (toEllipticCurveGeomIso curveULift).hom, Category.assoc, Category.assoc,
    pointHom_pow_left_comp, zero_toEllipticCurveGeomIso_hom]
  let W' : WeierstrassCurve R := curveULift.map φ
  let P' : Spec (.of R) ⟶ W'.projModel :=
    W'.projModelAffinePoint (equation_curveULift_zero.map φ)
  have hsq := curveULift.isPullback_projModelBaseChange φ
  have hlhs : (P' ≫ W'.projModelMulBy 4) ≫ curveULift.projModelBaseChange φ =
      Spec.map (CommRingCat.ofHom φ) ≫ point ≫ curveULift.projModelMulBy 4 := by
    rw [Category.assoc, projModelMulBy_projModelBaseChange φ 4, ← Category.assoc, point_def,
      projModelAffinePoint_projModelBaseChange, Category.assoc]
  have hrhs : W'.projModelZero ≫ curveULift.projModelBaseChange φ =
      Spec.map (CommRingCat.ofHom φ) ≫ curveULift.projModelZero :=
    curveULift.projModelZero_projModelBaseChange φ
  have heq : Spec.map (CommRingCat.ofHom φ) ≫ point ≫ curveULift.projModelMulBy 4 =
      Spec.map (CommRingCat.ofHom φ) ≫ curveULift.projModelZero ↔
      P' ≫ W'.projModelMulBy 4 = W'.projModelZero := by
    rw [← hlhs, ← hrhs]
    refine ⟨fun h ↦ hsq.hom_ext h (by dsimp only [P', W']; simp), fun h ↦ by rw [h]⟩
  rw [Nat.cast_ofNat, heq]
  dsimp only [P', W']
  have h0 : (curveULift.map φ).toAffine.Equation 0 0 := by
    rw [map_curveULift]
    exact equation_tateNormalForm_zero _ _
  have hP' : (curveULift.map φ).projModelAffinePoint (equation_curveULift_zero.map φ) =
      (curveULift.map φ).projModelAffinePoint h0 :=
    (projModelAffinePoint_inj _).mpr ⟨map_zero φ, map_zero φ⟩
  rw [hP']
  have key {W : WeierstrassCurve R} [W.IsElliptic] (a b : R) (hW : W = tateNormalForm a b)
      (h0 : W.toAffine.Equation 0 0) :
      W.projModelAffinePoint h0 ≫ W.projModelMulBy 4 = W.projModelZero ↔ a = 1 := by
    subst hW
    exact projModelAffinePoint_zero_projModelMulBy_four_eq_projModelZero_iff
  exact key (φ curveULift.a₁) (φ curveULift.a₃) (map_curveULift φ) h0

private noncomputable def toYOneFourRing : UniversalTate.Ring →+* YOneFourRing :=
  let b₀ : YOneFourRing := algebraMap YOneFourPoly YOneFourRing (MvPolynomial.X 0)
  have hb₀ : IsUnit (b₀ * (1 - 16 * b₀)) := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := YOneFourRing)
      (MvPolynomial.X 0 * (1 - 16 * MvPolynomial.X 0) : YOneFourPoly)
    rwa [map_mul, map_sub, map_one, map_mul, map_ofNat] at h
  UniversalTate.lift (isUnit_tateNormalForm_one_Δ_iff.mpr hb₀)

private noncomputable def toYOneFourRingULift :
    ULift.{u} UniversalTate.Ring →+* ULift.{u} YOneFourRing :=
  ULift.ringEquiv.symm.toRingHom.comp (toYOneFourRing.comp ULift.ringEquiv.toRingHom)

private theorem toYOneFourRingULift_a₁ : toYOneFourRingULift.{u} curveULift.a₁ = 1 := by
  ext
  simp [toYOneFourRingULift, toYOneFourRing, curve, polyCurve, ULift.ringEquiv]

private theorem toYOneFourRingULift_a₃ :
    toYOneFourRingULift.{u} curveULift.a₃ =
      .up (algebraMap YOneFourPoly YOneFourRing (MvPolynomial.X 0)) := by
  ext
  simp [toYOneFourRingULift, toYOneFourRing, curve, polyCurve, ULift.ringEquiv]

private noncomputable def fromSpecYOneFour : Spec (.of (ULift.{u} YOneFourRing)) ⟶ yOne.{u} 4 :=
  ((exists_comp_yOneι_four_spec_iff toYOneFourRingULift.{u}).mpr toYOneFourRingULift_a₁).choose

private theorem fromSpecYOneFour_yOneι :
    fromSpecYOneFour.{u} ≫ yOneι 4 = Spec.map (CommRingCat.ofHom toYOneFourRingULift) :=
  ((exists_comp_yOneι_four_spec_iff toYOneFourRingULift.{u}).mpr
    toYOneFourRingULift_a₁).choose_spec

private noncomputable def yOneFourCoordHom : ULift.{u} YOneFourRing →+* Γ(yOne.{u} 4, ⊤) :=
  let t := (yOne.{u} 4).isoSpec.inv ≫ yOneι 4
  let φ : ULift.{u} UniversalTate.Ring →+* Γ(yOne.{u} 4, ⊤) := (Spec.preimage t).hom
  have ha₁ : φ curveULift.a₁ = 1 :=
    (exists_comp_yOneι_four_spec_iff φ).mp ⟨(yOne.{u} 4).isoSpec.inv, (Spec.map_preimage t).symm⟩
  have hΔ : IsUnit (tateNormalForm 1 (φ curveULift.a₃)).Δ := by
    have hmap : curveULift.map φ = tateNormalForm 1 (φ curveULift.a₃) := by
      rw [map_curveULift, ha₁]
    rw [← hmap, map_Δ]
    exact curveULift.isUnit_Δ.map φ
  have hb : IsUnit (φ curveULift.a₃ * (1 - 16 * φ curveULift.a₃)) :=
    isUnit_tateNormalForm_one_Δ_iff.mp hΔ
  (IsLocalization.Away.lift (MvPolynomial.X 0 * (1 - 16 * MvPolynomial.X 0) : YOneFourPoly)
    (g := MvPolynomial.eval₂Hom (Int.castRingHom _) ![φ curveULift.a₃])
    (by simpa [map_ofNat] using hb)).comp ULift.ringEquiv.toRingHom

private theorem yOneFourCoordHom_comp_toYOneFourRingULift :
    yOneFourCoordHom.{u}.comp toYOneFourRingULift =
      (Spec.preimage ((yOne.{u} 4).isoSpec.inv ≫ yOneι 4)).hom := by
  let t := (yOne.{u} 4).isoSpec.inv ≫ yOneι 4
  let φ : ULift.{u} UniversalTate.Ring →+* Γ(yOne.{u} 4, ⊤) := (Spec.preimage t).hom
  have ha₁ : φ curveULift.a₁ = 1 :=
    (exists_comp_yOneι_four_spec_iff φ).mp ⟨(yOne.{u} 4).isoSpec.inv, (Spec.map_preimage t).symm⟩
  have hx₀ : (ULift.ringEquiv.symm : Ring ≃+* ULift.{u} Ring).toRingHom
      (algebraMap (MvPolynomial (Fin 2) ℤ) Ring (MvPolynomial.X 0)) = curveULift.a₁ := by
    simp [curve, polyCurve, ULift.ringEquiv]
  have hx₁ : (ULift.ringEquiv.symm : Ring ≃+* ULift.{u} Ring).toRingHom
      (algebraMap (MvPolynomial (Fin 2) ℤ) Ring (MvPolynomial.X 1)) = curveULift.a₃ := by
    simp [curve, polyCurve, ULift.ringEquiv]
  suffices (yOneFourCoordHom.{u}.comp toYOneFourRingULift).comp
      (ULift.ringEquiv.symm : Ring ≃+* ULift.{u} Ring).toRingHom =
      φ.comp (ULift.ringEquiv.symm : Ring ≃+* ULift.{u} Ring).toRingHom by
    ext ⟨x⟩
    exact congr($this x)
  ext
  · simp only [RingHom.comp_apply, hx₀, toYOneFourRingULift_a₁, map_one, ha₁]
  · simp only [RingHom.comp_apply, hx₁, toYOneFourRingULift_a₃]
    simp [yOneFourCoordHom, φ, t, ULift.ringEquiv]

private noncomputable def toSpecYOneFour :
    yOne.{u} 4 ⟶ Spec (.of (ULift.{u} YOneFourRing)) :=
  (yOne.{u} 4).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom yOneFourCoordHom)

private theorem toSpecYOneFour_comp :
    toSpecYOneFour.{u} ≫ Spec.map (CommRingCat.ofHom toYOneFourRingULift) = yOneι 4 := by
  have hmap : Spec.map (CommRingCat.ofHom yOneFourCoordHom.{u}) ≫
      Spec.map (CommRingCat.ofHom toYOneFourRingULift) =
        Spec.map (Spec.preimage ((yOne.{u} 4).isoSpec.inv ≫ yOneι 4)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, yOneFourCoordHom_comp_toYOneFourRingULift]
    rfl
  exact (Category.assoc _ _ _).trans <|
    (congrArg ((yOne.{u} 4).isoSpec.hom ≫ ·) (hmap.trans (Spec.map_preimage _))).trans <|
      Iso.hom_inv_id_assoc _ _

/-- **Explicit identification of `Y₁(4)`** (Kubert, Table 3): `Y₁(4)` is isomorphic to
`Spec ℤ[b, 1/(b(1 - 16b))]`, cut out of `Spec ℤ[A, B][Δ⁻¹]` by `A = 1`. -/
noncomputable def yOneFourIso : yOne.{u} 4 ≅ Spec (.of (ULift.{u} YOneFourRing)) where
  hom := toSpecYOneFour
  inv := fromSpecYOneFour
  hom_inv_id := (cancel_mono (yOneι.{u} 4)).mp <| by
    rw [Category.assoc, fromSpecYOneFour_yOneι, toSpecYOneFour_comp, Category.id_comp]
  inv_hom_id := by
    set g := fromSpecYOneFour.{u} ≫ toSpecYOneFour
    have hg : g ≫ Spec.map (CommRingCat.ofHom toYOneFourRingULift) =
        Spec.map (CommRingCat.ofHom toYOneFourRingULift) := by
      rw [Category.assoc, toSpecYOneFour_comp, fromSpecYOneFour_yOneι]
    have hpre := congrArg Spec.preimage hg
    rw [Spec.preimage_comp, Spec.preimage_map] at hpre
    have hb₀ : (Spec.preimage g).hom
        (.up (algebraMap YOneFourPoly YOneFourRing (MvPolynomial.X 0))) =
          .up (algebraMap YOneFourPoly YOneFourRing (MvPolynomial.X 0)) := by
      rw [← toYOneFourRingULift_a₃]
      exact congr(($hpre).hom curveULift.a₃)
    suffices Spec.preimage g = 𝟙 _ by
      rw [← Spec.map_preimage g, this, Spec.map_id]
    ext1
    suffices ((ULift.ringEquiv : ULift.{u} YOneFourRing ≃+* YOneFourRing).toRingHom.comp
        ((Spec.preimage g).hom.comp ULift.ringEquiv.symm.toRingHom)) = RingHom.id YOneFourRing by
      ext ⟨x⟩
      simpa [ULift.ringEquiv] using congr(($this) x)
    apply IsLocalization.ringHom_ext
      (.powers (MvPolynomial.X 0 * (1 - 16 * MvPolynomial.X 0) : YOneFourPoly))
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) (Fin.forall_fin_one.mpr ?_)
    simpa [ULift.ringEquiv] using congrArg ULift.down hb₀

/-- `Y₁(4)` over `Spec ℤ` is smooth of relative dimension `1` over the terminal scheme. -/
instance smoothOfRelativeDimension_one_terminal_from_yOne_four :
    SmoothOfRelativeDimension 1 (terminal.from (yOne.{u} 4)) := by
  rw [terminal.hom_ext (terminal.from (yOne.{u} 4)) (yOneFourIso.hom ≫ terminal.from _)]
  have hcomp : SmoothOfRelativeDimension (0 + 1) (yOneFourIso.{u}.hom ≫ terminal.from _) :=
    inferInstance
  simpa using hcomp

/-- The universal elliptic curve over `UniversalTate.yOne N`: the base change of the universal Tate
normal form along `UniversalTate.yOneι N`. -/
noncomputable abbrev yOneCurve (N : ℕ) : EllipticCurveGeom (yOne.{u} N) :=
  curveGeom.{u}.baseChange (yOneι.{u} N)

/-- The canonical cartesian morphism from `yOneCurve N` to `curveGeom` over `yOneι N`. -/
noncomputable def yOneCurveProj (N : ℕ) : (yOneCurve.{u} N).carrier ⟶ curveGeom.{u}.carrier :=
  (curveGeom.{u}.baseChangeIso (yOneι.{u} N)).hom ≫ pullback.fst _ _

theorem isPullback_yOneCurveProj (N : ℕ) :
    IsPullback (yOneCurveProj.{u} N) (yOneCurve N).structureMap curveGeom.structureMap (yOneι N) :=
  curveGeom.isPullback_baseChange (yOneι N)

@[reassoc]
theorem zero_yOneCurveProj (N : ℕ) :
    (yOneCurve.{u} N).zero ≫ yOneCurveProj N = yOneι N ≫ curveGeom.zero := by
  simp [yOneCurveProj]

/-- The universal point `(0, 0)` on `yOneCurve N`, pulled back from `curveGeom`. -/
noncomputable def yOneCurvePoint (N : ℕ) :
    𝟙_ (Over (yOne.{u} N)) ⟶ Over.mk (yOneCurve.{u} N).structureMap :=
  EllipticCurveGeom.pointsPullback (isPullback_yOneCurveProj N) (zero_yOneCurveProj N) pointHom

@[reassoc (attr := simp)]
theorem yOneCurvePoint_left_yOneCurveProj (N : ℕ) :
    (yOneCurvePoint.{u} N).left ≫ yOneCurveProj N = yOneι N ≫ pointHom.left :=
  EllipticCurveGeom.pointsPullback_left_comp _ _ _

/-- For `N ≥ 4`, the universal point `(0, 0)` on `yOneCurve N` has naive exact order `N`. -/
theorem isOfNaiveExactOrder_yOneCurvePoint {N : ℕ} (h4 : 4 ≤ N) :
    (yOneCurve.{u} N).IsOfNaiveExactOrder (yOneCurvePoint N) N := by
  have : NeZero N := ⟨by omega⟩
  have hex : yOneCurvePoint.{u} N ^ N = 1 ∧
      ∀ k : ℕ, 0 < k → k < N → ∀ s,
        (yOneCurvePoint.{u} N ^ k).left s ≠ (yOneCurve N).zero s :=
    ((yOneCurve.{u} N).exists_yOne_iff h4).mp
      ⟨𝟙 _, yOneCurveProj N,
        by simpa only [Category.id_comp] using isPullback_yOneCurveProj N,
        by simp only [Category.id_comp, zero_yOneCurveProj],
        by simp only [Category.id_comp, yOneCurvePoint_left_yOneCurveProj]⟩
  have hφ : (yOneCurve.{u} N).IsFiberwiseInjective
      ((zmodMonoidHomEquiv N _).symm ⟨yOneCurvePoint N, hex.1⟩) := by
    rw [EllipticCurveGeom.isFiberwiseInjective_zmod_iff,
      zmodMonoidHomEquiv_symm_apply_ofAdd_one]
    exact hex.2
  have h := EllipticCurveGeom.isFiberwiseInjective_iff_isOfNaiveExactOrder.mp hφ
  rwa [zmodMonoidHomEquiv_symm_apply_ofAdd_one] at h

end TauCeti.AlgebraicGeometry.UniversalTate

/-! ### Comparison `(EllObj.yOne B N).base ≅ B × UniversalTate.yOne N` and `Y₁(4)` over `B` -/

namespace TauCeti.AlgebraicGeometry.EllObj

private theorem existsUnique_hom_prodCurve_yOneCurve {B : Scheme.{u}} {N : ℕ} (h4 : 4 ≤ N)
    {X : EllObj B}
    {φ : Multiplicative (ZMod N) →* (𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap)}
    (hφ : X.curve.IsFiberwiseInjective φ) :
    ∃! k : X ⟶ prodCurve B (UniversalTate.yOneCurve.{u} N),
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
        (prodCurvePoint B (UniversalTate.yOneCurvePoint N)) = φ (.ofAdd 1) := by
  refine (homProdCurveEquiv X).existsUnique_congr_left.mpr ?_
  have hg₀ := UniversalTate.isPullback_yOneCurveProj.{u} N
  have h0₀ := UniversalTate.zero_yOneCurveProj.{u} N
  obtain ⟨⟨f, g⟩, ⟨hg, h₀, hgP⟩, huniq⟩ :=
    X.curve.existsUnique_yOne_of_isFiberwiseInjective h4 hφ
  dsimp only at hg h₀ hgP
  let g' := EllipticCurveGeom.baseChangeLift hg₀ hg.toCommSq (h := f) rfl
  have hg' : IsPullback g' X.curve.structureMap
      (UniversalTate.yOneCurve N).structureMap f :=
    EllipticCurveGeom.isPullback_baseChangeLift hg₀ hg rfl
  have h₀' : X.curve.zero ≫ g' = f ≫ (UniversalTate.yOneCurve N).zero :=
    EllipticCurveGeom.zero_baseChangeLift hg₀ hg.toCommSq rfl h0₀ h₀
  have hg'P : (φ (.ofAdd 1)).left ≫ g' = f ≫ (UniversalTate.yOneCurvePoint N).left := by
    refine hg₀.hom_ext ?_ ?_
    · rw [Category.assoc, EllipticCurveGeom.baseChangeLift_fst, hgP, Category.assoc,
        Category.assoc, UniversalTate.yOneCurvePoint_left_yOneCurveProj]
    · rw [Category.assoc, hg'.w, Category.assoc,
        EllipticCurveGeom.left_comp_structureMap, EllipticCurveGeom.left_comp_structureMap_assoc]
      simp
  refine ⟨⟨(f, g'), hg', h₀'⟩, ?_, fun fg hfg ↦ Subtype.ext ?_⟩
  · dsimp only
    rw [pointsPullback_prodCurvePoint_eq_iff, Equiv.apply_symm_apply]
    exact hg'P
  · have hfgP : (φ (.ofAdd 1)).left ≫ fg.1.2 =
        fg.1.1 ≫ (UniversalTate.yOneCurvePoint N).left := by
      simpa using (pointsPullback_prodCurvePoint_eq_iff _ _ _).mp hfg
    have hpair := huniq (fg.1.1, fg.1.2 ≫ UniversalTate.yOneCurveProj N)
      ⟨fg.2.1.paste_horiz hg₀,
        by rw [reassoc_of% fg.2.2, h0₀, Category.assoc],
        by rw [reassoc_of% hfgP, UniversalTate.yOneCurvePoint_left_yOneCurveProj,
          Category.assoc]⟩
    simp only [Prod.mk.injEq] at hpair
    refine Prod.ext hpair.1 (hg₀.hom_ext ?_ ?_)
    · rw [hpair.2, EllipticCurveGeom.baseChangeLift_fst]
    · rw [fg.2.1.w, hpair.1, EllipticCurveGeom.baseChangeLift_structureMap]

private noncomputable def prodYOneUniversal (B : Scheme.{u}) {N : ℕ} [NeZero N] (h4 : 4 ≤ N) :
    (ModuliProblem.gammaOneNaive B N).obj (op (prodCurve B (UniversalTate.yOneCurve.{u} N))) :=
  let hP₀ := UniversalTate.isOfNaiveExactOrder_yOneCurvePoint.{u} h4
  let φ₀ : Multiplicative (ZMod N) →* _ :=
    (zmodMonoidHomEquiv N _).symm ⟨UniversalTate.yOneCurvePoint N, hP₀.pow_eq_one⟩
  have hφ₀ : (UniversalTate.yOneCurve.{u} N).IsFiberwiseInjective φ₀ :=
    EllipticCurveGeom.isFiberwiseInjective_iff_isOfNaiveExactOrder.mpr <| by
      rw [zmodMonoidHomEquiv_symm_apply_ofAdd_one]
      exact hP₀
  (ModuliProblem.naiveLevelEquiv _).symm
    ⟨(EllipticCurveGeom.pointsPullback (isPullback_prodCurveProj B _)
        (zero_prodCurveProj B _)).comp φ₀, hφ₀.pointsPullback _ _⟩

private theorem naiveLevelEquiv_map_prodYOneUniversal {B : Scheme.{u}} {N : ℕ} [NeZero N]
    (h4 : 4 ≤ N) {X : EllObj B} (k : X ⟶ prodCurve B (UniversalTate.yOneCurve.{u} N)) :
    (ModuliProblem.naiveLevelEquiv X
        ((ModuliProblem.gammaOneNaive B N).map k.op (prodYOneUniversal B h4))).1 (.ofAdd 1) =
      EllipticCurveGeom.pointsPullback k.isPullback k.zero_total
        (prodCurvePoint B (UniversalTate.yOneCurvePoint N)) := by
  rw [ModuliProblem.naiveLevelEquiv_map, MonoidHom.comp_apply]
  dsimp only [prodYOneUniversal]
  rw [Equiv.apply_symm_apply, MonoidHom.comp_apply, zmodMonoidHomEquiv_symm_apply_ofAdd_one,
    prodCurvePoint_def]

private noncomputable def prodYOneRepresentableBy (B : Scheme.{u}) {N : ℕ} [NeZero N]
    (h4 : 4 ≤ N) :
    (ModuliProblem.gammaOneNaive B N).RepresentableBy
      (prodCurve B (UniversalTate.yOneCurve.{u} N)) :=
  let α₀ := prodYOneUniversal B h4
  have hbij : ∀ X : EllObj B, Function.Bijective
      (fun k : X ⟶ prodCurve B (UniversalTate.yOneCurve.{u} N) ↦
        (ModuliProblem.gammaOneNaive B N).map k.op α₀) := fun X ↦ by
    constructor
    · intro k₁ k₂ hk
      have hα := (ModuliProblem.naiveLevelEquiv X
        ((ModuliProblem.gammaOneNaive B N).map k₂.op α₀)).2
      have h1 := congrArg (fun α ↦ (ModuliProblem.naiveLevelEquiv X α).1 (.ofAdd 1)) hk
      rw [naiveLevelEquiv_map_prodYOneUniversal h4 k₁] at h1
      exact (existsUnique_hom_prodCurve_yOneCurve h4 hα).unique h1
        (naiveLevelEquiv_map_prodYOneUniversal h4 k₂).symm
    · intro α
      obtain ⟨k, hk, -⟩ :=
        existsUnique_hom_prodCurve_yOneCurve h4 (ModuliProblem.naiveLevelEquiv X α).2
      refine ⟨k, (ModuliProblem.naiveLevelEquiv X).injective (Subtype.ext ?_)⟩
      refine (zmodMonoidHomEquiv N _).injective (Subtype.ext ?_)
      rw [coe_zmodMonoidHomEquiv_apply, coe_zmodMonoidHomEquiv_apply,
        naiveLevelEquiv_map_prodYOneUniversal h4, hk]
  { homEquiv := Equiv.ofBijective _ (hbij _)
    homEquiv_comp f k := (Equiv.ofBijective_apply _ _ _).trans <|
      (congrArg (fun m ↦ (ModuliProblem.gammaOneNaive B N).map m α₀)
        (op_comp (f := f) (g := k))).trans <|
          Functor.map_comp_apply (ModuliProblem.gammaOneNaive B N) k.op f.op α₀ }

/-- **For `N ≥ 4`, `EllObj.yOne B N` is isomorphic in `Ell/B` to `B × UniversalTate.yOne N` with
its pulled-back universal elliptic curve.** -/
noncomputable def yOneIsoProdCurve (B : Scheme.{u}) {N : ℕ} [NeZero N] (h4 : 4 ≤ N) :
    yOne B N ≅ prodCurve B (UniversalTate.yOneCurve.{u} N) :=
  (ModuliProblem.gammaOneNaiveRepresentableBy h4).uniqueUpToIso (prodYOneRepresentableBy B h4)

/-- **For `N ≥ 4`, the base of `EllObj.yOne B N` is `B × UniversalTate.yOne N` over `B`.** -/
noncomputable def yOneBaseIso (B : Scheme.{u}) {N : ℕ} [NeZero N] (h4 : 4 ≤ N) :
    (yOne B N).base ≅ B ⨯ UniversalTate.yOne.{u} N where
  hom := (yOneIsoProdCurve B h4).hom.base
  inv := (yOneIsoProdCurve B h4).inv.base
  hom_inv_id := (comp_base _ _).symm.trans <|
    (congrArg Hom.base (yOneIsoProdCurve B h4).hom_inv_id).trans (id_base _)
  inv_hom_id := (comp_base _ _).symm.trans <|
    (congrArg Hom.base (yOneIsoProdCurve B h4).inv_hom_id).trans (id_base _)

@[reassoc (attr := simp)]
theorem yOneBaseIso_hom_fst (B : Scheme.{u}) {N : ℕ} [NeZero N] (h4 : 4 ≤ N) :
    (yOneBaseIso B h4).hom ≫ prod.fst = (yOne B N).structureMap :=
  (yOneIsoProdCurve B h4).hom.base_structureMap

@[reassoc]
theorem yOneBaseIso_inv_structureMap (B : Scheme.{u}) {N : ℕ} [NeZero N] (h4 : 4 ≤ N) :
    (yOneBaseIso B h4).inv ≫ (yOne B N).structureMap = prod.fst :=
  (yOneIsoProdCurve B h4).inv.base_structureMap

/-- **The fine moduli scheme `Y₁(4)` over `B` has structure morphism smooth of relative dimension
`1` over `B`.** -/
instance smoothOfRelativeDimension_one_yOne_four_structureMap (B : Scheme.{u}) :
    SmoothOfRelativeDimension 1 (yOne B 4).structureMap := by
  have : SmoothOfRelativeDimension 1 (prod.fst : B ⨯ UniversalTate.yOne.{u} 4 ⟶ B) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasBinaryProduct' _ _).flip inferInstance
  rw [← yOneBaseIso_hom_fst B (N := 4) le_rfl]
  have hcomp : SmoothOfRelativeDimension (0 + 1)
      ((yOneBaseIso B (N := 4) le_rfl).hom ≫ prod.fst) :=
    inferInstance
  simpa using hcomp

end TauCeti.AlgebraicGeometry.EllObj

/-! ### Smoothness of relative dimension one for representable étale moduli problems -/

namespace TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData

/-- **Rigidifier transfer of smooth relative dimension one.** Let `𝒫` be a moduli problem over
`Ell/B` represented by `U`, with `[LocallyOfFinitePresentation U.structureMap]` and étale
relative-representability data `D`. If `Ell/B` admits an étale surjective rigidifier `𝒬`
represented by an object `V` whose structure morphism is smooth of relative dimension `1`, then
`U.structureMap` is smooth of relative dimension `1`. -/
theorem smoothOfRelativeDimension_one_of_rigidifier {B : Scheme.{u}} {P Q : ModuliProblem B}
    {U V : EllObj B} (D : P.RelRepData) (R : P.RepresentableBy U) (heP : D.HasProperty @Etale)
    [LocallyOfFinitePresentation U.structureMap]
    (DQ : Q.RelRepData) (RQ : Q.RepresentableBy V) (heQ : DQ.HasProperty @Etale)
    (hsQ : DQ.HasProperty @Surjective) [SmoothOfRelativeDimension 1 V.structureMap] :
    SmoothOfRelativeDimension 1 U.structureMap := by
  -- `W = U_{𝒬_U}` represents `𝒬 ⊗ 𝒫`, with étale surjective `a₁ : W ⟶ U` and étale `a₂ : W ⟶ V`.
  let S := DQ.tensorRepresentableBy R
  let a₁ := U.baseChangeFunctorHom (DQ.rep U)
  let a₂ := RQ.homEquiv.symm (S.homEquiv (𝟙 _)).1
  have : Etale a₁.base := by
    rw [EllObj.baseChangeFunctorHom_base]
    exact DQ.hasProperty_iff.mp heQ U
  have : Surjective a₁.base := by
    rw [EllObj.baseChangeFunctorHom_base]
    exact DQ.hasProperty_iff.mp hsQ U
  have ha₂ : RQ.homEquiv a₂ = (S.homEquiv (𝟙 _)).1 := RQ.homEquiv.apply_symm_apply _
  have : MorphismProperty.RespectsIso @Etale.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : Etale a₂.base := D.mem_base_of_forget_snd RQ S a₂ ha₂ (D.hasProperty_iff.mp heP V)
  have hcomp : SmoothOfRelativeDimension (0 + 1) (a₂.base ≫ V.structureMap) := inferInstance
  have ha₁U : SmoothOfRelativeDimension 1 (a₁.base ≫ U.structureMap) := by
    rw [a₁.base_structureMap, ← a₂.base_structureMap]
    simpa using hcomp
  exact SmoothOfRelativeDimension.of_comp_surjective a₁.base U.structureMap

-- Every scheme `B` is covered by the basic opens `D(2)` and `D(3)`: in a residue field, `2 = 0`
-- and `3 = 0` would imply `1 = 3 - 2 = 0`.
private theorem basicOpen_two_sup_basicOpen_three_eq_top (B : Scheme.{u}) :
    B.basicOpen (2 : Γ(B, ⊤)) ⊔ B.basicOpen (3 : Γ(B, ⊤)) = ⊤ := by
  refine eq_top_iff.mpr fun b _ ↦ ?_
  by_contra hb
  rw [TopologicalSpace.Opens.mem_sup, not_or] at hb
  have h2 : (2 : B.residueField b) = 0 := by
    rw [← map_ofNat (B.evaluation ⊤ b trivial).hom 2]
    exact (B.evaluation_eq_zero_iff_notMem_basicOpen b trivial 2).mpr hb.1
  have h3 : (3 : B.residueField b) = 0 := by
    rw [← map_ofNat (B.evaluation ⊤ b trivial).hom 3]
    exact (B.evaluation_eq_zero_iff_notMem_basicOpen b trivial 3).mpr hb.2
  have h1 : (1 : B.residueField b) = 0 := by
    have : (3 : B.residueField b) - (2 : B.residueField b) = 1 := by norm_num
    rw [← this, h3, h2, sub_self]
  exact one_ne_zero h1

private theorem natCast_residueField_basicOpen_ne_zero (B : Scheme.{u}) (n : ℕ)
    (b : (B.basicOpen (n : Γ(B, ⊤))).toScheme) :
    (n : (B.basicOpen (n : Γ(B, ⊤))).toScheme.residueField b) ≠ 0 := by
  refine ((B.basicOpen (n : Γ(B, ⊤))).ι).natCast_residueField_ne_zero ?_
  have hb : (B.basicOpen (n : Γ(B, ⊤))).ι b ∈ B.basicOpen (n : Γ(B, ⊤)) := b.2
  rw [← map_natCast (B.evaluation ⊤ _ trivial).hom n]
  exact fun h0 ↦ ((B.evaluation_eq_zero_iff_notMem_basicOpen _ trivial _).mp h0) hb

private theorem smoothOfRelativeDimension_morphismRestrict_of_pullbackObj {B : Scheme.{u}}
    (U : EllObj B) (W : B.Opens)
    (h : SmoothOfRelativeDimension 1 (U.pullbackObj W.ι).structureMap) :
    SmoothOfRelativeDimension 1 (U.structureMap ∣_ W) := by
  have : SmoothOfRelativeDimension 1 (pullback.snd U.structureMap W.ι) := by
    rwa [EllObj.pullbackObj_structureMap] at h
  have heq : U.structureMap ∣_ W =
      (pullbackRestrictIsoRestrict U.structureMap W).inv ≫ pullback.snd U.structureMap W.ι := by
    rw [Iso.eq_inv_comp, pullbackRestrictIsoRestrict_hom_morphismRestrict]
  rw [heq]
  have hcomp : SmoothOfRelativeDimension (0 + 1)
      ((pullbackRestrictIsoRestrict U.structureMap W).inv ≫
        pullback.snd U.structureMap W.ι) := inferInstance
  simpa using hcomp

/-- **Every representable étale moduli problem has universal base smooth of relative dimension
one.** Let `𝒫` be a moduli problem over `Ell/B` represented by `U = (E/M)`, with `M ⟶ B` locally
of finite presentation and with étale relative-representability data `D`. Then `U.structureMap` is
smooth of relative dimension `1`. -/
theorem smoothOfRelativeDimension_one_of_representableBy {B : Scheme.{u}} {P : ModuliProblem B}
    {U : EllObj B} (D : P.RelRepData) (R : P.RepresentableBy U) (heP : D.HasProperty @Etale)
    [LocallyOfFinitePresentation U.structureMap] :
    SmoothOfRelativeDimension 1 U.structureMap := by
  let V : Bool → B.Opens := fun c ↦ cond c (B.basicOpen (2 : Γ(B, ⊤))) (B.basicOpen (3 : Γ(B, ⊤)))
  have hV : iSup V = ⊤ := by
    rw [iSup_bool_eq]
    exact basicOpen_two_sup_basicOpen_three_eq_top B
  have : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{u} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension 1)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1) V hV fun c ↦
    smoothOfRelativeDimension_morphismRestrict_of_pullbackObj U (V c) ?_
  have : LocallyOfFinitePresentation (U.pullbackObj (V c).ι).structureMap := by
    rw [EllObj.pullbackObj_structureMap]
    exact MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback U.structureMap (V c).ι) inferInstance
  cases c
  · -- Over `V false = D(3)`, `3` is invertible; rigidify by `[Γ(3)]_naive`.
    have h3 : ∀ b : (V false).toScheme, (3 : (V false).toScheme.residueField b) ≠ 0 :=
      natCast_residueField_basicOpen_ne_zero B 3
    exact (D.baseChange (V false).ι).smoothOfRelativeDimension_one_of_rigidifier
      (representableByPullbackObj (V false).ι R) (heP.baseChange (V false).ι)
      gammaNaiveRelRepData (gammaNaiveThreeRepresentableBy _)
      (hasProperty_etale_gammaNaiveRelRepData h3)
      (hasProperty_surjective_gammaNaiveRelRepData h3)
  · -- Over `V true = D(2)`, `4 = 2²` is invertible; rigidify by `[Γ₁(4)]_naive`.
    have h4 : ∀ b : (V true).toScheme, (4 : (V true).toScheme.residueField b) ≠ 0 := fun b ↦ by
      have h2 := natCast_residueField_basicOpen_ne_zero B 2 b
      have h22 : (2 : (V true).toScheme.residueField b) * 2 = 4 := by norm_num
      rw [← h22]
      exact mul_ne_zero h2 h2
    exact (D.baseChange (V true).ι).smoothOfRelativeDimension_one_of_rigidifier
      (representableByPullbackObj (V true).ι R) (heP.baseChange (V true).ι)
      gammaOneNaiveRelRepData (gammaOneNaiveRepresentableBy (N := 4) le_rfl)
      (hasProperty_etale_gammaOneNaiveRelRepData h4)
      (hasProperty_surjective_gammaOneNaiveRelRepData h4)

end TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData

namespace TauCeti.AlgebraicGeometry.EllObj

variable (B : Scheme.{u}) (N : ℕ) [NeZero N]

/-- **`Y₁(N)` is smooth of relative dimension `1` over `B`.** For `N ≥ 4` invertible on `B`, the
structure morphism of the fine moduli scheme `Y₁(N)` to `B` is smooth of relative dimension `1`;
in particular `Y₁(N)` is smooth of relative dimension `1` over `Spec ℤ[1/N]`. -/
theorem smoothOfRelativeDimension_one_yOne_structureMap
    (hN : ∀ b : B, (N : B.residueField b) ≠ 0) (h4 : 4 ≤ N) :
    SmoothOfRelativeDimension 1 (yOne B N).structureMap := by
  have : Smooth (yOne B N).structureMap := smooth_yOne_structureMap B N hN h4
  exact ModuliProblem.gammaOneNaiveRelRepData.smoothOfRelativeDimension_one_of_representableBy
    (ModuliProblem.gammaOneNaiveRepresentableBy h4)
    (ModuliProblem.hasProperty_etale_gammaOneNaiveRelRepData hN)

end TauCeti.AlgebraicGeometry.EllObj
