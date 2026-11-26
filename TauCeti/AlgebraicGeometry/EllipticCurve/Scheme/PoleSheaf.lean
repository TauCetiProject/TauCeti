/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Characterization
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Divisor.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Image
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Prime
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Pole sheaves and the cubic polarisation of a projective Weierstrass model

For any Weierstrass curve `W` over a commutative ring `R` (no ellipticity hypothesis), `n[0]` is a
relative effective Cartier divisor on `W.projModel`, and the **pole sheaf** `𝒪(n[0])`
(`WeierstrassCurve.poleSheaf W n`) is the dual of `𝒪(-n[0])`. Multiplication by `Z` embeds `𝒪(-1)`
into `𝒪` with image ideal sheaf `3[0]`, giving `𝒪(-3[0]) ≅ 𝒪(-1)`
(`zeroSectionDivisorPowThreeSheafIso`), the pairing `𝒪(-3[0]) ⊗ 𝒪(1) ≅ 𝒪`
(`poleSheafThreePairingIso`), and by duality `𝒪(3[0]) ≅ 𝒪(1)`
(`poleSheafThreeIsoProjModelTwistingSheafOne`). Since `𝒪(1)` is ample on `W.projModel`, `𝒪(n[0])`
is ample for every `n > 0` (`isAmple_poleSheaf`).

## Main definitions and results

* `projModelTwistingSheaf`, `zMulHom`, `zeroSectionDivisorPowThreeSheafIso`, `poleSheaf`,
  `zeroSectionDivisorPowThreeTensorTwistingSheafOneIso`, `poleSheafThreePairingIso`,
  `poleSheafThreeIsoProjModelTwistingSheafOne`.
* `zeroSectionDivisor_pow_three_eq_imageIdealSheaf`, `mk_poleSheaf_three`, `mk_poleSheaf_three_mul`,
  `isGloballyGenerated_poleSheaf_three_mul`, `isAmple_poleSheaf`.
* `pullback_mk_projModelTwistingSheaf_of_isPullback` / `_projModelBaseChange` /
  `_projModelVariableChangeIso_hom`, and the matching `pullback_mk_poleSheaf_*` theorems.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.2.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.1 and III.3.
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Sections 5 and 7.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
  HomogeneousLocalization MvPolynomial TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-! ### Twisting sheaves of the projective Weierstrass model -/

private theorem iSup_basicOpen_coord_ulift_eq_top :
    ⨆ i : ULift.{u} (Fin 3),
      Proj.basicOpen W.toProjective.grading (W.toProjective.coord i.down) = ⊤ := by
  rw [← Equiv.ulift.symm.iSup_comp]; exact W.iSup_basicOpen_coord_eq_top

/-- Every twisting sheaf `𝒪(n)` on `W.projModel` is invertible. -/
instance isInvertible_twistingSheaf_grading (n : ℤ) :
    TauCeti.SheafOfModules.IsInvertible (R := W.projModel.ringCatSheaf)
      (Proj.twistingSheaf W.toProjective.grading n) :=
  Proj.isInvertible_twistingSheaf_of_iSup_eq_top (fun i : ULift.{u} (Fin 3) ↦
    W.toProjective.coord i.down) (fun i ↦ W.toProjective.coord_mem_grading i.down)
    W.iSup_basicOpen_coord_ulift_eq_top n

/-- The twisting sheaf `𝒪(n)` (`n : ℤ`) on `W.projModel`, packaged as an invertible sheaf. -/
noncomputable def projModelTwistingSheaf (n : ℤ) : InvertibleSheaf W.projModel :=
  ⟨Proj.twistingSheaf W.toProjective.grading n, inferInstance⟩

/-- The underlying module of `projModelTwistingSheaf W n` is `Proj.twistingSheaf`. -/
@[simp] theorem projModelTwistingSheaf_obj (n : ℤ) :
    (W.projModelTwistingSheaf n).obj = Proj.twistingSheaf W.toProjective.grading n := (rfl)

/-- In the Picard group of `W.projModel`, `[𝒪(n)] = [𝒪(1)] ^ n` for every `n : ℤ`. -/
theorem mk_projModelTwistingSheaf_eq_zpow (n : ℤ) :
    LineBundleClass.mk (W.projModelTwistingSheaf n) =
      LineBundleClass.mk (W.projModelTwistingSheaf 1) ^ n :=
  Proj.lineBundleClass_twistingSheaf_eq_zpow (fun i : ULift.{u} (Fin 3) ↦
    W.toProjective.coord i.down) (fun i ↦ W.toProjective.coord_mem_grading i.down)
    W.iSup_basicOpen_coord_ulift_eq_top n

/-- The degree-zero twisting sheaf `𝒪(0)` on `W.projModel` has trivial line-bundle class. -/
@[simp] theorem mk_projModelTwistingSheaf_zero :
    LineBundleClass.mk (W.projModelTwistingSheaf 0) = 1 := by
  rw [W.mk_projModelTwistingSheaf_eq_zpow 0, zpow_zero]

/-- In the Picard group of `W.projModel`, `[𝒪(m + n)] = [𝒪(m)] * [𝒪(n)]`. -/
theorem mk_projModelTwistingSheaf_add (m n : ℤ) :
    LineBundleClass.mk (W.projModelTwistingSheaf (m + n)) =
      LineBundleClass.mk (W.projModelTwistingSheaf m) *
        LineBundleClass.mk (W.projModelTwistingSheaf n) := by
  rw [W.mk_projModelTwistingSheaf_eq_zpow, W.mk_projModelTwistingSheaf_eq_zpow m,
    W.mk_projModelTwistingSheaf_eq_zpow n, zpow_add]

/-- Every nonnegative twist `𝒪(n)` (`n : ℕ`) on `W.projModel` is globally generated. -/
theorem isGloballyGenerated_projModelTwistingSheaf (n : ℕ) :
    (W.projModelTwistingSheaf n).IsGloballyGenerated :=
  Proj.isGloballyGenerated_twistingSheaf (fun i : ULift.{u} (Fin 3) ↦
    W.toProjective.coord i.down) (fun i ↦ W.toProjective.coord_mem_grading i.down)
    W.iSup_basicOpen_coord_ulift_eq_top n

/-- Every positive twist `𝒪(n)` (`0 < n`) on `W.projModel` is ample. -/
theorem isAmple_projModelTwistingSheaf {n : ℕ} (hn : 0 < n) :
    (LineBundleClass.mk (W.projModelTwistingSheaf n)).IsAmple :=
  Proj.isAmple_twistingSheaf (fun i : ULift.{u} (Fin 3) ↦ W.toProjective.coord i.down)
    (fun i ↦ W.toProjective.coord_mem_grading i.down) W.iSup_basicOpen_coord_ulift_eq_top hn

/-! ### The hyperplane section `Z = 0` and the divisor `3[0]` -/

private noncomputable def zMulToZero :
    Proj.twistingSheaf W.toProjective.grading (-1) ⟶
      Proj.twistingSheaf W.toProjective.grading 0 where
  val :=
    { app U := ModuleCat.ofHom
        (X := (Proj.twistingSheaf W.toProjective.grading (-1)).val.obj U)
        (Y := (Proj.twistingSheaf W.toProjective.grading 0).val.obj U)
        (Proj.twistingSheaf.mul W.toProjective.grading U.unop 1 (-1)
          (Proj.toTwistingSheaf W.toProjective.grading rfl U.unop
            ⟨W.toProjective.coord 2, W.toProjective.coord_mem_grading 2⟩))
      naturality _ := rfl }

/-- Multiplication by `Z`, as a morphism `𝒪(-1) ⟶ 𝒪_{W.projModel}` with image ideal `3[0]`. -/
noncomputable def zMulHom :
    Proj.twistingSheaf W.toProjective.grading (-1) ⟶
      SheafOfModules.unit W.projModel.ringCatSheaf :=
  W.zMulToZero ≫ (Proj.unitIsoTwistingSheafZero W.toProjective.grading).inv

/-- On sections over `U`, `zMulHom` multiplies by `Z / 1` and reads the result as a function. -/
theorem zMulHom_app_apply (U : W.projModel.Opens)
    (s : Γ(Proj.twistingSheaf W.toProjective.grading (-1), U)) :
    W.zMulHom.app U s = (Proj.sectionsLinearEquivTwistingSheafZero W.toProjective.grading U).symm
      (Proj.twistingSheaf.mul W.toProjective.grading U 1 (-1)
        (Proj.toTwistingSheaf W.toProjective.grading rfl U
          ⟨W.toProjective.coord 2, W.toProjective.coord_mem_grading 2⟩) s) :=
  (ConcreteCategory.congr_hom (Scheme.Modules.Hom.comp_app (X := W.projModel) (U := U)
      W.zMulToZero (Proj.unitIsoTwistingSheafZero W.toProjective.grading).inv) s).trans
    (Proj.unitIsoTwistingSheafZero_inv_app_apply U _)

/-- Pointwise in each localization, `zMulHom` multiplies by `Z / 1`. -/
@[simp] theorem zMulHom_app_apply_val (U : W.projModel.Opens)
    (s : Γ(Proj.twistingSheaf W.toProjective.grading (-1), U)) (x : U) :
    ((W.zMulHom.app U s).val x).val = Localization.mk (W.toProjective.coord 2) 1 * s.val x := by
  rw [W.zMulHom_app_apply U s, Proj.sectionsLinearEquivTwistingSheafZero_symm_apply_val,
    Proj.twistingSheaf.mul_apply, Proj.toTwistingSheaf_apply_apply]

/-- Multiplication by `Z` is injective on sections over every open `U`. -/
theorem zMulHom_app_injective (U : W.projModel.Opens) : Function.Injective (W.zMulHom.app U) := by
  refine (injective_iff_map_eq_zero _).mpr fun s hs ↦ Proj.twistingSheaf.ext fun x ↦ ?_
  let := x.val.isPrime
  have hz0 : Localization.mk (W.toProjective.coord 2) 1 * s.val x = 0 :=
    (W.zMulHom_app_apply_val U s x).symm.trans <|
      (congrArg (fun a : Γ(W.projModel, U) ↦ (a.val x).val) hs).trans
        HomogeneousLocalization.val_zero
  have hreg := IsLocalization.nonZeroDivisors_le_comap x.val.asHomogeneousIdeal.toIdeal.primeCompl
    (Localization x.val.asHomogeneousIdeal.toIdeal.primeCompl)
    W.toProjective.coord_two_mem_nonZeroDivisors
  rw [Localization.mk_one_eq_algebraMap] at hz0
  exact (mem_nonZeroDivisors_iff_left.mp hreg _ hz0).trans (Proj.twistingSheaf.zero_apply x).symm

/-- Multiplication by `Z` is a monomorphism `𝒪(-1) ⟶ 𝒪_{W.projModel}`. -/
instance mono_zMulHom : Mono W.zMulHom :=
  (SheafOfModules.forget _).mono_of_mono_map <|
    PresheafOfModules.mono_of_injective fun U ↦ W.zMulHom_app_injective U.unop

private noncomputable def zOverCoord (i : Fin 3) :
    Away W.toProjective.grading (W.toProjective.coord i) :=
  Away.mk W.toProjective.grading (W.toProjective.coord_mem_grading i) 1
    (W.toProjective.coord 2) (by simpa using W.toProjective.coord_mem_grading 2)

private theorem zMulHom_app_chartGenerator (i : Fin 3) :
    W.zMulHom.app (Proj.basicOpen W.toProjective.grading (W.toProjective.coord i))
      (Proj.twistingSheaf.chartGenerator (-1) (W.toProjective.coord i)
        (W.toProjective.coord_mem_grading i) _ le_rfl) =
      Proj.awayToSection W.toProjective.grading (W.toProjective.coord i) (W.zOverCoord i) := by
  set U := Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)
  apply Subtype.ext; funext x; apply HomogeneousLocalization.val_injective
  let := x.val.isPrime
  refine (W.zMulHom_app_apply_val U _ x).trans <| Eq.trans ?_
    (Proj.val_awayToSection_mk_apply (W.toProjective.coord_mem_grading i) 1
      (W.toProjective.coord 2) (by simpa using W.toProjective.coord_mem_grading 2) x).symm
  refine (congrArg (_ * ·) (Proj.twistingSheaf.chartGenerator_apply (-1)
    (W.toProjective.coord i) (W.toProjective.coord_mem_grading i) U le_rfl x)).trans ?_
  simp only [Int.reduceNeg, neg_neg, Int.toNat_one, Int.toNat_of_nonpos (by decide : (-1 : ℤ) ≤ 0),
    pow_zero, pow_one, Localization.mk_mul, mul_one, one_mul]

private theorem zMulHom_imageIdeal_basicOpen (i : Fin 3) :
    W.zMulHom.imageIdeal (Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)) =
      Ideal.span {(Proj.awayToSection W.toProjective.grading (W.toProjective.coord i)
        (W.zOverCoord i))} := by
  set U := Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)
  let eqv := Proj.twistingSheaf.chartSectionsLinearEquiv (-1) (W.toProjective.coord i)
    (W.toProjective.coord_mem_grading i) U le_rfl
  let e := Proj.twistingSheaf.chartGenerator (-1) (W.toProjective.coord i)
    (W.toProjective.coord_mem_grading i) U le_rfl
  have hψ (a : Γ(W.projModel, U)) : W.zMulHom.app U (a • e) =
      a * Proj.awayToSection W.toProjective.grading (W.toProjective.coord i) (W.zOverCoord i) :=
    ((W.zMulHom.val.app (op U)).hom.map_smul a e).trans
      (congrArg (a * ·) (W.zMulHom_app_chartGenerator i))
  ext s; rw [Scheme.Modules.Hom.mem_imageIdeal, Ideal.mem_span_singleton']
  refine ⟨fun ⟨t, ht⟩ ↦ ⟨eqv.symm t, ?_⟩, fun ⟨a, ha⟩ ↦ ⟨a • e, (hψ a).trans ha⟩⟩
  exact ((congrArg (W.zMulHom.app U) ((eqv.apply_symm_apply t).symm.trans
    (Proj.twistingSheaf.chartSectionsLinearEquiv_apply ..))).trans (hψ (eqv.symm t))).symm.trans ht

private theorem chartι_appLE_awayToSection_coord_two (i : Fin 3)
    (h : (⊤ : (Spec (.of (W.toProjective.ChartRing i))).Opens) ≤
      W.chartι i ⁻¹ᵁ Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)) :
    (W.chartι i).appLE (Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)) ⊤ h
      (Proj.awayToSection W.toProjective.grading (W.toProjective.coord i) (W.zOverCoord i)) =
      (Scheme.ΓSpecIso (.of (W.toProjective.ChartRing i))).inv (W.toProjective.chartPoint i 2) := by
  let 𝒜 := W.toProjective.grading; let U := Proj.basicOpen 𝒜 (W.toProjective.coord i)
  let φ := CommRingCat.ofHom (W.toProjective.awayEquivChartRing i).toRingHom
  let g : Spec (.of (W.toProjective.ChartRing i)) ⟶ U.toScheme :=
    Spec.map φ ≫ (Proj.basicOpenIsoSpec 𝒜 (W.toProjective.coord i)
      (W.toProjective.coord_mem_grading i) one_pos).inv
  -- `chartι_def` coerces `awayEquivChartRing i` to a ring hom, which is `φ` by definition.
  have hchart : W.chartι i = g ≫ U.ι := by
    rw [W.chartι_def i, ← Proj.basicOpenIsoSpec_inv_ι, Category.assoc]; rfl
  have happ : (W.chartι i).appLE U ⊤ h (Proj.awayToSection 𝒜 (W.toProjective.coord i)
      (W.zOverCoord i)) =
      g.appTop (U.topIso.inv (Proj.awayToSection 𝒜 (W.toProjective.coord i) (W.zOverCoord i))) := by
    refine (ConcreteCategory.congr_hom (((W.chartι i).congr_appLE hchart U ⊤ h _).trans
      (Scheme.Hom.appLE_comp_appLE g U.ι U ⊤ ⊤ U.ι_preimage_self.ge le_top).symm) _).trans ?_
    have hι : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
      rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
      exact congrArg (Proj 𝒜).presheaf.map (Subsingleton.elim _ _)
    -- `g ⁻¹ᵁ ⊤ = ⊤` and `g.app ⊤ = g.appTop` hold by definition.
    have htop : g.appLE ⊤ ⊤ le_top = g.appTop := Scheme.Hom.appLE_eq_app g
    rw [CommRingCat.comp_apply, hι, htop]
  rw [happ]; simp only [g, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [Proj.basicOpenIsoSpec_inv_appTop_awayToSection 𝒜 (W.toProjective.coord_mem_grading i)
    one_pos (W.zOverCoord i)]
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (W.toProjective.ChartRing i))).hom).1
  rw [Iso.inv_hom_id_apply]
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality φ) _).trans <| by
    dsimp only [𝒜]; rw [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    exact (congrArg (W.toProjective.awayEquivChartRing i)
      (W.toProjective.awayEquivChartRing_symm_mk_X i 2).symm).trans
      ((RingEquiv.apply_symm_apply _ _).trans (W.toProjective.chartPoint_apply i 2).symm)

/-- The divisor `3[0]` is the image ideal sheaf of `Z : 𝒪(-1) ⟶ 𝒪_{W.projModel}`. -/
theorem zeroSectionDivisor_pow_three_eq_imageIdealSheaf :
    W.zeroSectionDivisor ^ 3 = W.zMulHom.imageIdealSheaf := by
  have h (i : Fin 3) : (W.zeroSectionDivisor ^ 3).comap (W.chartι i) =
      W.zMulHom.imageIdealSheaf.comap (W.chartι i) := by
    rw [W.zeroSectionDivisor_pow_three_comap_chartι i]; apply Scheme.IdealSheafData.ext_of_isAffine
    set U : W.projModel.affineOpens := ⟨Proj.basicOpen W.toProjective.grading
      (W.toProjective.coord i),
      Proj.isAffineOpen_basicOpen _ _ (W.toProjective.coord_mem_grading i) one_pos⟩
    have htop : (⊤ : (Spec (.of (W.toProjective.ChartRing i))).Opens) ≤ W.chartι i ⁻¹ᵁ U.val :=
      fun x _ ↦ by
        rw [Scheme.Hom.mem_preimage]; dsimp only [U]; rw [← W.opensRange_chartι i]; exact ⟨x, rfl⟩
    rw [Scheme.IdealSheafData.ideal_comap_of_le _ (W.chartι i) U ⟨⊤, isAffineOpen_top _⟩ htop,
      Scheme.Modules.Hom.imageIdealSheaf_ideal, W.zMulHom_imageIdeal_basicOpen i,
      Ideal.map_span, Set.image_singleton]
    simp only [Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id,
      CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_span, Set.image_singleton]
    exact congrArg (Ideal.span {·}) (W.chartι_appLE_awayToSection_coord_two i htop).symm
  exact Scheme.IdealSheafData.ext_of_comap_openCover
    (Scheme.Cover.mkOfCovers (ULift.{u} (Fin 3))
      (fun i ↦ Spec (.of (W.toProjective.ChartRing i.down))) (fun i ↦ W.chartι i.down) fun y ↦ by
        obtain ⟨i, x, hx⟩ := W.exists_mem_range_chartι y; exact ⟨⟨i⟩, x, hx⟩)
    fun i ↦ h i.down

/-- Canonical isomorphism `𝒪(-3[0]) ≅ 𝒪(-1)` induced by multiplication by `Z`. -/
noncomputable def zeroSectionDivisorPowThreeSheafIso :
    (W.zeroSectionDivisor ^ 3).sheaf ≅ Proj.twistingSheaf W.toProjective.grading (-1) :=
  eqToIso (congrArg Scheme.IdealSheafData.sheaf W.zeroSectionDivisor_pow_three_eq_imageIdealSheaf)
    ≪≫ W.zMulHom.imageIdealSheafIso.symm

/-- Composing `zeroSectionDivisorPowThreeSheafIso.inv` with `(3[0]).sheafι` gives `zMulHom`. -/
@[simp, reassoc] theorem zeroSectionDivisorPowThreeSheafIso_inv_sheafι :
    W.zeroSectionDivisorPowThreeSheafIso.inv ≫ (W.zeroSectionDivisor ^ 3).sheafι = W.zMulHom := by
  have heq : (eqToIso (congrArg Scheme.IdealSheafData.sheaf
      W.zeroSectionDivisor_pow_three_eq_imageIdealSheaf)).inv ≫
        (W.zeroSectionDivisor ^ 3).sheafι = W.zMulHom.imageIdealSheaf.sheafι :=
    (congrArg (· ≫ _) (eqToIso.inv _)).trans <|
      (eqToHom_naturality (f := Scheme.IdealSheafData.sheaf)
        (g := fun _ ↦ SheafOfModules.unit W.projModel.ringCatSheaf)
        Scheme.IdealSheafData.sheafι
        W.zeroSectionDivisor_pow_three_eq_imageIdealSheaf.symm).symm.trans
        (Category.comp_id _)
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) heq).trans W.zMulHom.imageIdealSheafIso_hom_ι

/-- Composing `zeroSectionDivisorPowThreeSheafIso.hom` with `zMulHom` gives `(3[0]).sheafι`. -/
@[simp, reassoc] theorem zeroSectionDivisorPowThreeSheafIso_hom_zMulHom :
    W.zeroSectionDivisorPowThreeSheafIso.hom ≫ W.zMulHom = (W.zeroSectionDivisor ^ 3).sheafι := by
  rw [← W.zeroSectionDivisorPowThreeSheafIso_inv_sheafι]
  exact Iso.hom_inv_id_assoc (C := SheafOfModules W.projModel.ringCatSheaf)
    W.zeroSectionDivisorPowThreeSheafIso (W.zeroSectionDivisor ^ 3).sheafι

/-- In the Picard group of `W.projModel`, `[𝒪(-3[0])] = [𝒪(1)]⁻¹` (no ellipticity hypothesis). -/
theorem mk_toInvertibleSheaf_zeroSectionDivisor_pow_three :
    LineBundleClass.mk (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf =
      (LineBundleClass.mk (W.projModelTwistingSheaf 1))⁻¹ := by
  have hneg : LineBundleClass.mk (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf =
      LineBundleClass.mk (W.projModelTwistingSheaf (-1)) := by
    rw [LineBundleClass.mk_eq_mk_iff,
      Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj, projModelTwistingSheaf_obj]
    exact ⟨W.zeroSectionDivisorPowThreeSheafIso⟩
  rw [hneg, W.mk_projModelTwistingSheaf_eq_zpow (-1), zpow_neg_one]

/-! ### Pole sheaves `𝒪(n[0])` -/

/-- The **pole sheaf** `𝒪(n[0])` (`n : ℕ`) on `W.projModel`, dual to `𝒪(-n[0])`. -/
noncomputable def poleSheaf (n : ℕ) : InvertibleSheaf W.projModel :=
  (W.isEffectiveCartier_zeroSectionDivisor_pow n).toInvertibleSheaf.dual

/-- `poleSheaf W n` is the dual of the invertible ideal sheaf of `W.zeroSectionDivisor ^ n`. -/
theorem poleSheaf_def (n : ℕ) :
    W.poleSheaf n = (W.isEffectiveCartier_zeroSectionDivisor_pow n).toInvertibleSheaf.dual := (rfl)

/-- The underlying sheaf of `poleSheaf W n` is the dual of the ideal sheaf of `n[0]`. -/
@[simp] theorem poleSheaf_obj (n : ℕ) :
    (W.poleSheaf n).obj = (W.zeroSectionDivisor ^ n).sheaf.dual := by
  rw [poleSheaf_def, InvertibleSheaf.dual_obj,
    Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj]

/-- In the Picard group of `W.projModel`, `[𝒪(n[0])] = [𝒪([0])] ^ n`. -/
theorem mk_poleSheaf_eq_pow (n : ℕ) :
    LineBundleClass.mk (W.poleSheaf n) = LineBundleClass.mk (W.poleSheaf 1) ^ n := by
  rw [poleSheaf_def, poleSheaf_def,
    LineBundleClass.mk_dual_toInvertibleSheaf_pow W.isEffectiveCartier_zeroSectionDivisor,
    LineBundleClass.mk_dual_toInvertibleSheaf_congr _ _ (pow_one _)]

/-- `𝒪(0[0])` has trivial class in the Picard group of `W.projModel`. -/
@[simp] theorem mk_poleSheaf_zero : LineBundleClass.mk (W.poleSheaf 0) = 1 :=
  LineBundleClass.mk_dual_toInvertibleSheaf_pow_zero _

/-- In the Picard group of `W.projModel`, `[𝒪((m + n)[0])] = [𝒪(m[0])] * [𝒪(n[0])]`. -/
theorem mk_poleSheaf_add (m n : ℕ) : LineBundleClass.mk (W.poleSheaf (m + n)) =
    LineBundleClass.mk (W.poleSheaf m) * LineBundleClass.mk (W.poleSheaf n) :=
  LineBundleClass.mk_dual_toInvertibleSheaf_pow_add _ _ _

/-! ### Base-change and variable-change invariance -/

section BaseChange

variable {W} {R' : Type u} [CommRing R'] {W' : WeierstrassCurve R'}
  {g : W'.projModel ⟶ W.projModel} {f : Spec (.of R') ⟶ Spec (.of R)}
  (hg : IsPullback g W'.projModelOver W.projModelOver f)
  (h0 : W'.projModelZero ≫ g = f ≫ W.projModelZero)

include hg h0 in
/-- Along a pointed cartesian square of projective Weierstrass models, `𝒪(n)` pulls back. -/
theorem pullback_mk_projModelTwistingSheaf_of_isPullback (n : ℤ) :
    LineBundleClass.pullback g (LineBundleClass.mk (W.projModelTwistingSheaf n)) =
      LineBundleClass.mk (W'.projModelTwistingSheaf n) := by
  have h1 : LineBundleClass.pullback g (LineBundleClass.mk (W.projModelTwistingSheaf 1)) =
      LineBundleClass.mk (W'.projModelTwistingSheaf 1) := by
    apply inv_injective
    rw [← LineBundleClass.pullback_inv, ← W.mk_toInvertibleSheaf_zeroSectionDivisor_pow_three,
      ← W'.mk_toInvertibleSheaf_zeroSectionDivisor_pow_three]
    exact hg.pullback_mk_toInvertibleSheaf_ker_pow W.projModelZero_projModelOver
      W'.projModelZero_projModelOver h0 W.zeroSectionDivisor_def W'.zeroSectionDivisor_def _ _
  rw [W.mk_projModelTwistingSheaf_eq_zpow n, W'.mk_projModelTwistingSheaf_eq_zpow n,
    LineBundleClass.pullback_zpow, h1]

include hg h0 in
/-- Along any pointed cartesian square of projective models, `𝒪(n[0])` pulls back to `𝒪(n[0])`. -/
theorem pullback_mk_poleSheaf_of_isPullback (n : ℕ) :
    LineBundleClass.pullback g (LineBundleClass.mk (W.poleSheaf n)) =
      LineBundleClass.mk (W'.poleSheaf n) :=
  hg.pullback_mk_dual_toInvertibleSheaf_ker_pow W.projModelZero_projModelOver
    W'.projModelZero_projModelOver h0 W.zeroSectionDivisor_def W'.zeroSectionDivisor_def _ _

end BaseChange

/-- Under `projModelBaseChange W f`, `𝒪(n)` pulls back to `𝒪(n)` of `W.map f`. -/
theorem pullback_mk_projModelTwistingSheaf_projModelBaseChange {R' : Type u} [CommRing R']
    (f : R →+* R') (n : ℤ) : LineBundleClass.pullback (W.projModelBaseChange f)
      (LineBundleClass.mk (W.projModelTwistingSheaf n)) =
      LineBundleClass.mk ((W.map f).projModelTwistingSheaf n) :=
  pullback_mk_projModelTwistingSheaf_of_isPullback (W.isPullback_projModelBaseChange f)
    (W.projModelZero_projModelBaseChange f) n

/-- Admissible changes of variables preserve `[𝒪(n)]` on `W.projModel`. -/
theorem pullback_mk_projModelTwistingSheaf_projModelVariableChangeIso_hom
    (C : VariableChange R) (n : ℤ) : LineBundleClass.pullback (W.projModelVariableChangeIso C).hom
      (LineBundleClass.mk (W.projModelTwistingSheaf n)) =
      LineBundleClass.mk ((C • W).projModelTwistingSheaf n) :=
  pullback_mk_projModelTwistingSheaf_of_isPullback (W.isPullback_projModelVariableChangeIso_hom C)
    ((W.projModelZero_projModelVariableChangeIso_hom C).trans (Category.id_comp _).symm) n

/-- Under `projModelBaseChange W f`, `𝒪(n[0])` pulls back to `𝒪(n[0])` of `W.map f`. -/
theorem pullback_mk_poleSheaf_projModelBaseChange {R' : Type u} [CommRing R'] (f : R →+* R')
    (n : ℕ) : LineBundleClass.pullback (W.projModelBaseChange f)
      (LineBundleClass.mk (W.poleSheaf n)) = LineBundleClass.mk ((W.map f).poleSheaf n) :=
  pullback_mk_poleSheaf_of_isPullback (W.isPullback_projModelBaseChange f)
    (W.projModelZero_projModelBaseChange f) n

/-- Under `projModelVariableChangeIso W C`, `𝒪(n[0])` pulls back to `𝒪(n[0])` of `C • W`. -/
theorem pullback_mk_poleSheaf_projModelVariableChangeIso_hom (C : VariableChange R) (n : ℕ) :
    LineBundleClass.pullback (W.projModelVariableChangeIso C).hom
      (LineBundleClass.mk (W.poleSheaf n)) = LineBundleClass.mk ((C • W).poleSheaf n) :=
  pullback_mk_poleSheaf_of_isPullback (W.isPullback_projModelVariableChangeIso_hom C)
    ((W.projModelZero_projModelVariableChangeIso_hom C).trans (Category.id_comp _).symm) n

/-! ### Cubic polarisation `𝒪(3[0]) ≅ 𝒪(1)` and ampleness -/

open MonoidalCategory in
/-- Canonical monoidal pairing `𝒪(-3[0]) ⊗ 𝒪(1) ≅ 𝒪_{W.projModel}` in `W.projModel.Modules`,
combining `zeroSectionDivisorPowThreeSheafIso` on the first factor with twisting-sheaf
multiplication `𝒪(-1) ⊗ 𝒪(1) ≅ 𝒪(0) ≅ 𝒪_{W.projModel}`. -/
noncomputable def zeroSectionDivisorPowThreeTensorTwistingSheafOneIso :
    (W.zeroSectionDivisor ^ 3).sheaf ⊗ Proj.twistingSheaf W.toProjective.grading 1 ≅
      𝟙_ W.projModel.Modules :=
  whiskerRightIso W.zeroSectionDivisorPowThreeSheafIso
      (Proj.twistingSheaf W.toProjective.grading 1) ≪≫
    Proj.twistingSheaf.tensorObjIso W.toProjective.coord
      W.toProjective.coord_mem_grading W.iSup_basicOpen_coord_eq_top (-1) 1 ≪≫
    eqToIso (congrArg (Proj.twistingSheaf W.toProjective.grading) (neg_add_cancel 1)) ≪≫
    (Proj.unitIsoTwistingSheafZero W.toProjective.grading).symm

open MonoidalCategory in
/-- Defining equation for `zeroSectionDivisorPowThreeTensorTwistingSheafOneIso`. -/
theorem zeroSectionDivisorPowThreeTensorTwistingSheafOneIso_def :
    W.zeroSectionDivisorPowThreeTensorTwistingSheafOneIso =
      whiskerRightIso W.zeroSectionDivisorPowThreeSheafIso
          (Proj.twistingSheaf W.toProjective.grading 1) ≪≫
        Proj.twistingSheaf.tensorObjIso W.toProjective.coord
          W.toProjective.coord_mem_grading W.iSup_basicOpen_coord_eq_top (-1) 1 ≪≫
        eqToIso (congrArg (Proj.twistingSheaf W.toProjective.grading) (neg_add_cancel 1)) ≪≫
        (Proj.unitIsoTwistingSheafZero W.toProjective.grading).symm :=
  (rfl)

open MonoidalCategory in
private noncomputable def poleSheafThreePairingSheafIso :
    (InvertibleSheaf.tensorProduct
        (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf
        (W.projModelTwistingSheaf 1)).obj ≅
      (InvertibleSheaf.trivial W.projModel).obj :=
  InvertibleSheaf.tensorProductObjIso
      (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf
      (W.projModelTwistingSheaf 1) ≪≫
    tensorIso (eqToIso (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf_obj)
      (eqToIso (W.projModelTwistingSheaf_obj 1)) ≪≫
    W.zeroSectionDivisorPowThreeTensorTwistingSheafOneIso ≪≫
    (InvertibleSheaf.trivialObjIsoUnit W.projModel).symm

/-- Canonical pairing `𝒪(-3[0]) ⊗ 𝒪(1) ≅ 𝒪_{W.projModel}` of invertible sheaves on `W.projModel`,
packaging `zeroSectionDivisorPowThreeTensorTwistingSheafOneIso`. -/
noncomputable def poleSheafThreePairingIso :
    InvertibleSheaf.tensorProduct
        (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf
        (W.projModelTwistingSheaf 1) ≅ InvertibleSheaf.trivial W.projModel :=
  -- `poleSheafThreePairingSheafIso` is constructed in `W.projModel.Modules`, which is
  -- definitionally `SheafOfModules W.projModel.ringCatSheaf` (the ambient category of
  -- `InvertibleSheaf W.projModel`).
  ObjectProperty.isoMk _ W.poleSheafThreePairingSheafIso

open MonoidalCategory in
/-- On underlying `𝒪_{W.projModel}`-modules, `poleSheafThreePairingIso` is
`zeroSectionDivisorPowThreeTensorTwistingSheafOneIso` transported across `tensorProductObjIso`,
`toInvertibleSheaf_obj`, `projModelTwistingSheaf_obj`, and `trivialObjIsoUnit`. -/
theorem poleSheafThreePairingIso_hom_hom :
    W.poleSheafThreePairingIso.hom.hom =
      (InvertibleSheaf.tensorProductObjIso
          (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf
          (W.projModelTwistingSheaf 1)).hom ≫
        ((eqToIso (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf_obj).hom ⊗ₘ
          (eqToIso (W.projModelTwistingSheaf_obj 1)).hom) ≫
        W.zeroSectionDivisorPowThreeTensorTwistingSheafOneIso.hom ≫
        (InvertibleSheaf.trivialObjIsoUnit W.projModel).inv :=
  (rfl)

/-- Canonical identification `𝒪(3[0]) ≅ 𝒪(1)` obtained by dualizing `poleSheafThreePairingIso`. -/
noncomputable def poleSheafThreeIsoProjModelTwistingSheafOne :
    W.poleSheaf 3 ≅ W.projModelTwistingSheaf 1 :=
  eqToIso (W.poleSheaf_def 3) ≪≫
    InvertibleSheaf.dualIsoOfTensorIsoTrivial W.poleSheafThreePairingIso

/-- `poleSheafThreeIsoProjModelTwistingSheafOne` is `dualIsoOfTensorIsoTrivial` applied to
`poleSheafThreePairingIso` along `poleSheaf_def 3`. -/
theorem poleSheafThreeIsoProjModelTwistingSheafOne_def :
    W.poleSheafThreeIsoProjModelTwistingSheafOne =
      eqToIso (W.poleSheaf_def 3) ≪≫
        InvertibleSheaf.dualIsoOfTensorIsoTrivial W.poleSheafThreePairingIso :=
  (rfl)

/-- **`[𝒪(3[0])] = [𝒪(1)]` in the Picard group of `W.projModel`.** -/
theorem mk_poleSheaf_three :
    LineBundleClass.mk (W.poleSheaf 3) = LineBundleClass.mk (W.projModelTwistingSheaf 1) := by
  rw [poleSheaf_def, ← LineBundleClass.inv_mk,
    W.mk_toInvertibleSheaf_zeroSectionDivisor_pow_three, inv_inv]

/-- **`[𝒪(3m[0])] = [𝒪(m)]` in the Picard group of `W.projModel`.** -/
theorem mk_poleSheaf_three_mul (m : ℕ) :
    LineBundleClass.mk (W.poleSheaf (3 * m)) =
      LineBundleClass.mk (W.projModelTwistingSheaf (m : ℤ)) := by
  rw [W.mk_poleSheaf_eq_pow (3 * m), pow_mul, ← W.mk_poleSheaf_eq_pow 3, W.mk_poleSheaf_three,
    W.mk_projModelTwistingSheaf_eq_zpow (m : ℤ), zpow_natCast]

/-- Every multiple `𝒪(3m[0])` (`m : ℕ`) of the cubic pole sheaf is globally generated on
`W.projModel`. -/
theorem isGloballyGenerated_poleSheaf_three_mul (m : ℕ) :
    (W.poleSheaf (3 * m)).IsGloballyGenerated := by
  obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.mp (W.mk_poleSheaf_three_mul m)
  exact (InvertibleSheaf.isGloballyGenerated_iff_of_iso e).mpr
    (W.isGloballyGenerated_projModelTwistingSheaf m)

/-- **Ampleness of the pole sheaves `𝒪(n[0])`.** For every Weierstrass curve `W` over any
commutative ring `R` and every `n > 0`, the pole sheaf `𝒪(n[0])` is ample on `W.projModel` (see
`mk_poleSheaf_three_mul`). -/
theorem isAmple_poleSheaf {n : ℕ} (hn : 0 < n) :
    (LineBundleClass.mk (W.poleSheaf n)).IsAmple := by
  have h3 : (LineBundleClass.mk (W.poleSheaf 1) ^ 3).IsAmple := by
    rw [← W.mk_poleSheaf_eq_pow 3, W.mk_poleSheaf_three]
    exact W.isAmple_projModelTwistingSheaf (by decide : 0 < 1)
  rw [W.mk_poleSheaf_eq_pow n]
  exact (LineBundleClass.IsAmple.of_pow (by decide : 0 < 3) h3).pow hn

end WeierstrassCurve
