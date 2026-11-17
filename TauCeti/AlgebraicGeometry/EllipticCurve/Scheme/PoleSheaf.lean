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
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality

/-!
# Pole sheaves and the cubic polarisation of a projective Weierstrass model

For any Weierstrass curve `W` over a commutative ring `R`, with no ellipticity hypothesis, the
multiples `n[0]` of the zero section `[0 : 1 : 0]` are relative effective Cartier divisors on
`W.projModel` (`WeierstrassCurve.isRelativeEffectiveCartier_zeroSectionDivisor_pow`). The
**pole sheaf** `𝒪(n[0])` (`WeierstrassCurve.poleSheaf W n`) is the dual of the invertible ideal
sheaf `𝒪(-n[0])` of `n[0]`. Its sections allow poles of order at most `n` along the zero section
and no poles elsewhere, and its formation commutes with arbitrary pointed cartesian squares — in
particular with arbitrary ring homomorphisms and admissible changes of variables.

The hyperplane `Z = 0` meets `W.projModel` in the divisor `3[0]`
(`WeierstrassCurve.zeroSectionDivisor_pow_three_comap_chartι`), and `Z` is a nonzerodivisor in the
homogeneous coordinate ring `R[X, Y, Z] ⧸ (W(X, Y, Z))`
(`WeierstrassCurve.Projective.coord_two_mem_nonZeroDivisors`). Multiplication by `Z` therefore
embeds the twisting sheaf `𝒪(-1)` of `W.projModel = Proj (R[X, Y, Z] ⧸ (W))` into the structure
sheaf with image ideal sheaf `3[0]`, giving a canonical isomorphism `𝒪(-3[0]) ≅ 𝒪(-1)` over every
commutative ring and without any ellipticity hypothesis
(`WeierstrassCurve.zeroSectionDivisorPowThreeSheafIso`).

Passing to duals identifies `𝒪(3[0])` with the hyperplane bundle `𝒪(1)` of `W.projModel`
(`WeierstrassCurve.poleSheafThreeIsoProjModelTwistingSheafOne` and
`WeierstrassCurve.mk_poleSheaf_three`), again without any ellipticity hypothesis. Since `𝒪(1)` on
`W.projModel` is ample, `𝒪(3[0])` is ample, and hence `𝒪(n[0])` is ample for every `n > 0`
(`WeierstrassCurve.isAmple_poleSheaf`).

## Main definitions

* `WeierstrassCurve.projModelTwistingSheaf W n`: the twisting sheaf `𝒪(n)` (`n : ℤ`) on
  `W.projModel`, packaged as an invertible sheaf.
* `WeierstrassCurve.zMulHom W`: multiplication by the homogeneous coordinate `Z`, as a
  monomorphism `𝒪(-1) ⟶ 𝒪_{W.projModel}`.
* `WeierstrassCurve.zeroSectionDivisorPowThreeSheafIso W`: the canonical isomorphism
  `𝒪(-3[0]) ≅ 𝒪(-1)` of `𝒪_{W.projModel}`-modules.
* `WeierstrassCurve.poleSheaf W n`: the invertible sheaf `𝒪(n[0])` (`n : ℕ`) on the projective
  model of any Weierstrass curve `W`.
* `WeierstrassCurve.poleSheafThreeIsoProjModelTwistingSheafOne W`: the canonical isomorphism
  `𝒪(3[0]) ≅ 𝒪(1)` of invertible sheaves on `W.projModel`.

## Main results

* `WeierstrassCurve.zeroSectionDivisor_pow_three_eq_imageIdealSheaf`: the divisor `3[0]` is the
  image ideal sheaf of multiplication by `Z : 𝒪(-1) ⟶ 𝒪_{W.projModel}`.
* `WeierstrassCurve.mk_toInvertibleSheaf_zeroSectionDivisor_pow_three`: `[𝒪(-3[0])] = [𝒪(1)]⁻¹`.
* `WeierstrassCurve.pullback_mk_projModelTwistingSheaf_of_isPullback`,
  `WeierstrassCurve.pullback_mk_projModelTwistingSheaf_projModelBaseChange`, and
  `WeierstrassCurve.pullback_mk_projModelTwistingSheaf_projModelVariableChangeIso_hom`:
  functoriality of `[𝒪(n)]` under pointed cartesian squares, base change, and admissible changes of
  variables.
* `WeierstrassCurve.mk_poleSheaf_eq_pow`, `WeierstrassCurve.mk_poleSheaf_add`,
  `WeierstrassCurve.pullback_mk_poleSheaf_of_isPullback`,
  `WeierstrassCurve.pullback_mk_poleSheaf_projModelBaseChange`, and
  `WeierstrassCurve.pullback_mk_poleSheaf_projModelVariableChangeIso_hom`: additivity and
  functoriality of `[𝒪(n[0])]` in the Picard group.
* `WeierstrassCurve.mk_poleSheaf_three` and `WeierstrassCurve.mk_poleSheaf_three_mul`:
  `[𝒪(3[0])] = [𝒪(1)]` and `[𝒪(3m[0])] = [𝒪(m)]`.
* `WeierstrassCurve.isGloballyGenerated_poleSheaf_three_mul`: `𝒪(3m[0])` is globally generated for
  every `m : ℕ`.
* `WeierstrassCurve.isAmple_poleSheaf`: `𝒪(n[0])` is ample on `W.projModel` for every `n > 0`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.2.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 and III.3.
* R. Hartshorne, *Algebraic Geometry*, Chapter II, Sections 5 and 7.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
  HomogeneousLocalization MvPolynomial TauCeti.AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-! ### Twisting sheaves of the projective Weierstrass model -/

/-- The three standard degree-one opens `D₊(X)`, `D₊(Y)`, `D₊(Z)` cover `W.projModel`. -/
theorem iSup_basicOpen_coord_eq_top :
    ⨆ i : Fin 3, Proj.basicOpen W.toProjective.grading (W.toProjective.coord i) = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _ W.toProjective.irrelevant_le_span_range_coord

private theorem iSup_basicOpen_coord_ulift_eq_top :
    ⨆ i : ULift.{u} (Fin 3),
      Proj.basicOpen W.toProjective.grading (W.toProjective.coord i.down) = ⊤ := by
  rw [← Equiv.ulift.symm.iSup_comp]
  exact W.iSup_basicOpen_coord_eq_top

/-- Every integer twisting sheaf `𝒪(n)` on `W.projModel` is invertible, since the degree-one
coordinates `X, Y, Z` cover `W.projModel`. -/
instance isInvertible_twistingSheaf_grading (n : ℤ) :
    TauCeti.SheafOfModules.IsInvertible (R := W.projModel.ringCatSheaf)
      (Proj.twistingSheaf W.toProjective.grading n) :=
  Proj.isInvertible_twistingSheaf_of_iSup_eq_top
    (fun i : ULift.{u} (Fin 3) ↦ W.toProjective.coord i.down)
    (fun i ↦ W.toProjective.coord_mem_grading i.down)
    W.iSup_basicOpen_coord_ulift_eq_top n

/-- The twisting sheaf `𝒪(n)` (`n : ℤ`) on the projective Weierstrass model `W.projModel`,
packaged as an invertible sheaf. -/
noncomputable def projModelTwistingSheaf (n : ℤ) : InvertibleSheaf W.projModel :=
  ⟨Proj.twistingSheaf W.toProjective.grading n, inferInstance⟩

/-- The underlying module of `projModelTwistingSheaf W n` is `Proj.twistingSheaf`. -/
@[simp]
theorem projModelTwistingSheaf_obj (n : ℤ) :
    (W.projModelTwistingSheaf n).obj = Proj.twistingSheaf W.toProjective.grading n :=
  (rfl)

/-- In the Picard group of `W.projModel`, the class of `𝒪(n)` is `[𝒪(1)] ^ n` for every `n : ℤ`. -/
theorem mk_projModelTwistingSheaf_eq_zpow (n : ℤ) :
    LineBundleClass.mk (W.projModelTwistingSheaf n) =
      LineBundleClass.mk (W.projModelTwistingSheaf 1) ^ n :=
  Proj.lineBundleClass_twistingSheaf_eq_zpow
    (fun i : ULift.{u} (Fin 3) ↦ W.toProjective.coord i.down)
    (fun i ↦ W.toProjective.coord_mem_grading i.down)
    W.iSup_basicOpen_coord_ulift_eq_top n

/-- The degree-zero twisting sheaf `𝒪(0)` on `W.projModel` has trivial line-bundle class. -/
@[simp]
theorem mk_projModelTwistingSheaf_zero :
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
  Proj.isGloballyGenerated_twistingSheaf
    (fun i : ULift.{u} (Fin 3) ↦ W.toProjective.coord i.down)
    (fun i ↦ W.toProjective.coord_mem_grading i.down)
    W.iSup_basicOpen_coord_ulift_eq_top n

/-- Every positive twist `𝒪(n)` (`0 < n`) on `W.projModel` is ample. -/
theorem isAmple_projModelTwistingSheaf {n : ℕ} (hn : 0 < n) :
    (LineBundleClass.mk (W.projModelTwistingSheaf n)).IsAmple :=
  Proj.isAmple_twistingSheaf
    (fun i : ULift.{u} (Fin 3) ↦ W.toProjective.coord i.down)
    (fun i ↦ W.toProjective.coord_mem_grading i.down)
    W.iSup_basicOpen_coord_ulift_eq_top hn

/-! ### The hyperplane section `Z = 0` and the divisor `3[0]` -/

/-- Multiplication by the homogeneous coordinate `Z` on sections, sending `𝒪(-1)` to `𝒪(0)`. -/
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

/-- Multiplication by the homogeneous coordinate `Z`, as a morphism of `𝒪_{W.projModel}`-modules
`𝒪(-1) ⟶ 𝒪_{W.projModel}`. Its image ideal sheaf is the divisor `3[0]`
(`zeroSectionDivisor_pow_three_eq_imageIdealSheaf`). -/
noncomputable def zMulHom :
    Proj.twistingSheaf W.toProjective.grading (-1) ⟶
      SheafOfModules.unit W.projModel.ringCatSheaf :=
  W.zMulToZero ≫ (Proj.unitIsoTwistingSheafZero W.toProjective.grading).inv

/-- On sections over an open `U`, `zMulHom` multiplies a section of `𝒪(-1)` by `Z / 1` and reads
the degree-zero result as a regular function. -/
theorem zMulHom_app_apply (U : W.projModel.Opens)
    (s : Γ(Proj.twistingSheaf W.toProjective.grading (-1), U)) :
    W.zMulHom.app U s =
      (Proj.sectionsLinearEquivTwistingSheafZero W.toProjective.grading U).symm
        (Proj.twistingSheaf.mul W.toProjective.grading U 1 (-1)
          (Proj.toTwistingSheaf W.toProjective.grading rfl U
            ⟨W.toProjective.coord 2, W.toProjective.coord_mem_grading 2⟩) s) :=
  (ConcreteCategory.congr_hom (Scheme.Modules.Hom.comp_app (X := W.projModel) (U := U)
      W.zMulToZero (Proj.unitIsoTwistingSheafZero W.toProjective.grading).inv) s).trans
    (Proj.unitIsoTwistingSheafZero_inv_app_apply U _)

/-- Pointwise in each localization, `zMulHom` multiplies by `Z / 1`. -/
@[simp]
theorem zMulHom_app_apply_val (U : W.projModel.Opens)
    (s : Γ(Proj.twistingSheaf W.toProjective.grading (-1), U)) (x : U) :
    ((W.zMulHom.app U s).1 x).val =
      Localization.mk (W.toProjective.coord 2) 1 * s.1 x := by
  rw [W.zMulHom_app_apply U s, Proj.sectionsLinearEquivTwistingSheafZero_symm_apply_val,
    Proj.twistingSheaf.mul_apply, Proj.toTwistingSheaf_apply_apply]

/-- Multiplication by `Z` is injective on sections over every open `U`, because `Z` is a
nonzerodivisor in the homogeneous coordinate ring of `W`. -/
theorem zMulHom_app_injective (U : W.projModel.Opens) :
    Function.Injective (W.zMulHom.app U) := by
  refine (injective_iff_map_eq_zero _).mpr fun s hs ↦ Proj.twistingSheaf.ext fun x ↦ ?_
  let := x.1.isPrime
  have hz0 : Localization.mk (W.toProjective.coord 2) 1 * s.1 x = 0 :=
    (W.zMulHom_app_apply_val U s x).symm.trans
      ((congrArg (fun a : Γ(W.projModel, U) ↦ (a.1 x).val) hs).trans
        HomogeneousLocalization.val_zero)
  have hreg : algebraMap W.toProjective.CoordinateRing
      (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) (W.toProjective.coord 2) ∈
      nonZeroDivisors (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
    IsLocalization.nonZeroDivisors_le_comap x.1.asHomogeneousIdeal.toIdeal.primeCompl _
      W.toProjective.coord_two_mem_nonZeroDivisors
  rw [Localization.mk_one_eq_algebraMap] at hz0
  exact (mem_nonZeroDivisors_iff_left.mp hreg _ hz0).trans (Proj.twistingSheaf.zero_apply x).symm

/-- Multiplication by `Z` is a monomorphism `𝒪(-1) ⟶ 𝒪_{W.projModel}`. -/
instance mono_zMulHom : Mono W.zMulHom :=
  (SheafOfModules.forget _).mono_of_mono_map <|
    PresheafOfModules.mono_of_injective fun U ↦ W.zMulHom_app_injective U.unop

/-- On the standard open `D₊(Xᵢ)`, `zMulHom` sends the chart basis section `Xᵢ⁻¹` of `𝒪(-1)` to the
regular function `Z / Xᵢ`. -/
private theorem zMulHom_app_chartGenerator (i : Fin 3) :
    W.zMulHom.app (Proj.basicOpen W.toProjective.grading (W.toProjective.coord i))
      (Proj.twistingSheaf.chartGenerator (-1) (W.toProjective.coord i)
        (W.toProjective.coord_mem_grading i) _ le_rfl) =
      Proj.awayToSection W.toProjective.grading (W.toProjective.coord i)
        (Away.mk W.toProjective.grading (W.toProjective.coord_mem_grading i) 1
          (W.toProjective.coord 2) (by simpa using W.toProjective.coord_mem_grading 2)) := by
  set U := Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  let := x.1.isPrime
  refine (W.zMulHom_app_apply_val U _ x).trans
    (Eq.trans ?_ (Proj.val_awayToSection_mk_apply (W.toProjective.coord_mem_grading i) 1
      (W.toProjective.coord 2) (by simpa using W.toProjective.coord_mem_grading 2) x).symm)
  refine (congrArg (_ * ·) (Proj.twistingSheaf.chartGenerator_apply (-1)
    (W.toProjective.coord i) (W.toProjective.coord_mem_grading i) U le_rfl x)).trans ?_
  simp only [Int.reduceNeg, neg_neg, Int.toNat_one, Int.toNat_of_nonpos (by decide : (-1 : ℤ) ≤ 0),
    pow_zero, pow_one, Localization.mk_mul, mul_one, one_mul]

/-- On the standard open `D₊(Xᵢ)`, the image ideal of `zMulHom` is generated by `Z / Xᵢ`. -/
private theorem zMulHom_imageIdeal_basicOpen (i : Fin 3) :
    W.zMulHom.imageIdeal (Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)) =
      Ideal.span {(Proj.awayToSection W.toProjective.grading (W.toProjective.coord i)
        (Away.mk W.toProjective.grading (W.toProjective.coord_mem_grading i) 1
          (W.toProjective.coord 2) (by simpa using W.toProjective.coord_mem_grading 2)))} := by
  set U := Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)
  let eqv := Proj.twistingSheaf.chartSectionsLinearEquiv (-1) (W.toProjective.coord i)
    (W.toProjective.coord_mem_grading i) U le_rfl
  let e := Proj.twistingSheaf.chartGenerator (-1) (W.toProjective.coord i)
    (W.toProjective.coord_mem_grading i) U le_rfl
  let ψ : Γ(Proj.twistingSheaf W.toProjective.grading (-1), U) →ₗ[Γ(W.projModel, U)]
      Γ(W.projModel, U) := (W.zMulHom.val.app (op U)).hom
  have hψ (a : Γ(W.projModel, U)) : W.zMulHom.app U (a • e) =
      a * Proj.awayToSection W.toProjective.grading (W.toProjective.coord i)
        (Away.mk W.toProjective.grading (W.toProjective.coord_mem_grading i) 1
          (W.toProjective.coord 2) (by simpa using W.toProjective.coord_mem_grading 2)) :=
    (ψ.map_smul a e).trans (congrArg (a * ·) (W.zMulHom_app_chartGenerator i))
  ext s
  rw [Scheme.Modules.Hom.mem_imageIdeal, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨eqv.symm t, ?_⟩
    have ht : t = eqv.symm t • e :=
      (eqv.apply_symm_apply t).symm.trans (Proj.twistingSheaf.chartSectionsLinearEquiv_apply ..)
    exact ((congrArg (W.zMulHom.app U) ht).trans (hψ (eqv.symm t))).symm
  · rintro ⟨a, rfl⟩
    exact ⟨a • e, hψ a⟩

/-- Pulling `Z / Xᵢ` back along the chart `chartι W i` gives `chartPoint i 2` in `ChartRing i`. -/
private theorem chartι_appLE_awayToSection_coord_two (i : Fin 3)
    (h : (⊤ : (Spec (.of (W.toProjective.ChartRing i))).Opens) ≤
      W.chartι i ⁻¹ᵁ Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)) :
    (W.chartι i).appLE (Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)) ⊤ h
      (Proj.awayToSection W.toProjective.grading (W.toProjective.coord i)
        (Away.mk W.toProjective.grading (W.toProjective.coord_mem_grading i) 1
          (W.toProjective.coord 2) (by simpa using W.toProjective.coord_mem_grading 2))) =
      (Scheme.ΓSpecIso (.of (W.toProjective.ChartRing i))).inv
        (W.toProjective.chartPoint i 2) := by
  let 𝒜 := W.toProjective.grading
  let U := Proj.basicOpen 𝒜 (W.toProjective.coord i)
  let a := Away.mk 𝒜 (W.toProjective.coord_mem_grading i) 1 (W.toProjective.coord 2)
    (by simpa using W.toProjective.coord_mem_grading 2)
  let φ := CommRingCat.ofHom (W.toProjective.awayEquivChartRing i).toRingHom
  let g : Spec (.of (W.toProjective.ChartRing i)) ⟶ U.toScheme :=
    Spec.map φ ≫ (Proj.basicOpenIsoSpec 𝒜 (W.toProjective.coord i)
      (W.toProjective.coord_mem_grading i) one_pos).inv
  have hchart : W.chartι i = g ≫ U.ι := by
    rw [W.chartι_def i, ← Proj.basicOpenIsoSpec_inv_ι, Category.assoc]
    rfl
  -- Evaluate `(g ≫ U.ι).appLE U ⊤ h` via `U.ι.appLE` and `g.appTop`.
  have happ : (W.chartι i).appLE U ⊤ h (Proj.awayToSection 𝒜 (W.toProjective.coord i) a) =
      g.appTop (U.topIso.inv (Proj.awayToSection 𝒜 (W.toProjective.coord i) a)) := by
    have hcomp := Scheme.Hom.appLE_comp_appLE g U.ι U ⊤ ⊤ U.ι_preimage_self.ge le_top
    have h₁ : ∀ {f₁ f₂ : Spec (.of (W.toProjective.ChartRing i)) ⟶ Proj 𝒜}
        (_ : f₁ = f₂) (e₁ : ⊤ ≤ f₁ ⁻¹ᵁ U) (e₂ : ⊤ ≤ f₂ ⁻¹ᵁ U),
        f₁.appLE U ⊤ e₁ = f₂.appLE U ⊤ e₂ := by
      rintro _ _ rfl _ _
      rfl
    refine (ConcreteCategory.congr_hom ((h₁ hchart h _).trans hcomp.symm)
      (Proj.awayToSection 𝒜 (W.toProjective.coord i) a)).trans ?_
    have hι : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
      rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
      exact congrArg (Proj 𝒜).presheaf.map (Subsingleton.elim _ _)
    -- The proof `le_top : ⊤ ≤ ⊤` has type `⊤ ≤ g ⁻¹ᵁ ⊤` only up to unfolding `Scheme.Hom.preimage`,
    -- so `Scheme.Hom.appLE_eq_app` is applied by unification against `g.appTop` instead of `rw`.
    have hgTop : g.appLE ⊤ ⊤ le_top = g.appTop := Scheme.Hom.appLE_eq_app g
    rw [CommRingCat.comp_apply, hι, hgTop]
  rw [happ]
  simp only [g, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [Proj.basicOpenIsoSpec_inv_appTop_awayToSection 𝒜 (W.toProjective.coord_mem_grading i)
    one_pos a]
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (W.toProjective.ChartRing i))).hom).1
  rw [Iso.inv_hom_id_apply]
  calc (Scheme.ΓSpecIso (.of (W.toProjective.ChartRing i))).hom
        ((Spec.map φ).appTop ((Scheme.ΓSpecIso (.of (Away 𝒜 (W.toProjective.coord i)))).inv a))
      = φ ((Scheme.ΓSpecIso (.of (Away 𝒜 (W.toProjective.coord i)))).hom
          ((Scheme.ΓSpecIso (.of (Away 𝒜 (W.toProjective.coord i)))).inv a)) :=
        ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality φ) _
    _ = W.toProjective.awayEquivChartRing i a := by
        rw [Iso.inv_hom_id_apply]
        rfl
    _ = W.toProjective.chartPoint i 2 :=
        (congrArg (W.toProjective.awayEquivChartRing i)
          (W.toProjective.awayEquivChartRing_symm_mk_X i 2).symm).trans
          ((RingEquiv.apply_symm_apply _ _).trans (W.toProjective.chartPoint_apply i 2).symm)

/-- **The divisor `3[0]` is the image ideal sheaf of `Z : 𝒪(-1) ⟶ 𝒪_{W.projModel}`.** No
ellipticity hypothesis is needed. -/
theorem zeroSectionDivisor_pow_three_eq_imageIdealSheaf :
    W.zeroSectionDivisor ^ 3 = W.zMulHom.imageIdealSheaf := by
  have h (i : Fin 3) :
      (W.zeroSectionDivisor ^ 3).comap (W.chartι i) =
        W.zMulHom.imageIdealSheaf.comap (W.chartι i) := by
    rw [W.zeroSectionDivisor_pow_three_comap_chartι i]
    apply Scheme.IdealSheafData.ext_of_isAffine
    set U : W.projModel.affineOpens :=
      ⟨Proj.basicOpen W.toProjective.grading (W.toProjective.coord i),
        Proj.isAffineOpen_basicOpen _ _ (W.toProjective.coord_mem_grading i) one_pos⟩
    have htop : (⊤ : (Spec (.of (W.toProjective.ChartRing i))).Opens) ≤ W.chartι i ⁻¹ᵁ U.1 :=
      fun x _ ↦ by
        rw [Scheme.Hom.mem_preimage]
        dsimp only [U]
        rw [← W.opensRange_chartι i]
        exact ⟨x, rfl⟩
    rw [Scheme.IdealSheafData.ideal_comap_of_le _ (W.chartι i) U ⟨⊤, isAffineOpen_top _⟩ htop,
      Scheme.Modules.Hom.imageIdealSheaf_ideal, W.zMulHom_imageIdeal_basicOpen i,
      Ideal.map_span, Set.image_singleton]
    simp only [Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id,
      CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x ↦ Ideal.span {x}) (W.chartι_appLE_awayToSection_coord_two i htop).symm
  exact Scheme.IdealSheafData.ext_of_comap_openCover
    (Scheme.Cover.mkOfCovers (ULift.{u} (Fin 3))
      (fun i ↦ Spec (.of (W.toProjective.ChartRing i.down)))
      (fun i ↦ W.chartι i.down) fun y ↦ by
        obtain ⟨i, hi⟩ := W.exists_mem_range_chartι y
        obtain ⟨x, hx⟩ := Set.mem_range.mp hi
        exact ⟨⟨i⟩, x, hx⟩) fun i ↦ h i.down

/-- **Canonical identification `𝒪(-3[0]) ≅ 𝒪(-1)`.** Multiplication by `Z` identifies the ideal
sheaf of the divisor `3[0]` on `W.projModel` with the twisting sheaf `𝒪(-1)`, over every
commutative ring and without any ellipticity hypothesis. -/
noncomputable def zeroSectionDivisorPowThreeSheafIso :
    (W.zeroSectionDivisor ^ 3).sheaf ≅ Proj.twistingSheaf W.toProjective.grading (-1) :=
  eqToIso (congrArg Scheme.IdealSheafData.sheaf
      W.zeroSectionDivisor_pow_three_eq_imageIdealSheaf) ≪≫
    W.zMulHom.imageIdealSheafIso.symm

/-- Composing the inverse of `zeroSectionDivisorPowThreeSheafIso` with the inclusion of `3[0]` into
the structure sheaf recovers multiplication by `Z`. -/
@[simp, reassoc]
theorem zeroSectionDivisorPowThreeSheafIso_inv_sheafι :
    W.zeroSectionDivisorPowThreeSheafIso.inv ≫ (W.zeroSectionDivisor ^ 3).sheafι = W.zMulHom :=
  (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (Scheme.IdealSheafData.eqToIso_inv_sheafι
      W.zeroSectionDivisor_pow_three_eq_imageIdealSheaf)).trans
      W.zMulHom.imageIdealSheafIso_hom_ι

/-- Composing `zeroSectionDivisorPowThreeSheafIso` with multiplication by `Z` recovers the inclusion
of `3[0]` into the structure sheaf. -/
@[simp, reassoc]
theorem zeroSectionDivisorPowThreeSheafIso_hom_zMulHom :
    W.zeroSectionDivisorPowThreeSheafIso.hom ≫ W.zMulHom = (W.zeroSectionDivisor ^ 3).sheafι := by
  rw [← W.zeroSectionDivisorPowThreeSheafIso_inv_sheafι]
  exact Iso.hom_inv_id_assoc (C := SheafOfModules W.projModel.ringCatSheaf)
    W.zeroSectionDivisorPowThreeSheafIso (W.zeroSectionDivisor ^ 3).sheafι

/-- Without any ellipticity hypothesis, the ideal sheaf `𝒪(-3[0])` has line-bundle class
`[𝒪(1)]⁻¹` in the Picard group of `W.projModel`. -/
theorem mk_toInvertibleSheaf_zeroSectionDivisor_pow_three :
    LineBundleClass.mk (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf =
      (LineBundleClass.mk (W.projModelTwistingSheaf 1))⁻¹ := by
  have hneg :
      LineBundleClass.mk (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf =
        LineBundleClass.mk (W.projModelTwistingSheaf (-1)) := by
    rw [LineBundleClass.mk_eq_mk_iff,
      Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj,
      projModelTwistingSheaf_obj]
    exact ⟨W.zeroSectionDivisorPowThreeSheafIso⟩
  rw [hneg, W.mk_projModelTwistingSheaf_eq_zpow (-1), zpow_neg_one]

/-! ### Base-change and variable-change invariance of twisting sheaves -/

/-- Along any pointed cartesian square of projective Weierstrass models, the twisting sheaf `𝒪(n)`
pulls back in the Picard group to `𝒪(n)` for every `n : ℤ`. -/
theorem pullback_mk_projModelTwistingSheaf_of_isPullback {W : WeierstrassCurve R}
    {R' : Type u} [CommRing R'] {W' : WeierstrassCurve R'}
    {g : W'.projModel ⟶ W.projModel} {f : Spec (.of R') ⟶ Spec (.of R)}
    (hg : IsPullback g W'.projModelOver W.projModelOver f)
    (h0 : W'.projModelZero ≫ g = f ≫ W.projModelZero) (n : ℤ) :
    LineBundleClass.pullback g (LineBundleClass.mk (W.projModelTwistingSheaf n)) =
      LineBundleClass.mk (W'.projModelTwistingSheaf n) := by
  have h1 : LineBundleClass.pullback g (LineBundleClass.mk (W.projModelTwistingSheaf 1)) =
      LineBundleClass.mk (W'.projModelTwistingSheaf 1) := by
    apply inv_injective
    rw [← LineBundleClass.pullback_inv,
      ← W.mk_toInvertibleSheaf_zeroSectionDivisor_pow_three,
      ← W'.mk_toInvertibleSheaf_zeroSectionDivisor_pow_three]
    exact (W.isEffectiveCartier_zeroSectionDivisor_pow 3).pullback_mk_toInvertibleSheaf_of_eq_comap
      (W'.isEffectiveCartier_zeroSectionDivisor_pow 3)
      (zeroSectionDivisor_pow_eq_comap_of_isPullback hg h0 3)
  rw [W.mk_projModelTwistingSheaf_eq_zpow n, W'.mk_projModelTwistingSheaf_eq_zpow n,
    LineBundleClass.pullback_zpow, h1]

/-- Under `projModelBaseChange W f`, the twisting sheaf `𝒪(n)` pulls back in the Picard group to
`𝒪(n)` of `W.map f`, for every `n : ℤ` and with no ellipticity hypothesis. -/
theorem pullback_mk_projModelTwistingSheaf_projModelBaseChange
    {R' : Type u} [CommRing R'] (f : R →+* R') (n : ℤ) :
    LineBundleClass.pullback (W.projModelBaseChange f)
        (LineBundleClass.mk (W.projModelTwistingSheaf n)) =
      LineBundleClass.mk ((W.map f).projModelTwistingSheaf n) :=
  pullback_mk_projModelTwistingSheaf_of_isPullback (W.isPullback_projModelBaseChange f)
    (W.projModelZero_projModelBaseChange f) n

/-- An admissible change of variables preserves the twisting sheaves `𝒪(n)` on `W.projModel`, for
every `n : ℤ` and with no ellipticity hypothesis. -/
theorem pullback_mk_projModelTwistingSheaf_projModelVariableChangeIso_hom
    (C : VariableChange R) (n : ℤ) :
    LineBundleClass.pullback (W.projModelVariableChangeIso C).hom
        (LineBundleClass.mk (W.projModelTwistingSheaf n)) =
      LineBundleClass.mk ((C • W).projModelTwistingSheaf n) :=
  pullback_mk_projModelTwistingSheaf_of_isPullback (f := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩)
    (by simp [W.projModelZero_projModelVariableChangeIso_hom]) n

/-! ### Pole sheaves `𝒪(n[0])` and ampleness of the cubic polarisation -/

section PoleSheaf

/-- The **pole sheaf** `𝒪(n[0])` (`n : ℕ`) on the projective model of any Weierstrass curve `W`:
the dual of the invertible ideal sheaf `𝒪(-n[0])` of the effective Cartier divisor `n[0]`. -/
noncomputable def poleSheaf (n : ℕ) : InvertibleSheaf W.projModel :=
  (W.isEffectiveCartier_zeroSectionDivisor_pow n).toInvertibleSheaf.dual

/-- `poleSheaf W n` is the dual of the invertible ideal sheaf of `W.zeroSectionDivisor ^ n`. -/
theorem poleSheaf_def (n : ℕ) :
    W.poleSheaf n =
      (W.isEffectiveCartier_zeroSectionDivisor_pow n).toInvertibleSheaf.dual :=
  (rfl)

/-- The underlying sheaf of `poleSheaf W n` is the dual of the ideal sheaf of `n[0]`. -/
@[simp]
theorem poleSheaf_obj (n : ℕ) :
    (W.poleSheaf n).obj = (W.zeroSectionDivisor ^ n).sheaf.dual := by
  rw [poleSheaf_def, InvertibleSheaf.dual_obj,
    Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj]

/-- In the Picard group of `W.projModel`, `[𝒪(n[0])] = [𝒪([0])] ^ n`. -/
theorem mk_poleSheaf_eq_pow (n : ℕ) :
    LineBundleClass.mk (W.poleSheaf n) = LineBundleClass.mk (W.poleSheaf 1) ^ n := by
  have h₁ := W.isEffectiveCartier_zeroSectionDivisor
  rw [poleSheaf_def,
    LineBundleClass.mk_dual_toInvertibleSheaf_congr _ (TauCeti.isEffectiveCartier_pow h₁ n) rfl,
    LineBundleClass.mk_dual_toInvertibleSheaf_pow h₁ n]
  congr 1
  rw [poleSheaf_def, LineBundleClass.mk_dual_toInvertibleSheaf_congr _ h₁ (pow_one _)]

/-- `𝒪(0[0])` has trivial class in the Picard group of `W.projModel`. -/
@[simp]
theorem mk_poleSheaf_zero : LineBundleClass.mk (W.poleSheaf 0) = 1 := by
  rw [W.mk_poleSheaf_eq_pow 0, pow_zero]

/-- In the Picard group of `W.projModel`, `[𝒪((m + n)[0])] = [𝒪(m[0])] * [𝒪(n[0])]`. -/
theorem mk_poleSheaf_add (m n : ℕ) :
    LineBundleClass.mk (W.poleSheaf (m + n)) =
      LineBundleClass.mk (W.poleSheaf m) * LineBundleClass.mk (W.poleSheaf n) := by
  rw [W.mk_poleSheaf_eq_pow (m + n), W.mk_poleSheaf_eq_pow m, W.mk_poleSheaf_eq_pow n, pow_add]

/-- **Pointed-pullback functoriality of `𝒪(n[0])`.** Along any pointed cartesian square of
projective Weierstrass models, `𝒪(n[0])` pulls back in the Picard group to `𝒪(n[0])`. -/
theorem pullback_mk_poleSheaf_of_isPullback {W : WeierstrassCurve R}
    {R' : Type u} [CommRing R'] {W' : WeierstrassCurve R'}
    {g : W'.projModel ⟶ W.projModel} {f : Spec (.of R') ⟶ Spec (.of R)}
    (hg : IsPullback g W'.projModelOver W.projModelOver f)
    (h0 : W'.projModelZero ≫ g = f ≫ W.projModelZero) (n : ℕ) :
    LineBundleClass.pullback g (LineBundleClass.mk (W.poleSheaf n)) =
      LineBundleClass.mk (W'.poleSheaf n) :=
  (W.isEffectiveCartier_zeroSectionDivisor_pow n).pullback_mk_dual_toInvertibleSheaf_of_eq_comap
    (W'.isEffectiveCartier_zeroSectionDivisor_pow n)
    (zeroSectionDivisor_pow_eq_comap_of_isPullback hg h0 n)

/-- **Base-change functoriality of `𝒪(n[0])`.** Under `projModelBaseChange W f`, the pole sheaf
`𝒪(n[0])` pulls back in the Picard group to `𝒪(n[0])` of `W.map f`. -/
theorem pullback_mk_poleSheaf_projModelBaseChange {R' : Type u} [CommRing R'] (f : R →+* R')
    (n : ℕ) :
    LineBundleClass.pullback (W.projModelBaseChange f) (LineBundleClass.mk (W.poleSheaf n)) =
      LineBundleClass.mk ((W.map f).poleSheaf n) :=
  pullback_mk_poleSheaf_of_isPullback (W.isPullback_projModelBaseChange f)
    (W.projModelZero_projModelBaseChange f) n

/-- **Variable-change invariance of `𝒪(n[0])`.** Under `projModelVariableChangeIso W C`, the pole
sheaf `𝒪(n[0])` pulls back in the Picard group to `𝒪(n[0])` of `C • W`. -/
theorem pullback_mk_poleSheaf_projModelVariableChangeIso_hom (C : VariableChange R) (n : ℕ) :
    LineBundleClass.pullback (W.projModelVariableChangeIso C).hom
        (LineBundleClass.mk (W.poleSheaf n)) =
      LineBundleClass.mk ((C • W).poleSheaf n) :=
  pullback_mk_poleSheaf_of_isPullback (f := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩)
    (by simp [W.projModelZero_projModelVariableChangeIso_hom]) n

/-- The underlying sheaf isomorphism of the pairing `𝒪(-3[0]) ⊗ 𝒪(1) ≅ 𝒪_{W.projModel}`. -/
private noncomputable def poleSheafThreePairingSheafIso :
    let h₃ := W.isEffectiveCartier_zeroSectionDivisor_pow 3
    @Iso (SheafOfModules W.projModel.ringCatSheaf) _
      (InvertibleSheaf.tensorProduct h₃.toInvertibleSheaf (W.projModelTwistingSheaf 1)).obj
      (InvertibleSheaf.trivial W.projModel).obj :=
  let C := SheafOfModules W.projModel.ringCatSheaf
  let h₃ := W.isEffectiveCartier_zeroSectionDivisor_pow 3
  let eTensor :
      @Iso C _
        (InvertibleSheaf.tensorProduct h₃.toInvertibleSheaf (W.projModelTwistingSheaf 1)).obj
        (TauCeti.SheafOfModules.tensorProduct W.projModel.sheaf
          (W.zeroSectionDivisor ^ 3).sheaf (Proj.twistingSheaf W.toProjective.grading 1)) :=
    @eqToIso C _ _ _ (by
      rw [InvertibleSheaf.tensorProduct_obj, h₃.toInvertibleSheaf_obj,
        W.projModelTwistingSheaf_obj])
  let eCongr :
      @Iso C _
        (TauCeti.SheafOfModules.tensorProduct W.projModel.sheaf
          (W.zeroSectionDivisor ^ 3).sheaf (Proj.twistingSheaf W.toProjective.grading 1))
        (TauCeti.SheafOfModules.tensorProduct W.projModel.sheaf
          (Proj.twistingSheaf W.toProjective.grading (-1))
          (Proj.twistingSheaf W.toProjective.grading 1)) :=
    TauCeti.SheafOfModules.tensorProductCongrLeft W.projModel.sheaf
      W.zeroSectionDivisorPowThreeSheafIso
  let eMul :
      @Iso C _
        (TauCeti.SheafOfModules.tensorProduct W.projModel.sheaf
          (Proj.twistingSheaf W.toProjective.grading (-1))
          (Proj.twistingSheaf W.toProjective.grading 1))
        (Proj.twistingSheaf W.toProjective.grading (-1 + 1)) :=
    Proj.twistingSheaf.tensorProductIso W.toProjective.coord
      W.toProjective.coord_mem_grading W.iSup_basicOpen_coord_eq_top (-1) 1
  let eZero :
      @Iso C _
        (Proj.twistingSheaf W.toProjective.grading (-1 + 1))
        (Proj.twistingSheaf W.toProjective.grading 0) :=
    @eqToIso C _ _ _ (congrArg (Proj.twistingSheaf W.toProjective.grading) (neg_add_cancel 1))
  let eUnit :
      @Iso C _
        (Proj.twistingSheaf W.toProjective.grading 0)
        (SheafOfModules.unit W.projModel.ringCatSheaf) :=
    (Proj.unitIsoTwistingSheafZero W.toProjective.grading).symm
  let eTriv :
      @Iso C _
        (SheafOfModules.unit W.projModel.ringCatSheaf)
        (InvertibleSheaf.trivial W.projModel).obj :=
    (InvertibleSheaf.trivialObjIsoUnit W.projModel).symm
  @Iso.trans C _ _ _ _ eTensor <|
    @Iso.trans C _ _ _ _ eCongr <|
      @Iso.trans C _ _ _ _ eMul <|
        @Iso.trans C _ _ _ _ eZero <|
          @Iso.trans C _ _ _ _ eUnit eTriv

/-- The pairing `𝒪(-3[0]) ⊗ 𝒪(1) ≅ 𝒪_{W.projModel}` obtained by composing
`zeroSectionDivisorPowThreeSheafIso : 𝒪(-3[0]) ≅ 𝒪(-1)` with the twisting-sheaf multiplication
`𝒪(-1) ⊗ 𝒪(1) ≅ 𝒪(0) ≅ 𝒪_{W.projModel}`. -/
private noncomputable def poleSheafThreePairingIso :
    InvertibleSheaf.tensorProduct
        (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf
        (W.projModelTwistingSheaf 1) ≅
      InvertibleSheaf.trivial W.projModel :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible W.projModel)
    (Scheme.Modules.isoOfSheafIso W.projModel W.poleSheafThreePairingSheafIso)

/-- **Canonical identification `𝒪(3[0]) ≅ 𝒪(1)`.** Dualizing `𝒪(-3[0]) ≅ 𝒪(-1)` against the
multiplication pairing `𝒪(-1) ⊗ 𝒪(1) ≅ 𝒪(0) ≅ 𝒪_{W.projModel}` canonically identifies the cubic
pole sheaf `𝒪(3[0])` with the hyperplane bundle `𝒪(1)` of `W.projModel`. -/
noncomputable def poleSheafThreeIsoProjModelTwistingSheafOne :
    W.poleSheaf 3 ≅ W.projModelTwistingSheaf 1 :=
  InvertibleSheaf.dualIsoOfTensorIsoTrivial W.poleSheafThreePairingIso

/-- Transporting the canonical duality pairing `𝒪(-3[0]) ⊗ 𝒪(3[0]) ≅ 𝒪_{W.projModel}` along the
inverse of `poleSheafThreeIsoProjModelTwistingSheafOne` recovers the composite of
`zeroSectionDivisorPowThreeSheafIso : 𝒪(-3[0]) ≅ 𝒪(-1)` with the twisting-sheaf multiplication
`𝒪(-1) ⊗ 𝒪(1) ≅ 𝒪(0) ≅ 𝒪_{W.projModel}`. -/
@[reassoc]
theorem tensorProductCongrRight_poleSheafThreeIsoProjModelTwistingSheafOne_inv_tensorDualIso_hom :
    let C := SheafOfModules W.projModel.ringCatSheaf
    let h₃ := W.isEffectiveCartier_zeroSectionDivisor_pow 3
    ((InvertibleSheaf.tensorProductCongrRight
        (L := h₃.toInvertibleSheaf)
        W.poleSheafThreeIsoProjModelTwistingSheafOne).inv ≫
      (eqToIso (congrArg (InvertibleSheaf.tensorProduct h₃.toInvertibleSheaf)
        (W.poleSheaf_def 3))).hom ≫
      (InvertibleSheaf.tensorDualIso h₃.toInvertibleSheaf).hom).hom =
      (@eqToIso C _ _ _ (by
        rw [InvertibleSheaf.tensorProduct_obj, h₃.toInvertibleSheaf_obj,
          W.projModelTwistingSheaf_obj])).hom ≫
      (TauCeti.SheafOfModules.tensorProductCongrLeft W.projModel.sheaf
        W.zeroSectionDivisorPowThreeSheafIso).hom ≫
      (Proj.twistingSheaf.tensorProductIso W.toProjective.coord
        W.toProjective.coord_mem_grading W.iSup_basicOpen_coord_eq_top (-1) 1).hom ≫
      (@eqToIso C _ _ _
        (congrArg (Proj.twistingSheaf W.toProjective.grading) (neg_add_cancel 1))).hom ≫
      (Proj.unitIsoTwistingSheafZero W.toProjective.grading).inv ≫
      (InvertibleSheaf.trivialObjIsoUnit W.projModel).inv := by
  have h0 :
      (InvertibleSheaf.tensorProductCongrRight
          (L := (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf)
          W.poleSheafThreeIsoProjModelTwistingSheafOne).inv ≫
        (eqToIso (congrArg
          (InvertibleSheaf.tensorProduct
            (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf)
          (W.poleSheaf_def 3))).hom ≫
        (InvertibleSheaf.tensorDualIso
          (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf).hom =
        W.poleSheafThreePairingIso.hom :=
    (congrArg (fun k ↦
        (InvertibleSheaf.tensorProductCongrRight
          (L := (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf)
          W.poleSheafThreeIsoProjModelTwistingSheafOne).inv ≫ k)
      (Category.id_comp _)).trans
      (InvertibleSheaf.tensorProductCongrRight_dualIsoOfTensorIsoTrivial_inv_tensorDualIso_hom
        W.poleSheafThreePairingIso)
  refine (congrArg (fun f ↦ f.hom) h0).trans (SheafOfModules.hom_ext ?_)
  simp only [poleSheafThreePairingIso, poleSheafThreePairingSheafIso, ObjectProperty.isoMk,
    ObjectProperty.homMk, Scheme.Modules.isoOfSheafIso_hom_val]
  rfl

/-- On underlying `𝒪_{W.projModel}`-modules, evaluating the inverse of
`poleSheafThreeIsoProjModelTwistingSheafOne` against `𝒪(-3[0])` recovers
`zeroSectionDivisorPowThreeSheafIso` followed by the twisting-sheaf multiplication
`𝒪(-1) ⊗ 𝒪(1) ≅ 𝒪(0) ≅ 𝒪_{W.projModel}`. -/
@[reassoc]
theorem whiskerLeft_poleSheafThreeIsoProjModelTwistingSheafOne_inv_ev :
    let C := SheafOfModules W.projModel.ringCatSheaf
    let h₃ := W.isEffectiveCartier_zeroSectionDivisor_pow 3
    (MonoidalCategory.whiskerLeft (C := C)
        h₃.toInvertibleSheaf.obj
        (W.poleSheafThreeIsoProjModelTwistingSheafOne.inv.hom ≫
          (@eqToIso C _ _ _ (by rw [W.poleSheaf_def, InvertibleSheaf.dual_obj])).hom)) ≫
        (InvertibleSheaf.evaluationDualIsoSheaf h₃.toInvertibleSheaf).hom =
      (InvertibleSheaf.tensorProductObjIso h₃.toInvertibleSheaf
        (W.projModelTwistingSheaf 1)).inv ≫
      (@eqToIso C _ _ _ (by
        rw [InvertibleSheaf.tensorProduct_obj, h₃.toInvertibleSheaf_obj,
          W.projModelTwistingSheaf_obj])).hom ≫
      (TauCeti.SheafOfModules.tensorProductCongrLeft W.projModel.sheaf
        W.zeroSectionDivisorPowThreeSheafIso).hom ≫
      (Proj.twistingSheaf.tensorProductIso W.toProjective.coord
        W.toProjective.coord_mem_grading W.iSup_basicOpen_coord_eq_top (-1) 1).hom ≫
      (@eqToIso C _ _ _
        (congrArg (Proj.twistingSheaf W.toProjective.grading) (neg_add_cancel 1))).hom ≫
      (Proj.unitIsoTwistingSheafZero W.toProjective.grading).inv := by
  let C := SheafOfModules W.projModel.ringCatSheaf
  have hpair : W.poleSheafThreePairingIso.hom.hom = W.poleSheafThreePairingSheafIso.hom :=
    SheafOfModules.hom_ext <| by
      simp only [poleSheafThreePairingIso, ObjectProperty.isoMk, ObjectProperty.homMk,
        Scheme.Modules.isoOfSheafIso_hom_val]
  have hcancel :
      W.poleSheafThreePairingSheafIso.hom ≫
          (InvertibleSheaf.trivialObjIsoUnit W.projModel).hom =
        (@eqToIso C _ _ _ (by
          rw [InvertibleSheaf.tensorProduct_obj,
            (W.isEffectiveCartier_zeroSectionDivisor_pow 3).toInvertibleSheaf_obj,
            W.projModelTwistingSheaf_obj])).hom ≫
        (TauCeti.SheafOfModules.tensorProductCongrLeft W.projModel.sheaf
          W.zeroSectionDivisorPowThreeSheafIso).hom ≫
        (Proj.twistingSheaf.tensorProductIso W.toProjective.coord
          W.toProjective.coord_mem_grading W.iSup_basicOpen_coord_eq_top (-1) 1).hom ≫
        (@eqToIso C _ _ _
          (congrArg (Proj.twistingSheaf W.toProjective.grading) (neg_add_cancel 1))).hom ≫
        (Proj.unitIsoTwistingSheafZero W.toProjective.grading).inv :=
    (Category.assoc _ _ _).trans <|
      congrArg (_ ≫ ·) <| (Category.assoc _ _ _).trans <|
        congrArg (_ ≫ ·) <| (Category.assoc _ _ _).trans <|
          congrArg (_ ≫ ·) <| (Category.assoc _ _ _).trans <|
            congrArg (_ ≫ ·) <| (Category.assoc _ _ _).trans <|
              (congrArg (_ ≫ ·)
                (InvertibleSheaf.trivialObjIsoUnit W.projModel).inv_hom_id).trans
                (Category.comp_id _)
  exact (InvertibleSheaf.whiskerLeft_dualIsoOfTensorIsoTrivial_inv_ev
      W.poleSheafThreePairingIso).trans
    (congrArg (fun k ↦ (InvertibleSheaf.tensorProductObjIso _ _).inv ≫ k)
      ((congrArg (fun k ↦ k ≫ _) hpair).trans hcancel))

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
commutative ring `R` and every `n > 0`, the pole sheaf `𝒪(n[0])` is ample on `W.projModel`: its
cube `𝒪(3n[0])` is isomorphic to the positive twisting sheaf `𝒪(n)`. -/
theorem isAmple_poleSheaf {n : ℕ} (hn : 0 < n) :
    (LineBundleClass.mk (W.poleSheaf n)).IsAmple := by
  have h3 : (LineBundleClass.mk (W.poleSheaf 1) ^ 3).IsAmple := by
    rw [← W.mk_poleSheaf_eq_pow 3, W.mk_poleSheaf_three]
    exact W.isAmple_projModelTwistingSheaf (by decide : 0 < 1)
  rw [W.mk_poleSheaf_eq_pow n]
  exact (LineBundleClass.IsAmple.of_pow (by decide : 0 < 3) h3).pow hn

end PoleSheaf

end WeierstrassCurve
