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

/-!
# Pole sheaves and the cubic polarisation of a projective Weierstrass model

For an elliptic Weierstrass curve `W` over a commutative ring `R`, the multiples `n[0]` of the
zero section `[0 : 1 : 0]` are relative effective Cartier divisors on `W.projModel`
(`WeierstrassCurve.isRelativeEffectiveCartier_zeroSectionDivisor_pow`). The **pole sheaf**
`𝒪(n[0])` (`WeierstrassCurve.poleSheaf W n`) is the dual of the invertible ideal sheaf
`𝒪(-n[0])` of `n[0]`. Its sections allow poles of order at most `n` along the zero section and no
poles elsewhere, and its formation commutes with arbitrary ring homomorphisms and admissible
changes of variables.

The hyperplane `Z = 0` meets `W.projModel` in the divisor `3[0]`
(`WeierstrassCurve.zeroSectionDivisor_pow_three_comap_chartι`), and `Z` is a nonzerodivisor in the
homogeneous coordinate ring `R[X, Y, Z] ⧸ (W(X, Y, Z))`
(`WeierstrassCurve.Projective.coord_two_mem_nonZeroDivisors`). Multiplication by `Z` therefore
embeds the twisting sheaf `𝒪(-1)` of `W.projModel = Proj (R[X, Y, Z] ⧸ (W))` into the structure
sheaf with image ideal sheaf `3[0]`, giving a canonical isomorphism `𝒪(-3[0]) ≅ 𝒪(-1)` over every
commutative ring and without any ellipticity hypothesis
(`WeierstrassCurve.zeroSectionDivisorPowThreeSheafIso`).

Passing to duals when `W` is elliptic identifies `𝒪(3[0])` with the hyperplane bundle `𝒪(1)` of
`W.projModel` (`WeierstrassCurve.poleSheafThreeIsoProjModelTwistingSheafOne` and
`WeierstrassCurve.mk_poleSheaf_three`). Since `𝒪(1)` on `W.projModel` is ample, `𝒪(3[0])` is
ample, and hence `𝒪(n[0])` is ample for every `n > 0` (`WeierstrassCurve.isAmple_poleSheaf`).

## Main definitions

* `WeierstrassCurve.projModelTwistingSheaf W n`: the twisting sheaf `𝒪(n)` (`n : ℤ`) on
  `W.projModel`, packaged as an invertible sheaf.
* `WeierstrassCurve.zMulHom W`: multiplication by the homogeneous coordinate `Z`, as a
  monomorphism `𝒪(-1) ⟶ 𝒪_{W.projModel}`.
* `WeierstrassCurve.zeroSectionDivisorPowThreeSheafIso W`: the canonical isomorphism
  `𝒪(-3[0]) ≅ 𝒪(-1)` of `𝒪_{W.projModel}`-modules, requiring no ellipticity hypothesis.
* `WeierstrassCurve.poleSheaf W n`: the invertible sheaf `𝒪(n[0])` (`n : ℕ`) on the projective
  model of an elliptic Weierstrass curve `W`.
* `WeierstrassCurve.poleSheafThreeIsoProjModelTwistingSheafOne W`: the canonical isomorphism
  `𝒪(3[0]) ≅ 𝒪(1)` of invertible sheaves on `W.projModel`.

## Main results

* `WeierstrassCurve.zeroSectionDivisor_pow_three_eq_imageIdealSheaf`: the divisor `3[0]` is the
  image ideal sheaf of multiplication by `Z : 𝒪(-1) ⟶ 𝒪_{W.projModel}`.
* `WeierstrassCurve.isEffectiveCartier_zeroSectionDivisor_pow_three` and
  `WeierstrassCurve.mk_toInvertibleSheaf_zeroSectionDivisor_pow_three`: `3[0]` is an effective
  Cartier divisor with `[𝒪(-3[0])] = [𝒪(1)]⁻¹`, without any ellipticity hypothesis.
* `WeierstrassCurve.pullback_mk_projModelTwistingSheaf` and
  `WeierstrassCurve.pullback_mk_projModelTwistingSheaf_projModelVariableChangeIso`: functoriality
  of `[𝒪(n)]` under base change and admissible changes of variables.
* `WeierstrassCurve.mk_poleSheaf`, `WeierstrassCurve.mk_poleSheaf_add`,
  `WeierstrassCurve.pullback_mk_poleSheaf`, and
  `WeierstrassCurve.pullback_mk_poleSheaf_projModelVariableChangeIso`: additivity and functoriality
  of `[𝒪(n[0])]` in the Picard group.
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
  (rfl)

/-- Pointwise in each localization, `zMulHom` multiplies by `Z / 1`. -/
@[simp]
theorem zMulHom_app_apply_val (U : W.projModel.Opens)
    (s : Γ(Proj.twistingSheaf W.toProjective.grading (-1), U)) (x : U) :
    ((W.zMulHom.app U s).1 x).val =
      Localization.mk (W.toProjective.coord 2) 1 * s.1 x :=
  Proj.sectionsLinearEquivTwistingSheafZero_symm_apply_val U _ x

/-- Multiplication by `Z` is injective on sections over every open `U`, because `Z` is a
nonzerodivisor in the homogeneous coordinate ring of `W`. -/
theorem zMulHom_app_injective (U : W.projModel.Opens) :
    Function.Injective (W.zMulHom.app U) := by
  refine (injective_iff_map_eq_zero _).mpr fun s hs ↦ Proj.twistingSheaf.ext fun x ↦ ?_
  let := x.1.isPrime
  obtain ⟨V, hxV, iVU, d, j, hdj, r, t, hr, ht, hV, hsV⟩ :=
    Proj.twistingSheaf.exists_const s x.1 x.2
  have hsx : s.1 x = Localization.mk r ⟨t, hV hxV⟩ :=
    congrArg (fun u ↦ u.1 ⟨x.1, hxV⟩) hsV
  have hz0 : Localization.mk (W.toProjective.coord 2) 1 * s.1 x = 0 :=
    (W.zMulHom_app_apply_val U s x).symm.trans
      ((congrArg (fun a : Γ(W.projModel, U) ↦ (a.1 x).val) hs).trans
        HomogeneousLocalization.val_zero)
  rw [hsx, Localization.mk_mul, one_mul, Localization.mk_eq_mk'_apply,
    IsLocalization.mk'_eq_zero_iff] at hz0
  obtain ⟨⟨c, hc⟩, hcr⟩ := hz0
  have hcr' : W.toProjective.coord 2 * (c * r) = 0 := by linear_combination hcr
  have hca : c * r = 0 :=
    mem_nonZeroDivisors_iff_left.mp W.toProjective.coord_two_mem_nonZeroDivisors _ hcr'
  refine hsx.trans (Eq.trans ?_ (Proj.twistingSheaf.zero_apply x).symm)
  rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨c, hc⟩, hca⟩

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

/-- Under `(Proj.basicOpenIsoSpec 𝒜 (coord i) ...).inv`, a fraction `a` in `Away 𝒜 (coord i)`
corresponds to `(Proj.basicOpen 𝒜 (coord i)).topIso.inv (awayToSection a)`. -/
private theorem basicOpenIsoSpec_inv_appTop_awayToSection (i : Fin 3)
    (a : Away W.toProjective.grading (W.toProjective.coord i)) :
    (Proj.basicOpenIsoSpec W.toProjective.grading (W.toProjective.coord i)
      (W.toProjective.coord_mem_grading i) one_pos).inv.appTop
        ((Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)).topIso.inv
          (Proj.awayToSection W.toProjective.grading (W.toProjective.coord i) a)) =
      (Scheme.ΓSpecIso
        (.of (Away W.toProjective.grading (W.toProjective.coord i)))).inv a := by
  let 𝒜 := W.toProjective.grading
  let U := Proj.basicOpen 𝒜 (W.toProjective.coord i)
  have hbo' :
      (Proj.basicOpenIsoSpec 𝒜 (W.toProjective.coord i)
        (W.toProjective.coord_mem_grading i) one_pos).hom.appTop
          ((Scheme.ΓSpecIso (.of (Away 𝒜 (W.toProjective.coord i)))).inv a) =
        U.topIso.inv (Proj.awayToSection 𝒜 (W.toProjective.coord i) a) := by
    rw [Proj.basicOpenIsoSpec_hom,
      show (Proj.basicOpenToSpec 𝒜 (W.toProjective.coord i)).appTop = _ from
        Proj.basicOpenToSpec_app_top 𝒜 (W.toProjective.coord i)]
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    exact CommRingCat.comp_apply (Proj.awayToSection 𝒜 (W.toProjective.coord i)) U.topIso.inv a
  rw [← hbo', ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id,
    Scheme.Hom.id_appTop, CommRingCat.id_apply]

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
    rw [CommRingCat.comp_apply, hι,
      show g.appLE ⊤ ⊤ le_top = g.appTop from Scheme.Hom.appLE_eq_app g]
  rw [happ]
  simp only [g, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [W.basicOpenIsoSpec_inv_appTop_awayToSection i a]
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
  let 𝒰 : W.projModel.OpenCover :=
    Scheme.Cover.mkOfCovers (ULift.{u} (Fin 3))
      (fun i ↦ Spec (.of (W.toProjective.ChartRing i.down)))
      (fun i ↦ W.chartι i.down) fun y ↦ by
        obtain ⟨i, x, hx⟩ := W.exists_mem_range_chartι y
        exact ⟨⟨i⟩, x, hx⟩
  refine Scheme.IdealSheafData.ext_of_comap_openCover 𝒰 fun ⟨i⟩ ↦ ?_
  change (W.zeroSectionDivisor ^ 3).comap (W.chartι i) =
    W.zMulHom.imageIdealSheaf.comap (W.chartι i)
  rw [W.zeroSectionDivisor_pow_three_comap_chartι i]
  apply Scheme.IdealSheafData.ext_of_isAffine
  set U : W.projModel.affineOpens :=
    ⟨Proj.basicOpen W.toProjective.grading (W.toProjective.coord i),
      Proj.isAffineOpen_basicOpen _ _ (W.toProjective.coord_mem_grading i) one_pos⟩
  have htop : (⊤ : (Spec (.of (W.toProjective.ChartRing i))).Opens) ≤ W.chartι i ⁻¹ᵁ U.1 :=
    fun x _ ↦ by
      change W.chartι i x ∈ Proj.basicOpen W.toProjective.grading (W.toProjective.coord i)
      rw [← W.opensRange_chartι i]
      exact ⟨x, rfl⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_le _ (W.chartι i) U ⟨⊤, isAffineOpen_top _⟩ htop,
    Scheme.Modules.Hom.imageIdealSheaf_ideal, W.zMulHom_imageIdeal_basicOpen i,
    Ideal.map_span, Set.image_singleton]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_span, Set.image_singleton]
  exact congrArg (fun x ↦ Ideal.span {x}) (W.chartι_appLE_awayToSection_coord_two i htop).symm

/-- **Canonical identification `𝒪(-3[0]) ≅ 𝒪(-1)`.** Multiplication by `Z` identifies the ideal
sheaf of the divisor `3[0]` on `W.projModel` with the twisting sheaf `𝒪(-1)`, over every
commutative ring and without any ellipticity hypothesis. -/
noncomputable def zeroSectionDivisorPowThreeSheafIso :
    (W.zeroSectionDivisor ^ 3).sheaf ≅ Proj.twistingSheaf W.toProjective.grading (-1) :=
  eqToIso (congrArg Scheme.IdealSheafData.sheaf
      W.zeroSectionDivisor_pow_three_eq_imageIdealSheaf) ≪≫
    W.zMulHom.imageIdealSheafIso.symm

private theorem eqToIso_inv_sheafι {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.sheaf h)).inv ≫ I.sheafι = J.sheafι := by
  subst h
  simp only [eqToIso_refl, Iso.refl_inv]
  exact Category.id_comp _

/-- Composing the inverse of `zeroSectionDivisorPowThreeSheafIso` with the inclusion of `3[0]` into
the structure sheaf recovers multiplication by `Z`. -/
@[simp, reassoc]
theorem zeroSectionDivisorPowThreeSheafIso_inv_sheafι :
    W.zeroSectionDivisorPowThreeSheafIso.inv ≫ (W.zeroSectionDivisor ^ 3).sheafι = W.zMulHom :=
  (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (eqToIso_inv_sheafι W.zeroSectionDivisor_pow_three_eq_imageIdealSheaf)).trans
      W.zMulHom.imageIdealSheafIso_hom_ι

/-- The divisor `3[0]` on `W.projModel` is an effective Cartier divisor over every commutative ring,
with no ellipticity hypothesis. -/
theorem isEffectiveCartier_zeroSectionDivisor_pow_three :
    (W.zeroSectionDivisor ^ 3).IsEffectiveCartier := by
  rw [Scheme.IdealSheafData.isEffectiveCartier_iff_isInvertible_sheaf]
  exact ObjectProperty.prop_of_iso (SheafOfModules.isInvertible W.projModel)
    W.zeroSectionDivisorPowThreeSheafIso.symm (W.projModelTwistingSheaf (-1)).property

/-- Without any ellipticity hypothesis, the ideal sheaf `𝒪(-3[0])` has line-bundle class
`[𝒪(1)]⁻¹` in the Picard group of `W.projModel`. -/
theorem mk_toInvertibleSheaf_zeroSectionDivisor_pow_three :
    LineBundleClass.mk W.isEffectiveCartier_zeroSectionDivisor_pow_three.toInvertibleSheaf =
      (LineBundleClass.mk (W.projModelTwistingSheaf 1))⁻¹ := by
  have hneg :
      LineBundleClass.mk W.isEffectiveCartier_zeroSectionDivisor_pow_three.toInvertibleSheaf =
        LineBundleClass.mk (W.projModelTwistingSheaf (-1)) := by
    rw [LineBundleClass.mk_eq_mk_iff,
      Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj,
      projModelTwistingSheaf_obj]
    exact ⟨W.zeroSectionDivisorPowThreeSheafIso⟩
  rw [hneg, W.mk_projModelTwistingSheaf_eq_zpow (-1), zpow_neg_one]

/-! ### Base-change and variable-change invariance -/

/-- Under `projModelBaseChange W f`, the twisting sheaf `𝒪(n)` pulls back in the Picard group to
`𝒪(n)` of `W.map f`, for every `n : ℤ` and with no ellipticity hypothesis. -/
theorem pullback_mk_projModelTwistingSheaf {R' : Type u} [CommRing R'] (f : R →+* R') (n : ℤ) :
    LineBundleClass.pullback (W.projModelBaseChange f)
        (LineBundleClass.mk (W.projModelTwistingSheaf n)) =
      LineBundleClass.mk ((W.map f).projModelTwistingSheaf n) := by
  have hW := W.isEffectiveCartier_zeroSectionDivisor_pow_three
  have hWf := (W.map f).isEffectiveCartier_zeroSectionDivisor_pow_three
  have hcomap : ((W.zeroSectionDivisor ^ 3).comap (W.projModelBaseChange f)).IsEffectiveCartier :=
    W.zeroSectionDivisor_pow_map f 3 ▸ hWf
  have h1 : LineBundleClass.pullback (W.projModelBaseChange f)
      (LineBundleClass.mk (W.projModelTwistingSheaf 1)) =
      LineBundleClass.mk ((W.map f).projModelTwistingSheaf 1) := by
    apply inv_injective
    rw [← LineBundleClass.pullbackHom_apply, ← map_inv, LineBundleClass.pullbackHom_apply,
      ← W.mk_toInvertibleSheaf_zeroSectionDivisor_pow_three,
      ← (W.map f).mk_toInvertibleSheaf_zeroSectionDivisor_pow_three,
      hW.pullback_mk_toInvertibleSheaf hcomap,
      LineBundleClass.mk_toInvertibleSheaf_congr hcomap hWf (W.zeroSectionDivisor_pow_map f 3).symm]
  rw [W.mk_projModelTwistingSheaf_eq_zpow n, (W.map f).mk_projModelTwistingSheaf_eq_zpow n,
    ← LineBundleClass.pullbackHom_apply, map_zpow, LineBundleClass.pullbackHom_apply, h1]

/-- An admissible change of variables pulls `[0]` back to `[0]`. -/
@[simp]
theorem zeroSectionDivisor_variableChange (C : VariableChange R) :
    (C • W).zeroSectionDivisor =
      W.zeroSectionDivisor.comap (W.projModelVariableChangeIso C).hom := by
  have hpb : IsPullback (C • W).projModelZero (𝟙 (Spec (.of R)))
      (W.projModelVariableChangeIso C).hom W.projModelZero :=
    IsPullback.of_vert_isIso
      ⟨by rw [Category.id_comp, W.projModelZero_projModelVariableChangeIso_hom]⟩
  rw [zeroSectionDivisor_def, zeroSectionDivisor_def]
  exact Scheme.IdealSheafData.ker_eq_comap_of_isPullback W.projModelZero hpb

/-- An admissible change of variables pulls `n[0]` back to `n[0]`. -/
theorem zeroSectionDivisor_pow_variableChange (C : VariableChange R) (n : ℕ) :
    (C • W).zeroSectionDivisor ^ n =
      (W.zeroSectionDivisor ^ n).comap (W.projModelVariableChangeIso C).hom := by
  rw [zeroSectionDivisor_variableChange, Scheme.IdealSheafData.comap_pow]

/-- An admissible change of variables preserves the twisting sheaves `𝒪(n)` on `W.projModel`, for
every `n : ℤ` and with no ellipticity hypothesis. -/
theorem pullback_mk_projModelTwistingSheaf_projModelVariableChangeIso
    (C : VariableChange R) (n : ℤ) :
    LineBundleClass.pullback (W.projModelVariableChangeIso C).hom
        (LineBundleClass.mk (W.projModelTwistingSheaf n)) =
      LineBundleClass.mk ((C • W).projModelTwistingSheaf n) := by
  have hW := W.isEffectiveCartier_zeroSectionDivisor_pow_three
  have hCW := (C • W).isEffectiveCartier_zeroSectionDivisor_pow_three
  have hcomap :
      ((W.zeroSectionDivisor ^ 3).comap (W.projModelVariableChangeIso C).hom).IsEffectiveCartier :=
    W.zeroSectionDivisor_pow_variableChange C 3 ▸ hCW
  have h1 : LineBundleClass.pullback (W.projModelVariableChangeIso C).hom
      (LineBundleClass.mk (W.projModelTwistingSheaf 1)) =
      LineBundleClass.mk ((C • W).projModelTwistingSheaf 1) := by
    apply inv_injective
    rw [← LineBundleClass.pullbackHom_apply, ← map_inv, LineBundleClass.pullbackHom_apply,
      ← W.mk_toInvertibleSheaf_zeroSectionDivisor_pow_three,
      ← (C • W).mk_toInvertibleSheaf_zeroSectionDivisor_pow_three,
      hW.pullback_mk_toInvertibleSheaf hcomap,
      LineBundleClass.mk_toInvertibleSheaf_congr hcomap hCW
        (W.zeroSectionDivisor_pow_variableChange C 3).symm]
  rw [W.mk_projModelTwistingSheaf_eq_zpow n, (C • W).mk_projModelTwistingSheaf_eq_zpow n,
    ← LineBundleClass.pullbackHom_apply, map_zpow, LineBundleClass.pullbackHom_apply, h1]

/-! ### Pole sheaves `𝒪(n[0])` and ampleness of the cubic polarisation -/

section PoleSheaf

variable [W.IsElliptic]

/-- The **pole sheaf** `𝒪(n[0])` (`n : ℕ`) on the projective model of an elliptic Weierstrass
curve `W`: the dual of the invertible ideal sheaf `𝒪(-n[0])` of the relative effective Cartier
divisor `n[0]`. -/
noncomputable def poleSheaf (n : ℕ) : InvertibleSheaf W.projModel :=
  (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier.toInvertibleSheaf.dual

/-- `poleSheaf W n` is the dual of the invertible ideal sheaf of `W.zeroSectionDivisor ^ n`. -/
theorem poleSheaf_def (n : ℕ) :
    W.poleSheaf n =
      (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow
        n).isEffectiveCartier.toInvertibleSheaf.dual :=
  (rfl)

/-- In the Picard group of `W.projModel`, `[𝒪(n[0])] = [𝒪([0])] ^ n`. -/
theorem mk_poleSheaf (n : ℕ) :
    LineBundleClass.mk (W.poleSheaf n) = LineBundleClass.mk (W.poleSheaf 1) ^ n := by
  have h₁ := (W.isRelativeEffectiveCartier_zeroSectionDivisor).isEffectiveCartier
  rw [poleSheaf_def, ← LineBundleClass.inv_mk,
    LineBundleClass.mk_toInvertibleSheaf_congr _ (TauCeti.isEffectiveCartier_pow h₁ n) rfl,
    LineBundleClass.mk_toInvertibleSheaf_pow h₁ n, ← inv_pow]
  congr 1
  rw [poleSheaf_def, ← LineBundleClass.inv_mk,
    LineBundleClass.mk_toInvertibleSheaf_congr _ h₁ (pow_one _)]

/-- `𝒪(0[0])` has trivial class in the Picard group of `W.projModel`. -/
@[simp]
theorem mk_poleSheaf_zero : LineBundleClass.mk (W.poleSheaf 0) = 1 := by
  rw [W.mk_poleSheaf 0, pow_zero]

/-- In the Picard group of `W.projModel`, `[𝒪((m + n)[0])] = [𝒪(m[0])] * [𝒪(n[0])]`. -/
theorem mk_poleSheaf_add (m n : ℕ) :
    LineBundleClass.mk (W.poleSheaf (m + n)) =
      LineBundleClass.mk (W.poleSheaf m) * LineBundleClass.mk (W.poleSheaf n) := by
  rw [W.mk_poleSheaf (m + n), W.mk_poleSheaf m, W.mk_poleSheaf n, pow_add]

/-- **Base-change functoriality of `𝒪(n[0])`.** Under `projModelBaseChange W f`, the pole sheaf
`𝒪(n[0])` pulls back in the Picard group to `𝒪(n[0])` of `W.map f`. -/
theorem pullback_mk_poleSheaf {R' : Type u} [CommRing R'] (f : R →+* R') (n : ℕ) :
    LineBundleClass.pullback (W.projModelBaseChange f) (LineBundleClass.mk (W.poleSheaf n)) =
      LineBundleClass.mk ((W.map f).poleSheaf n) := by
  have hW := (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hWf := ((W.map f).isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hcomap : ((W.zeroSectionDivisor ^ n).comap (W.projModelBaseChange f)).IsEffectiveCartier :=
    W.zeroSectionDivisor_pow_map f n ▸ hWf
  rw [poleSheaf_def, poleSheaf_def, ← LineBundleClass.inv_mk, ← LineBundleClass.inv_mk,
    ← LineBundleClass.pullbackHom_apply, map_inv, LineBundleClass.pullbackHom_apply,
    hW.pullback_mk_toInvertibleSheaf hcomap,
    LineBundleClass.mk_toInvertibleSheaf_congr hcomap hWf (W.zeroSectionDivisor_pow_map f n).symm]

/-- **Variable-change invariance of `𝒪(n[0])`.** Under `projModelVariableChangeIso W C`, the pole
sheaf `𝒪(n[0])` pulls back in the Picard group to `𝒪(n[0])` of `C • W`. -/
theorem pullback_mk_poleSheaf_projModelVariableChangeIso (C : VariableChange R) (n : ℕ) :
    LineBundleClass.pullback (W.projModelVariableChangeIso C).hom
        (LineBundleClass.mk (W.poleSheaf n)) =
      LineBundleClass.mk ((C • W).poleSheaf n) := by
  have hW := (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hCW := ((C • W).isRelativeEffectiveCartier_zeroSectionDivisor_pow n).isEffectiveCartier
  have hcomap :
      ((W.zeroSectionDivisor ^ n).comap (W.projModelVariableChangeIso C).hom).IsEffectiveCartier :=
    W.zeroSectionDivisor_pow_variableChange C n ▸ hCW
  rw [poleSheaf_def, poleSheaf_def, ← LineBundleClass.inv_mk, ← LineBundleClass.inv_mk,
    ← LineBundleClass.pullbackHom_apply, map_inv, LineBundleClass.pullbackHom_apply,
    hW.pullback_mk_toInvertibleSheaf hcomap,
    LineBundleClass.mk_toInvertibleSheaf_congr hcomap hCW
      (W.zeroSectionDivisor_pow_variableChange C n).symm]

/-- Dualizing a pairing `L ⊗ M ≅ 𝒪_X` canonically identifies `L.dual` with `M`. -/
private noncomputable def dualIsoOfTensorIsoTrivial {X : Scheme.{u}} {L M : InvertibleSheaf X}
    (e : InvertibleSheaf.tensorProduct L M ≅ InvertibleSheaf.trivial X) : L.dual ≅ M :=
  (InvertibleSheaf.tensorTrivialRightIso L.dual).symm ≪≫
    InvertibleSheaf.tensorProductCongrRight e.symm ≪≫
    (InvertibleSheaf.tensorProductAssoc L.dual L M).symm ≪≫
    InvertibleSheaf.tensorProductCongrLeft
      (InvertibleSheaf.tensorProductComm L.dual L ≪≫ InvertibleSheaf.tensorDualIso L) ≪≫
    InvertibleSheaf.tensorTrivialLeftIso M

/-- **Canonical identification `𝒪(3[0]) ≅ 𝒪(1)`.** Dualizing `𝒪(-3[0]) ≅ 𝒪(-1)` against the
multiplication pairing `𝒪(-1) ⊗ 𝒪(1) ≅ 𝒪(0) ≅ 𝒪_{W.projModel}` canonically identifies the cubic
pole sheaf `𝒪(3[0])` with the hyperplane bundle `𝒪(1)` of `W.projModel`. -/
noncomputable def poleSheafThreeIsoProjModelTwistingSheafOne :
    W.poleSheaf 3 ≅ W.projModelTwistingSheaf 1 :=
  let h₃ := (W.isRelativeEffectiveCartier_zeroSectionDivisor_pow 3).isEffectiveCartier
  let eDiv : h₃.toInvertibleSheaf ≅ W.projModelTwistingSheaf (-1) :=
    ObjectProperty.isoMk (SheafOfModules.isInvertible W.projModel)
      (Scheme.Modules.isoOfSheafIso W.projModel
        (eqToIso h₃.toInvertibleSheaf_obj ≪≫ W.zeroSectionDivisorPowThreeSheafIso))
  let eMul :
      (InvertibleSheaf.tensorProduct (W.projModelTwistingSheaf (-1))
          (W.projModelTwistingSheaf 1)).obj ≅
        (InvertibleSheaf.trivial W.projModel).obj :=
    eqToIso (InvertibleSheaf.tensorProduct_obj
        (W.projModelTwistingSheaf (-1)) (W.projModelTwistingSheaf 1)) ≪≫
      Proj.twistingSheaf.tensorProductIso W.toProjective.coord
        W.toProjective.coord_mem_grading W.iSup_basicOpen_coord_eq_top (-1) 1 ≪≫
      (Proj.unitIsoTwistingSheafZero W.toProjective.grading).symm ≪≫
      (InvertibleSheaf.trivialObjIsoUnit W.projModel).symm
  dualIsoOfTensorIsoTrivial
    (InvertibleSheaf.tensorProductCongrLeft eDiv ≪≫
      ObjectProperty.isoMk (SheafOfModules.isInvertible W.projModel)
        (Scheme.Modules.isoOfSheafIso W.projModel eMul))

/-- **`[𝒪(3[0])] = [𝒪(1)]` in the Picard group of `W.projModel`.** -/
theorem mk_poleSheaf_three :
    LineBundleClass.mk (W.poleSheaf 3) = LineBundleClass.mk (W.projModelTwistingSheaf 1) := by
  rw [poleSheaf_def, ← LineBundleClass.inv_mk,
    LineBundleClass.mk_toInvertibleSheaf_congr _
      W.isEffectiveCartier_zeroSectionDivisor_pow_three rfl,
    W.mk_toInvertibleSheaf_zeroSectionDivisor_pow_three, inv_inv]

/-- **`[𝒪(3m[0])] = [𝒪(m)]` in the Picard group of `W.projModel`.** -/
theorem mk_poleSheaf_three_mul (m : ℕ) :
    LineBundleClass.mk (W.poleSheaf (3 * m)) =
      LineBundleClass.mk (W.projModelTwistingSheaf (m : ℤ)) := by
  rw [W.mk_poleSheaf (3 * m), pow_mul, ← W.mk_poleSheaf 3, W.mk_poleSheaf_three,
    W.mk_projModelTwistingSheaf_eq_zpow (m : ℤ), zpow_natCast]

/-- Every multiple `𝒪(3m[0])` (`m : ℕ`) of the cubic pole sheaf is globally generated on
`W.projModel`. -/
theorem isGloballyGenerated_poleSheaf_three_mul (m : ℕ) :
    (W.poleSheaf (3 * m)).IsGloballyGenerated := by
  obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.mp (W.mk_poleSheaf_three_mul m)
  exact (InvertibleSheaf.isGloballyGenerated_iff_of_iso e).mpr
    (W.isGloballyGenerated_projModelTwistingSheaf m)

/-- **Ampleness of the pole sheaves `𝒪(n[0])`.** For every elliptic Weierstrass curve `W` over any
commutative ring `R` and every `n > 0`, the pole sheaf `𝒪(n[0])` is ample on `W.projModel`: its
cube `𝒪(3n[0])` is isomorphic to the positive twisting sheaf `𝒪(n)`. -/
theorem isAmple_poleSheaf {n : ℕ} (hn : 0 < n) :
    (LineBundleClass.mk (W.poleSheaf n)).IsAmple := by
  have h3 : (LineBundleClass.mk (W.poleSheaf 1) ^ 3).IsAmple := by
    rw [← W.mk_poleSheaf 3, W.mk_poleSheaf_three]
    exact W.isAmple_projModelTwistingSheaf (by decide : 0 < 1)
  rw [W.mk_poleSheaf n]
  exact (LineBundleClass.IsAmple.of_pow (by decide : 0 < 3) h3).pow hn

end PoleSheaf

end WeierstrassCurve
