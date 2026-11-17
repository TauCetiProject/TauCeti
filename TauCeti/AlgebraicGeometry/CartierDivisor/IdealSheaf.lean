/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Basic
public import TauCeti.AlgebraicGeometry.CartierDivisor.Picard
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.ZeroLocus

/-!
# The ideal sheaf of an effective Cartier divisor

On an integral scheme, an effective Cartier divisor given by rational local equations
cuts out a closed subscheme with invertible ideal sheaf (`IsEffective.idealSheaf`). Its ideal is
`𝒪_X(-D)`, and hence its ideal line-bundle class is the inverse of the class of `𝒪_X(D)`.

Conversely, any effective Cartier ideal sheaf `I` (`I.IsEffectiveCartier`) determines a global
effective Cartier divisor `hI.toCartierDivisor` by gluing its local nonzerodivisor generators in the
Cartier-divisor sheaf `𝒦_X^× / 𝒪_X^×`. Taking ideal sheaves and Cartier divisors are mutually
inverse (`hI.idealSheaf_toCartierDivisor` and `hD.toCartierDivisor_idealSheaf`), compatible with
the monoid operations on effective Cartier ideal sheaves (`toCartierDivisor_top`,
`toCartierDivisor_mul`, `toCartierDivisor_pow`, `toCartierDivisor_prod`), and satisfy
`hI.toCartierDivisor.toLineBundleClass = (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹`.

This comparison allows computations with rational Cartier divisors to be used with the
closed-subscheme restriction sequences for effective Cartier divisors. No regularity,
dimension or Noetherian hypothesis is imposed on the integral scheme.

## References

* R. Hartshorne, *Algebraic Geometry*, Section II.6.
* The Stacks Project, *Divisors*, Tag 01WQ.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

universe u

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X] {D : CartierDivisor X}

/-- The closed-subscheme ideal sheaf of an effective Cartier divisor, with ideal module
`𝒪_X(-D)`. -/
def IsEffective.idealSheaf (hD : D.IsEffective) : X.IdealSheafData :=
  hD.sheafToUnit.imageIdealSheaf

/-- The ideal sheaf of an effective Cartier divisor is canonically `𝒪_X(-D)`. -/
def IsEffective.idealSheafIso (hD : D.IsEffective) : (-D).sheaf ≅ hD.idealSheaf.sheaf :=
  hD.sheafToUnit.imageIdealSheafIso

/-- The ideal-sheaf isomorphism respects the inclusions into rational functions. -/
@[simp, reassoc]
lemma IsEffective.idealSheafIso_hom_ι (hD : D.IsEffective) :
    hD.idealSheafIso.hom ≫ hD.idealSheaf.sheafι ≫ Scheme.toRationalFunctions X =
      (-D).sheafι := by
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ Scheme.toRationalFunctions X)
      hD.sheafToUnit.imageIdealSheafIso_hom_ι).trans hD.sheafToUnit_toRationalFunctions

/-- A regular function belongs to the ideal of `D` exactly when, as a rational section,
it belongs to `𝒪_X(-D)`. This holds on arbitrary opens. -/
@[simp]
lemma IsEffective.mem_idealSheaf_sections_iff (hD : D.IsEffective) (U : X.Opens)
    (a : Γ(X, U)) :
    a ∈ hD.idealSheaf.sections U ↔
      (Scheme.toRationalFunctions X).app U a ∈ (-D).sections U := by
  have hm : a ∈ hD.idealSheaf.sections U ↔ ∃ t, hD.sheafToUnit.app U t = a := by
    rw [IsEffective.idealSheaf, Scheme.Modules.Hom.imageIdealSheaf_sections,
      Scheme.Modules.Hom.mem_imageIdeal]
  refine hm.trans ⟨?_, ?_⟩
  · rintro ⟨t, rfl⟩
    exact (hD.toRationalFunctions_app_sheafToUnit_app U t).symm ▸ (-D).sheafι_app_mem U t
  · intro ha
    refine ⟨sectionMk _ ha, Scheme.toRationalFunctions_app_injective U ?_⟩
    exact (hD.toRationalFunctions_app_sheafToUnit_app U _).trans (sheafι_app_sectionMk _ ha)

/-- On an affine open, the ideal is characterized by membership in `𝒪_X(-D)`. -/
@[simp]
lemma IsEffective.mem_idealSheaf_ideal_iff (hD : D.IsEffective) (U : X.affineOpens)
    (a : Γ(X, U)) :
    a ∈ hD.idealSheaf.ideal U ↔
      (Scheme.toRationalFunctions X).app U.1 a ∈ (-D).sections U.1 :=
  (congrArg (a ∈ ·) (hD.idealSheaf.sections_eq_ideal U)).to_iff.symm.trans
    (hD.mem_idealSheaf_sections_iff U.1 a)

/-- On an affine open carrying a regular equation `a` of `D`, the ideal of the
closed subscheme is exactly `(a)`. -/
lemma IsEffective.idealSheaf_ideal_eq_span (hD : D.IsEffective) (U : X.affineOpens)
    [Nonempty U.1] {f : X.functionFieldˣ}
    (hf : Scheme.rationalUnitClass X U.1 (Additive.ofMul f) = D |_ U.1)
    {a : Γ(X, U)} (ha : X.germToFunctionField U.1 a = f) :
    hD.idealSheaf.ideal U = Ideal.span {a} := by
  ext s
  rw [hD.mem_idealSheaf_ideal_iff,
    mem_sections_iff_of_rationalUnitClass_eq le_rfl (rationalUnitClass_inv_eq_neg_of_eq hf),
    Scheme.rationalFunctionsEquiv_toRationalFunctions_app, Ideal.mem_span_singleton']
  refine exists_congr fun b ↦ ?_
  rw [← (X.germToFunctionField_injective U.1).eq_iff, map_mul, ha]
  exact ⟨fun h ↦ by rw [h]; simp [mul_comm],
    fun h ↦ by rw [← h]; simp [mul_comm]⟩

/-- The zero Cartier divisor cuts out the empty closed subscheme. -/
@[simp]
lemma IsEffective.idealSheaf_zero (h : (0 : CartierDivisor X).IsEffective) :
    h.idealSheaf = ⊤ := by
  apply Scheme.IdealSheafData.ext
  funext U
  apply eq_top_iff.mpr
  intro a _
  apply (h.mem_idealSheaf_ideal_iff U a).mpr
  simpa using (isEffective_iff_toRationalFunctions_mem_sections.mp isEffective_zero U.1 a)

/-- The ideal obtained from rational local equations is an effective Cartier ideal sheaf. -/
theorem IsEffective.isEffectiveCartier_idealSheaf (hD : D.IsEffective) :
    hD.idealSheaf.IsEffectiveCartier :=
  InvertibleSheaf.isEffectiveCartier_imageIdealSheaf
    ⟨(-D).sheaf, isInvertible_sheaf (-D)⟩ hD.sheafToUnit

/-- The ideal line bundle of the closed subscheme cut out by `D` has class `[𝒪_X(D)]⁻¹`.
In particular its dual, the bundle used by the effective-divisor Abel map, has class `[𝒪_X(D)]`. -/
theorem IsEffective.mk_idealSheaf_eq_inv (hD : D.IsEffective) :
    LineBundleClass.mk hD.isEffectiveCartier_idealSheaf.toInvertibleSheaf =
      D.toLineBundleClass⁻¹ := by
  let L : InvertibleSheaf X := ⟨(-D).sheaf, isInvertible_sheaf (-D)⟩
  have hclass : (-D).toLineBundleClass = LineBundleClass.mk L :=
    toLineBundleClass_eq_mk_iff.mpr ⟨Iso.refl _⟩
  exact (L.mk_toInvertibleSheaf_imageIdealSheaf hD.sheafToUnit).trans
    (hclass.symm.trans (toLineBundleClass_neg D))

end

end TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable section

/-- Two nonzero sections generating the same ideal sheaf on affine opens have the same Cartier
class on any nonempty open contained in their intersection. -/
private lemma rationalUnitClass_eq_of_ideal_eq_span {I : X.IdealSheafData}
    {U V : X.affineOpens} [Nonempty U.1] [Nonempty V.1]
    {a : Γ(X, U)} (ha : a ≠ 0) (hIa : I.ideal U = Ideal.span {a})
    {b : Γ(X, V)} (hb : b ≠ 0) (hIb : I.ideal V = Ideal.span {b})
    {W : X.Opens} [Nonempty W] (hWU : W ≤ U.1) (hWV : W ≤ V.1) :
    Scheme.rationalUnitClass X W
        (Additive.ofMul (Units.mk0 (X.germToFunctionField U.1 a)
          ((map_ne_zero_iff _ (X.germToFunctionField_injective U.1)).mpr ha))) =
      Scheme.rationalUnitClass X W
        (Additive.ofMul (Units.mk0 (X.germToFunctionField V.1 b)
          ((map_ne_zero_iff _ (X.germToFunctionField_injective V.1)).mpr hb))) := by
  set fa := Units.mk0 (X.germToFunctionField U.1 a)
    ((map_ne_zero_iff _ (X.germToFunctionField_injective U.1)).mpr ha)
  set fb := Units.mk0 (X.germToFunctionField V.1 b)
    ((map_ne_zero_iff _ (X.germToFunctionField_injective V.1)).mpr hb)
  obtain ⟨c, hc⟩ := I.exists_mul_eq_of_ideal_eq_span (IsSMulRegular.of_ne_zero hb) hIb hWV
    (I.map_mem_sections (homOfLE hWU) (I.mem_sections_of_ideal_eq_span hIa))
  obtain ⟨d, hd⟩ := I.exists_mul_eq_of_ideal_eq_span (IsSMulRegular.of_ne_zero ha) hIa hWU
    (I.map_mem_sections (homOfLE hWV) (I.mem_sections_of_ideal_eq_span hIb))
  have haW : X.germToFunctionField W (X.presheaf.map (homOfLE hWU).op a) =
      X.germToFunctionField U.1 a :=
    X.presheaf.germ_res_apply (homOfLE hWU) (genericPoint X) (Scheme.genericPoint_mem W) a
  have hbW : X.germToFunctionField W (X.presheaf.map (homOfLE hWV).op b) =
      X.germToFunctionField V.1 b :=
    X.presheaf.germ_res_apply (homOfLE hWV) (genericPoint X) (Scheme.genericPoint_mem W) b
  have hca : X.germToFunctionField W c * X.germToFunctionField V.1 b =
      X.germToFunctionField U.1 a := by
    rw [← hbW, ← haW, ← map_mul, mul_comm, hc]
  have hdb : X.germToFunctionField W d * X.germToFunctionField U.1 a =
      X.germToFunctionField V.1 b := by
    rw [← haW, ← hbW, ← map_mul, mul_comm, hd]
  have hcd : c * d = 1 := X.germToFunctionField_injective W <| by
    refine mul_right_cancel₀ ((map_ne_zero_iff _ (X.germToFunctionField_injective U.1)).mpr ha) ?_
    rw [map_mul, mul_assoc, hdb, hca, map_one, one_mul]
  let u : Γ(X, W)ˣ := ⟨c, d, hcd, (mul_comm d c).trans hcd⟩
  exact (Scheme.rationalUnitClass_eq_rationalUnitClass_iff X W fa fb).mpr
    ⟨u, Units.ext (by simpa [Scheme.regularUnitToFunctionField_apply, fa, fb] using hca)⟩

/-- **Unique Cartier divisor of an effective Cartier ideal sheaf.** On an integral scheme, an
effective Cartier ideal sheaf `I` has a unique global Cartier divisor restricting on every nonempty
affine open where `I = (b)` to the Cartier class of `b`. -/
theorem IsEffectiveCartier.existsUnique_cartierDivisor {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) :
    ∃! D : Scheme.CartierDivisor X,
      ∀ (V : X.affineOpens) [Nonempty V.1] {b : Γ(X, V)} (hb : b ≠ 0),
        I.ideal V = Ideal.span {b} →
        D |_ V.1 = Scheme.rationalUnitClass X V.1
          (Additive.ofMul (Units.mk0 (X.germToFunctionField V.1 b)
            ((map_ne_zero_iff _ (X.germToFunctionField_injective V.1)).mpr hb))) := by
  choose U hxU a ha hUa using (isEffectiveCartier_iff I).mp hI
  have hne : ∀ x, Nonempty (U x).1 := fun x ↦ ⟨⟨x, hxU x⟩⟩
  have ha0 : ∀ x, a x ≠ 0 := fun x ↦ (ha x).isLeftRegular.ne_zero
  let sf : ∀ x, ((Scheme.cartierDivisorSheaf X).obj.obj (op (U x).1) : Type u) :=
    fun x ↦ Scheme.rationalUnitClass X (U x).1 (Additive.ofMul
      (Units.mk0 (X.germToFunctionField (U x).1 (a x))
        ((map_ne_zero_iff _ (X.germToFunctionField_injective (U x).1)).mpr (ha0 x))))
  have hcompat : TopCat.Presheaf.IsCompatible (Scheme.cartierDivisorSheaf X).obj
      (fun x ↦ (U x).1) sf := by
    intro x y
    have : Nonempty ((U x).1 ⊓ (U y).1 : X.Opens) :=
      ⟨⟨genericPoint X, Scheme.genericPoint_mem (U x).1, Scheme.genericPoint_mem (U y).1⟩⟩
    -- Unfold the presheaf restriction map on `cartierDivisorSheaf` to the `|_` notation.
    change sf x |_ ((U x).1 ⊓ (U y).1) = sf y |_ ((U x).1 ⊓ (U y).1)
    rw [Scheme.rationalUnitClass_restrict X inf_le_left,
      Scheme.rationalUnitClass_restrict X inf_le_right]
    exact rationalUnitClass_eq_of_ideal_eq_span (ha0 x) (hUa x) (ha0 y) (hUa y)
      inf_le_left inf_le_right
  have htop : (⊤ : X.Opens) ≤ ⨆ x, (U x).1 := fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩
  obtain ⟨D, hD, huniq⟩ := (Scheme.cartierDivisorSheaf X).existsUnique_gluing'
    (fun x ↦ (U x).1) ⊤ (fun _ ↦ homOfLE le_top) htop sf hcompat
  have hD' : ∀ x, D |_ (U x).1 = sf x := hD
  refine ⟨D, fun V _ b hb hVb ↦ ?_, fun E hE ↦ huniq E fun x ↦ hE (U x) (ha0 x) (hUa x)⟩
  let W : V.1 → X.Opens := fun y ↦ V.1 ⊓ (U y.1).1
  have hcover : V.1 ≤ ⨆ y : V.1, W y := fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hx, hxU x⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (Scheme.cartierDivisorSheaf X) W V.1
    (fun _ ↦ homOfLE inf_le_left) hcover _ _ fun y ↦ ?_
  have : Nonempty (W y) := ⟨⟨y.1, y.2, hxU y.1⟩⟩
  -- Unfold the presheaf restriction map on `cartierDivisorSheaf` to the `|_` notation.
  change (D |_ V.1) |_ W y = (Scheme.rationalUnitClass X V.1 _) |_ W y
  rw [TopCat.Presheaf.restrict_restrict, ← TopCat.Presheaf.restrict_restrict inf_le_right le_top,
    hD' y.1, Scheme.rationalUnitClass_restrict X inf_le_right,
    Scheme.rationalUnitClass_restrict X inf_le_left]
  exact rationalUnitClass_eq_of_ideal_eq_span (ha0 y.1) (hUa y.1) hb hVb inf_le_right inf_le_left

/-- **The Cartier divisor of an effective Cartier ideal sheaf.** On an integral scheme, an effective
Cartier ideal sheaf `I` determines a global Cartier divisor by gluing the classes of its local
nonzerodivisor equations in `𝒦_X^× / 𝒪_X^×`. -/
def IsEffectiveCartier.toCartierDivisor {I : X.IdealSheafData} (hI : I.IsEffectiveCartier) :
    Scheme.CartierDivisor X :=
  hI.existsUnique_cartierDivisor.choose

/-- On any nonempty affine open where `I` is generated by a nonzero section `b`, the Cartier divisor
`hI.toCartierDivisor` restricts to the Cartier class of `b`. -/
theorem IsEffectiveCartier.toCartierDivisor_restrict {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) (V : X.affineOpens) [Nonempty V.1]
    {b : Γ(X, V)} (hb : b ≠ 0) (hVb : I.ideal V = Ideal.span {b}) :
    hI.toCartierDivisor |_ V.1 = Scheme.rationalUnitClass X V.1
      (Additive.ofMul (Units.mk0 (X.germToFunctionField V.1 b)
        ((map_ne_zero_iff _ (X.germToFunctionField_injective V.1)).mpr hb))) :=
  hI.existsUnique_cartierDivisor.choose_spec.1 V hb hVb

/-- A global Cartier divisor restricting on every nonempty affine open where `I = (b)` to the
Cartier class of `b` equals `hI.toCartierDivisor`. -/
theorem IsEffectiveCartier.eq_toCartierDivisor {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) {D : Scheme.CartierDivisor X}
    (hD : ∀ (V : X.affineOpens) [Nonempty V.1] {b : Γ(X, V)} (hb : b ≠ 0),
      I.ideal V = Ideal.span {b} →
      D |_ V.1 = Scheme.rationalUnitClass X V.1
        (Additive.ofMul (Units.mk0 (X.germToFunctionField V.1 b)
          ((map_ne_zero_iff _ (X.germToFunctionField_injective V.1)).mpr hb)))) :
    D = hI.toCartierDivisor :=
  hI.existsUnique_cartierDivisor.choose_spec.2 D hD

/-- The Cartier divisor attached to an effective Cartier ideal sheaf is effective. -/
theorem IsEffectiveCartier.isEffective_toCartierDivisor {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) : hI.toCartierDivisor.IsEffective := by
  refine Scheme.CartierDivisor.isEffective_iff_exists.mpr fun x ↦ ?_
  obtain ⟨U, hxU, a, ha, hUa⟩ := (isEffectiveCartier_iff I).mp hI x
  have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  have ha0 : a ≠ 0 := ha.isLeftRegular.ne_zero
  refine ⟨Units.mk0 (X.germToFunctionField U.1 a)
      ((map_ne_zero_iff _ (X.germToFunctionField_injective U.1)).mpr ha0),
    Scheme.CartierDivisor.isLocalEquationAt_iff.mpr
      ⟨U.1, hxU, (hI.toCartierDivisor_restrict U ha0 hUa).symm⟩,
    X.presheaf.germ U.1 x hxU a, ?_⟩
  exact X.algebraMap_germ_eq_germToFunctionField hxU a

/-- Taking the closed-subscheme ideal sheaf of `hI.toCartierDivisor` recovers `I`. -/
@[simp]
theorem IsEffectiveCartier.idealSheaf_toCartierDivisor {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) :
    hI.isEffective_toCartierDivisor.idealSheaf = I := by
  choose U hxU a ha hUa using (isEffectiveCartier_iff I).mp hI
  refine ext_of_iSup_eq_top U (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩) fun x ↦ ?_
  have : Nonempty (U x).1 := ⟨⟨x, hxU x⟩⟩
  have ha0 : a x ≠ 0 := (ha x).isLeftRegular.ne_zero
  rw [hUa x]
  exact hI.isEffective_toCartierDivisor.idealSheaf_ideal_eq_span (U x)
    (hI.toCartierDivisor_restrict (U x) ha0 (hUa x)).symm rfl

/-- Two effective Cartier ideal sheaves determine the same Cartier divisor if and only if they are
equal. -/
@[simp]
theorem IsEffectiveCartier.toCartierDivisor_eq_iff {I J : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier) :
    hI.toCartierDivisor = hJ.toCartierDivisor ↔ I = J := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  have hcongr {D E : Scheme.CartierDivisor X} (hD : D.IsEffective) (hE : E.IsEffective)
      (hDE : D = E) : hD.idealSheaf = hE.idealSheaf := by
    subst hDE
    rfl
  rw [← hI.idealSheaf_toCartierDivisor, ← hJ.idealSheaf_toCartierDivisor]
  exact hcongr _ _ h

/-- The line-bundle class of `hI.toCartierDivisor` is the inverse of the class of the invertible
ideal sheaf `I`. -/
@[simp]
theorem IsEffectiveCartier.toLineBundleClass_toCartierDivisor {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) :
    hI.toCartierDivisor.toLineBundleClass = (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ := by
  rw [← LineBundleClass.mk_toInvertibleSheaf_congr
      hI.isEffective_toCartierDivisor.isEffectiveCartier_idealSheaf hI
      hI.idealSheaf_toCartierDivisor,
    hI.isEffective_toCartierDivisor.mk_idealSheaf_eq_inv, inv_inv]

/-- The unit ideal sheaf corresponds to the zero Cartier divisor. -/
@[simp]
theorem IsEffectiveCartier.toCartierDivisor_top :
    (isEffectiveCartier_top X).toCartierDivisor = 0 := by
  refine ((isEffectiveCartier_top X).eq_toCartierDivisor fun V _ b hb hVb ↦ ?_).symm
  rw [ideal_top, Pi.top_apply, eq_comm, Ideal.span_singleton_eq_top] at hVb
  obtain ⟨u, rfl⟩ := hVb
  have h0 : (0 : Scheme.CartierDivisor X) |_ V.1 = 0 := map_zero _
  have hu : Units.map (X.germToFunctionField V.1).hom u =
      Units.mk0 (X.germToFunctionField V.1 ↑u)
        ((map_ne_zero_iff _ (X.germToFunctionField_injective V.1)).mpr hb) :=
    Units.ext rfl
  rw [h0, ← hu, Scheme.rationalUnitClass_germToFunctionField_eq_zero]

/-- The Cartier divisor of a product of effective Cartier ideal sheaves is the sum of their Cartier
divisors. -/
@[simp]
theorem IsEffectiveCartier.toCartierDivisor_mul {I J : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier) :
    (TauCeti.isEffectiveCartier_mul hI hJ).toCartierDivisor =
      hI.toCartierDivisor + hJ.toCartierDivisor := by
  have hlocal : ∀ x : X, ∃ W : X.affineOpens, x ∈ W.1 ∧
      (TauCeti.isEffectiveCartier_mul hI hJ).toCartierDivisor |_ W.1 =
        (hI.toCartierDivisor + hJ.toCartierDivisor) |_ W.1 := by
    intro x
    obtain ⟨U₁, hxU₁, a₁, ha₁, hIa₁⟩ := (isEffectiveCartier_iff I).mp hI x
    obtain ⟨U₂, hxU₂, a₂, ha₂, hJa₂⟩ := (isEffectiveCartier_iff J).mp hJ x
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (⟨hxU₁, hxU₂⟩ : x ∈ U₁.1 ⊓ U₂.1) (U₁.1 ⊓ U₂.1).isOpen
    replace hWU : W ≤ U₁.1 ⊓ U₂.1 := hWU
    have hWU₁ : W ≤ U₁.1 := hWU.trans inf_le_left
    have hWU₂ : W ≤ U₂.1 := hWU.trans inf_le_right
    have : Nonempty W := ⟨⟨x, hxW⟩⟩
    set b₁ := X.presheaf.map (homOfLE hWU₁).op a₁
    set b₂ := X.presheaf.map (homOfLE hWU₂).op a₂
    have hb₁ : b₁ ≠ 0 := (U₁.2.isSMulRegular_map hWU₁ ha₁).isLeftRegular.ne_zero
    have hb₂ : b₂ ≠ 0 := (U₂.2.isSMulRegular_map hWU₂ ha₂).isLeftRegular.ne_zero
    have hIW : I.ideal ⟨W, hW⟩ = Ideal.span {b₁} := by
      rw [← I.map_ideal (U := ⟨W, hW⟩) (V := U₁) hWU₁, hIa₁, Ideal.map_span, Set.image_singleton]
      rfl
    have hJW : J.ideal ⟨W, hW⟩ = Ideal.span {b₂} := by
      rw [← J.map_ideal (U := ⟨W, hW⟩) (V := U₂) hWU₂, hJa₂, Ideal.map_span, Set.image_singleton]
      rfl
    have hIJW : (I * J).ideal ⟨W, hW⟩ = Ideal.span {b₁ * b₂} := by
      rw [ideal_mul, Pi.mul_apply, hIW, hJW, Ideal.span_singleton_mul_span_singleton]
    refine ⟨⟨W, hW⟩, hxW, ?_⟩
    have hadd : (hI.toCartierDivisor + hJ.toCartierDivisor) |_ W =
        (hI.toCartierDivisor |_ W) + (hJ.toCartierDivisor |_ W) :=
      map_add ((Scheme.cartierDivisorSheaf X).obj.map (homOfLE (le_top : W ≤ ⊤)).op).hom _ _
    rw [(TauCeti.isEffectiveCartier_mul hI hJ).toCartierDivisor_restrict ⟨W, hW⟩
        (mul_ne_zero hb₁ hb₂) hIJW,
      hadd, hI.toCartierDivisor_restrict ⟨W, hW⟩ hb₁ hIW,
      hJ.toCartierDivisor_restrict ⟨W, hW⟩ hb₂ hJW, ← map_add, ← ofMul_mul]
    congr 2
    exact Units.ext (map_mul (X.germToFunctionField W).hom b₁ b₂)
  choose W hxW hW using hlocal
  have hcover : (⊤ : X.Opens) ≤ ⨆ x, (W x).1 := fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩
  exact TopCat.Sheaf.eq_of_locally_eq' (Scheme.cartierDivisorSheaf X) (fun x ↦ (W x).1) ⊤
    (fun _ ↦ homOfLE le_top) hcover _ _ hW

/-- The Cartier divisor of the `n`-th power of an effective Cartier ideal sheaf is `n` times its
Cartier divisor. -/
@[simp]
theorem IsEffectiveCartier.toCartierDivisor_pow {I : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) (n : ℕ) :
    (TauCeti.isEffectiveCartier_pow hI n).toCartierDivisor = n • hI.toCartierDivisor := by
  induction n with
  | zero =>
    have h0 : (TauCeti.isEffectiveCartier_pow hI 0).toCartierDivisor =
        (isEffectiveCartier_top X).toCartierDivisor :=
      ((TauCeti.isEffectiveCartier_pow hI 0).toCartierDivisor_eq_iff _).mpr
        (by rw [pow_zero, one_eq_top])
    rw [h0, toCartierDivisor_top, zero_smul]
  | succ n ih =>
    have hsucc : (TauCeti.isEffectiveCartier_pow hI (n + 1)).toCartierDivisor =
        (TauCeti.isEffectiveCartier_mul (TauCeti.isEffectiveCartier_pow hI n)
          hI).toCartierDivisor :=
      ((TauCeti.isEffectiveCartier_pow hI (n + 1)).toCartierDivisor_eq_iff _).mpr (pow_succ I n)
    rw [hsucc, toCartierDivisor_mul (TauCeti.isEffectiveCartier_pow hI n) hI, ih, succ_nsmul]

/-- The Cartier divisor of a finite product of effective Cartier ideal sheaves is the sum of their
Cartier divisors. -/
@[simp]
theorem IsEffectiveCartier.toCartierDivisor_prod {ι : Type*} (s : Finset ι)
    {I : ι → X.IdealSheafData} (hI : ∀ i ∈ s, (I i).IsEffectiveCartier) :
    (TauCeti.isEffectiveCartier_prod hI).toCartierDivisor =
      ∑ i ∈ s.attach, (hI i i.2).toCartierDivisor := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hemp : (TauCeti.isEffectiveCartier_prod hI).toCartierDivisor =
        (isEffectiveCartier_top X).toCartierDivisor :=
      ((TauCeti.isEffectiveCartier_prod hI).toCartierDivisor_eq_iff _).mpr
        (by rw [Finset.prod_empty, one_eq_top])
    rw [hemp, toCartierDivisor_top, Finset.attach_empty, Finset.sum_empty]
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, (I j).IsEffectiveCartier := fun j hj ↦ hI j (Finset.mem_insert_of_mem hj)
    have hins : (TauCeti.isEffectiveCartier_prod hI).toCartierDivisor =
        (TauCeti.isEffectiveCartier_mul (hI i (Finset.mem_insert_self i s))
          (TauCeti.isEffectiveCartier_prod hs)).toCartierDivisor :=
      ((TauCeti.isEffectiveCartier_prod hI).toCartierDivisor_eq_iff _).mpr (Finset.prod_insert hi)
    rw [hins, toCartierDivisor_mul (hI i (Finset.mem_insert_self i s))
        (TauCeti.isEffectiveCartier_prod hs), ih hs, Finset.attach_insert, Finset.sum_insert,
      Finset.sum_image]
    · exact fun x _ y _ h ↦ Subtype.ext (congrArg Subtype.val h :)
    · simpa using hi

end

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X] {D : CartierDivisor X}

/-- Taking the Cartier divisor of the closed-subscheme ideal sheaf of an effective Cartier divisor
recovers `D`. -/
@[simp]
theorem IsEffective.toCartierDivisor_idealSheaf (hD : D.IsEffective) :
    hD.isEffectiveCartier_idealSheaf.toCartierDivisor = D := by
  have hlocal : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      hD.isEffectiveCartier_idealSheaf.toCartierDivisor |_ U.1 = D |_ U.1 := by
    intro x
    obtain ⟨f, hf, c, hc⟩ := isEffective_iff_exists.mp hD x
    obtain ⟨W, hxW, c', rfl⟩ := X.presheaf.exists_germ_eq c
    obtain ⟨V, hxV, hV⟩ := isLocalEquationAt_iff.mp hf
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (⟨hxV, hxW⟩ : x ∈ V ⊓ W) (V ⊓ W).isOpen
    replace hUVW : U ≤ V ⊓ W := hUVW
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    set a := X.presheaf.map (homOfLE (hUVW.trans inf_le_right)).op c'
    have ha : X.germToFunctionField U a = f := by
      rw [← _root_.AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField X hxU, ← hc]
      exact congrArg _ (X.presheaf.germ_res_apply _ x hxU c')
    have ha0 : a ≠ 0 := fun h ↦ f.ne_zero (by rw [← ha, h, map_zero])
    have hDU : Scheme.rationalUnitClass X U (Additive.ofMul f) = D |_ U :=
      rationalUnitClass_eq_of_le (hUVW.trans inf_le_left) hV
    have hspan : hD.idealSheaf.ideal ⟨U, hU⟩ = Ideal.span {a} :=
      hD.idealSheaf_ideal_eq_span ⟨U, hU⟩ hDU ha
    refine ⟨⟨U, hU⟩, hxU, ?_⟩
    rw [hD.isEffectiveCartier_idealSheaf.toCartierDivisor_restrict ⟨U, hU⟩ ha0 hspan, ← hDU]
    congr 2
    exact Units.ext ha
  choose U hxU hU using hlocal
  have hcover : (⊤ : X.Opens) ≤ ⨆ x, (U x).1 := fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩
  exact TopCat.Sheaf.eq_of_locally_eq' (Scheme.cartierDivisorSheaf X) (fun x ↦ (U x).1) ⊤
    (fun _ ↦ homOfLE le_top) hcover _ _ hU

end

end TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
