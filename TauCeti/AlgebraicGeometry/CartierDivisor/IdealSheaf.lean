/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Basic
public import TauCeti.AlgebraicGeometry.CartierDivisor.Picard
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.ZeroLocus
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# The ideal sheaf of an effective Cartier divisor

On an integral scheme, an effective Cartier divisor given by rational local equations
cuts out a closed subscheme with invertible ideal sheaf. Its ideal is `𝒪_X(-D)`, and
hence its ideal line-bundle class is the inverse of the class of `𝒪_X(D)`.

This comparison allows computations with rational Cartier divisors to be used with the
closed-subscheme restriction sequences for effective Cartier divisors. No regularity,
dimension or Noetherian hypothesis is imposed on the integral scheme.

Conversely, `ofEffectiveCartier` glues local regular equations of any effective Cartier ideal
sheaf `I` into an effective Cartier divisor recovering `I`, with `[ofEffectiveCartier hI] = [I]⁻¹`
and additivity under ideal-sheaf multiplication (`ofEffectiveCartier_mul`).

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
      (Scheme.toRationalFunctions X).app U.val a ∈ (-D).sections U.val :=
  (congrArg (a ∈ ·) (hD.idealSheaf.sections_eq_ideal U)).to_iff.symm.trans
    (hD.mem_idealSheaf_sections_iff U.val a)

/-- On an affine open carrying a regular equation `a` of `D`, the ideal of the
closed subscheme is exactly `(a)`. -/
lemma IsEffective.idealSheaf_ideal_eq_span (hD : D.IsEffective) (U : X.affineOpens)
    [Nonempty U.val] {f : X.functionFieldˣ}
    (hf : Scheme.rationalUnitClass X U.val (Additive.ofMul f) = D |_ U.val)
    {a : Γ(X, U)} (ha : X.germToFunctionField U.val a = f) :
    hD.idealSheaf.ideal U = Ideal.span {a} := by
  ext s
  rw [hD.mem_idealSheaf_ideal_iff,
    mem_sections_iff_of_rationalUnitClass_eq le_rfl (rationalUnitClass_inv_eq_neg_of_eq hf),
    Scheme.rationalFunctionsEquiv_toRationalFunctions_app, Ideal.mem_span_singleton']
  refine exists_congr fun b ↦ ?_
  rw [← (X.germToFunctionField_injective U.val).eq_iff, map_mul, ha]
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
  simpa using (isEffective_iff_toRationalFunctions_mem_sections.mp isEffective_zero U.val a)

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

/-! ### The Cartier divisor of an effective Cartier ideal sheaf -/

section OfEffectiveCartier

variable {I J : X.IdealSheafData}

/-- Two Cartier divisors that agree on an affine open cover of `X` are equal. -/
private lemma eq_of_locally_eq_affine {D₁ D₂ : CartierDivisor X}
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧ D₁ |_ U.val = D₂ |_ U.val) : D₁ = D₂ := by
  choose U hxU hU using h
  refine (Scheme.cartierDivisorSheaf X).eq_of_locally_eq' (fun x ↦ (U x).val) ⊤
    (fun _ ↦ homOfLE le_top) (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩) _ _ fun x ↦ ?_
  simpa only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] using hU x

/-- If `I` is generated on affine opens `U` and `V` by regular sections `a` and `b`, then on any
nonempty `W ≤ U ⊓ V` their images in the function field have the same Cartier-divisor class. -/
private lemma rationalUnitClass_eq_of_ideal_eq_span {U V : X.affineOpens} {W : X.Opens}
    [Nonempty U.val] [Nonempty V.val] [Nonempty W] (hWU : W ≤ U.val) (hWV : W ≤ V.val)
    {a : Γ(X, U)} {b : Γ(X, V)} (ha : IsSMulRegular Γ(X, U) a) (hb : IsSMulRegular Γ(X, V) b)
    (hIa : I.ideal U = Ideal.span {a}) (hIb : I.ideal V = Ideal.span {b})
    (fa fb : X.functionFieldˣ) (hfa : X.germToFunctionField U.val a = fa)
    (hfb : X.germToFunctionField V.val b = fb) :
    Scheme.rationalUnitClass X W (Additive.ofMul fa) =
      Scheme.rationalUnitClass X W (Additive.ofMul fb) := by
  obtain ⟨u, hu⟩ := I.exists_mul_eq_of_ideal_eq_span ha hIa hWU
    (I.map_mem_sections (homOfLE hWV) (I.mem_sections_of_ideal_eq_span hIb))
  obtain ⟨v, hv⟩ := I.exists_mul_eq_of_ideal_eq_span hb hIb hWV
    (I.map_mem_sections (homOfLE hWU) (I.mem_sections_of_ideal_eq_span hIa))
  have hfaW : X.germToFunctionField W (X.presheaf.map (homOfLE hWU).op a) = fa :=
    (X.presheaf.germ_res_apply (homOfLE hWU) (genericPoint X) (Scheme.genericPoint_mem W) a).trans
      hfa
  have hfbW : X.germToFunctionField W (X.presheaf.map (homOfLE hWV).op b) = fb :=
    (X.presheaf.germ_res_apply (homOfLE hWV) (genericPoint X) (Scheme.genericPoint_mem W) b).trans
      hfb
  have hu' : X.germToFunctionField W u * fa = fb := by
    have := congrArg (X.germToFunctionField W) hu; rwa [map_mul, hfaW, hfbW, mul_comm] at this
  have hv' : X.germToFunctionField W v * fb = fa := by
    have := congrArg (X.germToFunctionField W) hv; rwa [map_mul, hfbW, hfaW, mul_comm] at this
  have huv : u * v = 1 := X.germToFunctionField_injective W <| mul_right_cancel₀ fa.ne_zero <| by
    rw [map_mul, map_one, one_mul, mul_assoc, mul_comm (X.germToFunctionField W v), ← mul_assoc,
      hu', mul_comm, hv']
  refine ((Scheme.rationalUnitClass_eq_rationalUnitClass_iff X W fb fa).mpr
    ⟨⟨u, v, huv, (mul_comm v u).trans huv⟩, Units.ext ?_⟩).symm
  rwa [Units.val_mul, Scheme.regularUnitToFunctionField_apply, Units.coe_map]

/-- **Existence and uniqueness of the Cartier divisor of an effective Cartier ideal sheaf.** On an
integral scheme, an effective Cartier ideal sheaf `I` determines a unique Cartier divisor
restricting on every affine open `U` with `I(U) = (a)` (regular `a`) to the rational class of `a`.
-/
theorem existsUnique_ofEffectiveCartier (hI : I.IsEffectiveCartier) :
    ∃! D : CartierDivisor X, ∀ (U : X.affineOpens) [Nonempty U.val] (a : Γ(X, U))
      (f : X.functionFieldˣ), IsSMulRegular Γ(X, U) a → I.ideal U = Ideal.span {a} →
        X.germToFunctionField U.val a = f →
          D |_ U.val = Scheme.rationalUnitClass X U.val (Additive.ofMul f) := by
  choose U hxU a ha hIa using (Scheme.IdealSheafData.isEffectiveCartier_iff I).mp hI
  have hne (x : X) : Nonempty (U x).val := ⟨⟨x, hxU x⟩⟩
  let f (x : X) : X.functionFieldˣ := letI := hne x
    Units.mk0 (X.germToFunctionField (U x).val (a x))
      (Scheme.isSMulRegular_iff_germToFunctionField_ne_zero.mp (ha x))
  have hcompat : TopCat.Presheaf.IsCompatible (Scheme.cartierDivisorSheaf X).obj
      (fun x ↦ (U x).val) fun x ↦
        letI := hne x; Scheme.rationalUnitClass X (U x).val (Additive.ofMul (f x)) := fun x y ↦ by
    have := hne x; have := hne y
    have : Nonempty ((U x).val ⊓ (U y).val : X.Opens) :=
      ⟨⟨genericPoint X, Scheme.genericPoint_mem _, Scheme.genericPoint_mem _⟩⟩
    exact (Scheme.rationalUnitClass_restrict X inf_le_left _).trans
      ((rationalUnitClass_eq_of_ideal_eq_span inf_le_left inf_le_right (ha x) (ha y)
        (hIa x) (hIa y) (f x) (f y) rfl rfl).trans
        (Scheme.rationalUnitClass_restrict X inf_le_right _).symm)
  obtain ⟨D, hD, -⟩ := (Scheme.cartierDivisorSheaf X).existsUnique_gluing' (fun x ↦ (U x).val) ⊤
    (fun _ ↦ homOfLE le_top) (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩) _ hcompat
  refine ⟨D, fun V hV b g hb hIb hbg ↦ ?_, fun D' hD' ↦ eq_of_locally_eq_affine fun x ↦
      ⟨U x, hxU x, letI := hne x; (hD' (U x) (a x) (f x) (ha x) (hIa x) rfl).trans (hD x).symm⟩⟩
  refine (Scheme.cartierDivisorSheaf X).eq_of_locally_eq' (fun x : X ↦ (U x).val ⊓ V.val) V.val
    (fun _ ↦ homOfLE inf_le_right) (fun x hx ↦ Opens.mem_iSup.mpr ⟨x, hxU x, hx⟩) _ _ fun x ↦ ?_
  have := hne x
  let W : X.Opens := (U x).val ⊓ V.val
  have : Nonempty W := ⟨⟨genericPoint X, Scheme.genericPoint_mem _, Scheme.genericPoint_mem _⟩⟩
  have hDx : D |_ (U x).val = Scheme.rationalUnitClass X (U x).val (Additive.ofMul (f x)) := hD x
  have hres : (D |_ V.val) |_ W = (Scheme.rationalUnitClass X V.val (Additive.ofMul g)) |_ W := by
    rw [TopCat.Presheaf.restrict_restrict (inf_le_right : W ≤ V.val) le_top D,
      ← TopCat.Presheaf.restrict_restrict (inf_le_left : W ≤ (U x).val) le_top D, hDx,
      Scheme.rationalUnitClass_restrict X inf_le_left,
      Scheme.rationalUnitClass_restrict X inf_le_right]
    exact rationalUnitClass_eq_of_ideal_eq_span inf_le_left inf_le_right (ha x) hb (hIa x) hIb
      (f x) g rfl hbg
  simpa only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] using hres

/-- The Cartier divisor on an integral scheme attached to an effective Cartier ideal sheaf `I`. -/
def ofEffectiveCartier (hI : I.IsEffectiveCartier) : CartierDivisor X :=
  (existsUnique_ofEffectiveCartier hI).choose

/-- Over an affine open `U` where `I(U) = (a)` with `a` regular, `ofEffectiveCartier hI` restricts
to the class of `a`. -/
theorem ofEffectiveCartier_restrict (hI : I.IsEffectiveCartier) (U : X.affineOpens) [Nonempty U.val]
    {a : Γ(X, U)} {f : X.functionFieldˣ} (ha : IsSMulRegular Γ(X, U) a)
    (hIa : I.ideal U = Ideal.span {a}) (hf : X.germToFunctionField U.val a = f) :
    ofEffectiveCartier hI |_ U.val = Scheme.rationalUnitClass X U.val (Additive.ofMul f) :=
  (existsUnique_ofEffectiveCartier hI).choose_spec.1 U a f ha hIa hf

/-- The Cartier divisor of an effective Cartier ideal sheaf is effective. -/
theorem isEffective_ofEffectiveCartier (hI : I.IsEffectiveCartier) :
    (ofEffectiveCartier hI).IsEffective := isEffective_iff_exists.mpr fun x ↦ by
  obtain ⟨U, hxU, a, ha, hIa⟩ := (Scheme.IdealSheafData.isEffectiveCartier_iff I).mp hI x
  have : Nonempty U.val := ⟨⟨x, hxU⟩⟩
  let f := Units.mk0 (X.germToFunctionField U.val a)
    (Scheme.isSMulRegular_iff_germToFunctionField_ne_zero.mp ha)
  refine ⟨f, isLocalEquationAt_of_rationalUnitClass_eq
    (ofEffectiveCartier_restrict hI U ha hIa rfl).symm hxU, ?_⟩
  rw [Units.val_mk0, ← X.algebraMap_germ_eq_germToFunctionField hxU]
  exact RingHom.mem_range_self _ _

/-- Recovering the closed-subscheme ideal sheaf of `ofEffectiveCartier hI` returns `I`. -/
@[simp]
theorem idealSheaf_isEffective_ofEffectiveCartier (hI : I.IsEffectiveCartier) :
    (isEffective_ofEffectiveCartier hI).idealSheaf = I := by
  choose U hxU a ha hIa using (Scheme.IdealSheafData.isEffectiveCartier_iff I).mp hI
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U
    (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩) fun x ↦ ?_
  have : Nonempty (U x).val := ⟨⟨x, hxU x⟩⟩
  let f := Units.mk0 (X.germToFunctionField (U x).val (a x))
    (Scheme.isSMulRegular_iff_germToFunctionField_ne_zero.mp (ha x))
  exact ((isEffective_ofEffectiveCartier hI).idealSheaf_ideal_eq_span (U x)
    (ofEffectiveCartier_restrict hI (U x) (ha x) (hIa x) (f := f) rfl).symm
    (a := a x) rfl).trans (hIa x).symm

/-- The Cartier divisor of an effective Cartier ideal sheaf depends only on the ideal sheaf. -/
theorem ofEffectiveCartier_congr (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (e : I = J) : ofEffectiveCartier hI = ofEffectiveCartier hJ := by subst e; rfl

/-- Two effective Cartier ideal sheaves determine the same Cartier divisor iff they are equal. -/
@[simp]
theorem ofEffectiveCartier_eq_iff (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier) :
    ofEffectiveCartier hI = ofEffectiveCartier hJ ↔ I = J := by
  refine ⟨fun h ↦ ?_, ofEffectiveCartier_congr hI hJ⟩
  have hcongr {D₁ D₂ : CartierDivisor X} (heq : D₁ = D₂) (h1 : D₁.IsEffective)
      (h2 : D₂.IsEffective) : h1.idealSheaf = h2.idealSheaf := by subst heq; rfl
  exact (idealSheaf_isEffective_ofEffectiveCartier hI).symm.trans
    ((hcongr h _ _).trans (idealSheaf_isEffective_ofEffectiveCartier hJ))

/-- Recovering the Cartier divisor from the ideal sheaf of an effective Cartier divisor returns the
original divisor. -/
@[simp]
theorem ofEffectiveCartier_isEffectiveCartier_idealSheaf (hD : D.IsEffective) :
    ofEffectiveCartier hD.isEffectiveCartier_idealSheaf = D := eq_of_locally_eq_affine fun x ↦ by
  obtain ⟨f, hf, g, hg⟩ := isEffective_iff_exists.mp hD x
  obtain ⟨V, hxV, hV⟩ := isLocalEquationAt_iff.mp hf
  obtain ⟨W, hxW, s, hs⟩ := X.presheaf.exists_germ_eq g
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (⟨hxV, hxW⟩ : x ∈ (V ⊓ W : X.Opens))
      (V ⊓ W).isOpen
  have hUV : U ≤ V := hUVW.trans inf_le_left; have hUW : U ≤ W := hUVW.trans inf_le_right
  have : Nonempty U := ⟨⟨x, hxU⟩⟩; have : Nonempty V := ⟨⟨x, hxV⟩⟩; have : Nonempty W := ⟨⟨x, hxW⟩⟩
  let a : Γ(X, U) := X.presheaf.map (homOfLE hUW).op s
  have haf : X.germToFunctionField U a = f := by
    rw [X.presheaf.germ_res_apply (homOfLE hUW) (genericPoint X) (Scheme.genericPoint_mem U) s,
      ← X.algebraMap_germ_eq_germToFunctionField hxW s, hs, hg]
  have hDU : Scheme.rationalUnitClass X U (Additive.ofMul f) = D |_ U := by
    rw [← Scheme.rationalUnitClass_restrict X hUV, hV,
      TopCat.Presheaf.restrict_restrict hUV le_top D]
  exact ⟨⟨U, hU⟩, hxU, (ofEffectiveCartier_restrict _ ⟨U, hU⟩
    (Scheme.isSMulRegular_iff_germToFunctionField_ne_zero.mpr (haf ▸ f.ne_zero))
    (hD.idealSheaf_ideal_eq_span ⟨U, hU⟩ hDU haf) haf).trans hDU⟩

/-- The empty effective Cartier divisor corresponds to the zero Cartier divisor. -/
@[simp]
theorem ofEffectiveCartier_top :
    ofEffectiveCartier (Scheme.IdealSheafData.isEffectiveCartier_top X) = 0 := by
  rw [ofEffectiveCartier_congr _ (isEffective_zero (X := X)).isEffectiveCartier_idealSheaf
    (isEffective_zero (X := X)).idealSheaf_zero.symm,
    ofEffectiveCartier_isEffectiveCartier_idealSheaf]

/-- Multiplication of effective Cartier ideal sheaves corresponds to addition of Cartier
divisors. -/
theorem ofEffectiveCartier_mul (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier) :
    ofEffectiveCartier (TauCeti.isEffectiveCartier_mul hI hJ) =
      ofEffectiveCartier hI + ofEffectiveCartier hJ := eq_of_locally_eq_affine fun x ↦ by
  obtain ⟨U, hxU, a, ha, hIa⟩ := (Scheme.IdealSheafData.isEffectiveCartier_iff I).mp hI x
  obtain ⟨V, hVU, hxV, b, hb, hJb⟩ := hJ.exists_eq_span_singleton_le U.val hxU
  have : Nonempty V.val := ⟨⟨x, hxV⟩⟩
  set a' : Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom a
  have ha' : IsSMulRegular Γ(X, V) a' := U.property.isSMulRegular_map hVU ha
  have hIa' : I.ideal V = Ideal.span {a'} := by
    rw [← I.map_ideal' (homOfLE hVU).op, hIa, Ideal.map_span, Set.image_singleton]
  have hIJa'b : (I * J).ideal V = Ideal.span {a' * b} := by
    simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hIa', hJb,
      Ideal.span_singleton_mul_span_singleton]
  let fa := Units.mk0 (X.germToFunctionField V.val a')
    (Scheme.isSMulRegular_iff_germToFunctionField_ne_zero.mp ha')
  let fb := Units.mk0 (X.germToFunctionField V.val b)
    (Scheme.isSMulRegular_iff_germToFunctionField_ne_zero.mp hb)
  refine ⟨V, hxV, ?_⟩
  rw [ofEffectiveCartier_restrict _ V (ha'.mul hb) hIJa'b (f := fa * fb) (by simp [fa, fb]),
    ofMul_mul, map_add, ← ofEffectiveCartier_restrict hI V ha' hIa' (f := fa) rfl,
    ← ofEffectiveCartier_restrict hJ V hb hJb (f := fb) rfl]
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_add]

/-- Powers of an effective Cartier ideal sheaf correspond to multiples of its Cartier divisor. -/
theorem ofEffectiveCartier_pow (hI : I.IsEffectiveCartier) (n : ℕ) :
    ofEffectiveCartier (TauCeti.isEffectiveCartier_pow hI n) = n • ofEffectiveCartier hI := by
  induction n with
  | zero =>
    rw [ofEffectiveCartier_congr _ (Scheme.IdealSheafData.isEffectiveCartier_top X)
      (by rw [pow_zero, Scheme.IdealSheafData.one_eq_top]), ofEffectiveCartier_top, zero_nsmul]
  | succ n ih =>
    have hn := TauCeti.isEffectiveCartier_pow hI n
    rw [ofEffectiveCartier_congr _ (TauCeti.isEffectiveCartier_mul hn hI) (pow_succ I n),
      ofEffectiveCartier_mul hn hI, ih, succ_nsmul]

/-- Finite products of effective Cartier ideal sheaves correspond to sums of Cartier divisors. -/
theorem ofEffectiveCartier_prod {ι : Type*} (s : Finset ι) {I : ι → X.IdealSheafData}
    (hI : ∀ i ∈ s, (I i).IsEffectiveCartier) :
    ofEffectiveCartier (TauCeti.isEffectiveCartier_prod hI) =
      ∑ i ∈ s.attach, ofEffectiveCartier (hI i i.property) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [ofEffectiveCartier_congr _ (Scheme.IdealSheafData.isEffectiveCartier_top X)
      (by rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]), ofEffectiveCartier_top,
      Finset.attach_empty, Finset.sum_empty]
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, (I j).IsEffectiveCartier := fun j hj ↦ hI j (Finset.mem_insert_of_mem hj)
    have h1 := hI i (Finset.mem_insert_self i s)
    have h2 := TauCeti.isEffectiveCartier_prod hs
    rw [ofEffectiveCartier_congr _ (TauCeti.isEffectiveCartier_mul h1 h2) (Finset.prod_insert hi),
      ofEffectiveCartier_mul h1 h2, ih hs, Finset.attach_insert, Finset.sum_insert,
      Finset.sum_image]
    · exact fun _ _ _ _ h ↦ Subtype.ext (congrArg Subtype.val h :)
    · simpa using hi

/-- The Cartier divisor of a globally principal effective Cartier ideal sheaf `(a)` is the
principal Cartier divisor of `a`. -/
theorem ofEffectiveCartier_ofIdealTop_span_singleton {a : Γ(X, ⊤)}
    (h : (Scheme.IdealSheafData.ofIdealTop (Ideal.span {a})).IsEffectiveCartier)
    {f : X.functionFieldˣ} (hf : X.germToFunctionField ⊤ a = f) :
    ofEffectiveCartier h = principalCartierDivisor X f := eq_of_locally_eq_affine fun x ↦ by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let a' : Γ(X, U) := X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a
  have ha'f : X.germToFunctionField U a' = f :=
    (X.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X)
      (Scheme.genericPoint_mem _) a).trans hf
  have hIa' :
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {a})).ideal ⟨U, hU⟩ = Ideal.span {a'} := by
    rw [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton]
  exact ⟨⟨U, hU⟩, hxU, (ofEffectiveCartier_restrict h ⟨U, hU⟩
    (Scheme.isSMulRegular_iff_germToFunctionField_ne_zero.mpr (ha'f ▸ f.ne_zero)) hIa' ha'f).trans
    (principalCartierDivisor_restrict X f U).symm⟩

/-- **The line-bundle class of `ofEffectiveCartier hI` is `[I]⁻¹`.** -/
@[simp]
theorem toLineBundleClass_ofEffectiveCartier (hI : I.IsEffectiveCartier) :
    (ofEffectiveCartier hI).toLineBundleClass = (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ := by
  have h := (isEffective_ofEffectiveCartier hI).mk_idealSheaf_eq_inv
  rw [LineBundleClass.mk_toInvertibleSheaf_congr _ hI
    (idealSheaf_isEffective_ofEffectiveCartier hI)] at h
  rw [h, inv_inv]

end OfEffectiveCartier

end

end TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
