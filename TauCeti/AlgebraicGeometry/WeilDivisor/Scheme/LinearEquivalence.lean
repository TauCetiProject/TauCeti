/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.LocallyPrincipal

/-!
# Isomorphic divisor sheaves come from linearly equivalent divisors

`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Sheaf.lean` attaches to a Weil divisor `D` on an
integral scheme the subsheaf `𝒪_X(D)` of the sheaf `𝒦_X` of rational functions, and shows in
`SchemeWeilDivisor.nonempty_iso_sheaf_of_linearlyEquivalent` that linearly equivalent divisors
have isomorphic sheaves. This file proves the converse for locally principal divisors: the
isomorphism class of `𝒪_X(D)` determines the class of `D` in the divisor class group.

The mechanism is that an `𝒪_X`-linear map from `𝒪_X(D)` to `𝒦_X` is multiplication by a rational
function. A local equation for `D` near the generic point exhibits `𝒪_X(D)` as generated there by
one rational function, and `𝒦_X` is the constant sheaf with value `K(X)`, so the multiplier read
off near the generic point already computes the map over every open subset. An isomorphism
`𝒪_X(D) ≅ 𝒪_X(E)` is therefore multiplication by a unit `g` of `K(X)`, and comparing the local
equations of `D - div g` and of `E` at each codimension-one point gives `E = D - div g`.

## Main declarations

* `SchemeWeilDivisor.inv_localEquation_mem_sections`: the inverse of a local equation for `D` on
  `U` is a section of `𝒪_X(D)` over `U`;
* `SchemeWeilDivisor.IsLocallyPrincipal.exists_rationalFunctionsMul_eq`: every `𝒪_X`-linear map
  `𝒪_X(D) ⟶ 𝒦_X` is the inclusion followed by multiplication by a rational function;
* `SchemeWeilDivisor.IsLocallyPrincipal.exists_sheafι_app_ne_zero`: `𝒪_X(D)` has a section which
  is a nonzero rational function;
* `SchemeWeilDivisor.linearlyEquivalent_of_nonempty_iso_sheaf` and
  `SchemeWeilDivisor.nonempty_iso_sheaf_iff_linearlyEquivalent`: locally principal divisors with
  isomorphic sheaves are linearly equivalent, and conversely.

On a curve every Weil divisor is locally principal, so this makes the comparison map
`SchemeWeilDivisor.classGroupToLineBundleClass` of
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/LineBundle.lean` injective: that is the injectivity
half of `Cl(X) ≅ Pic X`.

The statement is Hartshorne, *Algebraic Geometry*, II, Proposition 6.13; the argument given here
is the standard one, run through the constant sheaf `𝒦_X` rather than through stalks at the
generic point. The proofs reuse the divisor sheaf and its multiplication isomorphisms from
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Sheaf.lean`, the local equations of
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/LocallyPrincipal.lean`, and Mathlib's
`TopCat.Presheaf.exists_le_germ_eq` and `AlgebraicGeometry.Scheme.ord`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

noncomputable section

section General

variable {X : Scheme.{u}}

/-- An open subset with no points is the empty one. -/
private lemma eq_bot_of_not_nonempty {U : X.Opens} (h : ¬ Nonempty U) : U = ⊥ :=
  (Opens.not_nonempty_iff_eq_bot U).mp fun hne ↦ h (Set.nonempty_coe_sort.mpr hne)

end General

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

/-- The inverse of a local equation for `D` on `U` is a section of `𝒪_X(D)` over `U`: its order
at a codimension-one point of `U` is exactly `-D`. -/
lemma inv_localEquation_mem_sections {D : SchemeWeilDivisor X} {U : X.Opens} [Nonempty U]
    {f : Additive X.functionFieldˣ}
    (hf : ∀ y : CodimensionOnePoint X, (y : X) ∈ U → WeilDivisor.coeff D y = orderAt y f) :
    (Scheme.rationalFunctionsEquiv U).symm
        ((Additive.toMul f : X.functionFieldˣ) : X.functionField)⁻¹ ∈ sections D U := by
  refine mem_sections.mpr fun y hy ↦ Or.inr ?_
  rw [LinearEquiv.apply_symm_apply, Scheme.ord_inv, hf y hy, orderAt_apply]

/-- **An `𝒪_X`-linear map from `𝒪_X(D)` to the rational functions is multiplication by a rational
function.** A local equation for `D` near the generic point trivializes `𝒪_X(D)` there, and the
resulting multiplier is independent of the open subset because `𝒦_X` is the constant sheaf. -/
theorem IsLocallyPrincipal.exists_rationalFunctionsMul_eq {D : SchemeWeilDivisor X}
    (hD : IsLocallyPrincipal D) (ψ : sheaf D ⟶ Scheme.rationalFunctions X) :
    ∃ g : X.functionField, ψ = sheafι D ≫ Scheme.rationalFunctionsMul X g := by
  -- `NatTrans.naturality_apply` for the underlying map of presheaves, read in the
  -- `Scheme.Modules.Hom.app` normal form used below
  have hnat {M N : X.Modules} (χ : M ⟶ N) {V W : X.Opens} (i : W ⟶ V) (x : Γ(M, V)) :
      Scheme.Modules.Hom.app χ W (M.presheaf.map i.op x) =
        N.presheaf.map i.op (Scheme.Modules.Hom.app χ V x) :=
    χ.mapPresheaf.naturality_apply i.op x
  obtain ⟨U₀, hU₀, f, hf⟩ := isLocallyPrincipal_iff.mp hD (genericPoint X)
  have : Nonempty U₀ := ⟨⟨_, hU₀⟩⟩
  set fK : X.functionField := ((Additive.toMul f : X.functionFieldˣ) : X.functionField)
  have hfK : fK ≠ 0 := Units.ne_zero _
  obtain ⟨s₀, hs₀⟩ := (range_sheafι_app D U₀).ge (inv_localEquation_mem_sections hf)
  have hιs₀ : Scheme.rationalFunctionsEquiv U₀ (Scheme.Modules.Hom.app (sheafι D) U₀ s₀) =
      fK⁻¹ := by
    rw [hs₀, LinearEquiv.apply_symm_apply]
  refine ⟨fK * Scheme.rationalFunctionsEquiv U₀ (Scheme.Modules.Hom.app ψ U₀ s₀), ?_⟩
  set g := fK * Scheme.rationalFunctionsEquiv U₀ (Scheme.Modules.Hom.app ψ U₀ s₀) with hgdef
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext s
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  -- over an empty open subset `𝒦_X` has only the zero section, so there is nothing to compare
  by_cases hU : Nonempty U
  · refine (Scheme.rationalFunctionsEquiv U).injective ?_
    rw [Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app]
    rcases eq_or_ne (Scheme.rationalFunctionsEquiv U
      (Scheme.Modules.Hom.app (sheafι D) U s)) 0 with h0 | h0
    · have hs0 : s = 0 :=
        sheafι_app_injective D U
          ((Scheme.rationalFunctionsEquiv U).injective (by simp [h0]))
      rw [hs0]
      simp
    · set t := Scheme.rationalFunctionsEquiv U (Scheme.Modules.Hom.app (sheafι D) U s) with htdef
      have hgen : genericPoint X ∈ (U ⊓ U₀ : X.Opens) :=
        ⟨Scheme.genericPoint_mem U, hU₀⟩
      -- shrink to an open subset on which the rational function `t * f` is regular
      obtain ⟨W, hWV, hgenW, a, ha⟩ := X.presheaf.exists_le_germ_eq (t * fK) hgen
      have : Nonempty W := ⟨⟨_, hgenW⟩⟩
      have hWU : W ≤ U := hWV.trans inf_le_left
      have hWU₀ : W ≤ U₀ := hWV.trans inf_le_right
      have hgerm : X.germToFunctionField W a = t * fK := ha
      -- the restriction of `s` to `W` is `a` times the restriction of `s₀`
      have hres : (sheaf D).presheaf.map (homOfLE hWU).op s =
          a • (sheaf D).presheaf.map (homOfLE hWU₀).op s₀ := by
        refine sheafι_app_injective D W ((Scheme.rationalFunctionsEquiv W).injective ?_)
        rw [hnat (sheafι D) (homOfLE hWU) s, Scheme.rationalFunctionsEquiv_map,
          Scheme.Modules.Hom.app_smul, map_smul, hnat (sheafι D) (homOfLE hWU₀) s₀,
          Scheme.rationalFunctionsEquiv_map, hιs₀, Algebra.smul_def,
          RingHom.algebraMap_toAlgebra, hgerm, ← htdef, mul_assoc, mul_inv_cancel₀ hfK, mul_one]
      have hψ : Scheme.rationalFunctionsEquiv U (Scheme.Modules.Hom.app ψ U s) = g * t := by
        rw [← Scheme.rationalFunctionsEquiv_map (homOfLE hWU)
          (Scheme.Modules.Hom.app ψ U s), ← hnat ψ (homOfLE hWU) s, hres,
          Scheme.Modules.Hom.app_smul, map_smul, hnat ψ (homOfLE hWU₀) s₀,
          Scheme.rationalFunctionsEquiv_map, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
          hgerm, hgdef]
        ring
      rw [hψ]
  · have := Scheme.subsingleton_rationalFunctions U (eq_bot_of_not_nonempty hU)
    exact Subsingleton.elim _ _

/-- A local equation near the generic point exhibits a section of `𝒪_X(D)` which is a nonzero
rational function. -/
theorem IsLocallyPrincipal.exists_sheafι_app_ne_zero {D : SchemeWeilDivisor X}
    (hD : IsLocallyPrincipal D) :
    ∃ (U : X.Opens) (s : Γ(sheaf D, U)), Scheme.Modules.Hom.app (sheafι D) U s ≠ 0 := by
  obtain ⟨U₀, hU₀, f, hf⟩ := isLocallyPrincipal_iff.mp hD (genericPoint X)
  have : Nonempty U₀ := ⟨⟨_, hU₀⟩⟩
  obtain ⟨s₀, hs₀⟩ := (range_sheafι_app D U₀).ge (inv_localEquation_mem_sections hf)
  refine ⟨U₀, s₀, ?_⟩
  rw [hs₀]
  simp only [ne_eq, EmbeddingLike.map_eq_zero_iff, inv_eq_zero]
  exact Units.ne_zero _

/-- Only multiplication by `1` fixes the inclusion of `𝒪_X(D)` into the rational functions. -/
private lemma eq_one_of_sheafι_comp_eq {D : SchemeWeilDivisor X} (hD : IsLocallyPrincipal D)
    {c : X.functionField} (h : sheafι D ≫ Scheme.rationalFunctionsMul X c = sheafι D) :
    c = 1 := by
  obtain ⟨U, s, hs⟩ := hD.exists_sheafι_app_ne_zero
  have hU : Nonempty U := by
    by_contra hU
    have := Scheme.subsingleton_rationalFunctions U (eq_bot_of_not_nonempty hU)
    exact hs (Subsingleton.elim _ _)
  have hne : Scheme.rationalFunctionsEquiv U (Scheme.Modules.Hom.app (sheafι D) U s) ≠ 0 := by
    simpa using hs
  have key := ConcreteCategory.congr_hom (congrArg (fun η ↦ Scheme.Modules.Hom.app η U) h) s
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at key
  have := congrArg (Scheme.rationalFunctionsEquiv U) key
  rw [Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app] at this
  exact mul_right_cancel₀ hne (by rw [this, one_mul])

/-- If the inclusion of `𝒪_X(D)` into `𝒦_X` factors through `𝒪_X(E)` after multiplication by `c`,
then multiplication by `c` carries the sections of `𝒪_X(D)` into those of `𝒪_X(E)`. -/
private lemma mem_sections_of_factor {D E : SchemeWeilDivisor X} {c : X.functionField}
    {χ : sheaf D ⟶ sheaf E}
    (hχ : χ ≫ sheafι E = sheafι D ≫ Scheme.rationalFunctionsMul X c)
    (U : X.Opens) {t : Γ(Scheme.rationalFunctions X, U)} (ht : t ∈ sections D U) :
    Scheme.Modules.Hom.app (Scheme.rationalFunctionsMul X c) U t ∈ sections E U := by
  obtain ⟨s, rfl⟩ := (range_sheafι_app D U).ge ht
  have key := ConcreteCategory.congr_hom (congrArg (fun η ↦ Scheme.Modules.Hom.app η U) hχ) s
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at key
  rw [← key]
  exact sheafι_app_mem E U _

/-- **Isomorphic divisor sheaves come from linearly equivalent divisors.** This is the converse of
`SchemeWeilDivisor.nonempty_iso_sheaf_of_linearlyEquivalent`. -/
theorem linearlyEquivalent_of_nonempty_iso_sheaf {D E : SchemeWeilDivisor X}
    (hD : IsLocallyPrincipal D) (hE : IsLocallyPrincipal E)
    (h : Nonempty (sheaf D ≅ sheaf E)) :
    (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent D E := by
  obtain ⟨φ⟩ := h
  -- both directions of `φ`, read inside `𝒦_X`, are multiplications by rational functions
  obtain ⟨g, hg⟩ := hD.exists_rationalFunctionsMul_eq (φ.hom ≫ sheafι E)
  obtain ⟨g', hg'⟩ := hE.exists_rationalFunctionsMul_eq (φ.inv ≫ sheafι D)
  have hg'g : g' * g = 1 := by
    refine eq_one_of_sheafι_comp_eq hD ?_
    rw [Scheme.rationalFunctionsMul_mul, ← Category.assoc, ← hg, Category.assoc, ← hg',
      Iso.hom_inv_id_assoc]
  set gu : X.functionFieldˣ := Units.mk0 g (right_ne_zero_of_mul_eq_one hg'g) with hgudef
  have hgu : (gu : X.functionField) = g := by rw [hgudef, Units.val_mk0]
  have hguinv : ((gu⁻¹ : X.functionFieldˣ) : X.functionField) = g' :=
    Units.inv_eq_of_mul_eq_one_left (by rw [hgu]; exact hg'g)
  set γ : Additive X.functionFieldˣ := Additive.ofMul gu with hγdef
  have hγ : ((Additive.toMul γ : X.functionFieldˣ) : X.functionField) = g := by
    rw [hγdef, toMul_ofMul, hgu]
  have hγneg : ((Additive.toMul (-γ) : X.functionFieldˣ) : X.functionField) = g' := by
    rw [hγdef, toMul_neg, toMul_ofMul, hguinv]
  set F : SchemeWeilDivisor X :=
    D - (WeilDivisor.OrderSystem.ofScheme X).principalDivisor γ with hFdef
  -- multiplying by `g` and by `g'` are mutually inverse on sections
  have hcancel : ∀ (U : X.Opens) (t : Γ(Scheme.rationalFunctions X, U)),
      Scheme.Modules.Hom.app (Scheme.rationalFunctionsMul X g) U
        (Scheme.Modules.Hom.app (Scheme.rationalFunctionsMul X g') U t) = t := fun U t ↦ by
    have key := ConcreteCategory.congr_hom
      (congrArg (fun η ↦ Scheme.Modules.Hom.app η U) (Scheme.rationalFunctionsMul_inv_comp gu)) t
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] at key
    rwa [hgu, hguinv] at key
  -- the two divisors `F` and `E` have the same sections over every open subset
  have hsec : ∀ U : X.Opens, sections F U = sections E U := by
    intro U
    refine le_antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    · have h1 := mem_sections_of_factor
        ((sheafMulIso_inv_ι γ D).trans (by rw [hγneg])) U ht
      have h2 := mem_sections_of_factor hg U h1
      rwa [hcancel] at h2
    · have h1 := mem_sections_of_factor hg' U ht
      have h2 := mem_sections_of_factor ((sheafMul_ι γ D).trans (by rw [hγ])) U h1
      rwa [hcancel] at h2
  -- comparing local equations at a codimension-one point turns that into equal coefficients
  have hFlp : IsLocallyPrincipal F := hD.sub (isLocallyPrincipal_principalDivisor γ)
  have hcoeff : ∀ y : CodimensionOnePoint X, WeilDivisor.coeff F y = WeilDivisor.coeff E y := by
    intro y
    obtain ⟨U₁, hy₁, h₁, hh₁⟩ := isLocallyPrincipal_iff.mp hFlp (y : X)
    obtain ⟨U₂, hy₂, h₂, hh₂⟩ := isLocallyPrincipal_iff.mp hE (y : X)
    have hyU : (y : X) ∈ (U₁ ⊓ U₂ : X.Opens) := ⟨hy₁, hy₂⟩
    have : Nonempty (U₁ ⊓ U₂ : X.Opens) := ⟨⟨_, hyU⟩⟩
    have m1 : (Scheme.rationalFunctionsEquiv (U₁ ⊓ U₂ : X.Opens)).symm
        ((Additive.toMul h₁ : X.functionFieldˣ) : X.functionField)⁻¹ ∈
          sections E (U₁ ⊓ U₂ : X.Opens) := by
      rw [← hsec]
      exact inv_localEquation_mem_sections fun z hz ↦ hh₁ z hz.1
    have m2 : (Scheme.rationalFunctionsEquiv (U₁ ⊓ U₂ : X.Opens)).symm
        ((Additive.toMul h₂ : X.functionFieldˣ) : X.functionField)⁻¹ ∈
          sections F (U₁ ⊓ U₂ : X.Opens) := by
      rw [hsec]
      exact inv_localEquation_mem_sections fun z hz ↦ hh₂ z hz.2
    have b1 := (mem_sections.mp m1 y hyU).resolve_left (by
      simp only [LinearEquiv.apply_symm_apply, inv_eq_zero]
      exact Units.ne_zero _)
    have b2 := (mem_sections.mp m2 y hyU).resolve_left (by
      simp only [LinearEquiv.apply_symm_apply, inv_eq_zero]
      exact Units.ne_zero _)
    rw [LinearEquiv.apply_symm_apply, Scheme.ord_inv, ← orderAt_apply, ← hh₁ y hy₁] at b1
    rw [LinearEquiv.apply_symm_apply, Scheme.ord_inv, ← orderAt_apply, ← hh₂ y hy₂] at b2
    omega
  refine (WeilDivisor.OrderSystem.linearlyEquivalent_iff_exists_principalDivisor _).mpr ⟨γ, ?_⟩
  rw [← WeilDivisor.ext hcoeff, hFdef]
  abel

/-- **Two divisor sheaves are isomorphic exactly when the divisors are linearly equivalent.** -/
theorem nonempty_iso_sheaf_iff_linearlyEquivalent {D E : SchemeWeilDivisor X}
    (hD : IsLocallyPrincipal D) (hE : IsLocallyPrincipal E) :
    Nonempty (sheaf D ≅ sheaf E) ↔
      (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent D E :=
  ⟨linearlyEquivalent_of_nonempty_iso_sheaf hD hE, nonempty_iso_sheaf_of_linearlyEquivalent⟩

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
