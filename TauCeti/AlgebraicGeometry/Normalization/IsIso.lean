/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
public import TauCeti.AlgebraicGeometry.Scheme.IntegrallyClosed

/-!
# Recognizing the relative normalization

Let `f : X ⟶ Y` be quasi-compact and quasi-separated, and factor it as `f = f₁ ≫ f₂` with
`f₂ : T ⟶ Y` integral. The universal property of the relative normalization gives a morphism
`f.normalizationDesc f₁ f₂ H : f.normalization ⟶ T` over `Y`. This file characterizes when it is
an isomorphism, that is, when `T` is the normalization of `Y` in `X`: exactly when, for every affine
open `U ⊆ Y`, the restriction `Γ(T, f₂ ⁻¹ U) → Γ(X, f ⁻¹ U)` along `f₁` is injective with image the
integral closure of `Γ(Y, U)` in `Γ(X, f ⁻¹ U)`.

The main application is to normal schemes. Let `T` be an integral scheme whose local rings are
integrally closed, and `g : T ⟶ Y` an integral morphism. Then `T` is the normalization of `Y` in
the function field of `T`, along the generic point `Spec k(T) ⟶ T ⟶ Y`. On a nonempty affine open
`V` of `T`, the ring `Γ(T, V)` is an integrally closed domain with fraction field `k(T)`
(`AlgebraicGeometry.IsAffineOpen.isIntegrallyClosed`), and it is integral over `Γ(Y, U)` when
`V = g ⁻¹ U`, so it is the integral closure of `Γ(Y, U)` in `k(T)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_normalizationDesc_iff`: `f.normalizationDesc f₁ f₂ H` is an
  isomorphism if and only if, over every affine open of `Y`, the sections of `T` map injectively
  onto the integral closure.
* `TauCeti.AlgebraicGeometry.isIso_normalizationDesc_fromSpecStalk_genericPoint`: an integral
  scheme with integrally closed local rings, integral over `Y`, is the normalization of `Y` in its
  function field.
* `TauCeti.AlgebraicGeometry.isIso_morphismRestrict_fromNormalization_of_isIntegrallyClosed`:
  the normalization of an integral scheme in its function field is an isomorphism over every
  affine open with integrally closed ring of sections.

## References

* The Stacks Project, Tag 035H (relative normalization).
-/

public section

namespace AlgebraicGeometry.Scheme.Hom

open CategoryTheory

universe u

variable {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  (f₁ : X ⟶ T) (f₂ : T ⟶ Y) [IsIntegralHom f₂]

/-- The preimage under `f.normalizationDesc f₁ f₂ H` of the preimage of `U` under `f₂` is the
preimage of `U` in the relative normalization. -/
@[simp]
theorem normalizationDesc_preimage_preimage (H : f = f₁ ≫ f₂) (U : Y.Opens) :
    f.normalizationDesc f₁ f₂ H ⁻¹ᵁ f₂ ⁻¹ᵁ U = f.fromNormalization ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, normalizationDesc_comp]

/-- Over an affine open `U ⊆ Y`, the sections of `f.normalizationDesc f₁ f₂ H`, read in the integral
closure of `Γ(Y, U)` in `Γ(X, f ⁻¹ U)` through `normalizationObjIso`, are the restriction maps of
`f₁`. -/
theorem normalizationDesc_app_normalizationObjIso (H : f = f₁ ≫ f₂) {U : Y.Opens}
    (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    (f.normalizationDesc f₁ f₂ H).app (f₂ ⁻¹ᵁ U) ≫
        f.normalization.presheaf.map
          (eqToHom (f.normalizationDesc_preimage_preimage f₁ f₂ H U).symm).op ≫
        (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom (Subalgebra.val _).toRingHom =
      f₁.appLE (f₂ ⁻¹ᵁ U) (f ⁻¹ᵁ U) (by simp [H]) := by
  have h := Scheme.Hom.comp_appLE f.toNormalization (f.normalizationDesc f₁ f₂ H) (f₂ ⁻¹ᵁ U)
    (f ⁻¹ᵁ U) (by simp [H])
  simp only [toNormalization_normalizationDesc] at h
  rw [h, normalizationObjIso_hom_val, map_appLE]

/-- Over an affine open `U ⊆ Y`, the map of sections of `f.normalizationDesc f₁ f₂ H` is an
isomorphism if and only if the restriction `Γ(T, f₂ ⁻¹ U) → Γ(X, f ⁻¹ U)` along `f₁` is injective
and its image contains every element integral over `Γ(Y, U)`. -/
theorem isIso_normalizationDesc_app_iff (H : f = f₁ ≫ f₂) {U : Y.Opens} (hU : IsAffineOpen U) :
    IsIso ((f.normalizationDesc f₁ f₂ H).app (f₂ ⁻¹ᵁ U)) ↔
      Function.Injective (f₁.appLE (f₂ ⁻¹ᵁ U) (f ⁻¹ᵁ U) (by simp [H])) ∧
      ∀ s, (f.app U).hom.IsIntegralElem s →
        s ∈ (f₁.appLE (f₂ ⁻¹ᵁ U) (f ⁻¹ᵁ U) (by simp [H])).hom.range := by
  let := (f.app U).hom.toAlgebra
  let e := f.normalization.presheaf.map
      (eqToHom (f.normalizationDesc_preimage_preimage f₁ f₂ H U).symm).op ≫
    (f.normalizationObjIso hU).hom
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e
  have hval := f.normalizationDesc_app_normalizationObjIso f₁ f₂ H hU
  rw [ConcreteCategory.isIso_iff_bijective, ← he.of_comp_iff' ]
  set ψ := e.hom.comp ((f.normalizationDesc f₁ f₂ H).app (f₂ ⁻¹ᵁ U)).hom
  have hψ (b) : (ψ b : Γ(X, f ⁻¹ᵁ U)) =
      f₁.appLE (f₂ ⁻¹ᵁ U) (f ⁻¹ᵁ U) (by simp [H]) b := by
    -- `ψ b` is the composite of the maps in `hval` applied to `b`.
    rw [← hval]
    rfl
  refine ⟨fun h ↦ ⟨fun a b hab ↦ h.1 (Subtype.ext ((hψ a).trans (hab.trans (hψ b).symm))),
      fun s hs ↦ ?_⟩, fun h ↦ ⟨fun a b hab ↦ h.1 ((hψ a).symm.trans
        ((congrArg Subtype.val hab).trans (hψ b))), fun t ↦ ?_⟩⟩
  · obtain ⟨b, hb⟩ := h.2 ⟨s, hs⟩
    exact ⟨b, (hψ b).symm.trans (congrArg Subtype.val hb)⟩
  · obtain ⟨b, hb⟩ := h.2 t.1 t.2
    exact ⟨b, Subtype.ext ((hψ b).trans hb)⟩

/-- **Recognizing the relative normalization.** For `f = f₁ ≫ f₂` with `f₂` integral, the morphism
`f.normalizationDesc f₁ f₂ H : f.normalization ⟶ T` is an isomorphism if and only if, for every
affine open `U ⊆ Y`, the restriction `Γ(T, f₂ ⁻¹ U) → Γ(X, f ⁻¹ U)` along `f₁` is injective and its
image contains every element integral over `Γ(Y, U)`. Its image is always contained in the integral
closure, since `f₂` is integral. -/
theorem isIso_normalizationDesc_iff (H : f = f₁ ≫ f₂) :
    IsIso (f.normalizationDesc f₁ f₂ H) ↔ ∀ U : Y.Opens, IsAffineOpen U →
      Function.Injective (f₁.appLE (f₂ ⁻¹ᵁ U) (f ⁻¹ᵁ U) (by simp [H])) ∧
      ∀ s, (f.app U).hom.IsIntegralElem s →
        s ∈ (f₁.appLE (f₂ ⁻¹ᵁ U) (f ⁻¹ᵁ U) (by simp [H])).hom.range := by
  have hcover : ⨆ U : Y.affineOpens, f₂ ⁻¹ᵁ U.1 = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _) _ hcover]
  refine ⟨fun h U hU ↦ ?_, fun h U ↦ ?_⟩
  · have := h ⟨U, hU⟩
    rw [MorphismProperty.isomorphisms.iff,
      isIso_morphismRestrict_iff_isIso_app _ (hU.preimage f₂)] at this
    exact (f.isIso_normalizationDesc_app_iff f₁ f₂ H hU).1 this
  · rw [MorphismProperty.isomorphisms.iff,
      isIso_morphismRestrict_iff_isIso_app _ (U.2.preimage f₂)]
    exact (f.isIso_normalizationDesc_app_iff f₁ f₂ H U.2).2 (h U U.2)

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

open CategoryTheory _root_.AlgebraicGeometry

universe u

variable {T Y : Scheme.{u}}

/-- **A normal scheme integral over `Y` is the normalization of `Y` in its function field.** If `T`
is an integral scheme whose local rings are integrally closed and `g : T ⟶ Y` is integral, then the
morphism from the relative normalization of `Y` in `Spec k(T)`, along `Spec k(T) ⟶ T ⟶ Y`, to `T`
is an isomorphism. -/
theorem isIso_normalizationDesc_fromSpecStalk_genericPoint [IsIntegral T]
    (hT : ∀ x : T, IsIntegrallyClosed (T.presheaf.stalk x)) (g : T ⟶ Y) [IsIntegralHom g] :
    IsIso ((T.fromSpecStalk (genericPoint T) ≫ g).normalizationDesc _ g rfl) := by
  rw [Scheme.Hom.isIso_normalizationDesc_iff]
  intro U hU
  by_cases hη : genericPoint T ∈ g ⁻¹ᵁ U
  · have : Nonempty (g ⁻¹ᵁ U) := ⟨⟨_, hη⟩⟩
    have hV := hU.preimage g
    let ι := (Scheme.ΓSpecIso T.functionField).inv ≫
      (Spec T.functionField).presheaf.map (homOfLE (le_top :
        T.fromSpecStalk (genericPoint T) ⁻¹ᵁ g ⁻¹ᵁ U ≤ ⊤)).op
    have := Scheme.isIso_presheaf_map_fromSpecStalk_preimage_le_top hη
    have hι : Function.Bijective ι.hom := ConcreteCategory.bijective_of_isIso _
    have key : (T.fromSpecStalk (genericPoint T)).appLE (g ⁻¹ᵁ U)
        ((T.fromSpecStalk (genericPoint T) ≫ g) ⁻¹ᵁ U)
        (by simp) = T.germToFunctionField (g ⁻¹ᵁ U) ≫ ι := by
      rw [← Scheme.fromSpecStalk_app hη, Scheme.Hom.app_eq_appLE]
      simp only [Scheme.Hom.comp_preimage]
    refine ⟨?_, fun s hs ↦ ?_⟩
    · rw [key]
      exact hι.1.comp (Scheme.germToFunctionField_injective T _)
    · obtain ⟨t, rfl⟩ := hι.2 s
      have happ : (T.fromSpecStalk (genericPoint T) ≫ g).app U =
          g.app U ≫ T.germToFunctionField (g ⁻¹ᵁ U) ≫ ι := by
        rw [Scheme.Hom.comp_app, Scheme.fromSpecStalk_app hη]
      rw [happ] at hs
      have ht : _root_.IsIntegral Γ(T, g ⁻¹ᵁ U) t := by
        obtain ⟨p, hp, hpe⟩ := hs
        refine ⟨p.map (g.app U).hom, hp.map _, hι.1 ?_⟩
        rw [Polynomial.eval₂_map, map_zero, Polynomial.hom_eval₂]
        exact hpe
      have := hV.isIntegrallyClosed fun x _ ↦ hT x
      have := functionField_isFractionRing_of_isAffineOpen T _ hV
      obtain ⟨b, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (K := T.functionField)).mp ht
      -- The algebra structure of `Γ(T, V)` on `k(T)` is the germ map, so this is `key` at `b`.
      exact ⟨b, by rw [key]; rfl⟩
  · have hV : g ⁻¹ᵁ U = ⊥ := Scheme.eq_bot_of_genericPoint_notMem hη
    have : Subsingleton Γ(T, g ⁻¹ᵁ U) := by
      rw [hV]
      infer_instance
    have : Subsingleton Γ(Spec T.functionField, (T.fromSpecStalk (genericPoint T) ≫ g) ⁻¹ᵁ U) := by
      rw [Scheme.Hom.comp_preimage, hV, Scheme.Hom.preimage_bot]
      infer_instance
    exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun _ _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- The normalization of an integral scheme `Y` in its function field, along `Spec k(Y) ⟶ Y`, is an
isomorphism over every affine open `U` whose ring of sections is integrally closed: the integral
closure of `Γ(Y, U)` in its fraction field `k(Y)` is `Γ(Y, U)` itself. -/
theorem isIso_morphismRestrict_fromNormalization_of_isIntegrallyClosed [IsIntegral Y]
    {U : Y.Opens} (hU : IsAffineOpen U) [IsIntegrallyClosed Γ(Y, U)] :
    IsIso ((Y.fromSpecStalk (genericPoint Y)).fromNormalization ∣_ U) := by
  set f := Y.fromSpecStalk (genericPoint Y)
  rw [isIso_morphismRestrict_iff_isIso_app _ hU, Scheme.Hom.fromNormalization_app _ hU]
  let := (f.app U).hom.toAlgebra
  suffices h : Function.Bijective
      (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(Spec Y.functionField, f ⁻¹ᵁ U))) by
    have : IsIso (CommRingCat.ofHom (algebraMap Γ(Y, U)
        (integralClosure Γ(Y, U) Γ(Spec Y.functionField, f ⁻¹ᵁ U)))) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr h
    infer_instance
  by_cases hη : genericPoint Y ∈ U
  · have : Nonempty U := ⟨⟨_, hη⟩⟩
    have := Scheme.isFractionRing_app_fromSpecStalk_genericPoint hU
    refine ⟨fun a b hab ↦ IsFractionRing.injective Γ(Y, U) _ (congrArg Subtype.val hab),
      fun ⟨x, hx⟩ ↦ ?_⟩
    obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
    exact ⟨a, rfl⟩
  · -- Otherwise `U` is empty and all the rings involved are zero.
    have hU : U = ⊥ := Scheme.eq_bot_of_genericPoint_notMem hη
    have : Subsingleton Γ(Y, U) := by
      rw [hU]
      infer_instance
    have : Subsingleton Γ(Spec Y.functionField, f ⁻¹ᵁ U) := by
      rw [hU, Scheme.Hom.preimage_bot]
      infer_instance
    exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end TauCeti.AlgebraicGeometry
