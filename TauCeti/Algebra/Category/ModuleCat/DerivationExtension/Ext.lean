/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.DerivationExtension.Basic
public import TauCeti.Algebra.Category.ModuleCat.Smooth.Coinduction

/-!
# Native extension classes of continuous derivations

The short exact sequence constructed in `DerivationExtension.Basic` gives a class in native
`CategoryTheory.Abelian.Ext` in the abelian category of discrete modules. Its existence follows
from continuous coinduction and enough injectives, with module universe `max u w`. Naturality
identifies pushforward along a module map with pullback, and an actual inner change of
derivation leaves this class unchanged. Vanishing detects an actual linear section of the
projection, so these classes record the obstruction to splitting the first-order deformation.

The extension is in the ambient discrete module category. Even when the original module has
a fixed central character, its self-extension need not have that same strict character.

## References

* Edward Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge Studies in Advanced
  Mathematics 103, Cambridge University Press, 2007, for infinitesimal deformations of modules
  over the completed enveloping algebra at the critical level.
* The construction of the underlying self-extension and its inner comparison is
  `TauCeti.DerivationExtension` in `DerivationExtension.Basic`; extension classes and their
  naturality use Mathlib's `ShortComplex.ShortExact.extClass`.
-/

public section

namespace TauCeti.DerivationExtension

open CategoryTheory CategoryTheory.Abelian

universe u w

variable {R : Type*} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  [TopologicalSpace A] [SeparatelyContinuousAdd A]
  {δ δ' : derivationLieAlgebra R A}

/-- The native extension class of the self-extension of a discrete module by a continuous
derivation, in the abelian category of discrete modules itself. -/
noncomputable def extClass (hδ : Continuous (δ : Module.End R A))
    (M : (discreteModules.{max u w} A).FullSubcategory) : Ext.{max u w} M M 1 :=
  (shortExact_discreteShortComplex hδ M).extClass

/-- The class is the connecting class of the actual short exact discrete-module sequence. -/
theorem extClass_def (hδ : Continuous (δ : Module.End R A))
    (M : (discreteModules.{max u w} A).FullSubcategory) :
    extClass hδ M = (shortExact_discreteShortComplex hδ M).extClass :=
  (rfl)

/-- Pushforward of the derivation class along a module map equals pullback of the class of
the target module. Both classes are computed in the category of discrete modules. -/
theorem extClass_naturality (hδ : Continuous (δ : Module.End R A))
    {M N : (discreteModules.{max u w} A).FullSubcategory} (f : M ⟶ N) :
    (extClass hδ M).comp (Ext.mk₀ f) (add_zero 1) =
      (Ext.mk₀ f).comp (extClass hδ N) (zero_add 1) := by
  let φ : discreteShortComplex hδ M ⟶ discreteShortComplex hδ N :=
    { τ₁ := f
      τ₂ := ObjectProperty.homMk (ModuleCat.ofHom (map f.hom.hom))
      τ₃ := f
      comm₁₂ := InducedCategory.hom_ext
        (ModuleCat.hom_ext (map_comp_inlHom (δ := δ) f.hom.hom).symm)
      comm₂₃ := InducedCategory.hom_ext
        (ModuleCat.hom_ext (sndHom_comp_map (δ := δ) f.hom.hom)) }
  exact (shortExact_discreteShortComplex hδ M).extClass_naturality
    (shortExact_discreteShortComplex hδ N) φ

/-- Changing the derivation by the inner derivation of an actual element of the algebra
preserves its native discrete-module extension class. -/
theorem extClass_eq_of_inner (hδ : Continuous (δ : Module.End R A))
    (hδ' : Continuous (δ' : Module.End R A)) (b : A)
    (h : δ' = δ + innerDerivation R b)
    (M : (discreteModules.{max u w} A).FullSubcategory) :
    extClass hδ M = extClass hδ' M := by
  let φ : discreteShortComplex hδ M ⟶ discreteShortComplex hδ' M :=
    { τ₁ := 𝟙 M
      τ₂ := ObjectProperty.homMk (ModuleCat.ofHom (innerEquiv M.obj h).toLinearMap)
      τ₃ := 𝟙 M
      comm₁₂ := by
        apply InducedCategory.hom_ext
        simpa using ModuleCat.hom_ext (innerEquiv_comp_inlHom M.obj h).symm
      comm₂₃ := by
        apply InducedCategory.hom_ext
        simpa using ModuleCat.hom_ext (sndHom_comp_innerEquiv M.obj h) }
  have hn := (shortExact_discreteShortComplex hδ M).extClass_naturality
    (shortExact_discreteShortComplex hδ' M) φ
  -- Normalize the short-complex endpoint presentations before the native identity laws match.
  dsimp only [φ, discreteShortComplex] at hn
  simpa only [Ext.comp_mk₀_id, Ext.mk₀_id_comp, extClass] using! hn

/-- The class vanishes exactly when the projection of the self-extension admits an
`A`-linear section. This is a splitting in the discrete module category, whose morphisms
are all the underlying module maps. -/
theorem extClass_eq_zero_iff (hδ : Continuous (δ : Module.End R A))
    (M : (discreteModules.{max u w} A).FullSubcategory) :
    extClass hδ M = 0 ↔ ∃ s : M.obj →ₗ[A] DerivationExtension δ M.obj,
      sndHom δ M.obj ∘ₗ s = LinearMap.id := by
  have hS := shortExact_discreteShortComplex hδ M
  constructor
  · intro h
    have hx₀ : (Ext.mk₀ (𝟙 M)).comp (extClass hδ M) (zero_add 1) = 0 := by
      simpa only [Ext.mk₀_id_comp] using h
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ M hS (Ext.mk₀ (𝟙 M)) (zero_add 1) hx₀
    obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
    have hs : s ≫ (discreteShortComplex hδ M).g = 𝟙 M :=
      (Ext.mk₀_bijective _ _).injective (by simpa only [Ext.mk₀_comp_mk₀] using hx)
    exact ⟨s.hom.hom, congrArg (fun f => f.hom.hom) hs⟩
  · rintro ⟨s, hs⟩
    let σ : M ⟶ (discreteShortComplex hδ M).X₂ := ObjectProperty.homMk (ModuleCat.ofHom s)
    have hσ : σ ≫ (discreteShortComplex hδ M).g = 𝟙 M :=
      InducedCategory.hom_ext (ModuleCat.hom_ext hs)
    have hzero := congrArg (fun c => (Ext.mk₀ σ).comp c (zero_add 1)) hS.comp_extClass
    rw [Ext.mk₀_comp_mk₀_assoc, hσ] at hzero
    simp only [Ext.comp_zero] at hzero
    -- Normalize the endpoints of the short complex before simplifying the identity.
    dsimp only [discreteShortComplex] at hzero
    simpa only [Ext.mk₀_id_comp, Ext.comp_zero, extClass, hS] using! hzero

/-- The zero derivation gives the split self-extension and hence the zero class. -/
@[simp]
theorem extClass_zero (M : (discreteModules.{max u w} A).FullSubcategory) :
    extClass (δ := (0 : derivationLieAlgebra R A)) continuous_zero M = 0 := by
  apply (extClass_eq_zero_iff continuous_zero M).mpr
  refine ⟨{ toFun := fun v => ⟨0, v⟩
            map_add' := fun _ _ => by ext <;> simp
            map_smul' := fun _ _ => by ext <;> simp }, ?_⟩
  ext
  simp

/-- Every continuous inner derivation has zero extension class. -/
theorem extClass_inner (b : A)
    (hb : Continuous (innerDerivation R b : Module.End R A))
    (M : (discreteModules.{max u w} A).FullSubcategory) : extClass hb M = 0 := by
  rw [← extClass_eq_of_inner (δ := (0 : derivationLieAlgebra R A)) continuous_zero hb b
    (by simp)]
  exact extClass_zero M

end TauCeti.DerivationExtension
