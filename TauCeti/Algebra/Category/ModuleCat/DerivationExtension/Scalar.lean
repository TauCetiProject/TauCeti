/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.DerivationExtension.Basic
public import TauCeti.Algebra.Lie.Derivation.Continuous
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.ShortComplex.Pushout

/-!
# Central scalars and derivation self-extensions

For a central element `z` of an associative algebra, the map
`E_δ(M) → E_(z • δ)(M)`, `(u, v) ↦ (z • u, v)`, pushes the derivation self-extension forward
along central multiplication on `M`. We construct this map and identify the resulting pushout
with `E_(z • δ)(M)` in the abelian category of discrete modules. Consequently its native
`Ext¹` class is the pushforward of the class of `E_δ(M)` along central multiplication.
This applies to every element of the full algebraic center, including nonunits and zero.

The self-extension construction follows E. Frenkel, *Langlands Correspondence for Loop Groups*
(2007). The extension-class comparison uses Mathlib's
`ShortComplex.ShortExact.extClass_naturality` and its pushout universal property.
-/

public section

namespace TauCeti.DerivationExtension

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w

variable {R : Type*} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  (z : Subalgebra.center R A) (δ : derivationLieAlgebra R A)

section Module

variable (M : Type v) [AddCommGroup M] [Module A M]

/-- The central-scalar comparison, multiplying the submodule coordinate by `z` and fixing
the quotient coordinate. -/
def scalarMap : DerivationExtension δ M →ₗ[A] DerivationExtension (z • δ) M where
  toFun x := ⟨(z : A) • x.fst, x.snd⟩
  map_add' x y := by ext <;> simp [smul_add]
  map_smul' a x := by
    ext
    · simp only [fst_smul, derivationLieAlgebra.center_smul_apply, smul_add, RingHom.id_apply]
      simp only [← mul_smul]
      rw [Subalgebra.mem_center_iff.mp z.property a]
    · simp

@[simp]
theorem fst_scalarMap (x : DerivationExtension δ M) :
    (scalarMap z δ M x).fst = (z : A) • x.fst :=
  (rfl)

@[simp]
theorem snd_scalarMap (x : DerivationExtension δ M) :
    (scalarMap z δ M x).snd = x.snd :=
  (rfl)

/-- The comparison restricts to central multiplication on the submodule. -/
theorem scalarMap_comp_inlHom :
    scalarMap z δ M ∘ₗ inlHom δ M =
      inlHom (z • δ) M ∘ₗ Module.End.smulLeft (z : A) z.property := by
  ext x
  · simp only [LinearMap.comp_apply, fst_scalarMap, fst_inlHom]
    exact (Module.End.smulLeft_apply (M := M) (z : A) z.property x).symm
  · simp

/-- The comparison induces the identity on the quotient. -/
@[simp]
theorem sndHom_comp_scalarMap :
    sndHom (z • δ) M ∘ₗ scalarMap z δ M = sndHom δ M := by
  ext x
  simp

end Module

section Discrete

variable [TopologicalSpace A] [SeparatelyContinuousMul A]
  (hδ : Continuous (δ : Module.End R A)) (M : (discreteModules.{v} A).FullSubcategory)

/-- The central-scalar comparison as a morphism of actual discrete-module extensions. -/
def discreteScalarMap : discreteShortComplex hδ M ⟶
    discreteShortComplex (derivationLieAlgebra.continuous_center_smul z hδ) M where
  τ₁ := ObjectProperty.homMk (ModuleCat.ofHom (Module.End.smulLeft (z : A) z.property))
  τ₂ := ObjectProperty.homMk (ModuleCat.ofHom (scalarMap z δ M.obj))
  τ₃ := 𝟙 _
  comm₁₂ := by
    apply ObjectProperty.hom_ext
    exact ModuleCat.hom_ext (scalarMap_comp_inlHom z δ M.obj).symm
  comm₂₃ := by
    apply ObjectProperty.hom_ext
    exact ModuleCat.hom_ext (sndHom_comp_scalarMap z δ M.obj)

-- Endpoint equations are named rewrites: ordinary importing simp can leave identities whose
-- dependent short-complex endpoint presentations differ. Coordinate and pushout-leg rules do
-- have robust simplifier forms.
theorem discreteScalarMap_τ₁ : (discreteScalarMap z δ hδ M).τ₁ =
    ObjectProperty.homMk (ModuleCat.ofHom (Module.End.smulLeft (z : A) z.property)) :=
  (rfl)

@[simp]
theorem discreteScalarMap_τ₂ : (discreteScalarMap z δ hδ M).τ₂ =
    ObjectProperty.homMk (ModuleCat.ofHom (scalarMap z δ M.obj)) :=
  (rfl)

theorem discreteScalarMap_τ₃ : (discreteScalarMap z δ hδ M).τ₃ = 𝟙 M :=
  (rfl)

/-- Pushing the self-extension along central multiplication gives the self-extension of the
centrally scaled derivation, in the category of discrete modules. -/
noncomputable def discretePushIso :
    (discreteShortComplex hδ M).push (discreteScalarMap z δ hδ M).τ₁ ≅
      discreteShortComplex (derivationLieAlgebra.continuous_center_smul z hδ) M := by
  let φ := discreteScalarMap z δ hδ M
  let ψ : (discreteShortComplex hδ M).push φ.τ₁ ⟶
      discreteShortComplex (derivationLieAlgebra.continuous_center_smul z hδ) M :=
    { τ₁ := 𝟙 M
      τ₂ := pushout.desc φ.τ₂
        (discreteShortComplex (derivationLieAlgebra.continuous_center_smul z hδ) M).f
        φ.comm₁₂.symm
      τ₃ := 𝟙 M
      -- Direct universal-property equations preserve the selected endpoint carriers.
      comm₁₂ := (Category.id_comp _).trans (pushout.inr_desc _ _ _).symm
      comm₂₃ := by
        apply pushout.hom_ext
        · exact (pushout.inl_desc_assoc _ _ _ _).trans
            (φ.comm₂₃.trans (pushout.inl_desc_assoc _ _ _ _).symm)
        · exact (pushout.inr_desc_assoc _ _ _ _).trans
            ((discreteShortComplex
              (derivationLieAlgebra.continuous_center_smul z hδ) M).zero.trans
              ((zero_comp).symm.trans (pushout.inr_desc_assoc _ _ _ _).symm)) }
  have : IsIso ψ.τ₁ := inferInstanceAs (IsIso (𝟙 M))
  have : IsIso ψ.τ₃ := inferInstanceAs (IsIso (𝟙 M))
  have : IsIso ψ.τ₂ := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ ψ
    ((shortExact_discreteShortComplex hδ M).push φ.τ₁)
    (shortExact_discreteShortComplex _ M)
  exact ShortComplex.isoMk (Iso.refl M) (asIso ψ.τ₂) (Iso.refl M)
    ψ.comm₁₂ ψ.comm₂₃

theorem discretePushIso_hom_τ₁ : (discretePushIso z δ hδ M).hom.τ₁ = 𝟙 M :=
  (rfl)

theorem discretePushIso_hom_τ₃ : (discretePushIso z δ hδ M).hom.τ₃ = 𝟙 M :=
  (rfl)

theorem discretePushIso_inv_τ₁ : (discretePushIso z δ hδ M).inv.τ₁ = 𝟙 M :=
  (rfl)

theorem discretePushIso_inv_τ₃ : (discretePushIso z δ hδ M).inv.τ₃ = 𝟙 M :=
  (rfl)

/-- On the original extension, the pushout comparison is `(u,v) ↦ (z • u,v)`. -/
@[reassoc (attr := simp)]
theorem inl_discretePushIso_hom_τ₂ :
    pushout.inl (discreteShortComplex hδ M).f (discreteScalarMap z δ hδ M).τ₁ ≫
      (discretePushIso z δ hδ M).hom.τ₂ = (discreteScalarMap z δ hδ M).τ₂ := by
  unfold discretePushIso
  exact pushout.inl_desc _ _ _

/-- On the new submodule, the pushout comparison is the original inclusion. -/
@[reassoc (attr := simp)]
theorem inr_discretePushIso_hom_τ₂ :
    pushout.inr (discreteShortComplex hδ M).f (discreteScalarMap z δ hδ M).τ₁ ≫
      (discretePushIso z δ hδ M).hom.τ₂ =
        (discreteShortComplex (derivationLieAlgebra.continuous_center_smul z hδ) M).f := by
  unfold discretePushIso
  exact pushout.inr_desc _ _ _

variable [HasExt.{w} (discreteModules.{v} A).FullSubcategory]

/-- Central scaling of a derivation pushes its native discrete-module extension class forward
along central multiplication on the module. -/
theorem extClass_center_smul :
    (shortExact_discreteShortComplex
      (derivationLieAlgebra.continuous_center_smul z hδ) M).extClass =
      (shortExact_discreteShortComplex hδ M).extClass.comp
        (Ext.mk₀ (ObjectProperty.homMk
          (ModuleCat.ofHom (Module.End.smulLeft (z : A) z.property)))) (add_zero 1) := by
  have h := (shortExact_discreteShortComplex hδ M).extClass_naturality
    (shortExact_discreteShortComplex (derivationLieAlgebra.continuous_center_smul z hδ) M)
    (discreteScalarMap z δ hδ M)
  -- Identify the endpoints before simplifying the dependent Ext composition.
  simp only [discreteScalarMap_τ₁, discreteScalarMap_τ₃] at h
  dsimp only [discreteShortComplex] at h ⊢
  simpa using h.symm

end Discrete

end TauCeti.DerivationExtension
