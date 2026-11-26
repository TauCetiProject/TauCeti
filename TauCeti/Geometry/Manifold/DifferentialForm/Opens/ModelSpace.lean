/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Opens

/-!
# Flat differential forms on open subsets of normed spaces

On an open subset of a real normed space, the canonical tangent coordinates identify a
rough differential form with a field of continuous alternating maps. This file compares
regularity and exterior differentiation of such a form with those of an ambient
representative. Only values on the open subset matter; no smooth extension across its
boundary is required. In every degree the flat field is already the underlying function of
`RoughForm`; in degree one `RoughForm.flatOneFormEquiv` additionally identifies alternating
maps with continuous linear maps using Mathlib's `ContinuousAlternatingMap.ofSubsingletonLIE`.

The main comparisons are `isSmoothForm_opens_iff`,
`mextDerivWithin_opens_eq_extDerivWithin`, and `mextDeriv_opens_eq_extDeriv`. The last two
hold even at points of nondifferentiability, with the native total derivatives on both sides.
Their degree-zero specialization is `RoughForm.flatOneFormEquiv_mextDeriv_ofFunction`.
-/

public section

noncomputable section

open Set Filter TopologicalSpace Bundle
open scoped Manifold Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Opens E} {k : ℕ}

/-- The coordinate expression of a form on an open subset agrees locally with any ambient
representative. -/
theorem RoughForm.inChartAt_opens_eventuallyEq (ω : RoughForm 𝓘(ℝ, E) U F k)
    (ω₀ : E → E [⋀^Fin k]→L[ℝ] F) (hω : ∀ x : U, ω x = ω₀ x) (x : U) :
    ω.inChartAt x =ᶠ[𝓝 (x : E)] ω₀ := by
  have he := U.chartAt_subtypeVal_symm_eventuallyEq (H := E) (x := x)
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply] at he
  filter_upwards [he.eventually_nhds] with z hz
  have hz₀ : id =ᶠ[𝓝 z] Subtype.val ∘ (chartAt E x).symm := hz
  have hz' : (Subtype.val ∘ (extChartAt 𝓘(ℝ, E) x).symm) =ᶠ[𝓝 z] id := hz₀.symm
  have hp : ((extChartAt 𝓘(ℝ, E) x).symm z : E) = z := hz'.self_of_nhds
  have hd : mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) x).symm (range 𝓘(ℝ, E)) z =
      ContinuousLinearMap.id ℝ E := by
    ext v
    have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (Subtype.val ∘ (extChartAt 𝓘(ℝ, E) x).symm) z = ContinuousLinearMap.id ℝ E := by
      rw [mfderiv_eq_fderiv, hz'.fderiv_eq, fderiv_id]
      -- The canonical tangent identifications of the normed model are identities.
      rfl
    have hdv := congrArg (fun L ↦ L v) hd
    rw [Manifold.mfderiv_subtype_val_comp_apply] at hdv
    simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ]
    -- The inverse chart's target tangent fibre is the same flat model fibre.
    convert! hdv
  ext v
  rw [RoughForm.inChartAt_apply, hd, hω, hp]
  -- In the flat tangent coordinates the identity acts pointwise on the tuple.
  rfl

/-- Regularity of a form on an open subset is exactly regularity of any ambient
representative on that subset. The representative need not be regular outside it. -/
theorem isSmoothForm_opens_iff {n : WithTop ℕ∞}
    {ω : RoughForm 𝓘(ℝ, E) U F k} {ω₀ : E → E [⋀^Fin k]→L[ℝ] F}
    (hω : ∀ x : U, ω x = ω₀ x) :
    IsSmoothForm 𝓘(ℝ, E) n ω ↔ ContDiffOn ℝ n ω₀ U := by
  rw [isSmoothForm_def, U.isOpen.contDiffOn_iff]
  have key (x : U) :
      ContDiffWithinAt ℝ n (ω.inChartAt x) (range 𝓘(ℝ, E))
          (extChartAt 𝓘(ℝ, E) x x) ↔ ContDiffAt ℝ n ω₀ (x : E) := by
    -- The canonical open-subtype chart is the ambient inclusion.
    have hx : extChartAt 𝓘(ℝ, E) x x = (x : E) := rfl
    rw [hx, modelWithCornersSelf_coe, range_id,
      contDiffWithinAt_univ]
    have heq : ω.inChartAt x =ᶠ[𝓝 (x : E)] ω₀ := ω.inChartAt_opens_eventuallyEq ω₀ hω x
    exact ⟨fun h ↦ h.congr_of_eventuallyEq heq.symm,
      fun h ↦ h.congr_of_eventuallyEq heq⟩
  exact ⟨fun h x hx ↦ (key ⟨x, hx⟩).mp
      (ω.contDiffWithinAt_range_inChartAt_of_contMDiffAt (h ⟨x, hx⟩)),
    fun h x ↦ contMDiffAt_form_of_contDiffWithinAt_inChartAt_self
      ((key x).mpr (h x.property))⟩

/-- Exterior differentiation within an arbitrary subset of an open model domain agrees
with flat exterior differentiation of an ambient representative. No regularity is needed. -/
theorem mextDerivWithin_opens_eq_extDerivWithin
    {ω : RoughForm 𝓘(ℝ, E) U F k} {ω₀ : E → E [⋀^Fin k]→L[ℝ] F}
    (hω : ∀ x : U, ω x = ω₀ x) (s : Set U) (x : U) :
    mextDerivWithin ω s x = extDerivWithin ω₀ (Subtype.val '' s) (x : E) := by
  have he := U.chartAt_subtypeVal_symm_eventuallyEq (H := E) (x := x)
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply] at he
  have hs : (extChartAt 𝓘(ℝ, E) x).symm ⁻¹' s =ᶠ[𝓝 (x : E)] Subtype.val '' s := by
    filter_upwards [he] with z hz
    have hp : ((extChartAt 𝓘(ℝ, E) x).symm z : E) = z := hz.symm
    constructor
    · intro hz
      exact ⟨_, hz, hp⟩
    · rintro ⟨y, hy, rfl⟩
      have hxy : (extChartAt 𝓘(ℝ, E) x).symm (y : E) = y := Subtype.ext hp
      simpa only [mem_preimage, hxy] using hy
  -- The canonical open-subtype chart is the ambient inclusion.
  have hx : extChartAt 𝓘(ℝ, E) x x = (x : E) := rfl
  rw [mextDerivWithin_def, hx, modelWithCornersSelf_coe,
    range_id, inter_univ]
  rw [(ω.inChartAt_opens_eventuallyEq ω₀ hω x).extDerivWithin_eq_nhds,
    extDerivWithin_congr_set hs]

/-- Exterior differentiation on an open model domain is flat exterior differentiation of
any ambient representative, independently of its values outside the domain. -/
theorem mextDeriv_opens_eq_extDeriv
    {ω : RoughForm 𝓘(ℝ, E) U F k} {ω₀ : E → E [⋀^Fin k]→L[ℝ] F}
    (hω : ∀ x : U, ω x = ω₀ x) (x : U) :
    mextDeriv ω x = extDeriv ω₀ (x : E) := by
  rw [← mextDerivWithin_univ, mextDerivWithin_opens_eq_extDerivWithin hω,
    image_univ, Subtype.range_coe_subtype]
  exact extDerivWithin_of_mem_nhds (U.isOpen.mem_nhds x.property)

/-- A regular form on an open model domain has an ambient representative regular on that
domain. This asserts no regularity of the representative across its boundary. -/
theorem IsSmoothForm.exists_contDiffOn_opens {n : WithTop ℕ∞}
    {ω : RoughForm 𝓘(ℝ, E) U F k} (hω : IsSmoothForm 𝓘(ℝ, E) n ω) :
    ∃ ω₀ : E → E [⋀^Fin k]→L[ℝ] F, ContDiffOn ℝ n ω₀ U ∧ ∀ x : U, ω x = ω₀ x := by
  let ω₀ := Function.extend (Subtype.val : U → E)
    (ω : U → E [⋀^Fin k]→L[ℝ] F) (0 : E → E [⋀^Fin k]→L[ℝ] F)
  have heq (x : U) : ω x = ω₀ x :=
    (Subtype.val_injective.extend_apply
      (ω : U → E [⋀^Fin k]→L[ℝ] F) (0 : E → E [⋀^Fin k]→L[ℝ] F) x).symm
  exact ⟨ω₀, (isSmoothForm_opens_iff heq).mp hω, heq⟩

/-- A form on an open model domain is closed exactly when its ambient representative has
vanishing flat exterior derivative on that domain. -/
theorem mextDeriv_opens_eq_zero_iff
    {ω : RoughForm 𝓘(ℝ, E) U F k} {ω₀ : E → E [⋀^Fin k]→L[ℝ] F}
    (hω : ∀ x : U, ω x = ω₀ x) :
    mextDeriv ω = 0 ↔ ∀ x ∈ U, extDeriv ω₀ x = 0 := by
  constructor
  · intro h x hx
    exact (mextDeriv_opens_eq_extDeriv hω ⟨x, hx⟩).symm.trans (congrFun h ⟨x, hx⟩)
  · intro h
    funext x
    exact (mextDeriv_opens_eq_extDeriv hω x).trans (h x x.property)

/-- Degree-one rough forms on a canonical open model domain are exactly fields of
continuous linear maps. This is a pointwise equivalence, imposing no continuity in the base. -/
def RoughForm.flatOneFormEquiv (U : Opens E) :
    RoughForm 𝓘(ℝ, E) U F 1 ≃ₗ[ℝ] (U → E →L[ℝ] F) :=
  LinearEquiv.piCongrRight fun _ ↦
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F)
      (ι := Fin 1) 0).toLinearEquiv.symm

/-- The flat one-form adapter evaluates on the singleton tangent tuple. -/
@[simp]
theorem RoughForm.flatOneFormEquiv_apply (ω : RoughForm 𝓘(ℝ, E) U F 1) (x : U) (v : E) :
    flatOneFormEquiv U ω x v = ω x ![v] := by
  exact congrArg (fun w : Fin 1 → E ↦ ω x w) (Matrix.const_fin1_eq v)

/-- The inverse adapter evaluates the linear field on the unique member of a tangent tuple. -/
@[simp]
theorem RoughForm.flatOneFormEquiv_symm_apply (η : U → E →L[ℝ] F) (x : U) (v : Fin 1 → E) :
    (flatOneFormEquiv U).symm η x v = η x (v 0) := by
  rfl

/-- For one-forms, regularity of an ambient covector representative is equivalent to
regularity of the manifold form. -/
theorem isSmoothForm_opens_one_iff {n : WithTop ℕ∞}
    {ω : RoughForm 𝓘(ℝ, E) U F 1} {η : E → E →L[ℝ] F}
    (hω : ∀ x : U, RoughForm.flatOneFormEquiv U ω x = η x) :
    IsSmoothForm 𝓘(ℝ, E) n ω ↔ ContDiffOn ℝ n η U := by
  let L := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F)
    (ι := Fin 1) 0).toContinuousLinearEquiv
  have heq (x : U) : ω x = L (η x) := by
    apply L.symm.injective
    rw [ContinuousLinearEquiv.symm_apply_apply]
    -- The adapter is the pointwise inverse of this native linear isometry.
    convert! hω x
  rw [isSmoothForm_opens_iff (ω₀ := fun y ↦ L (η y)) heq]
  exact L.comp_contDiffOn_iff

/-- The flat covector field of a regular one-form is continuous, even when no global
ambient smooth extension exists. -/
theorem IsSmoothForm.continuous_flatOneFormEquiv {n : WithTop ℕ∞}
    {ω : RoughForm 𝓘(ℝ, E) U F 1} (hω : IsSmoothForm 𝓘(ℝ, E) n ω) :
    Continuous (RoughForm.flatOneFormEquiv U ω) := by
  obtain ⟨ω₀, hω₀, heq⟩ := hω.exists_contDiffOn_opens
  let L := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F)
    (ι := Fin 1) 0).symm
  have hc : Continuous (fun x : U ↦ ω₀ x) :=
    hω₀.continuousOn.comp_continuous continuous_subtypeVal fun x ↦ x.property
  exact (L.continuous.comp hc).congr fun x ↦ congrArg L (heq x).symm

/-- The flat one-form adapter of the differential of a restricted function is its ambient
Fréchet derivative, including the junk values at points of nondifferentiability. -/
@[simp]
theorem RoughForm.flatOneFormEquiv_mextDeriv_ofFunction (f : E → F) (x : U) :
    flatOneFormEquiv U (mextDeriv (ofFunction 𝓘(ℝ, E) fun y : U ↦ f y)) x =
      fderiv ℝ f (x : E) := by
  ext v
  rw [flatOneFormEquiv_apply, mextDeriv_opens_eq_extDeriv
    (ω₀ := fun y ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f y))
    (fun y ↦ ofFunction_apply_eq_constOfIsEmpty _ y), extDeriv_constOfIsEmpty]
  rfl

end TauCeti
