/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Extension by zero of compactly supported bundle sections

A compactly supported native section over an open subset extends by zero to a section on the
ambient manifold. Its closed support is exactly the image of the original closed support.
In particular, compactness is required in the open subset, not just in its ambient closure:
this ensures that extension by zero is smooth at the frontier.

`ContMDiffSection.extendByZeroLinearMap` is the resulting linear map between the existing
compactly supported section submodules. Restriction recovers the original section; conversely,
extension recovers any ambient section whose closed support lies in the open subset. Extension
also intertwines multiplication by ambient smooth scalar functions with their restrictions.
These are algebraic operations on test sections; no topology on compactly supported sections is
chosen here.
-/

public noncomputable section

open Bundle Set TopologicalSpace Filter
open scoped Manifold ContDiff Topology

namespace ContMDiffSection

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω} {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)] {U : Opens M}

/-- Closed support commutes with restriction to an open subset. -/
@[simp]
theorem tsupport_restrict (s : Cₛ^n⟮I; F, V⟯) :
    (s.restrict U).tsupport = Subtype.val ⁻¹' s.tsupport := by
  rw [tsupport_def, tsupport_def]
  -- The open carrier and the subtype of its underlying set are the same manifold.
  erw [U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val {x | s x ≠ 0}]
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage]
  erw [restrict_apply]
  rfl

variable [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V] [T2Space M]

/-- Extend a compactly supported section over an open subset by zero. -/
def extendByZero (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) : Cₛ^n⟮I; F, V⟯ where
  toFun x := by
    classical
    exact if hx : x ∈ U then s.1 ⟨x, hx⟩ else 0
  contMDiff_toFun := by
    have hK : IsClosed (Subtype.val '' s.1.tsupport : Set M) :=
      ((mem_compactlySupported.mp s.2).image continuous_subtype_val).isClosed
    intro x
    by_cases hx : x ∈ U
    · have hs := (Pullback.contMDiff_iff
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M))
        (contMDiff_subtype_val (U := U))).mp s.1.contMDiff |>.2
      apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp
      exact (hs ⟨x, hx⟩).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by
        simp [Pullback.lift])
    · have hxK : x ∉ (Subtype.val '' s.1.tsupport : Set M) := by
        rintro ⟨y, -, rfl⟩
        exact hx y.2
      apply ((contMDiff_zeroSection 𝕜 V).of_le le_top x).congr_of_eventuallyEq
      filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
      by_cases hyU : y ∈ U
      · have hyS : (⟨y, hyU⟩ : U) ∉ s.1.tsupport := fun h => hy ⟨⟨y, hyU⟩, h, rfl⟩
        erw [dite_eq_left hyU, s.1.eq_zero_of_notMem_tsupport hyS]
        rfl
      · simp [hyU, zeroSection]

/-- The pointwise formula for extension by zero. -/
theorem extendByZero_apply (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) (x : M) :
    extendByZero s x =
      open Classical in if hx : x ∈ U then s.1 ⟨x, hx⟩ else 0 := (rfl)

/-- Inside the open subset, extension keeps the original fibre value. -/
@[simp]
theorem extendByZero_apply_of_mem (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) (x : U) :
    extendByZero s x = s.1 x := by
  erw [extendByZero_apply, dite_eq_left x.2]

/-- Outside the open subset, extension is zero. -/
@[simp]
theorem extendByZero_apply_of_notMem (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) {x : M}
    (hx : x ∉ U) : extendByZero s x = 0 := by
  rw [extendByZero_apply]
  simp [hx]

/-- The closed support of extension by zero is exactly the image of the original closed support.
Compactness in the open subset ensures that this image is already closed in the ambient base. -/
@[simp]
theorem tsupport_extendByZero (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) :
    (extendByZero s).tsupport = Subtype.val '' s.1.tsupport := by
  have hnonzero : {x : M | extendByZero s x ≠ 0} =
      Subtype.val '' {x : U | s.1 x ≠ 0} := by
    classical
    ext x
    by_cases hx : x ∈ U
    · simp only [mem_ofPred_eq, mem_image]
      erw [extendByZero_apply, dite_eq_left hx]
      exact ⟨fun h => ⟨⟨x, hx⟩, h, rfl⟩, fun ⟨y, hy, heq⟩ => by
        subst x
        exact hy⟩
    · simp [extendByZero_apply, hx, show ¬ ∃ y : U, s.1 y ≠ 0 ∧ (y : M) = x by
        rintro ⟨y, -, rfl⟩; exact hx y.2]
  rw [tsupport_def, hnonzero, tsupport_def]
  apply le_antisymm
  · exact closure_minimal (image_mono subset_closure)
      (by simpa only [← tsupport_def] using
        ((mem_compactlySupported.mp s.2).image continuous_subtype_val).isClosed)
  · exact image_closure_subset_closure_image continuous_subtype_val

/-- Extension by zero preserves compact support. -/
theorem extendByZero_mem_compactlySupported (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) :
    extendByZero s ∈ compactlySupported I F n V := by
  rw [mem_compactlySupported, tsupport_extendByZero]
  exact (mem_compactlySupported.mp s.2).image continuous_subtype_val

/-- Extension by zero as a linear map on compactly supported native section spaces. -/
def extendByZeroLinearMap : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) →ₗ[𝕜]
    compactlySupported I F n V where
  toFun s := ⟨extendByZero s, extendByZero_mem_compactlySupported s⟩
  map_add' s t := by
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ U <;> simp [extendByZero_apply, hx]
    rfl
  map_smul' c s := by
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ U <;> simp [extendByZero_apply, hx]
    rfl

/-- The section underlying the linear extension map is extension by zero. -/
@[simp]
theorem extendByZeroLinearMap_coe (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) :
    dsimp% only [ContinuousMap.coe_mk]
      ((extendByZeroLinearMap s).1 = extendByZero s) := (rfl)

/-- Restriction of extension by zero is the original section. -/
@[simp]
theorem restrict_extendByZero (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) :
    (extendByZero s).restrict U = s.1 := by
  ext x
  simp

/-- Extension by zero is injective. -/
theorem extendByZeroLinearMap_injective : Function.Injective
    (extendByZeroLinearMap (I := I) (F := F) (n := n) (V := V) (U := U)) := by
  intro s t h
  apply Subtype.ext
  have h' := congrArg (fun s : compactlySupported I F n V => s.1.restrict U) h
  -- Normalize the continuous inclusion in the dependent pullback-fibre types.
  erw [extendByZeroLinearMap_coe, extendByZeroLinearMap_coe] at h'
  simpa only [restrict_extendByZero] using h'

omit [T2Space M] in
/-- A compactly supported ambient section supported inside `U` remains compactly supported
when restricted to `U`. Compact support alone would not suffice at the frontier of `U`. -/
theorem restrict_mem_compactlySupported (s : compactlySupported I F n V)
    (hs : s.1.tsupport ⊆ U) : s.1.restrict U ∈ compactlySupported I F n
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) := by
  rw [mem_compactlySupported, tsupport_restrict]
  exact Topology.IsInducing.subtypeVal.isCompact_preimage'
    (mem_compactlySupported.mp s.2) (fun x hx => ⟨⟨x, hs hx⟩, rfl⟩)

/-- An ambient compactly supported section whose closed support lies in the open subset is
recovered by extending its restriction. -/
@[simp]
theorem extendByZero_restrict (s : compactlySupported I F n V) (hs : s.1.tsupport ⊆ U) :
    extendByZero ⟨s.1.restrict U, restrict_mem_compactlySupported s hs⟩ = s.1 := by
  ext x
  by_cases hx : x ∈ U
  · erw [extendByZero_apply, dite_eq_left hx]
    exact restrict_apply s.1 U ⟨x, hx⟩
  · rw [extendByZero_apply_of_notMem _ hx]
    exact (s.1.eq_zero_of_notMem_tsupport (fun h => hx (hs h))).symm

/-- The image of extension by zero consists exactly of the compactly supported ambient sections
whose closed support lies in the open subset. -/
theorem mem_range_extendByZeroLinearMap_iff (s : compactlySupported I F n V) :
    s ∈ LinearMap.range (extendByZeroLinearMap (I := I) (F := F) (n := n) (V := V) (U := U)) ↔
      s.1.tsupport ⊆ U := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [extendByZeroLinearMap_coe, tsupport_extendByZero]
    exact fun _ ⟨x, _, hx⟩ => hx ▸ x.2
  · intro hs
    refine ⟨⟨s.1.restrict U, restrict_mem_compactlySupported s hs⟩, Subtype.ext ?_⟩
    exact extendByZero_restrict s hs

/-- Extension commutes with multiplication by an ambient smooth scalar function, restricted
on the source. This is the module compatibility used to localize test sections. -/
@[simp]
theorem extendByZero_smul_function (f : C^n⟮I, M; 𝕜⟯)
    (s : compactlySupported I F n
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) :
    extendByZero
      ⟨f.comp (⟨Subtype.val, contMDiff_subtype_val⟩ : C^n⟮I, U; I, M⟯) • s.1,
        smul_function_mem_compactlySupported _ s.2⟩ = f • extendByZero s := by
  ext x
  by_cases hx : x ∈ U <;> simp [extendByZero_apply, hx]
  rfl

end ContMDiffSection
