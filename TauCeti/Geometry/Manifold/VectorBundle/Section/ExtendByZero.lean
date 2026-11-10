/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module

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

variable [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V] [T2Space M]

/-- The image of a compactly supported section's closed support under an open inclusion is
closed in the ambient Hausdorff manifold. -/
theorem isClosed_image_tsupport (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) :
    IsClosed (Subtype.val '' s.1.tsupport : Set M) :=
  ((mem_compactlySupported.mp s.2).image continuous_subtype_val).isClosed

/-- Extend a compactly supported section over an open subset by zero. -/
def extendByZero (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) : Cₛ^n⟮I; F, V⟯ where
  toFun x := by
    classical
    exact if hx : x ∈ U then s.1 ⟨x, hx⟩ else 0
  contMDiff_toFun := by
    have hK := isClosed_image_tsupport s
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
        -- Normalize the pullback fibre before comparing total-space values.
        erw [dite_eq_left hyU, s.1.eq_zero_of_notMem_tsupport hyS]
        rfl
      · simp [hyU, zeroSection]

/-- The pointwise formula for extension by zero. -/
theorem extendByZero_apply (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) (x : M) :
    dsimp% only [ContinuousMap.coe_mk]
      (extendByZero s x =
        open Classical in if hx : x ∈ U then s.1 ⟨x, hx⟩ else 0) := (rfl)

/-- Inside the open subset, extension keeps the original fibre value. -/
@[simp]
theorem extendByZero_apply_of_mem (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) (x : U) :
    dsimp% only [ContinuousMap.coe_mk] (extendByZero s x = s.1 x) := by
  -- The dependent conditional has pullback fibres, definitionally equal to `V x`.
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
      rw [extendByZero_apply_of_mem s ⟨x, hx⟩]
      exact ⟨fun h => ⟨⟨x, hx⟩, h, rfl⟩, fun ⟨y, hy, heq⟩ => by
        subst x
        exact hy⟩
    · simp [extendByZero_apply, hx, show ¬ ∃ y : U, s.1 y ≠ 0 ∧ (y : M) = x by
        rintro ⟨y, -, rfl⟩; exact hx y.2]
  have hK := isClosed_image_tsupport s
  rw [tsupport_def] at hK
  rw [tsupport_def, hnonzero, tsupport_def]
  apply le_antisymm
  · exact closure_minimal (image_mono subset_closure) hK
  · exact image_closure_subset_closure_image continuous_subtype_val

/-- Extension by zero preserves compact support. -/
theorem extendByZero_mem_compactlySupported (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) :
    extendByZero s ∈ compactlySupported I F n V := by
  rw [mem_compactlySupported, tsupport_extendByZero]
  exact (mem_compactlySupported.mp s.2).image continuous_subtype_val

/-- Extension by zero preserves the zero section. -/
@[simp]
theorem extendByZero_zero :
    extendByZero (0 : compactlySupported I F n
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) = 0 := by
  ext x
  by_cases hx : x ∈ U
  · rw [extendByZero_apply_of_mem _ ⟨x, hx⟩]
    exact congrFun (coe_zero (I := I) (F := F) (n := n)) (⟨x, hx⟩ : U)
  · simp [extendByZero_apply_of_notMem _ hx]

/-- Extension by zero preserves addition. -/
@[simp]
theorem extendByZero_add (s t : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) :
    extendByZero (s + t) = extendByZero s + extendByZero t := by
  ext x
  by_cases hx : x ∈ U
  · simp only [coe_add, Pi.add_apply]
    rw [extendByZero_apply_of_mem _ ⟨x, hx⟩, extendByZero_apply_of_mem s ⟨x, hx⟩,
      extendByZero_apply_of_mem t ⟨x, hx⟩]
    exact congrFun (coe_add s.1 t.1) ⟨x, hx⟩
  · simp [extendByZero_apply_of_notMem _ hx]

/-- Extension by zero commutes with ground-field scalar multiplication. -/
@[simp]
theorem extendByZero_smul (c : 𝕜) (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) :
    extendByZero (c • s) = c • extendByZero s := by
  ext x
  by_cases hx : x ∈ U
  · simp only [coe_smul, Pi.smul_apply]
    rw [extendByZero_apply_of_mem _ ⟨x, hx⟩, extendByZero_apply_of_mem s ⟨x, hx⟩]
    exact congrFun (coe_smul c s.1) ⟨x, hx⟩
  · simp [extendByZero_apply_of_notMem _ hx]

/-- Extension by zero as a linear map on compactly supported native section spaces. -/
def extendByZeroLinearMap : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V) →ₗ[𝕜]
    compactlySupported I F n V where
  toFun s := ⟨extendByZero s, extendByZero_mem_compactlySupported s⟩
  map_add' s t := Subtype.ext (extendByZero_add s t)
  map_smul' c s := Subtype.ext (extendByZero_smul c s)

/-- The section underlying the linear extension map is extension by zero. -/
@[simp]
theorem extendByZeroLinearMap_apply (s : compactlySupported I F n
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
theorem extendByZero_injective : Function.Injective
    (extendByZero (I := I) (F := F) (n := n) (V := V) (U := U)) := by
  intro s t h
  apply Subtype.ext
  simpa only [restrict_extendByZero] using congrArg (fun s => s.restrict U) h

/-- Equality of extensions by zero is equivalent to equality of the original sections. -/
@[simp]
theorem extendByZero_inj (s t : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V)) :
    extendByZero s = extendByZero t ↔ s = t :=
  extendByZero_injective.eq_iff

/-- The linear extension-by-zero map is injective. -/
theorem extendByZeroLinearMap_injective : Function.Injective
    (extendByZeroLinearMap (I := I) (F := F) (n := n) (V := V) (U := U)) := by
  intro s t h
  exact extendByZero_injective (congrArg Subtype.val h)

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
  · rw [extendByZero_apply_of_mem _ ⟨x, hx⟩, restrict_apply]
  · rw [extendByZero_apply_of_notMem _ hx]
    exact (s.1.eq_zero_of_notMem_tsupport (fun h => hx (hs h))).symm

/-- The image of extension by zero consists exactly of the compactly supported ambient sections
whose closed support lies in the open subset. -/
theorem mem_range_extendByZeroLinearMap_iff (s : compactlySupported I F n V) :
    s ∈ LinearMap.range (extendByZeroLinearMap (I := I) (F := F) (n := n) (V := V) (U := U)) ↔
      s.1.tsupport ⊆ U := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [extendByZeroLinearMap_apply, tsupport_extendByZero]
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
  by_cases hx : x ∈ U
  · rw [smul_apply, extendByZero_apply_of_mem _ ⟨x, hx⟩,
      extendByZero_apply_of_mem s ⟨x, hx⟩]
    exact smul_apply _ s.1 ⟨x, hx⟩
  · simp [extendByZero_apply_of_notMem _ hx]

end ContMDiffSection
