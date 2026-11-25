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

`ContMDiffSection.extendByZeroToOpenLinearMap` extends compactly supported sections between
nested open subsets, with its support, identity and composition laws, and
`ContMDiffSection.restrictUnivLinearMap` restricts compactly supported sections to the universal
open subset.
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
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
    IsClosed (Subtype.val '' s.val.tsupport : Set M) :=
  ((mem_compactlySupported.mp s.property).image continuous_subtypeVal).isClosed

/-- Extend a compactly supported section over an open subset by zero. -/
def extendByZero (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) : Cₛ^n⟮I; F, V⟯ where
  toFun x := by
    classical
    exact if hx : x ∈ U then s.val ⟨x, hx⟩ else 0
  contMDiff_toFun := by
    have hK := isClosed_image_tsupport s
    intro x
    by_cases hx : x ∈ U
    · have hs := (Pullback.contMDiff_iff
        (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))
        (contMDiff_subtypeVal (U := U))).mp s.val.contMDiff |>.2
      apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp
      exact (hs ⟨x, hx⟩).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by
        simp [Pullback.lift])
    · have hxK : x ∉ (Subtype.val '' s.val.tsupport : Set M) := by
        rintro ⟨y, -, rfl⟩
        exact hx y.property
      apply ((contMDiff_zeroSection 𝕜 V).of_le le_top x).congr_of_eventuallyEq
      filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
      by_cases hyU : y ∈ U
      · have hyS : (⟨y, hyU⟩ : U) ∉ s.val.tsupport := fun h => hy ⟨⟨y, hyU⟩, h, rfl⟩
        -- Normalize the pullback fibre before comparing total-space values.
        erw [dite_eq_left hyU, s.val.eq_zero_of_notMem_tsupport hyS]
        rfl
      · simp [hyU, zeroSection]

/-- The pointwise formula for extension by zero. -/
theorem extendByZero_apply (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) (x : M) :
    dsimp% only [ContinuousMap.coe_mk]
      (extendByZero s x =
        open Classical in if hx : x ∈ U then s.val ⟨x, hx⟩ else 0) := (rfl)

/-- Inside the open subset, extension keeps the original fibre value. -/
@[simp]
theorem extendByZero_apply_of_mem (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) (x : U) :
    dsimp% only [ContinuousMap.coe_mk] (extendByZero s x = s.val x) := by
  -- The dependent conditional has pullback fibres, definitionally equal to `V x`.
  erw [extendByZero_apply, dite_eq_left x.property]

/-- Outside the open subset, extension is zero. -/
@[simp]
theorem extendByZero_apply_of_notMem (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) {x : M}
    (hx : x ∉ U) : extendByZero s x = 0 := by
  rw [extendByZero_apply]
  simp [hx]

/-- The closed support of extension by zero is exactly the image of the original closed support.
Compactness in the open subset ensures that this image is already closed in the ambient base. -/
@[simp]
theorem tsupport_extendByZero (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
    (extendByZero s).tsupport = Subtype.val '' s.val.tsupport := by
  have hnonzero : {x : M | extendByZero s x ≠ 0} =
      Subtype.val '' {x : U | s.val x ≠ 0} := by
    classical
    ext x
    by_cases hx : x ∈ U
    · simp only [mem_ofPred_eq, mem_image]
      rw [extendByZero_apply_of_mem s ⟨x, hx⟩]
      exact ⟨fun h => ⟨⟨x, hx⟩, h, rfl⟩, fun ⟨y, hy, heq⟩ => by
        subst x
        exact hy⟩
    · simp [extendByZero_apply, hx, show ¬ ∃ y : U, s.val y ≠ 0 ∧ (y : M) = x by
        rintro ⟨y, -, rfl⟩; exact hx y.property]
  have hK := isClosed_image_tsupport s
  rw [tsupport_def] at hK
  rw [tsupport_def, hnonzero, tsupport_def]
  apply le_antisymm
  · exact closure_minimal (image_mono subset_closure) hK
  · exact image_closure_subset_closure_image continuous_subtypeVal

/-- Extension by zero preserves compact support. -/
theorem extendByZero_mem_compactlySupported (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
    extendByZero s ∈ compactlySupported I F n V := by
  rw [mem_compactlySupported, tsupport_extendByZero]
  exact (mem_compactlySupported.mp s.property).image continuous_subtypeVal

/-- Extension by zero preserves the zero section. -/
@[simp]
theorem extendByZero_zero :
    extendByZero (0 : compactlySupported I F n
      ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) = 0 := by
  ext x
  by_cases hx : x ∈ U
  · rw [extendByZero_apply_of_mem _ ⟨x, hx⟩]
    exact congrFun (coe_zero (I := I) (F := F) (n := n)) (⟨x, hx⟩ : U)
  · simp [extendByZero_apply_of_notMem _ hx]

/-- Extension by zero preserves addition. -/
@[simp]
theorem extendByZero_add (s t : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
    extendByZero (s + t) = extendByZero s + extendByZero t := by
  ext x
  by_cases hx : x ∈ U
  · simp only [coe_add, Pi.add_apply]
    rw [extendByZero_apply_of_mem _ ⟨x, hx⟩, extendByZero_apply_of_mem s ⟨x, hx⟩,
      extendByZero_apply_of_mem t ⟨x, hx⟩]
    exact congrFun (coe_add s.val t.val) ⟨x, hx⟩
  · simp [extendByZero_apply_of_notMem _ hx]

/-- Extension by zero commutes with ground-field scalar multiplication. -/
@[simp]
theorem extendByZero_smul (c : 𝕜) (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
    extendByZero (c • s) = c • extendByZero s := by
  ext x
  by_cases hx : x ∈ U
  · simp only [coe_smul, Pi.smul_apply]
    rw [extendByZero_apply_of_mem _ ⟨x, hx⟩, extendByZero_apply_of_mem s ⟨x, hx⟩]
    exact congrFun (coe_smul c s.val) ⟨x, hx⟩
  · simp [extendByZero_apply_of_notMem _ hx]

/-- Extension by zero as a linear map on compactly supported native section spaces. -/
def extendByZeroLinearMap : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) →ₗ[𝕜]
    compactlySupported I F n V where
  toFun s := ⟨extendByZero s, extendByZero_mem_compactlySupported s⟩
  map_add' s t := Subtype.ext (extendByZero_add s t)
  map_smul' c s := Subtype.ext (extendByZero_smul c s)

/-- The section underlying the linear extension map is extension by zero. -/
@[simp]
theorem extendByZeroLinearMap_apply (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
    dsimp% only [ContinuousMap.coe_mk]
      ((extendByZeroLinearMap s).val = extendByZero s) := (rfl)

/-- Restriction of extension by zero is the original section. -/
@[simp]
theorem restrict_extendByZero (s : compactlySupported I F n
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
    (extendByZero s).restrict U = s.val := by
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
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
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
    (hs : s.val.tsupport ⊆ U) : s.val.restrict U ∈ compactlySupported I F n
      ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) := by
  rw [mem_compactlySupported, tsupport_restrict]
  exact Topology.IsInducing.subtypeVal.isCompact_preimage'
    (mem_compactlySupported.mp s.property) (fun x hx => ⟨⟨x, hs hx⟩, rfl⟩)

/-- An ambient compactly supported section whose closed support lies in the open subset is
recovered by extending its restriction. -/
@[simp]
theorem extendByZero_restrict (s : compactlySupported I F n V) (hs : s.val.tsupport ⊆ U) :
    extendByZero ⟨s.val.restrict U, restrict_mem_compactlySupported s hs⟩ = s.val := by
  ext x
  by_cases hx : x ∈ U
  · rw [extendByZero_apply_of_mem _ ⟨x, hx⟩, restrict_apply]
  · rw [extendByZero_apply_of_notMem _ hx]
    exact (s.val.eq_zero_of_notMem_tsupport (fun h => hx (hs h))).symm

/-- The image of extension by zero consists exactly of the compactly supported ambient sections
whose closed support lies in the open subset. -/
theorem mem_range_extendByZeroLinearMap_iff (s : compactlySupported I F n V) :
    s ∈ LinearMap.range (extendByZeroLinearMap (I := I) (F := F) (n := n) (V := V) (U := U)) ↔
      s.val.tsupport ⊆ U := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [extendByZeroLinearMap_apply, tsupport_extendByZero]
    exact fun _ ⟨x, _, hx⟩ => hx ▸ x.property
  · intro hs
    refine ⟨⟨s.val.restrict U, restrict_mem_compactlySupported s hs⟩, Subtype.ext ?_⟩
    exact extendByZero_restrict s hs

/-- Extension commutes with multiplication by an ambient smooth scalar function, restricted
on the source. This is the module compatibility used to localize test sections. -/
@[simp]
theorem extendByZero_smul_function (f : C^n⟮I, M; 𝕜⟯)
    (s : compactlySupported I F n
      ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
    extendByZero
      ⟨f.comp (⟨Subtype.val, contMDiff_subtypeVal⟩ : C^n⟮I, U; I, M⟯) • s.val,
        smul_function_mem_compactlySupported _ s.property⟩ = f • extendByZero s := by
  ext x
  by_cases hx : x ∈ U
  · rw [smul_apply, extendByZero_apply_of_mem _ ⟨x, hx⟩,
      extendByZero_apply_of_mem s ⟨x, hx⟩]
    exact smul_apply _ s.val ⟨x, hx⟩
  · simp [extendByZero_apply_of_notMem _ hx]

end ContMDiffSection

namespace ContMDiffSection
section IntermediateOpen

variable {𝕜 E H M F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [LocallyCompactSpace E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] {n : ℕ∞ω}
  [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M] {U D : Opens M}

/-- Extend a compactly supported section from one open subset to a larger open subset. -/
def extendByZeroToOpenLinearMap (h : U ≤ D) :
    compactlySupported I F n ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) →ₗ[𝕜]
      compactlySupported I F n ((⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V) := by
  let L := (restrictLinearMap I F n V D).comp
    ((compactlySupported I F n V).subtype.comp
      (extendByZeroLinearMap (I := I) (F := F) (n := n) (V := V) (U := U)))
  refine L.codRestrict (compactlySupported I F n
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(D, M)) *ᵖ V)) ?_
  intro s
  -- Codomain restriction retains the composite section; only its support membership is owed.
  change (restrictLinearMap I F n V D) (extendByZeroLinearMap s).val ∈ _
  -- The law matches this goal only after unfolding the pullback along the bundled
  -- inclusion (`ContinuousMap.coe_mk`), which `rw` does not do.
  erw [restrictLinearMap_apply]
  apply restrict_mem_compactlySupported (extendByZeroLinearMap s)
  -- The law matches this goal only after unfolding the pullback along the bundled
  -- inclusion (`ContinuousMap.coe_mk`), which `rw` does not do.
  erw [extendByZeroLinearMap_apply, tsupport_extendByZero]
  rintro _ ⟨u, _, rfl⟩
  exact h u.property

omit [LocallyCompactSpace E] [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M] in
/-- The underlying section is the restriction of the ambient extension by zero. -/
theorem extendByZeroToOpenLinearMap_val (h : U ≤ D)
    (s : compactlySupported I F n ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
    (extendByZeroToOpenLinearMap h s).val = (extendByZero s).restrict D := by
  -- Forget the codomain membership proof, then evaluate the composed linear maps.
  change (restrictLinearMap I F n V D) (extendByZeroLinearMap s).val = _
  -- The law matches this goal only after unfolding the pullback along the bundled
  -- inclusion (`ContinuousMap.coe_mk`), which `rw` does not do.
  erw [restrictLinearMap_apply, extendByZeroLinearMap_apply]

omit [LocallyCompactSpace E] [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M] in
/-- The support of an intermediate extension is the image of its original support. -/
theorem tsupport_extendByZeroToOpenLinearMap (h : U ≤ D)
    (s : compactlySupported I F n ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
    (extendByZeroToOpenLinearMap h s).val.tsupport = (Opens.inclusion h) '' s.val.tsupport := by
  rw [extendByZeroToOpenLinearMap_val, tsupport_restrict, tsupport_extendByZero]
  ext x
  constructor
  · rintro ⟨u, hu, heq⟩
    exact ⟨u, hu, Subtype.ext heq⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

omit [LocallyCompactSpace E] [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M] in
/-- Extension along the identity inclusion preserves the section. -/
theorem extendByZeroToOpenLinearMap_refl
    (s : compactlySupported I F n ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
    extendByZeroToOpenLinearMap (V := V) le_rfl s = s := by
  apply Subtype.ext
  rw [extendByZeroToOpenLinearMap_val]
  exact restrict_extendByZero s

omit [LocallyCompactSpace E] [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M] in
/-- Intermediate extension followed by ambient extension is ambient extension. -/
theorem extendByZero_extendByZeroToOpenLinearMap (h : U ≤ D)
    (s : compactlySupported I F n ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
    extendByZero (extendByZeroToOpenLinearMap h s) = extendByZero s := by
  have hs : (extendByZero s).tsupport ⊆ D := by
    rw [tsupport_extendByZero]
    rintro _ ⟨u, _, rfl⟩
    exact h u.property
  let t : compactlySupported I F n V := ⟨extendByZero s, extendByZero_mem_compactlySupported s⟩
  have he := extendByZero_restrict t hs
  refine (congrArg extendByZero ?_).trans he
  apply Subtype.ext
  exact extendByZeroToOpenLinearMap_val h s

omit [LocallyCompactSpace E] [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M] in
/-- Extension through nested open subsets composes. -/
theorem extendByZeroToOpenLinearMap_comp {D' : Opens M} (h : U ≤ D) (h' : D ≤ D')
    (s : compactlySupported I F n ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
    extendByZeroToOpenLinearMap h' (extendByZeroToOpenLinearMap h s) =
      extendByZeroToOpenLinearMap (h.trans h') s := by
  apply Subtype.ext
  rw [extendByZeroToOpenLinearMap_val, extendByZeroToOpenLinearMap_val]
  rw [extendByZero_extendByZeroToOpenLinearMap]

/-- Restriction to the universal open subset on compactly supported sections. -/
def restrictUnivLinearMap : compactlySupported I F n V →ₗ[𝕜]
    compactlySupported I F n
      ((⟨Subtype.val, continuous_subtypeVal⟩ : C((⊤ : Opens M), M)) *ᵖ V) := by
  let L := (restrictLinearMap I F n V (⊤ : Opens M)).comp (compactlySupported I F n V).subtype
  refine L.codRestrict _ (fun s ↦ ?_)
  -- The codomain restriction asks for compact support of the ordinary restricted section.
  change (restrictLinearMap I F n V ⊤) s.val ∈ _
  -- The law matches this goal only after unfolding the pullback along the bundled
  -- inclusion (`ContinuousMap.coe_mk`), which `rw` does not do.
  erw [restrictLinearMap_apply]
  exact restrict_mem_compactlySupported s (U := (⊤ : Opens M)) (Set.subset_univ _)

omit [LocallyCompactSpace E] [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M] [T2Space M] in
/-- The underlying universal-open restriction is ordinary section restriction. -/
theorem restrictUnivLinearMap_val (s : compactlySupported I F n V) :
    (restrictUnivLinearMap (I := I) (F := F) (n := n) s).val = s.val.restrict ⊤ := by
  -- The subtype value forgets only the compact-support proof of this restriction.
  change (restrictLinearMap I F n V ⊤) s.val = _
  -- The law matches this goal only after unfolding the pullback along the bundled
  -- inclusion (`ContinuousMap.coe_mk`), which `rw` does not do.
  erw [restrictLinearMap_apply]

end IntermediateOpen
end ContMDiffSection
