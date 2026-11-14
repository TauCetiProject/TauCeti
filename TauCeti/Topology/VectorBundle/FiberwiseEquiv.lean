/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Core.Basic

/-!
# Transporting vector-bundle structures along fibrewise continuous linear equivalences

Given a vector bundle `E₁` with model fibre `F` over `B` and continuous linear equivalences
`e b : E₁ b ≃L[𝕜] E₂ b`, pulling back the total-space topology of `E₁` equips `TotalSpace F E₂`
with a vector-bundle structure (`TauCeti.FiberwiseEquiv.totalSpaceTopology`, `fiberBundle`,
`vectorBundle`). Precomposing charts of `E₁` with `totalSpaceHomeomorph` gives linear charts of
`E₂` whose overlap transitions agree with those of `E₁` (`coordChangeL_trivialization`), leaving
`TauCeti.pointIndexedCore` unchanged (`pointIndexedCore_eq`).
-/

public section

open Bundle Set Topology

namespace TauCeti.FiberwiseEquiv

section Equiv

variable {𝕜 B : Type*} (F : Type*) [Semiring 𝕜]
  {E₁ E₂ : B → Type*} [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module 𝕜 (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module 𝕜 (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] (e : ∀ b, E₁ b ≃L[𝕜] E₂ b)

/-- The bijection of total spaces induced by the inverses of fibrewise equivalences. -/
def totalSpaceEquiv : TotalSpace F E₂ ≃ TotalSpace F E₁ where
  toFun p := ⟨p.proj, (e p.proj).symm p.2⟩
  invFun p := ⟨p.proj, e p.proj p.2⟩
  left_inv p := TotalSpace.mk_inj.2 <| (e p.proj).apply_symm_apply p.2
  right_inv p := TotalSpace.mk_inj.2 <| (e p.proj).symm_apply_apply p.2

@[simp] theorem totalSpaceEquiv_apply (p : TotalSpace F E₂) :
    totalSpaceEquiv F e p = ⟨p.proj, (e p.proj).symm p.2⟩ := (rfl)

@[simp] theorem totalSpaceEquiv_symm_apply (p : TotalSpace F E₁) :
    (totalSpaceEquiv F e).symm p = ⟨p.proj, e p.proj p.2⟩ := (rfl)

theorem proj_totalSpaceEquiv (p : TotalSpace F E₂) :
    (totalSpaceEquiv F e p).proj = p.proj := (rfl)

theorem proj_totalSpaceEquiv_symm (p : TotalSpace F E₁) :
    ((totalSpaceEquiv F e).symm p).proj = p.proj := (rfl)

section Homeomorph

variable [TopologicalSpace (TotalSpace F E₁)]

/-- Pull back the total-space topology of `E₁` to `TotalSpace F E₂` along `totalSpaceEquiv`. -/
@[instance_reducible]
def totalSpaceTopology : TopologicalSpace (TotalSpace F E₂) :=
  TopologicalSpace.induced (totalSpaceEquiv F e) inferInstance

/-- Continuity into `TotalSpace F E₂` equipped with `totalSpaceTopology F e`. -/
theorem continuous_totalSpace_iff {Y : Type*} [TopologicalSpace Y] {g : Y → TotalSpace F E₂} :
    @Continuous Y (TotalSpace F E₂) _ (totalSpaceTopology F e) g ↔
      Continuous (fun y => (⟨(g y).proj, (e (g y).proj).symm (g y).2⟩ : TotalSpace F E₁)) :=
  continuous_induced_rng

/-- Continuity of `(b, v) ↦ (b, (e b).symm v)` from `totalSpaceTopology F e`. -/
theorem continuous_totalSpace_to :
    @Continuous (TotalSpace F E₂) (TotalSpace F E₁) (totalSpaceTopology F e) _
      (fun p => ⟨p.proj, (e p.proj).symm p.2⟩) :=
  continuous_induced_dom

/-- With the induced topology on `TotalSpace F E₂`, `totalSpaceEquiv F e` is a homeomorphism
covering the identity on `B`. -/
def totalSpaceHomeomorph :
    @Homeomorph (TotalSpace F E₂) (TotalSpace F E₁) (totalSpaceTopology F e) inferInstance :=
  letI : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
  (totalSpaceEquiv F e).toHomeomorphOfIsInducing ⟨rfl⟩

@[simp] theorem totalSpaceHomeomorph_apply (p : TotalSpace F E₂) :
    totalSpaceHomeomorph F e p = ⟨p.proj, (e p.proj).symm p.2⟩ := (rfl)

@[simp] theorem totalSpaceHomeomorph_symm_apply (p : TotalSpace F E₁) :
    letI : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
    (totalSpaceHomeomorph F e).symm p = ⟨p.proj, e p.proj p.2⟩ := (rfl)

end Homeomorph

end Equiv

section FiberBundle

variable {𝕜 B : Type*} (F : Type*) [Semiring 𝕜] [TopologicalSpace B] [TopologicalSpace F]
  {E₁ : B → Type*} [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module 𝕜 (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [TopologicalSpace (TotalSpace F E₁)]
  {E₂ : B → Type*} [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module 𝕜 (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] (e : ∀ b, E₁ b ≃L[𝕜] E₂ b)

/-- Transport a local trivialization of `E₁` to `E₂` via `totalSpaceHomeomorph F e`. -/
def trivialization (t : Trivialization F (π F E₁)) :
    @Trivialization B F (TotalSpace F E₂) _ _ (totalSpaceTopology F e) (π F E₂) :=
  letI : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
  let h := totalSpaceHomeomorph F e
  { toOpenPartialHomeomorph := h.transOpenPartialHomeomorph t.toOpenPartialHomeomorph
    baseSet := t.baseSet
    open_baseSet := t.open_baseSet
    source_eq := by ext p; simp [t.source_eq, h]
    target_eq := t.target_eq
    proj_toFun p hp := t.proj_toFun (h p) (by simpa [h] using hp) }

@[simp] theorem baseSet_trivialization (t : Trivialization F (π F E₁)) :
    letI : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
    (trivialization F e t).baseSet = t.baseSet := (rfl)

@[simp] theorem trivialization_apply (t : Trivialization F (π F E₁)) (p : TotalSpace F E₂) :
    letI : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
    trivialization F e t p = t ⟨p.proj, (e p.proj).symm p.2⟩ := (rfl)

/-- Transport the `FiberBundle` structure of `E₁` along fibrewise equivalences. -/
@[instance_reducible]
def fiberBundle [FiberBundle F E₁] :
    letI : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
    FiberBundle F E₂ :=
  letI : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
  { totalSpaceMk_isInducing' b := by
      rw [← (totalSpaceHomeomorph F e).isInducing.of_comp_iff]
      exact (FiberBundle.totalSpaceMk_isInducing F E₁ b).comp (e b).symm.toHomeomorph.isInducing
    trivializationAtlas' := trivialization F e '' trivializationAtlas F E₁
    trivializationAt' b := trivialization F e (trivializationAt F E₁ b)
    mem_baseSet_trivializationAt' b := mem_baseSet_trivializationAt F E₁ b
    trivialization_mem_atlas' b := ⟨_, trivialization_mem_atlas F E₁ b, rfl⟩ }

@[simp] theorem trivializationAt_fiberBundle [FiberBundle F E₁] (b : B) :
    letI : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
    letI : FiberBundle F E₂ := fiberBundle F e
    trivializationAt F E₂ b = trivialization F e (trivializationAt F E₁ b) := (rfl)

/-- Transporting a linear trivialization of `E₁` along `e` yields a linear trivialization of
`E₂`. -/
theorem isLinear_trivialization [AddCommMonoid F] [Module 𝕜 F]
    (t : Trivialization F (π F E₁)) [t.IsLinear 𝕜] :
    letI : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
    (trivialization F e t).IsLinear 𝕜 := by
  let _ : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
  refine ⟨fun b hb => ?_⟩
  have hlin := t.linear 𝕜 (hb : b ∈ t.baseSet)
  exact ⟨fun _ _ => by simp only [trivialization_apply, map_add, hlin.map_add],
    fun _ _ => by simp only [trivialization_apply, map_smul, hlin.map_smul]⟩

end FiberBundle

section VectorBundle

variable {𝕜 B : Type*} (F : Type*) [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E₁ : B → Type*} [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module 𝕜 (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [TopologicalSpace (TotalSpace F E₁)]
  {E₂ : B → Type*} [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module 𝕜 (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] (e : ∀ b, E₁ b ≃L[𝕜] E₂ b)

/-- Coordinate changes between trivializations transported along `e` agree everywhere with the
original coordinate changes on `E₁`, since `e b` and `(e b).symm` cancel on overlaps. -/
theorem coordChangeL_trivialization
    (t t' : Trivialization F (π F E₁)) [t.IsLinear 𝕜] [t'.IsLinear 𝕜] (b : B) :
    letI : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
    letI := isLinear_trivialization F e t
    letI := isLinear_trivialization F e t'
    (trivialization F e t).coordChangeL 𝕜 (trivialization F e t') b =
      t.coordChangeL 𝕜 t' b := by
  let _ := totalSpaceTopology F e
  let _ := isLinear_trivialization F e t; let _ := isLinear_trivialization F e t'
  ext v
  by_cases hb : b ∈ t.baseSet ∩ t'.baseSet
  · have hb' : b ∈ (trivialization F e t).baseSet ∩ (trivialization F e t').baseSet := hb
    rw [Trivialization.coordChangeL_apply' _ _ hb', Trivialization.coordChangeL_apply' _ _ hb]
    exact congrArg (fun p => (t' p).2)
      ((totalSpaceHomeomorph F e).apply_symm_apply (t.toOpenPartialHomeomorph.symm (b, v)))
  · have hb' : b ∉ (trivialization F e t).baseSet ∩ (trivialization F e t').baseSet := hb
    simp only [Trivialization.coordChangeL, ContinuousLinearEquiv.coe_mk, hb, hb', dite_false,
      LinearEquiv.refl_apply]

variable [FiberBundle F E₁] [VectorBundle 𝕜 F E₁]

/-- Transport the `VectorBundle` structure of `E₁` along fibrewise continuous linear
equivalences. -/
theorem vectorBundle :
    letI : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
    letI : FiberBundle F E₂ := fiberBundle F e
    VectorBundle 𝕜 F E₂ := by
  let _ := totalSpaceTopology F e; let _ := fiberBundle F e
  refine ⟨?_, ?_⟩
  · rintro _ ⟨⟨t, ht, rfl⟩⟩
    have : MemTrivializationAtlas t := ⟨ht⟩
    exact isLinear_trivialization F e t
  · rintro _ _ ⟨⟨t, ht, rfl⟩⟩ ⟨⟨t', ht', rfl⟩⟩
    have : MemTrivializationAtlas t := ⟨ht⟩
    have : MemTrivializationAtlas t' := ⟨ht'⟩
    exact (continuousOn_coordChange 𝕜 t t').congr fun b _ =>
      congrArg ContinuousLinearEquiv.toContinuousLinearMap (coordChangeL_trivialization F e t t' b)

/-- Transporting a bundle along fibrewise continuous linear equivalences leaves its point-indexed
coordinate core strictly unchanged. -/
@[simp] theorem pointIndexedCore_eq :
    letI : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
    letI : FiberBundle F E₂ := fiberBundle F e
    letI : VectorBundle 𝕜 F E₂ := vectorBundle F e
    pointIndexedCore 𝕜 F E₂ = pointIndexedCore 𝕜 F E₁ := by
  let _ := totalSpaceTopology F e; let _ := fiberBundle F e; let _ := vectorBundle F e
  refine VectorBundleCore.ext (fun b => ?_) (fun b => ?_) (fun b c x => ?_)
  · exact (pointIndexedCore_localTriv_baseSet 𝕜 F E₂ b).trans <|
      (congrArg Trivialization.baseSet (trivializationAt_fiberBundle F e b)).trans <|
        (baseSet_trivialization F e (trivializationAt F E₁ b)).trans
          (pointIndexedCore_localTriv_baseSet 𝕜 F E₁ b).symm
  · rw [pointIndexedCore_indexAt, pointIndexedCore_indexAt]
  · rw [pointIndexedCore_coordChange, pointIndexedCore_coordChange]
    exact congrArg ContinuousLinearEquiv.toContinuousLinearMap
      (coordChangeL_trivialization F e (trivializationAt F E₁ b) (trivializationAt F E₁ c) x)

/-- Reading a vector of the transported bundle in its preferred chart applies `(e b).symm` and
then the preferred chart of `E₁`. -/
theorem pointIndexedCoreFiberEquiv_symm_apply_eq (b : B) (w : E₂ b) :
    letI : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
    letI : FiberBundle F E₂ := fiberBundle F e
    letI : VectorBundle 𝕜 F E₂ := vectorBundle F e
    (pointIndexedCoreFiberEquiv 𝕜 F E₂ b).symm w =
      (pointIndexedCoreFiberEquiv 𝕜 F E₁ b).symm ((e b).symm w) := by
  let _ := totalSpaceTopology F e; let _ := fiberBundle F e; let _ := vectorBundle F e
  simp only [pointIndexedCoreFiberEquiv_symm_apply, trivializationAt_fiberBundle,
    trivialization_apply]
  rfl

/-- The preferred-chart fibre equivalence of the transported bundle evaluates as that of `E₁`
followed by the fibrewise equivalence `e b`. -/
theorem pointIndexedCoreFiberEquiv_apply_eq (b : B) (v : F) :
    letI : TopologicalSpace (TotalSpace F E₂) := totalSpaceTopology F e
    letI : FiberBundle F E₂ := fiberBundle F e
    letI : VectorBundle 𝕜 F E₂ := vectorBundle F e
    pointIndexedCoreFiberEquiv 𝕜 F E₂ b v =
      e b (pointIndexedCoreFiberEquiv 𝕜 F E₁ b v) := by
  let _ := totalSpaceTopology F e; let _ := fiberBundle F e; let _ := vectorBundle F e
  apply (pointIndexedCoreFiberEquiv 𝕜 F E₂ b).symm.injective
  exact ((pointIndexedCoreFiberEquiv 𝕜 F E₂ b).symm_apply_apply v).trans <|
    ((pointIndexedCoreFiberEquiv 𝕜 F E₁ b).symm_apply_apply v).symm.trans <|
      (congrArg (pointIndexedCoreFiberEquiv 𝕜 F E₁ b).symm ((e b).symm_apply_apply _).symm).trans
        (pointIndexedCoreFiberEquiv_symm_apply_eq F e b _).symm

end VectorBundle

end TauCeti.FiberwiseEquiv
