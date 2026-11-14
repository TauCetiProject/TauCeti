/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.TransferInstance
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Transporting fibre and vector bundle structures across fibrewise equivalences

Given a fibre bundle `E : B → Type*` with model fibre `F` and a family of fibrewise equivalences
`φ : ∀ b, E' b ≃ E b`, `Bundle.TotalSpace.equivOfFiberwise` identifies `TotalSpace F E'` with
`TotalSpace F E` over the identity of `B`. Pulling back the total-space topology along this
equivalence (`FiberBundle.transferTopologicalSpace`) turns it into a homeomorphism
`FiberBundle.transferHomeomorph` covering the identity.

When each `φ b` is a homeomorphism `E' b ≃ₜ E b`, precomposing every trivialization of `E` with
`FiberBundle.transferHomeomorph` via `Bundle.Trivialization.compHomeomorph` equips `E'` with a
`FiberBundle F E'` structure (`FiberBundle.transfer`). When each `φ b` is a continuous linear
equivalence `E' b ≃L[𝕜] E b` and `E` is a `VectorBundle 𝕜 F E`, the transported trivializations are
`𝕜`-linear with the exact same coordinate changes as `E`, yielding `VectorBundle 𝕜 F E'`
(`VectorBundle.transfer`) whose preferred fibre equivalence at `b` is `φ b` followed by that of `E`
(`VectorBundle.continuousLinearEquivAt_transfer`).

For empty base spaces (such as empty clopen rank strata of a constant-rank bundle),
`FiberBundle.ofIsEmpty` and `VectorBundle.ofIsEmpty` supply the vacuous bundle instances.
-/

public section

open Bundle Set

namespace Bundle.Trivialization

@[simp]
theorem compHomeomorph_apply {B F Z Z' : Type*} [TopologicalSpace B] [TopologicalSpace F]
    [TopologicalSpace Z] [TopologicalSpace Z'] {proj : Z → B} (e : Trivialization F proj)
    (h : Z' ≃ₜ Z) (p : Z') :
    e.compHomeomorph h p = e (h p) := (rfl)

end Bundle.Trivialization

namespace Bundle.TotalSpace

variable (F : Type*) {B : Type*} {E' E : B → Type*}

/-- Identify two total spaces over the same base along a family of fibrewise equivalences. -/
-- Expose the forward map so `π F E ∘ equivOfFiberwise F φ` reduces to `π F E'` in dependent types.
@[expose]
def equivOfFiberwise (φ : ∀ b, E' b ≃ E b) : TotalSpace F E' ≃ TotalSpace F E where
  toFun p := ⟨p.proj, φ p.proj p.2⟩
  invFun p := ⟨p.proj, (φ p.proj).symm p.2⟩
  left_inv p := TotalSpace.ext rfl (heq_of_eq ((φ p.proj).symm_apply_apply p.2))
  right_inv p := TotalSpace.ext rfl (heq_of_eq ((φ p.proj).apply_symm_apply p.2))

@[simp]
theorem equivOfFiberwise_apply (φ : ∀ b, E' b ≃ E b) (p : TotalSpace F E') :
    equivOfFiberwise F φ p = ⟨p.proj, φ p.proj p.2⟩ := (rfl)

@[simp]
theorem equivOfFiberwise_symm_apply (φ : ∀ b, E' b ≃ E b) (p : TotalSpace F E) :
    (equivOfFiberwise F φ).symm p = ⟨p.proj, (φ p.proj).symm p.2⟩ := (rfl)

theorem proj_equivOfFiberwise (φ : ∀ b, E' b ≃ E b) (p : TotalSpace F E') :
    (equivOfFiberwise F φ p).proj = p.proj := (rfl)

theorem proj_equivOfFiberwise_symm (φ : ∀ b, E' b ≃ E b) (p : TotalSpace F E) :
    ((equivOfFiberwise F φ).symm p).proj = p.proj := (rfl)

end Bundle.TotalSpace

namespace FiberBundle

variable (F : Type*) {B : Type*} {E' E : B → Type*} [TopologicalSpace (TotalSpace F E)]

/-- Pull back the total-space topology of `E` along a family of fibrewise equivalences. -/
protected abbrev transferTopologicalSpace (φ : ∀ b, E' b ≃ E b) :
    TopologicalSpace (TotalSpace F E') :=
  (TotalSpace.equivOfFiberwise F φ).topologicalSpace

/-- With the pulled-back total-space topology, a family of fibrewise equivalences gives a
homeomorphism of total spaces covering the identity of the base. -/
-- Expose the underlying equivalence so `π F E ∘ transferHomeomorph F φ` reduces to `π F E'`.
@[expose]
def transferHomeomorph (φ : ∀ b, E' b ≃ E b) :
    letI : TopologicalSpace (TotalSpace F E') := FiberBundle.transferTopologicalSpace F φ
    TotalSpace F E' ≃ₜ TotalSpace F E :=
  (TotalSpace.equivOfFiberwise F φ).homeomorph

@[simp]
theorem transferHomeomorph_apply (φ : ∀ b, E' b ≃ E b) (p : TotalSpace F E') :
    letI : TopologicalSpace (TotalSpace F E') := FiberBundle.transferTopologicalSpace F φ
    transferHomeomorph F φ p = ⟨p.proj, φ p.proj p.2⟩ := (rfl)

@[simp]
theorem transferHomeomorph_symm_apply (φ : ∀ b, E' b ≃ E b) (p : TotalSpace F E) :
    letI : TopologicalSpace (TotalSpace F E') := FiberBundle.transferTopologicalSpace F φ
    (transferHomeomorph F φ).symm p = ⟨p.proj, (φ p.proj).symm p.2⟩ := (rfl)

theorem proj_transferHomeomorph (φ : ∀ b, E' b ≃ E b) (p : TotalSpace F E') :
    letI : TopologicalSpace (TotalSpace F E') := FiberBundle.transferTopologicalSpace F φ
    (transferHomeomorph F φ p).proj = p.proj := (rfl)

section Bundle

variable {F} [TopologicalSpace B] [TopologicalSpace F]
  [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle F E]

variable (F) in
/-- Transport a `FiberBundle` structure back along a family of fibrewise homeomorphisms, equipping
`TotalSpace F E'` with `FiberBundle.transferTopologicalSpace`. -/
@[instance_reducible]
def transfer (φ : ∀ b, E' b ≃ₜ E b) :
    letI : TopologicalSpace (TotalSpace F E') :=
      FiberBundle.transferTopologicalSpace F fun b ↦ (φ b).toEquiv
    FiberBundle F E' :=
  letI : TopologicalSpace (TotalSpace F E') :=
    FiberBundle.transferTopologicalSpace F fun b ↦ (φ b).toEquiv
  let h := transferHomeomorph F fun b ↦ (φ b).toEquiv
  { totalSpaceMk_isInducing' b :=
      h.isInducing.of_comp_iff.mp ((totalSpaceMk_isInducing F E b).comp (φ b).isInducing)
    trivializationAtlas' := (fun e : Trivialization F (π F E) ↦ e.compHomeomorph h) ''
      trivializationAtlas F E
    trivializationAt' b := (trivializationAt F E b).compHomeomorph h
    mem_baseSet_trivializationAt' b := mem_baseSet_trivializationAt F E b
    trivialization_mem_atlas' b := ⟨trivializationAt F E b, trivialization_mem_atlas F E b, rfl⟩ }

variable (F) in
theorem trivializationAt_transfer (φ : ∀ b, E' b ≃ₜ E b) (b : B) :
    letI : TopologicalSpace (TotalSpace F E') :=
      FiberBundle.transferTopologicalSpace F fun b ↦ (φ b).toEquiv
    letI : FiberBundle F E' := FiberBundle.transfer F φ
    trivializationAt F E' b =
      (trivializationAt F E b).compHomeomorph (transferHomeomorph F fun b ↦ (φ b).toEquiv) :=
  (rfl)

end Bundle

/-- Any fibre family over an empty base space is vacuously a `FiberBundle` for any topology on its
empty total space. -/
@[instance_reducible]
def ofIsEmpty {B : Type*} [TopologicalSpace B] [IsEmpty B] (F : Type*) [TopologicalSpace F]
    (E : B → Type*) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)] :
    FiberBundle F E where
  totalSpaceMk_isInducing' b := isEmptyElim b
  trivializationAtlas' := ∅
  trivializationAt' b := isEmptyElim b
  mem_baseSet_trivializationAt' b := isEmptyElim b
  trivialization_mem_atlas' b := isEmptyElim b

end FiberBundle

namespace VectorBundle

variable {𝕜 F B : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace B] {E' E : B → Type*}
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)]

private theorem isLinear_comp_transferHomeomorph (φ : ∀ b, E' b ≃L[𝕜] E b)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜] :
    let _ : TopologicalSpace (TotalSpace F E') :=
      FiberBundle.transferTopologicalSpace F fun b ↦ (φ b).toEquiv
    (e.compHomeomorph (FiberBundle.transferHomeomorph F fun b ↦ (φ b).toEquiv)).IsLinear 𝕜 := by
  let _ : TopologicalSpace (TotalSpace F E') :=
    FiberBundle.transferTopologicalSpace F fun b ↦ (φ b).toEquiv
  refine ⟨fun b hb ↦ ?_⟩
  have hlin := e.linear 𝕜 hb
  exact
    { map_add v w := by
        change (e ⟨b, φ b (v + w)⟩).2 = (e ⟨b, φ b v⟩).2 + (e ⟨b, φ b w⟩).2
        rw [map_add]
        exact hlin.map_add (φ b v) (φ b w)
      map_smul c v := by
        change (e ⟨b, φ b (c • v)⟩).2 = c • (e ⟨b, φ b v⟩).2
        rw [map_smul]
        exact hlin.map_smul c (φ b v) }

private theorem linearEquivAt_comp_transferHomeomorph (φ : ∀ b, E' b ≃L[𝕜] E b)
    (e : Trivialization F (π F E)) [e.IsLinear 𝕜] {b : B} (hb : b ∈ e.baseSet) :
    let _ : TopologicalSpace (TotalSpace F E') :=
      FiberBundle.transferTopologicalSpace F fun b ↦ (φ b).toEquiv
    let _ := isLinear_comp_transferHomeomorph φ e
    (e.compHomeomorph (FiberBundle.transferHomeomorph F fun b ↦ (φ b).toEquiv)).linearEquivAt 𝕜 b
      hb = (φ b).toLinearEquiv.trans (e.linearEquivAt 𝕜 b hb) := by
  let _ : TopologicalSpace (TotalSpace F E') :=
    FiberBundle.transferTopologicalSpace F fun b ↦ (φ b).toEquiv
  let _ := isLinear_comp_transferHomeomorph φ e
  ext v
  rfl

open scoped Classical in
private theorem coordChangeL_comp_transferHomeomorph (φ : ∀ b, E' b ≃L[𝕜] E b)
    (e e' : Trivialization F (π F E)) [e.IsLinear 𝕜] [e'.IsLinear 𝕜] (b : B) :
    let _ : TopologicalSpace (TotalSpace F E') :=
      FiberBundle.transferTopologicalSpace F fun b ↦ (φ b).toEquiv
    let _ := isLinear_comp_transferHomeomorph φ e
    let _ := isLinear_comp_transferHomeomorph φ e'
    (e.compHomeomorph (FiberBundle.transferHomeomorph F fun b ↦ (φ b).toEquiv)).coordChangeL 𝕜
      (e'.compHomeomorph (FiberBundle.transferHomeomorph F fun b ↦ (φ b).toEquiv)) b =
      e.coordChangeL 𝕜 e' b := by
  let _ : TopologicalSpace (TotalSpace F E') :=
    FiberBundle.transferTopologicalSpace F fun b ↦ (φ b).toEquiv
  let _ := isLinear_comp_transferHomeomorph φ e
  let _ := isLinear_comp_transferHomeomorph φ e'
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  change (if hb : b ∈ e.baseSet ∩ e'.baseSet then _ else _) =
    if hb : b ∈ e.baseSet ∩ e'.baseSet then _ else _
  split_ifs with hb
  · rw [linearEquivAt_comp_transferHomeomorph φ e hb.1,
      linearEquivAt_comp_transferHomeomorph φ e' hb.2]
    ext v
    simp
  · rfl

variable [FiberBundle F E] [VectorBundle 𝕜 F E]

variable (𝕜 F) in
/-- Transport a `VectorBundle` structure back along a family of fibrewise continuous linear
equivalences, over `FiberBundle.transfer`. -/
theorem transfer (φ : ∀ b, E' b ≃L[𝕜] E b) :
    letI : TopologicalSpace (TotalSpace F E') :=
      FiberBundle.transferTopologicalSpace F fun b ↦ (φ b).toEquiv
    letI : FiberBundle F E' := FiberBundle.transfer F fun b ↦ (φ b).toHomeomorph
    VectorBundle 𝕜 F E' := by
  let _ : TopologicalSpace (TotalSpace F E') :=
    FiberBundle.transferTopologicalSpace F fun b ↦ (φ b).toEquiv
  let _ : FiberBundle F E' := FiberBundle.transfer F fun b ↦ (φ b).toHomeomorph
  refine
    { trivialization_linear' := ?_
      continuousOn_coordChange' := ?_ }
  · rintro _ ⟨e, he, rfl⟩
    have : MemTrivializationAtlas e := ⟨he⟩
    exact isLinear_comp_transferHomeomorph φ e
  · rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    have : MemTrivializationAtlas e := ⟨he⟩
    have : MemTrivializationAtlas e' := ⟨he'⟩
    refine (continuousOn_coordChange 𝕜 e e').congr fun b _ ↦ ?_
    exact congrArg ContinuousLinearEquiv.toContinuousLinearMap
      (coordChangeL_comp_transferHomeomorph φ e e' b)

variable (𝕜 F) in
/-- In the transported vector bundle, the preferred continuous linear equivalence at `b` is `φ b`
followed by the preferred continuous linear equivalence of `E`. -/
theorem continuousLinearEquivAt_transfer (φ : ∀ b, E' b ≃L[𝕜] E b) (b : B) :
    letI : TopologicalSpace (TotalSpace F E') :=
      FiberBundle.transferTopologicalSpace F fun b ↦ (φ b).toEquiv
    letI : FiberBundle F E' := FiberBundle.transfer F fun b ↦ (φ b).toHomeomorph
    letI : VectorBundle 𝕜 F E' := VectorBundle.transfer 𝕜 F φ
    continuousLinearEquivAt 𝕜 F E' b = (φ b).trans (continuousLinearEquivAt 𝕜 F E b) := by
  let _ : TopologicalSpace (TotalSpace F E') :=
    FiberBundle.transferTopologicalSpace F fun b ↦ (φ b).toEquiv
  let _ : FiberBundle F E' := FiberBundle.transfer F fun b ↦ (φ b).toHomeomorph
  let _ : VectorBundle 𝕜 F E' := VectorBundle.transfer 𝕜 F φ
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  exact linearEquivAt_comp_transferHomeomorph φ (trivializationAt F E b)
    (mem_baseSet_trivializationAt F E b)

/-- Over an empty base space, `FiberBundle.ofIsEmpty` is vacuously a `VectorBundle`. -/
theorem ofIsEmpty (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
    [IsEmpty B] (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] (E : B → Type*)
    [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace F E)] :
    letI : FiberBundle F E := FiberBundle.ofIsEmpty F E
    VectorBundle 𝕜 F E :=
  letI : FiberBundle F E := FiberBundle.ofIsEmpty F E
  { trivialization_linear' := fun _ ⟨h⟩ ↦ h.elim
    continuousOn_coordChange' := fun _ _ ⟨h⟩ _ ↦ h.elim }

end VectorBundle
