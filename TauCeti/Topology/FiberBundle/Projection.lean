/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Bundled fibres of an arbitrary map

Mathlib's `FiberBundle` and `ContMDiffFiberBundle` classes are indexed over a dependent family
`E : B → Type*` with total space `Bundle.TotalSpace F E`, whereas geometric constructions such as
quotient projections, homogeneous spaces, and Ehresmann submersions begin from an unbundled map
`f : E → B` on an already-given space `E`.

This file introduces `TauCeti.ProjectionFiber F f : B → Type*`, the fibre of `f : E → B` over
`b : B` tagged with a phantom model fibre parameter `F : Type*`. Including `F` in the carrier type
lets both `ProjectionFiber F f b` and `Bundle.TotalSpace F (ProjectionFiber F f)` carry canonical
global `TopologicalSpace` instances induced from `E` without typeclass diamonds, while
`ProjectionFiber.totalSpaceHomeomorph` identifies `Bundle.TotalSpace F (ProjectionFiber F f)`
homeomorphically with `E` over `B`. Any `Bundle.Trivialization F f` of the map `f` transports along
this homeomorphism to a `Bundle.Trivialization F (π F (ProjectionFiber F f))` with definitionally
identical base set and coordinate changes.

## Main definitions and results

* `TauCeti.ProjectionFiber F f b`: points `val : E` with `f val = b`, equipped with the subspace
  topology from `E`.
* `TauCeti.ProjectionFiber.totalSpaceEquiv`, `TauCeti.ProjectionFiber.totalSpaceHomeomorph`: the
  canonical equivalence and homeomorphism `TotalSpace F (ProjectionFiber F f) ≃ₜ E` sending
  `⟨b, y⟩` to `y.val` and `x : E` to `⟨f x, ⟨x, rfl⟩⟩`.
* `Bundle.Trivialization.projectionFiber`: transports `t : Trivialization F f` to a trivialization
  of `π F (ProjectionFiber F f)` with the same `baseSet` and `coordChange`.
* `TauCeti.ProjectionFiber.fiberBundle`: packages a covering family `A : Set (Trivialization F f)`
  of local trivializations of `f` into a `FiberBundle F (ProjectionFiber F f)` structure.
-/

public section

open Bundle Function Set Topology

namespace TauCeti

/-- The fibre of a map `f : E → B` over `b : B`, tagged with a model fibre type `F` so that both
`ProjectionFiber F f b` and `Bundle.TotalSpace F (ProjectionFiber F f)` carry canonical subspace
topologies induced from `E` without typeclass ambiguity. -/
@[ext]
structure ProjectionFiber (F : Type*) {E B : Type*} (f : E → B) (b : B) where
  /-- The underlying point in the domain `E`. -/
  val : E
  /-- Proof that `val` lies in the fibre of `f` over `b`. -/
  map_val : f val = b

namespace ProjectionFiber

section SetTheory

variable (F : Type*) {E B : Type*} (f : E → B)

/-- `ProjectionFiber F f b` is equivalent to the set-theoretic fibre `{x : E // f x = b}`. -/
def equivSubtype (b : B) : ProjectionFiber F f b ≃ {x : E // f x = b} where
  toFun y := ⟨y.val, y.map_val⟩
  invFun y := ⟨y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coercing `equivSubtype F f b y` to `E` recovers `y.val`. -/
@[simp]
theorem coe_equivSubtype (b : B) (y : ProjectionFiber F f b) :
    ((equivSubtype F f b y : {x : E // f x = b}) : E) = y.val :=
  (rfl)

/-- Applying `(equivSubtype F f b).symm` preserves the underlying point in `E`. -/
@[simp]
theorem val_equivSubtype_symm (b : B) (y : {x : E // f x = b}) :
    ((equivSubtype F f b).symm y).val = y.1 :=
  (rfl)

/-- The bundled total space `TotalSpace F (ProjectionFiber F f)` is canonically equivalent to the
domain `E` via `⟨b, y⟩ ↦ y.val` and `x ↦ ⟨f x, ⟨x, rfl⟩⟩`. -/
def totalSpaceEquiv : TotalSpace F (ProjectionFiber F f) ≃ E where
  toFun p := p.2.val
  invFun x := ⟨f x, ⟨x, rfl⟩⟩
  left_inv p := by
    rcases p with ⟨b, x, rfl⟩
    rfl
  right_inv _ := rfl

/-- `totalSpaceEquiv F f` sends a bundled point `p` to `p.2.val`. -/
@[simp]
theorem totalSpaceEquiv_apply (p : TotalSpace F (ProjectionFiber F f)) :
    totalSpaceEquiv F f p = p.2.val :=
  (rfl)

/-- `totalSpaceEquiv F f` sends `⟨b, y⟩` to `y.val`. -/
theorem totalSpaceEquiv_mk (b : B) (y : ProjectionFiber F f b) :
    totalSpaceEquiv F f ⟨b, y⟩ = y.val :=
  (rfl)

/-- `(totalSpaceEquiv F f).symm` sends `x : E` to `⟨f x, ⟨x, rfl⟩⟩`. -/
@[simp]
theorem totalSpaceEquiv_symm_apply (x : E) :
    (totalSpaceEquiv F f).symm x = ⟨f x, ⟨x, rfl⟩⟩ :=
  (rfl)

/-- The base projection of `(totalSpaceEquiv F f).symm x` is `f x`. -/
theorem proj_totalSpaceEquiv_symm (x : E) :
    ((totalSpaceEquiv F f).symm x).proj = f x :=
  (rfl)

/-- The underlying domain point of `(totalSpaceEquiv F f).symm x` is `x`. -/
@[simp]
theorem val_snd_totalSpaceEquiv_symm (x : E) :
    ((totalSpaceEquiv F f).symm x).2.val = x :=
  (rfl)

/-- `totalSpaceEquiv F f` intertwines the bundle projection with `f`. -/
theorem map_totalSpaceEquiv (p : TotalSpace F (ProjectionFiber F f)) :
    f (totalSpaceEquiv F f p) = p.proj :=
  p.2.map_val

/-- Forgetful inclusion `ProjectionFiber.val` on each fibre is injective. -/
theorem val_injective (b : B) : Injective (ProjectionFiber.val : ProjectionFiber F f b → E) :=
  fun _ _ h ↦ ProjectionFiber.ext h

end SetTheory

section Topology

variable (F : Type*) {E B : Type*} [TopologicalSpace E] (f : E → B)

/-- Each fibre `ProjectionFiber F f b` carries the subspace topology induced from `E`. -/
instance instTopologicalSpace (b : B) : TopologicalSpace (ProjectionFiber F f b) :=
  TopologicalSpace.induced ProjectionFiber.val ‹TopologicalSpace E›

/-- `TotalSpace F (ProjectionFiber F f)` carries the topology induced from `E` along
`totalSpaceEquiv F f`. -/
instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace F (ProjectionFiber F f)) :=
  TopologicalSpace.induced (totalSpaceEquiv F f) ‹TopologicalSpace E›

/-- Inclusion of `ProjectionFiber F f b` into `E` is topology-inducing. -/
theorem isInducing_val (b : B) :
    IsInducing (ProjectionFiber.val : ProjectionFiber F f b → E) :=
  ⟨rfl⟩

/-- Inclusion of `ProjectionFiber F f b` into `E` is a topological embedding. -/
theorem isEmbedding_val (b : B) :
    IsEmbedding (ProjectionFiber.val : ProjectionFiber F f b → E) :=
  ⟨isInducing_val F f b, val_injective F f b⟩

/-- Forgetful inclusion `ProjectionFiber.val : ProjectionFiber F f b → E` is continuous. -/
@[fun_prop]
theorem continuous_val (b : B) :
    Continuous (ProjectionFiber.val : ProjectionFiber F f b → E) :=
  (isInducing_val F f b).continuous

/-- `totalSpaceEquiv F f` is topology-inducing by construction. -/
theorem isInducing_totalSpaceEquiv : IsInducing (totalSpaceEquiv F f) :=
  ⟨rfl⟩

/-- `ProjectionFiber F f b` is homeomorphic to the topological subspace `{x : E // f x = b}`. -/
def homeomorphSubtype (b : B) : ProjectionFiber F f b ≃ₜ {x : E // f x = b} :=
  (equivSubtype F f b).toHomeomorphOfIsInducing
    ⟨(induced_compose (f := equivSubtype F f b) (g := Subtype.val)).symm⟩

/-- `homeomorphSubtype` has underlying map `equivSubtype`. -/
@[simp]
theorem coe_homeomorphSubtype (b : B) :
    (homeomorphSubtype F f b : ProjectionFiber F f b → {x : E // f x = b}) = equivSubtype F f b :=
  (rfl)

/-- `(homeomorphSubtype F f b).symm` has underlying map `(equivSubtype F f b).symm`. -/
@[simp]
theorem coe_homeomorphSubtype_symm (b : B) :
    ((homeomorphSubtype F f b).symm : {x : E // f x = b} → ProjectionFiber F f b) =
      (equivSubtype F f b).symm :=
  (rfl)

/-- The canonical homeomorphism `TotalSpace F (ProjectionFiber F f) ≃ₜ E` over `B`. -/
def totalSpaceHomeomorph : TotalSpace F (ProjectionFiber F f) ≃ₜ E :=
  (totalSpaceEquiv F f).toHomeomorphOfIsInducing (isInducing_totalSpaceEquiv F f)

/-- `totalSpaceHomeomorph` has underlying map `totalSpaceEquiv`. -/
@[simp]
theorem coe_totalSpaceHomeomorph :
    (totalSpaceHomeomorph F f : TotalSpace F (ProjectionFiber F f) → E) = totalSpaceEquiv F f :=
  (rfl)

/-- `(totalSpaceHomeomorph F f).symm` has underlying map `(totalSpaceEquiv F f).symm`. -/
@[simp]
theorem coe_totalSpaceHomeomorph_symm :
    ((totalSpaceHomeomorph F f).symm : E → TotalSpace F (ProjectionFiber F f)) =
      (totalSpaceEquiv F f).symm :=
  (rfl)

/-- Fibre inclusion `TotalSpace.mk b : ProjectionFiber F f b → TotalSpace F (ProjectionFiber F f)`
is topology-inducing for every `b : B`. -/
theorem isInducing_totalSpaceMk (b : B) :
    IsInducing (@TotalSpace.mk B F (ProjectionFiber F f) b) :=
  (isInducing_totalSpaceEquiv F f).of_comp_iff.mp (isInducing_val F f b)

/-- If `f : E → B` is continuous, so is the bundle projection `π F (ProjectionFiber F f)`. -/
theorem continuous_proj [TopologicalSpace B] {f : E → B} (hf : Continuous f) :
    Continuous (π F (ProjectionFiber F f)) := by
  have hcomp : π F (ProjectionFiber F f) = f ∘ totalSpaceHomeomorph F f :=
    funext fun p ↦ p.2.map_val.symm
  rw [hcomp]
  exact hf.comp (totalSpaceHomeomorph F f).continuous

end Topology

end ProjectionFiber

end TauCeti

namespace Bundle.Trivialization

variable {F E B : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace E]
  {f : E → B}

/-- Transport a local trivialization `t` of an unbundled map `f : E → B` along
`TauCeti.ProjectionFiber.totalSpaceHomeomorph F f` to a local trivialization of the bundled
projection `π F (TauCeti.ProjectionFiber F f)`. -/
def projectionFiber (t : Trivialization F f) :
    Trivialization F (π F (TauCeti.ProjectionFiber F f)) :=
  { t.compHomeomorph (TauCeti.ProjectionFiber.totalSpaceHomeomorph F f) with
    source_eq := by
      ext p
      exact (t.compHomeomorph (TauCeti.ProjectionFiber.totalSpaceHomeomorph F f)).mem_source.trans
        (by simp [p.2.map_val])
    proj_toFun := fun p hp ↦
      ((t.compHomeomorph (TauCeti.ProjectionFiber.totalSpaceHomeomorph F f)).proj_toFun p hp).trans
        p.2.map_val }

/-- `t.projectionFiber` evaluates `t` on the underlying point in `E`. -/
@[simp]
theorem projectionFiber_apply (t : Trivialization F f)
    (p : TotalSpace F (TauCeti.ProjectionFiber F f)) :
    t.projectionFiber p = t (TauCeti.ProjectionFiber.totalSpaceEquiv F f p) :=
  (rfl)

/-- `t.projectionFiber` has the same `baseSet` as `t`. -/
@[simp]
theorem projectionFiber_baseSet (t : Trivialization F f) :
    t.projectionFiber.baseSet = t.baseSet :=
  (rfl)

/-- Partial-equivalence inverse of `t.projectionFiber`. -/
@[simp]
theorem projectionFiber_toPartialEquiv_symm_apply (t : Trivialization F f) (q : B × F) :
    t.projectionFiber.toPartialEquiv.symm q =
      (TauCeti.ProjectionFiber.totalSpaceEquiv F f).symm (t.toPartialEquiv.symm q) :=
  (rfl)

/-- Partial-homeomorphism inverse of `t.projectionFiber`. -/
@[simp]
theorem projectionFiber_toOpenPartialHomeomorph_symm_apply (t : Trivialization F f) (q : B × F) :
    t.projectionFiber.toOpenPartialHomeomorph.symm q =
      (TauCeti.ProjectionFiber.totalSpaceEquiv F f).symm (t.toOpenPartialHomeomorph.symm q) :=
  (rfl)

/-- Transporting trivializations to `ProjectionFiber F f` preserves `coordChange`. -/
@[simp]
theorem projectionFiber_coordChange (t₁ t₂ : Trivialization F f) (b : B) (y : F) :
    t₁.projectionFiber.coordChange t₂.projectionFiber b y = t₁.coordChange t₂ b y :=
  (rfl)

end Bundle.Trivialization

namespace TauCeti.ProjectionFiber

variable {F E B : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace E]
  {f : E → B}

/-- Package a covering set `A` of local trivializations of an unbundled map `f : E → B` into a
`FiberBundle F (ProjectionFiber F f)` structure with atlas `Trivialization.projectionFiber '' A`.
Install locally via `letI := ProjectionFiber.fiberBundle A hA`. -/
@[instance_reducible]
noncomputable def fiberBundle (A : Set (Trivialization F f))
    (hA : ∀ b : B, ∃ t ∈ A, b ∈ t.baseSet) :
    FiberBundle F (ProjectionFiber F f) where
  totalSpaceMk_isInducing' := isInducing_totalSpaceMk F f
  trivializationAtlas' := Bundle.Trivialization.projectionFiber '' A
  trivializationAt' b := (hA b).choose.projectionFiber
  mem_baseSet_trivializationAt' b := (hA b).choose_spec.2
  trivialization_mem_atlas' b := ⟨(hA b).choose, (hA b).choose_spec.1, rfl⟩

/-- The trivialization atlas of `ProjectionFiber.fiberBundle A hA` is
`Bundle.Trivialization.projectionFiber '' A`. -/
@[simp]
theorem trivializationAtlas_fiberBundle (A : Set (Trivialization F f))
    (hA : ∀ b : B, ∃ t ∈ A, b ∈ t.baseSet) :
    (letI := fiberBundle A hA; trivializationAtlas F (ProjectionFiber F f)) =
      Bundle.Trivialization.projectionFiber '' A :=
  (rfl)

/-- Package pointwise existence of local trivializations of `f : E → B` into a
`FiberBundle F (ProjectionFiber F f)` structure using the full trivialization atlas. -/
@[instance_reducible]
noncomputable def fiberBundleOfExists (h : ∀ b : B, ∃ t : Trivialization F f, b ∈ t.baseSet) :
    FiberBundle F (ProjectionFiber F f) :=
  fiberBundle univ fun b ↦
    let ⟨t, ht⟩ := h b
    ⟨t, mem_univ t, ht⟩

/-- The trivialization atlas of `ProjectionFiber.fiberBundleOfExists h` is the image of `univ` under
`Bundle.Trivialization.projectionFiber`. -/
theorem trivializationAtlas_fiberBundleOfExists
    (h : ∀ b : B, ∃ t : Trivialization F f, b ∈ t.baseSet) :
    (letI := fiberBundleOfExists h; trivializationAtlas F (ProjectionFiber F f)) =
      Bundle.Trivialization.projectionFiber '' univ :=
  (rfl)

end TauCeti.ProjectionFiber
