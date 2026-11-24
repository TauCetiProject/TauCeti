/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.RecursiveIn

/-!
# Staged partial functions

A staged partial function assigns each input a stream of optional values. Each successful
observation persists unchanged at all later stages. Unbounded search gives the partial function
specified by those observations. If the stage observations are uniformly computable in an oracle,
the resulting partial function is recursive in the same oracle.

A cofinal increasing clock preserves the partial function, although it can change discovery
times. Normalized bounded simulation yields such tables for fixed total oracles in
`TauCeti.Computability.SingleOracle.Staged.Basic`.

## References

* Cameron Freer's [supplied-data staging interface](https://github.com/cameronfreer/computable-model-theory/blob/a1fe761/ComputableModelTheory/Computability/StagedPartial.lean)
  bundles an effective approximation with a given partial function. Here the table and
  persistence determine the partial function, and effectivity is a separate hypothesis.
-/

public section

namespace TauCeti

/-- Finite observations of a partial function, with persistence of every discovered value.
Computability of the observations is a separate property of the stage table. -/
@[ext]
structure StagedPartial (α : Type*) (β : Type*) where
  /-- The optional value at a given input and stage. -/
  stage : α → ℕ → Option β
  /-- A discovered value remains unchanged as the stage increases. -/
  persistent {x : α} {s t : ℕ} {y : β} :
    s ≤ t → stage x s = some y → stage x t = some y

namespace StagedPartial

variable {α β γ : Type*} (P : StagedPartial α β)

/-- Search for the first successful observation of the input. -/
noncomputable def eval (x : α) : Part β :=
  Nat.rfindOpt (P.stage x)

/-- Evaluating a table searches for its first present observation. -/
theorem eval_def (x : α) : P.eval x = Nat.rfindOpt (P.stage x) := (rfl)

/-- The values of the partial function are exactly its successful observations. -/
theorem mem_eval_iff {x : α} {y : β} :
    y ∈ P.eval x ↔ ∃ s, P.stage x s = some y := by
  simpa only [eval_def, Option.mem_def] using
    (Nat.rfindOpt_mono fun hst hs => P.persistent hst hs)

/-- The partial function is undefined on an input exactly when every observation is absent. -/
theorem not_dom_eval_iff (x : α) : ¬(P.eval x).Dom ↔ ∀ s, P.stage x s = none := by
  simp only [Part.dom_iff_mem, P.mem_eval_iff, not_exists]
  exact forall_comm.trans <| forall_congr' fun _ => Option.eq_none_iff_forall_ne_some.symm

/-- Every value of the partial function is observed at all sufficiently large stages. -/
theorem mem_eval_iff_exists_forall_ge {x : α} {y : β} :
    y ∈ P.eval x ↔ ∃ s₀, ∀ s ≥ s₀, P.stage x s = some y := by
  rw [P.mem_eval_iff]
  exact ⟨fun ⟨s, h⟩ => ⟨s, fun _ hs => P.persistent hs h⟩, fun ⟨s, h⟩ => ⟨s, h s le_rfl⟩⟩

/-- Precompose the inputs to a stage table. -/
def comap {δ : Type*} (f : δ → α) : StagedPartial δ β where
  stage x := P.stage (f x)
  persistent := P.persistent

/-- A precomposed table observes the original table at the mapped input. -/
@[simp]
theorem stage_comap {δ : Type*} (f : δ → α) (x : δ) (s : ℕ) :
    (P.comap f).stage x s = P.stage (f x) s := (rfl)

/-- Evaluating a precomposed table evaluates the original table at the mapped input. -/
@[simp]
theorem eval_comap {δ : Type*} (f : δ → α) (x : δ) :
    (P.comap f).eval x = P.eval (f x) := (rfl)

/-- Change or discard successful outputs using an optional output map. -/
def filterMap (f : β → Option γ) : StagedPartial α γ where
  stage x s := (P.stage x s).bind f
  persistent hst h := by
    obtain ⟨y, hy, hz⟩ := Option.bind_eq_some_iff.1 h
    simpa only [P.persistent hst hy, Option.bind_some] using hz

/-- Optional output mapping binds each stage observation to the output map. -/
@[simp]
theorem stage_filterMap (f : β → Option γ) (x : α) (s : ℕ) :
    (P.filterMap f).stage x s = (P.stage x s).bind f := (rfl)

/-- Optional output mapping commutes with evaluation, with discarded outputs giving undefined
values. -/
@[simp]
theorem eval_filterMap (f : β → Option γ) (x : α) :
    (P.filterMap f).eval x = (P.eval x).bind (fun y => (f y : Part γ)) := by
  ext z
  simp only [mem_eval_iff, stage_filterMap, Option.bind_eq_some_iff, Part.mem_bind_iff,
    Part.mem_coe, Option.mem_def]
  exact ⟨fun ⟨s, y, hy, hz⟩ => ⟨y, ⟨s, hy⟩, hz⟩,
    fun ⟨y, ⟨s, hy⟩, hz⟩ => ⟨s, y, hy, hz⟩⟩

/-- Changing the successful output by a total function preserves persistence. -/
def map (f : β → γ) : StagedPartial α γ :=
  P.filterMap (some ∘ f)

/-- Mapping a stage table maps each present value. -/
@[simp]
theorem stage_map (f : β → γ) (x : α) (s : ℕ) :
    (P.map f).stage x s = (P.stage x s).map f := by
  rw [map, stage_filterMap, Option.map_eq_bind]

/-- Mapping observations commutes with taking the partial function. -/
@[simp]
theorem eval_map (f : β → γ) (x : α) : (P.map f).eval x = (P.eval x).map f := by
  rw [map, eval_filterMap]
  simp only [Function.comp_apply, Part.coe_some, Part.bind_some_eq_map]

/-- Observe the table at stages given by a monotone clock. -/
def reindex (t : ℕ → ℕ) (ht : Monotone t) : StagedPartial α β where
  stage x s := P.stage x (t s)
  persistent hst := P.persistent (ht hst)

/-- The reindexed table observes the old table at the clock value. -/
@[simp]
theorem stage_reindex {t : ℕ → ℕ} (ht : Monotone t) (x : α) (s : ℕ) :
    (P.reindex t ht).stage x s = P.stage x (t s) := (rfl)

/-- A cofinal clock does not lose any value of the partial function. -/
@[simp]
theorem eval_reindex {t : ℕ → ℕ} (ht : Monotone t) (hcof : ∀ s, ∃ k, s ≤ t k) (x : α) :
    (P.reindex t ht).eval x = P.eval x := by
  ext y
  simp only [mem_eval_iff, stage_reindex]
  exact ⟨fun ⟨k, h⟩ => ⟨t k, h⟩, fun ⟨s, h⟩ =>
    let ⟨k, hk⟩ := hcof s
    ⟨k, P.persistent hk h⟩⟩

section ComputableIn

variable [Primcodable α] [Primcodable β] {G : Set (ℕ →. ℕ)}

/-- Effective observations give a partial function recursive in the same oracle family. -/
theorem recursiveIn_eval (hP : ComputableIn₂ G P.stage) : RecursiveIn G P.eval :=
  RecursiveIn.rfindOpt hP

/-- Precomposing the inputs by an oracle-computable function preserves relative effectivity. -/
theorem computableIn₂_stage_comap {δ : Type*} [Primcodable δ] (hP : ComputableIn₂ G P.stage)
    {f : δ → α} (hf : ComputableIn G f) : ComputableIn₂ G (P.comap f).stage := by
  simpa only [ComputableIn₂, stage_comap] using
    hP.comp ((hf.comp ComputableIn.fst).pair ComputableIn.snd)

/-- An oracle-computable optional output map preserves the relative effectivity of a table. -/
theorem computableIn₂_stage_filterMap [Primcodable γ] (hP : ComputableIn₂ G P.stage)
    {f : β → Option γ} (hf : ComputableIn G f) : ComputableIn₂ G (P.filterMap f).stage := by
  simpa only [ComputableIn₂, stage_filterMap] using
    hP.option_bind (g := fun (_ : α × ℕ) y => f y) (hf.comp ComputableIn.snd)

/-- Mapping by an oracle-computable function preserves the relative effectivity of a table. -/
theorem computableIn₂_stage_map [Primcodable γ] (hP : ComputableIn₂ G P.stage)
    {f : β → γ} (hf : ComputableIn G f) : ComputableIn₂ G (P.map f).stage := by
  exact P.computableIn₂_stage_filterMap hP (Primrec.option_some.computableIn.comp hf)

/-- Reindexing by an oracle-computable monotone clock preserves relative effectivity. -/
theorem computableIn₂_stage_reindex (hP : ComputableIn₂ G P.stage)
    {t : ℕ → ℕ} (ht : Monotone t) (he : ComputableIn G t) :
    ComputableIn₂ G (P.reindex t ht).stage := by
  simpa only [ComputableIn₂, stage_reindex] using
    hP.comp (ComputableIn.fst.pair (he.comp ComputableIn.snd))

end ComputableIn

end StagedPartial

end TauCeti
