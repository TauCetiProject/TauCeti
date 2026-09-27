/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic
public import TauCeti.Topology.Homotopy.Path

/-!
# Semilocally simple connectivity: characterizations and path-homotopy-trivial neighbourhoods

This file characterizes the based pointwise predicate `SemilocallySimplyConnectedAt x` from
`TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic` by open neighbourhoods, by the
triviality of the map on fundamental groups induced by the inclusion of a neighbourhood, and by
homotopy of paths with a common endpoint. It introduces `SemilocallySimplyConnectedOn` and
`IsPathHomotopyTrivial`, and shows that on a locally path-connected space the based condition
yields open, path-connected neighbourhoods in which *all* loops, at every basepoint, are
null-homotopic in the ambient space (the unbased form, Brazas, Definition 2.2), which is what the
universal-cover construction consumes.

It is adapted from the Mathlib drafts
[#31449](https://github.com/leanprover-community/mathlib4/pull/31449),
[#31576](https://github.com/leanprover-community/mathlib4/pull/31576), and
[#38292](https://github.com/leanprover-community/mathlib4/pull/38292) by Kim Morrison, for
Stage 0.1 of the `TauCetiRoadmap/UniversalCovers` roadmap, following the earlier Tau Ceti
work in [#42](https://github.com/TauCetiProject/TauCeti/pull/42).
-/

noncomputable section

open Filter Set Topology TauCeti

variable {X : Type*} [TopologicalSpace X]

/-! ### SemilocallySimplyConnectedAt -/

/-- Characterization of `SemilocallySimplyConnectedAt x` by open neighbourhoods whose loops
based at `x` are null-homotopic in the ambient space. -/
public theorem semilocallySimplyConnectedAt_iff {x : X} :
    SemilocallySimplyConnectedAt x ↔
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ γ : Path x x, range γ ⊆ U → γ.Homotopic (Path.refl x) := by
  constructor
  · intro h
    obtain ⟨U, hU, hU_loops⟩ := semilocallySimplyConnectedAt_def.mp h
    obtain ⟨V, hVU, hV_open, hxV⟩ := mem_nhds_iff.mp hU
    exact ⟨V, hV_open, hxV, fun γ hγ ↦ hU_loops γ (hγ.trans hVU)⟩
  · rintro ⟨U, hU_open, hxU, hU_loops⟩
    exact semilocallySimplyConnectedAt_def.mpr ⟨U, hU_open.mem_nhds hxU, hU_loops⟩

/-- Characterization of `SemilocallySimplyConnectedAt x` by the fundamental group: the map
`π₁(U, x) → π₁(X, x)` induced by the inclusion of some neighbourhood `U` is trivial. -/
public theorem semilocallySimplyConnectedAt_iff_range_eq_bot {x : X} :
    SemilocallySimplyConnectedAt x ↔
      ∃ U ∈ 𝓝 x, ∀ hx : x ∈ U,
        (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
          ⟨x, hx⟩).range = ⊥ := by
  constructor
  · intro h
    obtain ⟨U, hU, hU_loops⟩ := semilocallySimplyConnectedAt_def.mp h
    refine ⟨U, hU, fun hx ↦ (TauCeti.FundamentalGroup.map_range_eq_bot_iff _ _).mpr fun γ ↦
      hU_loops _ ?_⟩
    rintro _ ⟨t, rfl⟩
    exact (γ t).property
  · rintro ⟨U, hU, hU_triv⟩
    refine semilocallySimplyConnectedAt_def.mpr ⟨U, hU, fun γ hγ ↦ ?_⟩
    have hmem : ∀ t, γ t ∈ U := fun t ↦ hγ ⟨t, rfl⟩
    have h := (TauCeti.FundamentalGroup.map_range_eq_bot_iff ⟨Subtype.val, continuous_subtype_val⟩
      (⟨x, mem_of_mem_nhds hU⟩ : U)).mp (hU_triv _) (γ.codRestrict hmem)
    rwa [Path.map_codRestrict] at h

/-- Characterization of `SemilocallySimplyConnectedAt x` by paths: some open neighbourhood `U`
of `x` has any two paths in `U` from `x` to a common endpoint homotopic in the ambient space. -/
public theorem semilocallySimplyConnectedAt_iff_paths {x : X} :
    SemilocallySimplyConnectedAt x ↔
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ {u : X} (γ γ' : Path x u), range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' := by
  rw [semilocallySimplyConnectedAt_iff]
  refine exists_congr fun U ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    ⟨fun hU_loops u γ γ' hγ hγ' ↦ ?_, fun hU_paths γ hγ ↦ ?_⟩
  · -- `γ.trans γ'.symm` is a loop at `x` in `U`, hence null-homotopic.
    refine Path.Homotopic.of_trans_symm (hU_loops _ ?_)
    rw [Path.trans_range, Path.symm_range]
    exact union_subset hγ hγ'
  · refine hU_paths γ (Path.refl x) hγ ?_
    simpa using hγ ⟨0, γ.source⟩

/-! ### SemilocallySimplyConnectedOn -/

variable {s t : Set X} {x : X}

/-- A space is semilocally simply connected on `s` if it is semilocally simply connected
at every point of `s`. -/
public def SemilocallySimplyConnectedOn (s : Set X) : Prop :=
  ∀ x ∈ s, SemilocallySimplyConnectedAt x

/-- Extract the pointwise `SemilocallySimplyConnectedAt x` statement from
`SemilocallySimplyConnectedOn s` and `x ∈ s`. -/
public theorem SemilocallySimplyConnectedOn.at (h : SemilocallySimplyConnectedOn s) (hx : x ∈ s) :
    SemilocallySimplyConnectedAt x :=
  h x hx

/-- Semilocal simple connectivity on a set restricts to any subset. -/
public theorem SemilocallySimplyConnectedOn.mono (h : SemilocallySimplyConnectedOn t)
    (hst : s ⊆ t) : SemilocallySimplyConnectedOn s :=
  fun x hx ↦ h x (hst hx)

/-- Set-level characterization of `SemilocallySimplyConnectedOn`: every point of `s` has an
open neighbourhood in which every loop based at that point is null-homotopic in the ambient
space. -/
public theorem semilocallySimplyConnectedOn_iff :
    SemilocallySimplyConnectedOn s ↔
      ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ γ : Path x x, range γ ⊆ U → γ.Homotopic (Path.refl x) :=
  forall₂_congr fun _ _ ↦ semilocallySimplyConnectedAt_iff

/-- Set-level path characterization of `SemilocallySimplyConnectedOn`: every point `x` of `s` has
an open neighbourhood in which paths from `x` to a common endpoint are homotopic in the ambient
space. -/
public theorem semilocallySimplyConnectedOn_iff_paths :
    SemilocallySimplyConnectedOn s ↔
      ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ {u : X} (γ γ' : Path x u), range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' :=
  forall₂_congr fun _ _ ↦ semilocallySimplyConnectedAt_iff_paths

/-- A semilocally simply connected space is semilocally simply connected on every subset. -/
public theorem SemilocallySimplyConnectedOn.of_semilocallySimplyConnectedSpace
    [SemilocallySimplyConnectedSpace X] (s : Set X) :
    SemilocallySimplyConnectedOn s :=
  fun x _ ↦ SemilocallySimplyConnectedSpace.semilocallySimplyConnectedAt x

/-! ### Path-homotopy-trivial neighbourhoods -/

/-- A subset `U` of a topological space `X` is *path-homotopy-trivial* if any two paths
in `X` whose images lie in `U` and which share endpoints are homotopic in `X`.
This is the form of "`U` is simply connected" used in the universal-cover
construction: it is weaker than `IsSimplyConnected U` because the homotopy is not required
to lie inside `U`. -/
public def IsPathHomotopyTrivial (U : Set X) : Prop :=
  ∀ ⦃a b : X⦄ (p q : Path a b), range p ⊆ U → range q ⊆ U → Path.Homotopic p q

/-- The defining characterization of a path-homotopy-trivial set. -/
public theorem isPathHomotopyTrivial_def :
    IsPathHomotopyTrivial U ↔
      ∀ ⦃a b : X⦄ (p q : Path a b), range p ⊆ U → range q ⊆ U → Path.Homotopic p q :=
  Iff.rfl

/-- In a locally path-connected space, a point at which the space is semilocally simply
connected has an open, path-connected, path-homotopy-trivial neighbourhood, as needed in the
construction of the universal cover. -/
public theorem SemilocallySimplyConnectedAt.exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial
    [LocallyPathConnectedSpace X] {x : X} (h : SemilocallySimplyConnectedAt x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧ IsPathHomotopyTrivial U := by
  obtain ⟨U, hU_open, hxU, hU_loops⟩ := semilocallySimplyConnectedAt_iff.mp h
  refine ⟨pathComponentIn U x, hU_open.pathComponentIn x, mem_pathComponentIn_self hxU,
    isPathConnected_pathComponentIn hxU, fun a b p q hp hq ↦ ?_⟩
  refine Path.Homotopic.of_trans_symm ?_
  -- Conjugate the loop `p.trans q.symm` at `a` back to `x` along a path `α` in the component.
  obtain ⟨α, hα⟩ : JoinedIn U x a := hp ⟨0, p.source⟩
  refine Path.Homotopic.of_conj_nullhomotopic
    (hU_loops ((α.trans (p.trans q.symm)).trans α.symm) ?_)
  simp only [Path.trans_range, Path.symm_range, union_subset_iff]
  exact ⟨⟨range_subset_iff.mpr hα, hp.trans pathComponentIn_subset,
    hq.trans pathComponentIn_subset⟩, range_subset_iff.mpr hα⟩

/-- In a locally path-connected semilocally simply connected space, every point has an open,
path-connected, path-homotopy-trivial neighbourhood. -/
public theorem exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial
    [SemilocallySimplyConnectedSpace X] [LocallyPathConnectedSpace X] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧ IsPathHomotopyTrivial U :=
  SemilocallySimplyConnectedAt.exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial
    (SemilocallySimplyConnectedSpace.semilocallySimplyConnectedAt x)

end
