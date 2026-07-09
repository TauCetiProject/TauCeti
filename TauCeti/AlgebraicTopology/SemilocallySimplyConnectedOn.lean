/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected
public import TauCeti.Topology.Homotopy.Path
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Semilocally simple connectivity on sets

This file develops the unbased, pointwise form of semilocal simple connectivity used by the
universal-cover construction. It is adapted from the Mathlib drafts
[#31449](https://github.com/leanprover-community/mathlib4/pull/31449),
[#31576](https://github.com/leanprover-community/mathlib4/pull/31576), and
[#38292](https://github.com/leanprover-community/mathlib4/pull/38292) by Kim Morrison, for
Stage 0.1 of the `TauCetiRoadmap/UniversalCovers` roadmap, following the earlier Tau Ceti
work in [#42](https://github.com/TauCetiProject/TauCeti/pull/42).
-/

noncomputable section

open CategoryTheory Filter FundamentalGroupoid Set Topology TauCeti

variable {X : Type*} [TopologicalSpace X]

namespace FundamentalGroup

/-- Mapping a loop class represented by a path is represented by mapping that path. -/
theorem map_fromPath {Y : Type*} [TopologicalSpace Y] (f : C(X, Y)) (base : X)
    (q : Path base base) :
    FundamentalGroup.map f base (FundamentalGroup.fromPath ⟦q⟧) =
      FundamentalGroup.fromPath ⟦q.map f.continuous⟧ := by
  rfl

end FundamentalGroup

/-! ### SemilocallySimplyConnectedAt -/

/-- A space is semilocally simply connected at `x` if `x` has a neighborhood `U` such that
the map from `π₁(U, base)` to `π₁(X, base)` induced by the inclusion is trivial for all
basepoints in `U`. Equivalently, every loop in `U` is nullhomotopic in `X`. -/
public def SemilocallySimplyConnectedAt (x : X) : Prop :=
  ∃ U ∈ 𝓝 x, ∀ (base : U),
    (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) base).range = ⊥

/-- Simply connected spaces are semilocally simply connected at every point. -/
public theorem SemilocallySimplyConnectedAt.of_simplyConnectedSpace
    [SimplyConnectedSpace X] (x : X) :
    SemilocallySimplyConnectedAt x :=
  ⟨univ, univ_mem, fun base ↦ by
    simp only [MonoidHom.range_eq_bot_iff]
    ext
    exact Subsingleton.elim (α := Path.Homotopic.Quotient base.val base.val) _ _⟩

/-- Characterization of `SemilocallySimplyConnectedAt x` by open neighborhoods whose loops are
nullhomotopic in the ambient space. -/
public theorem semilocallySimplyConnectedAt_iff {x : X} :
    SemilocallySimplyConnectedAt x ↔
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u : X} (γ : Path u u) (_ : range γ ⊆ U),
        Path.Homotopic γ (Path.refl u) := by
  constructor
  · -- Forward direction: SemilocallySimplyConnectedAt implies small loops are null
    intro ⟨U, hU_nhd, hU_loops⟩
    obtain ⟨V, hVU, hV_open, hx_in_V⟩ := mem_nhds_iff.mp hU_nhd
    refine ⟨V, hV_open, hx_in_V, ?_⟩
    intro u γ hγ_range
    -- Since range γ ⊆ V ⊆ U, γ takes values in U
    have hγ_mem : ∀ t, γ t ∈ U := fun t ↦ hVU (hγ_range ⟨t, rfl⟩)
    -- Restrict γ to a path in the subspace U
    let γ_U : Path (⟨u, γ.source ▸ hγ_mem 0⟩ : U) ⟨u, γ.target ▸ hγ_mem 1⟩ := γ.codRestrict hγ_mem
    -- The basepoint u' : U
    let u' : U := ⟨u, γ.source ▸ hγ_mem 0⟩
    -- The map from π₁(U, u') to π₁(X, u) has trivial range
    have h_range := hU_loops u'
    rw [MonoidHom.range_eq_bot_iff] at h_range
    have h_map_eq : FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ u'
        (FundamentalGroup.fromPath ⟦γ_U⟧) =
      FundamentalGroup.fromPath ⟦γ_U.map continuous_subtype_val⟧ :=
        FundamentalGroup.map_fromPath ⟨Subtype.val, continuous_subtype_val⟩ u' γ_U
    have h_map : FundamentalGroup.fromPath ⟦γ_U.map continuous_subtype_val⟧ =
        FundamentalGroup.fromPath ⟦Path.refl u⟧ := by
      rw [← h_map_eq, h_range]; rfl
    rw [Path.map_codRestrict] at h_map
    exact Quotient.eq.mp h_map
  · -- Backward direction: small loops null implies SemilocallySimplyConnectedAt
    intro ⟨U, hU_open, hx_in_U, hU_loops_null⟩
    refine ⟨U, hU_open.mem_nhds hx_in_U, ?_⟩; intro base
    simp only [MonoidHom.range_eq_bot_iff]; ext p
    obtain ⟨γ', rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath p)
    have hrange : range (γ'.map continuous_subtype_val) ⊆ U := by
      rintro _ ⟨t, rfl⟩
      exact (γ' t).property
    have hhom := hU_loops_null (γ'.map continuous_subtype_val) hrange
    have h_map_eq : FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ base
        (FundamentalGroup.fromPath ⟦γ'⟧) =
      FundamentalGroup.fromPath ⟦γ'.map continuous_subtype_val⟧ :=
        FundamentalGroup.map_fromPath ⟨Subtype.val, continuous_subtype_val⟩ base γ'
    rw [h_map_eq, Quotient.sound hhom]
    rfl

/-- Characterization of semilocally simply connected at a point: any two paths in U between
the same endpoints are homotopic. -/
public theorem semilocallySimplyConnectedAt_iff_paths {x : X} :
    SemilocallySimplyConnectedAt x ↔
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u u' : X} (γ γ' : Path u u'),
        range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' := by
  rw [semilocallySimplyConnectedAt_iff]
  constructor
  · intro ⟨U, hU_open, hx_in_U, hU_loops⟩
    refine ⟨U, hU_open, hx_in_U, ?_⟩
    intro u u' γ γ' hγ hγ'
    -- γ.trans γ'.symm is a loop in U, hence nullhomotopic
    have hloop : range (γ.trans γ'.symm) ⊆ U := by
      intro y hy
      simp only [Path.trans_range, Path.symm_range] at hy
      exact hy.elim (fun h ↦ hγ h) (fun h ↦ hγ' h)
    have hnull := hU_loops (γ.trans γ'.symm) hloop
    exact Path.Homotopic.of_trans_symm hnull
  · intro ⟨U, hU_open, hx_in_U, hU_paths⟩
    refine ⟨U, hU_open, hx_in_U, ?_⟩
    intro u γ hγ
    have hrefl : range (Path.refl u) ⊆ U := by
      simp only [Path.refl_range, singleton_subset_iff]
      exact hγ ⟨0, γ.source⟩
    exact hU_paths γ (Path.refl u) hγ hrefl

/-! ### SemilocallySimplyConnectedOn -/

variable {s t : Set X} {x : X}

/-- A space is semilocally simply connected on `s` if it is semilocally simply connected
at every point of `s`. -/
public def SemilocallySimplyConnectedOn (s : Set X) : Prop :=
  ∀ x ∈ s, SemilocallySimplyConnectedAt x

public theorem SemilocallySimplyConnectedOn.at (h : SemilocallySimplyConnectedOn s) (hx : x ∈ s) :
    SemilocallySimplyConnectedAt x :=
  h x hx

public theorem SemilocallySimplyConnectedOn.mono (h : SemilocallySimplyConnectedOn t)
    (hst : s ⊆ t) : SemilocallySimplyConnectedOn s :=
  fun x hx ↦ h x (hst hx)

/-- A subset `U` of a topological space `X` is *path-homotopy-trivial* if any two paths
in `X` whose images lie in `U` and which share endpoints are homotopic in `X`.
This is the form of "`U` is simply connected" used in the universal-cover
construction: it is weaker than `IsSimplyConnected U` because the homotopy is not required
to lie inside `U`. -/
public def IsPathHomotopyTrivial (U : Set X) : Prop :=
  ∀ ⦃a b : X⦄ (p q : Path a b), range p ⊆ U → range q ⊆ U → Path.Homotopic p q

/-- Unfold `IsPathHomotopyTrivial U` as the assertion that any two same-endpoint paths whose
ranges lie in `U` are homotopic in the ambient space `X`. -/
public theorem isPathHomotopyTrivial_iff {U : Set X} :
    IsPathHomotopyTrivial U ↔
      ∀ ⦃a b : X⦄ (p q : Path a b), range p ⊆ U → range q ⊆ U → Path.Homotopic p q :=
  Iff.rfl

/-- Apply path-homotopy triviality of `U` to compare two same-endpoint paths in `X` whose
ranges both lie in `U`. -/
public theorem IsPathHomotopyTrivial.apply {U : Set X} (hU : IsPathHomotopyTrivial U)
    ⦃a b : X⦄ (p q : Path a b) (hp : range p ⊆ U) (hq : range q ⊆ U) :
    Path.Homotopic p q :=
  hU p q hp hq

/-- Package the ambient homotopy comparison property for all same-endpoint paths with ranges in
`U` as `IsPathHomotopyTrivial U`. -/
public theorem IsPathHomotopyTrivial.mk {U : Set X}
    (hU : ∀ ⦃a b : X⦄ (p q : Path a b), range p ⊆ U → range q ⊆ U →
      Path.Homotopic p q) :
    IsPathHomotopyTrivial U :=
  hU

/-- Set-level characterization of `SemilocallySimplyConnectedOn`: every point of `s` has an
open neighborhood in which every loop is nullhomotopic in the ambient space. -/
public theorem semilocallySimplyConnectedOn_iff :
    SemilocallySimplyConnectedOn s ↔
    ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u : X} (γ : Path u u) (_ : range γ ⊆ U),
        Path.Homotopic γ (Path.refl u) :=
  forall₂_congr fun _ _ ↦ semilocallySimplyConnectedAt_iff

/-- Set-level path characterization of `SemilocallySimplyConnectedOn`: every point of `s` has an
open neighborhood in which same-endpoint paths with ranges in that neighborhood are homotopic in
the ambient space. -/
public theorem semilocallySimplyConnectedOn_iff_paths :
    SemilocallySimplyConnectedOn s ↔
    ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u u' : X} (γ γ' : Path u u'),
        range γ ⊆ U → range γ' ⊆ U → γ.Homotopic γ' :=
  forall₂_congr fun _ _ ↦ semilocallySimplyConnectedAt_iff_paths

/-! ### Bridging to `TauCeti.SemilocallySimplyConnectedSpace`

The class `TauCeti.SemilocallySimplyConnectedSpace` (see
`TauCeti.AlgebraicTopology.SemilocallySimplyConnected`) records the *based* form of semilocal
simple connectivity (Brazas, Definition 2.1): every point `x` has a neighbourhood in which every
loop *based at `x`* is null-homotopic in `X`. The `SemilocallySimplyConnectedAt` predicate above
is the *unbased* form (Brazas, Definition 2.2), asking the same of loops based at *any* point of
the neighbourhood. The two coincide on locally path-connected spaces, which is the setting for
covering-space theory, so the bridge below is stated under `[LocallyPathConnectedSpace X]`. -/

/-- On a locally path-connected space, the based class
`TauCeti.SemilocallySimplyConnectedSpace` implies the unbased pointwise predicate
`SemilocallySimplyConnectedAt` at every point. -/
public theorem SemilocallySimplyConnectedAt.of_semilocallySimplyConnectedSpace
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] (x : X) :
    SemilocallySimplyConnectedAt x := by
  obtain ⟨U, hUopen, hxU, hloop⟩ :=
    SemilocallySimplyConnectedSpace.exists_isOpen_mem_nhds_loops_nullhomotopic x
  refine semilocallySimplyConnectedAt_iff.mpr
    ⟨pathComponentIn U x, hUopen.pathComponentIn x, mem_pathComponentIn_self hxU, ?_⟩
  intro u γ hγ
  -- `γ` is a loop at `u` with range in the path component `U'` of `x`.
  have hu : u ∈ pathComponentIn U x := hγ ⟨0, γ.source⟩
  -- Join `x` to `u` inside `U'`.
  let hjoin : JoinedIn (pathComponentIn U x) x u :=
    (isPathConnected_pathComponentIn hxU).joinedIn _ (mem_pathComponentIn_self hxU) _ hu
  let δ : Path x u := hjoin.somePath
  have hδ : Set.range δ ⊆ pathComponentIn U x := Set.range_subset_iff.mpr hjoin.somePath_mem
  -- The conjugated loop `(δ.trans γ).trans δ.symm` is based at `x` and has range in `U`.
  have hδU : ∀ s, δ s ∈ pathComponentIn U x := fun s ↦ hδ ⟨s, rfl⟩
  have hsub : Set.range ((δ.trans γ).trans δ.symm) ⊆ pathComponentIn U x := by
    rw [Path.trans_range, Path.trans_range, Path.symm_range]
    exact Set.union_subset (Set.union_subset (fun _ ⟨s, hs⟩ ↦ hs ▸ hδU s) hγ)
      (fun _ ⟨s, hs⟩ ↦ hs ▸ hδU s)
  have hconj : ((δ.trans γ).trans δ.symm).Homotopic (Path.refl x) :=
    hloop _ fun t ↦ pathComponentIn_subset (hsub ⟨t, rfl⟩)
  -- Recover `γ ≃ refl u` from the conjugation.
  -- `of_trans_symm` on `p = δ.trans γ`, `q = δ`: `δ.trans γ ≃ δ`.
  have hδγ : (δ.trans γ).Homotopic δ := Path.Homotopic.of_trans_symm hconj
  -- Left-cancel `δ`.
  have hcancel : (δ.symm.trans (δ.trans γ)).Homotopic (δ.symm.trans δ) :=
    Path.Homotopic.hcomp (.refl δ.symm) hδγ
  have hleft : (δ.symm.trans (δ.trans γ)).Homotopic γ :=
    (Path.Homotopic.trans_assoc δ.symm δ γ).symm.trans <|
      ((Path.Homotopic.hcomp (Path.Homotopic.symm_trans δ) (.refl γ)).trans
        (Path.Homotopic.refl_trans γ))
  exact hleft.symm.trans (hcancel.trans (Path.Homotopic.symm_trans δ))

/-- On a locally path-connected semilocally simply connected space, every subset is pointwise
semilocally simply connected. -/
public theorem SemilocallySimplyConnectedOn.of_semilocallySimplyConnectedSpace
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] (s : Set X) :
    SemilocallySimplyConnectedOn s :=
  fun x _ ↦ .of_semilocallySimplyConnectedSpace x

/-! ### Helper lemmas for discreteness of path homotopy quotients -/

/-- In an SLSC space, every point has an open neighborhood `U` with the
`IsPathHomotopyTrivial U` property: any two paths in `U` with the same endpoints are
homotopic (so path homotopy classes are determined by endpoints).

This is `semilocallySimplyConnectedAt_iff_paths.mp` repackaged with the
`IsPathHomotopyTrivial` abstraction, which is the form most downstream users consume. -/
public theorem SemilocallySimplyConnectedAt.exists_pathHomotopyTrivial_neighborhood {x : X}
    (h : SemilocallySimplyConnectedAt x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathHomotopyTrivial U :=
  semilocallySimplyConnectedAt_iff_paths.mp h

/-- In a locally path-connected semilocally simply connected space, every point has an open
path-homotopy-trivial neighborhood. -/
public theorem exists_pathHomotopyTrivial_neighborhood
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathHomotopyTrivial U := by
  have hx := SemilocallySimplyConnectedAt.of_semilocallySimplyConnectedSpace x
  exact hx.exists_pathHomotopyTrivial_neighborhood

/-- An SLSC neighborhood can be chosen to be path-connected. In a locally path-connected space,
we can use the path component of x in an SLSC neighborhood V to get a neighborhood that is both
open, path-connected, and has the SLSC property (paths with same endpoints in U are homotopic). -/
public theorem SemilocallySimplyConnectedAt.exists_pathConnected_pathHomotopyTrivial_neighborhood
    [LocallyPathConnectedSpace X] {x : X} (h : SemilocallySimplyConnectedAt x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧ IsPathHomotopyTrivial U := by
  -- Take the path component of `x` in any SLSC neighborhood `V`. It is open by local
  -- path-connectedness, path-connected by construction, and inherits SLSC from `V` by
  -- composing the range subsets through `pathComponentIn_subset : pathComponentIn V x ⊆ V`.
  obtain ⟨V, hV_open, hx_in_V, hV_slsc⟩ := h.exists_pathHomotopyTrivial_neighborhood
  refine ⟨pathComponentIn V x, hV_open.pathComponentIn x, mem_pathComponentIn_self hx_in_V,
    isPathConnected_pathComponentIn hx_in_V, fun _ _ p q hp hq ↦ ?_⟩
  exact hV_slsc.apply p q (hp.trans pathComponentIn_subset) (hq.trans pathComponentIn_subset)

/-- In a locally path-connected semilocally simply connected space, every point has an open,
path-connected, path-homotopy-trivial neighborhood. -/
public theorem exists_pathConnected_pathHomotopyTrivial_neighborhood
    [SemilocallySimplyConnectedSpace X] [LocallyPathConnectedSpace X] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧ IsPathHomotopyTrivial U := by
  have hx := SemilocallySimplyConnectedAt.of_semilocallySimplyConnectedSpace x
  exact hx.exists_pathConnected_pathHomotopyTrivial_neighborhood

end
