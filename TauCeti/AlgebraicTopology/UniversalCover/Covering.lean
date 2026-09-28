/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.AlgebraicTopology.UniversalCover.Basic

/-!
# Universal cover: covering map, simple connectedness, universal property

Building on the sheet decomposition in
`TauCeti.AlgebraicTopology.UniversalCover.Basic`, this file shows that the endpoint projection
`UniversalCover.proj` is a covering map, and derives path-connectedness, simple connectedness,
and the universal lifting property of the universal cover.

This file is adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292), file
`Mathlib/AlgebraicTopology/FundamentalGroupoid/UniversalCover/Covering.lean`.

## Main results

* `UniversalCover.isCoveringMap`: the endpoint projection is a covering map.
* `UniversalCover.discreteTopology_fiber`: fibers of the universal cover are discrete.
* `UniversalCover.pathConnectedSpace`: the universal cover is path-connected.
* `UniversalCover.simplyConnectedSpace`: the universal cover is simply connected.
* `UniversalCover.existsUnique_continuousMap_lifts`: the universal lifting property.

## Implementation notes

`UniversalCover.isCoveringMap` does not assume `X` is path-connected. Over a point with no path
from `x₀` the preimage of a good neighbourhood is empty, hence evenly covered
(`IsEvenlyCovered.of_preimage_eq_empty`); over the path component of `x₀` the sheet
trivialization applies.
-/

public section
noncomputable section

open scoped unitInterval
open Topology

variable {X : Type*} [TopologicalSpace X]

namespace TauCeti.UniversalCover

variable {x₀ x : X}

/-- The endpoint projection `proj` is a covering map, assuming `X` is semilocally simply
connected and locally path-connected. Fibres over points outside the path component of `x₀` are
empty. -/
theorem isCoveringMap [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] (x₀ : X) :
    IsCoveringMap (proj (x₀ := x₀)) := by
  intro x
  obtain ⟨U, hU_open, hxU, hU_pathConn, hU_slsc⟩ :=
    exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial x
  -- This case split, which removes the path-connectedness hypothesis, is adapted from
  -- https://github.com/leanprover-community/mathlib4/pull/38292.
  cases isEmpty_or_nonempty (Path.Homotopic.Quotient x₀ x) with
  | inl h =>
    refine (IsEvenlyCovered.of_preimage_eq_empty Empty (hU_open.mem_nhds hxU)
      ?_).to_isEvenlyCovered_preimage
    apply Set.eq_empty_of_subset_empty
    simpa using sheet_exhaustive (x₀ := x₀) hU_pathConn hxU
  | inr h =>
    let S := sheet (x₀ := x₀) U hxU
    have : Nonempty (X → TauCeti.UniversalCover x₀) :=
      ⟨fun _ ↦ ofBasedPath x₀ (BasedPath.ofPath (Path.refl x₀))⟩
    have h_open_iff : ∀ q : Path.Homotopic.Quotient x₀ x, ∀ {W : Set X}, W ⊆ U →
        (IsOpen W ↔ IsOpen (proj (x₀ := x₀) ⁻¹' W ∩ S q)) := by
      intro q W hWU
      refine ⟨fun hW ↦ (hW.preimage (continuous_proj x₀)).inter (isOpen_sheet U hU_open hxU q),
        fun h_open_inter ↦ ?_⟩
      have h := isOpenMap_proj x₀ _ h_open_inter
      rwa [Set.image_preimage_inter,
        Set.inter_eq_left.mpr (hWU.trans (proj_surjOn_sheet hU_pathConn hxU q))] at h
    refine ((IsEvenlyCovered.of_trivialization (t :=
      IsOpen.trivializationDiscrete (f := proj (x₀ := x₀))
        S U hU_open h_open_iff (proj_injOn_sheet hU_slsc hxU)
        (proj_surjOn_sheet hU_pathConn hxU) (pairwise_disjoint_sheet hU_slsc hxU)
        (sheet_exhaustive hU_pathConn hxU))
      ?_).to_isEvenlyCovered_preimage)
    rw [IsOpen.trivializationDiscrete_baseSet]
    exact hxU

/-- Fibers of the universal cover are discrete. -/
instance discreteTopology_fiber [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ x : X) :
    DiscreteTopology (proj (x₀ := x₀) ⁻¹' {x}) :=
  (isCoveringMap x₀ x).discreteTopology_fiber

/-- Every point of `UniversalCover x₀` is joined to the point represented by the constant
path. The connecting path is the family of initial segments `t ↦ α |_[0, t]`. -/
theorem joined_basepoint_ofBasedPath (α : BasedPath x₀) :
    Joined (ofBasedPath x₀ (BasedPath.refl x₀)) (ofBasedPath x₀ α) :=
  -- Ported from https://github.com/leanprover-community/mathlib4/pull/44185.
  ⟨{  toFun t := ofBasedPath x₀ (α.initialSegmentFamily t)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }⟩

/-- The universal cover is path-connected. -/
instance pathConnectedSpace (x₀ : X) :
    PathConnectedSpace (TauCeti.UniversalCover x₀) := by
  refine ⟨⟨ofBasedPath x₀ (BasedPath.refl x₀)⟩, fun z₁ z₂ ↦ ?_⟩
  obtain ⟨α₁, rfl⟩ := surjective_ofBasedPath x₀ z₁
  obtain ⟨α₂, rfl⟩ := surjective_ofBasedPath x₀ z₂
  exact (joined_basepoint_ofBasedPath α₁).symm.trans (joined_basepoint_ofBasedPath α₂)

/-- The lift through `proj` of a path `γ` starting at the class of `α` ends at the class of
the concatenated based path `α.append γ`. -/
theorem liftPath_apply_one_eq_ofBasedPath_append
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] {α : BasedPath x₀} {y : X}
    (γ : Path (BasedPath.endpoint α) y) :
    (isCoveringMap x₀).liftPath γ (ofBasedPath x₀ α) (by simp) 1 =
      ofBasedPath x₀ (BasedPath.append α γ) := by
  -- Ported from https://github.com/leanprover-community/mathlib4/pull/44185.
  -- The lift is `t ↦ ofBasedPath (append α γ|_[0, t])`.
  let Γ : C(I, TauCeti.UniversalCover x₀) :=
    ⟨fun t ↦ ofBasedPath x₀ (BasedPath.append α (γ.initialSegmentFamily t)), by fun_prop⟩
  have hΓ_lifts : proj (x₀ := x₀) ∘ Γ = γ := by
    ext t
    simp [Γ]
  have hΓ_zero : Γ 0 = ofBasedPath x₀ α := by
    have h0 : ((α.toPath.trans (γ.initialSegmentFamily 0)).cast rfl (by simp)).Homotopic
        α.toPath := by
      rw [Path.initialSegmentFamily_zero]
      -- The remaining casts only change proof fields, so this is `α.toPath.trans (refl _)`.
      exact Path.Homotopic.trans_refl α.toPath
    exact ofBasedPath_eq_of_homotopic_toPath (by rw [BasedPath.endpoint_append]; simp) h0
  rw [← ((isCoveringMap x₀).eq_liftPath_iff' (γ := γ) (γ_0 := by simp) (Γ := Γ)).2
    ⟨hΓ_lifts, hΓ_zero⟩]
  -- `Γ` is given by an anonymous constructor; expose its value at `1`.
  change ofBasedPath x₀ (α.append (γ.initialSegmentFamily 1)) = _
  rw [Path.initialSegmentFamily_one]
  rfl

/-- **A loop whose appended class returns to `α` is nullhomotopic.** If appending the loop `γ` to
`α` leaves the class of `α` unchanged in the universal cover, then `γ` is trivial in the
path-homotopy quotient. -/
private theorem quotient_mk_eq_refl_of_ofBasedPath_append_eq {α : BasedPath x₀}
    (γ : Path (BasedPath.endpoint α) (BasedPath.endpoint α))
    (h_end : ofBasedPath x₀ (BasedPath.append α γ) = ofBasedPath x₀ α) :
    (Path.Homotopic.Quotient.mk γ : Path.Homotopic.Quotient
        (BasedPath.endpoint α) (BasedPath.endpoint α)) =
      Path.Homotopic.Quotient.refl (BasedPath.endpoint α) := by
  apply Quotient.sound
  apply Path.Homotopic.trans_left_cancel (e := α.toPath)
  have h := toPath_homotopic_of_ofBasedPath_eq h_end
  simp only [BasedPath.toPath_append] at h
  have h' : Path.Homotopic (α.toPath.trans γ) α.toPath := by
    convert h using 2
    ext t
    rfl
  exact h'.trans (Path.Homotopic.trans_refl α.toPath).symm

/-- The universal cover is simply connected. -/
instance simplyConnectedSpace [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) :
    SimplyConnectedSpace (TauCeti.UniversalCover x₀) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨pathConnectedSpace x₀, ?_⟩
  intro z p
  obtain ⟨α, rfl⟩ := surjective_ofBasedPath x₀ z
  let γ : Path (BasedPath.endpoint α) (BasedPath.endpoint α) :=
    (p.map (continuous_proj x₀)).cast
      (proj_ofBasedPath x₀ α).symm (proj_ofBasedPath x₀ α).symm
  have hγ0 : γ 0 = proj (ofBasedPath x₀ α) := by
    rw [proj_ofBasedPath]
    exact γ.source
  have hp_eq_lift :
      (p : C(I, TauCeti.UniversalCover x₀)) =
        (isCoveringMap x₀).liftPath γ (ofBasedPath x₀ α) hγ0 :=
    ((isCoveringMap x₀).eq_liftPath_iff' (γ := γ)
      (e := ofBasedPath x₀ α) (γ_0 := hγ0) (Γ := p)).2
      ⟨by ext t; rfl, p.source⟩
  have h_end : ofBasedPath x₀ (BasedPath.append α γ) = ofBasedPath x₀ α := by
    rw [← liftPath_apply_one_eq_ofBasedPath_append, ← hp_eq_lift]
    exact p.target
  have hγ_null := quotient_mk_eq_refl_of_ofBasedPath_append_eq γ h_end
  rw [← Path.Homotopic.Quotient.eq]
  apply (isCoveringMap x₀).injective_path_homotopic_map
    (ofBasedPath x₀ α) (ofBasedPath x₀ α)
  have hcast :=
    congrArg (Path.Homotopic.Quotient.cast · (proj_ofBasedPath x₀ α) (proj_ofBasedPath x₀ α))
      hγ_null
  simp only [γ, ← Path.Homotopic.Quotient.mk_map] at hcast ⊢
  simpa using hcast

/-- Universal property of the universal cover: a continuous map from a simply connected,
locally path-connected space lifts uniquely after specifying the image of one point. -/
theorem existsUnique_continuousMap_lifts {A : Type*} [TopologicalSpace A]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X)
    (f : C(A, X)) (a₀ : A) (e₀ : TauCeti.UniversalCover x₀) (he : proj e₀ = f a₀) :
    ∃! F : C(A, TauCeti.UniversalCover x₀), F a₀ = e₀ ∧ proj ∘ F = f :=
  (isCoveringMap x₀).existsUnique_continuousMap_lifts f a₀ e₀ he

end TauCeti.UniversalCover
