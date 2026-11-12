/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Spectral.LocallySpectral
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.InductiveDimension.Classes
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Worked examples: locally spectral spaces and maps

These examples test `TauCeti.IsLocallySpectralSpace` and `TauCeti.IsLocallySpectralMap` against
the standard positive and negative cases.

* Discrete `ℕ` is locally spectral but not compact, while `ℝ` is not locally spectral: its only
  spectral open subset is empty.
* The map from discrete `ℕ` to a point, the projection `ℕ × ℕ → ℕ` and the inclusion of `ℕ` into
  its one-point compactification are locally spectral but not spectral, so the relative notion
  is genuinely weaker than Mathlib's `IsSpectralMap` once the source is not spectral. The
  positive halves are instances of the cover criterion
  `TauCeti.IsLocallySpectralMap.of_forall_exists`.
* The hypothesis on the middle space in `TauCeti.IsLocallySpectralMap.comp` cannot be dropped.
  Send the point at infinity of the one-point compactification of `ℕ` to `0` and `n` to
  `1 / (n + 1)` in `ℝ`, and map `ℝ` to the Sierpiński space `Prop` by positivity. Both maps are
  locally spectral because `ℝ` has no nonempty spectral open subset, yet their composite is a
  continuous map between spectral spaces that is not spectral.
-/

open Set Filter Topology

namespace TauCeti

/-- Discrete `ℕ` is locally spectral although it is not compact. -/
example : IsLocallySpectralSpace ℕ ∧ ¬ CompactSpace ℕ :=
  ⟨isLocallySpectralSpace_iff.mpr fun n ↦ ⟨{n}, isOpen_discrete _, rfl, {}⟩,
    fun h ↦ (finite_univ_iff.mp (isCompact_iff_finite.mp h.isCompact_univ)).not_infinite
      inferInstance⟩

/-- The empty space is locally spectral. -/
example : IsLocallySpectralSpace Empty := isLocallySpectralSpace_iff.mpr fun x ↦ x.elim

/-- The real line is not locally spectral: a spectral open neighbourhood of `0` would be a
nonempty compact open subset of the connected noncompact space `ℝ`. -/
example : ¬ IsLocallySpectralSpace ℝ := fun h ↦ by
  obtain ⟨U, hUo, h0U, hUs⟩ := isLocallySpectralSpace_iff.mp h 0
  have hUc : IsCompact U := isCompact_iff_compactSpace.mpr hUs.toCompactSpace
  rcases isClopen_iff.mp ⟨hUc.isClosed, hUo⟩ with rfl | rfl
  · exact h0U
  · exact noncompact_univ ℝ hUc

/-- The map from discrete `ℕ` to a point is locally spectral without being spectral. -/
example : IsLocallySpectralMap (fun _ : ℕ ↦ PUnit.unit) ∧
    ¬ IsSpectralMap (fun _ : ℕ ↦ PUnit.unit) := by
  refine ⟨.of_forall_exists fun n ↦ ⟨{n}, univ, mapsTo_univ _ _, isOpen_discrete _, isOpen_univ,
    rfl, inferInstance, continuous_of_discreteTopology, fun _ _ _ ↦ (toFinite _).isCompact⟩,
    fun h ↦ ?_⟩
  have := h.isCompact_preimage_of_isOpen isOpen_univ isCompact_univ
  rw [preimage_univ, isCompact_iff_finite] at this
  exact infinite_univ this

/-- The identity of the one-point space is locally spectral. -/
example : IsLocallySpectralMap (id : PUnit → PUnit) := isLocallySpectralMap_id

/-- The characteristic function of `{0}` on `ℝ` is not locally spectral, since it is not
continuous. -/
example : ¬ IsLocallySpectralMap (fun x : ℝ ↦ x = 0) := fun h ↦
  not_isOpen_singleton (0 : ℝ) (continuous_Prop.mp h.continuous)

/-- The projection `ℕ × ℕ → ℕ` of discrete spaces is locally spectral but not spectral: the inverse
image of a point is infinite. -/
example : IsLocallySpectralMap (Prod.fst : ℕ × ℕ → ℕ) ∧ ¬ IsSpectralMap (Prod.fst : ℕ × ℕ → ℕ) := by
  refine ⟨.of_forall_exists fun p ↦ ⟨{p}, {p.1}, mapsTo_singleton.mpr rfl, isOpen_discrete _,
    isOpen_discrete _, rfl, inferInstance, continuous_of_discreteTopology,
    fun _ _ _ ↦ (toFinite _).isCompact⟩, fun h ↦ ?_⟩
  have := h.isCompact_preimage_of_isOpen (isOpen_discrete {0}) isCompact_singleton
  rw [isCompact_iff_finite] at this
  exact infinite_of_injective_forall_mem (f := fun n : ℕ ↦ ((0, n) : ℕ × ℕ))
    (fun _ _ h ↦ congrArg Prod.snd h) (fun _ ↦ rfl) this

/-- The inclusion of discrete `ℕ` into its one-point compactification is locally spectral but not
spectral, so agreement of the two notions needs a spectral source even over a spectral target. -/
example : IsLocallySpectralMap ((↑) : ℕ → OnePoint ℕ) ∧ ¬ IsSpectralMap ((↑) : ℕ → OnePoint ℕ) := by
  refine ⟨.of_forall_exists fun n ↦ ⟨{n}, {(n : OnePoint ℕ)}, mapsTo_singleton.mpr rfl,
    isOpen_discrete _, ?_, rfl, inferInstance, continuous_of_discreteTopology,
    fun _ _ _ ↦ (toFinite _).isCompact⟩, fun h ↦ ?_⟩
  · rw [← image_singleton]
    exact OnePoint.isOpen_image_coe.mpr (isOpen_discrete _)
  · have := h.isCompact_preimage_of_isOpen isOpen_univ isCompact_univ
    rw [preimage_univ, isCompact_iff_finite] at this
    exact infinite_univ this

/-- Composition of locally spectral maps needs a locally spectral middle space. Let
`f : OnePoint ℕ → ℝ` send `n` to `1 / (n + 1)` and the point at infinity to `0`, and let
`g : ℝ → Prop` be positivity, valued in the Sierpiński space. Both maps are locally spectral, but
their composite `x ↦ (x ≠ ∞)` between spectral spaces is not: the open point `True` pulls back to
the noncompact subset `ℕ`. -/
example : ∃ (f : OnePoint ℕ → ℝ) (g : ℝ → Prop),
    IsLocallySpectralMap f ∧ IsLocallySpectralMap g ∧ ¬ IsLocallySpectralMap (g ∘ f) := by
  -- The only spectral open subset of `ℝ` is empty, so continuous maps into or out of `ℝ` are
  -- locally spectral.
  have hR (U : Set ℝ) (hUo : IsOpen U) (hUs : SpectralSpace U) : U = ∅ := by
    have hUc : IsCompact U := isCompact_iff_compactSpace.mpr hUs.toCompactSpace
    refine (isClopen_iff.mp ⟨hUc.isClosed, hUo⟩).resolve_right ?_
    rintro rfl
    exact noncompact_univ ℝ hUc
  let f : OnePoint ℕ → ℝ := fun x ↦ x.elim 0 fun n ↦ 1 / ((n : ℝ) + 1)
  let g : ℝ → Prop := fun x ↦ 0 < x
  have hf : IsLocallySpectralMap f := by
    refine .of_isSpectralMap_restrict ((OnePoint.continuous_iff_from_nat f).mpr
      tendsto_one_div_add_atTop_nhds_zero_nat) fun U V hUV _ hVo _ hVs ↦ ?_
    obtain rfl := hR V hVo hVs
    obtain rfl := mapsTo_empty_iff.mp hUV
    exact ⟨continuous_of_discreteTopology, fun _ _ _ ↦ (toFinite _).isCompact⟩
  have hg : IsLocallySpectralMap g := by
    refine .of_isSpectralMap_restrict (continuous_Prop.mpr isOpen_Ioi)
      fun U V hUV hUo _ hUs _ ↦ ?_
    obtain rfl := hR U hUo hUs
    exact ⟨continuous_of_discreteTopology, fun _ _ _ ↦ (toFinite _).isCompact⟩
  refine ⟨f, g, hf, hg, fun h ↦ ?_⟩
  -- `OnePoint ℕ` is compact, Hausdorff and totally disconnected, so its clopen subsets form a basis
  -- of compact opens.
  have : SpectralSpace (OnePoint ℕ) :=
    { toPrespectralSpace := .of_isTopologicalBasis isTopologicalBasis_isClopen
        fun _ hU ↦ hU.isClosed.isCompact }
  have : SpectralSpace Prop := spectralSpace_prop
  have hpre : g ∘ f ⁻¹' {True} = range ((↑) : ℕ → OnePoint ℕ) := by
    ext x
    induction x using OnePoint.rec <;> simp [f, g, Nat.cast_add_one_pos]
  have hc := (isLocallySpectralMap_iff_isSpectralMap.mp h).isCompact_preimage_of_isOpen
    isOpen_singleton_true isCompact_singleton
  rw [hpre, ← image_univ, OnePoint.isOpenEmbedding_coe.isEmbedding.isCompact_iff.symm,
    isCompact_iff_finite] at hc
  exact infinite_univ hc

/-- Every map out of an empty space is spectral in both senses. -/
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [IsEmpty X] (f : X → Y) :
    IsLocallySpectralMap f ∧ IsSpectralMap f :=
  have hf : IsSpectralMap f := ⟨continuous_of_discreteTopology, fun _ _ _ ↦ (toFinite _).isCompact⟩
  ⟨hf.isLocallySpectralMap, hf⟩

end TauCeti
