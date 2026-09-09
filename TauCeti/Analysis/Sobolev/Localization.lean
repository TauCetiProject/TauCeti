/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Sets.Opens

/-!
# Smooth cutoffs for compact exhaustion

This file supplies smooth cutoffs for the localization step in the local-to-global arguments
behind Meyers--Serrin.  A compact exhaustion packages these cutoffs for successive interior
compact sets.  This file does not claim any density theorem.

## Main declarations

* `TauCeti.exists_contDiff_cutoff` gives a smooth, compactly supported cutoff which is one on a
  neighborhood of a compact set and supported in a prescribed open neighborhood.
* `TauCeti.CompactExhaustion.exists_contDiff_cutoff` gives the corresponding cutoff for two
  successive terms of a compact exhaustion of an open set.

## References

The pointwise bump construction uses Mathlib's `exists_contDiff_tsupport_subset`.  The
localization role is the standard cutoff step in L. C. Evans, *Partial Differential Equations*,
Section 5.2.
-/

public section

open Function Set TopologicalSpace
open scoped BigOperators ContDiff Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A compact set contained in an open set admits a smooth cutoff equal to one on a neighborhood
of the compact set.

The cutoff takes values in `[0, 1]`, has compact support, and its topological support is contained
in the prescribed open set. -/
theorem exists_contDiff_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ψ : E → ℝ,
      ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧ EqOn ψ 1 K ∧
        K ⊆ interior (ψ ⁻¹' {1}) ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U := by
  classical
  let bump : K → E → ℝ := fun x =>
    Classical.choose (exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
      (hU.mem_nhds (hKU x.2)))
  have hbump (x : K) :
      tsupport (bump x) ⊆ U ∧ HasCompactSupport (bump x) ∧ ContDiff ℝ ∞ (bump x) ∧
        range (bump x) ⊆ Icc 0 1 ∧ bump x (x : E) = 1 := by
    dsimp [bump]
    exact Classical.choose_spec (exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
      (hU.mem_nhds (hKU x.2)))
  have hbump_nonneg (x : K) (y : E) : 0 ≤ bump x y :=
    ((hbump x).2.2.2.1 ⟨y, rfl⟩).1
  have hcover : K ⊆ ⋃ x : K, (bump x) ⁻¹' Ioi (1 / 2 : ℝ) := by
    intro y hy
    let x : K := ⟨y, hy⟩
    refine mem_iUnion.2 ⟨x, ?_⟩
    -- Unpack preimage membership and coerce the compact-set subtype back to `E`.
    change (1 / 2 : ℝ) < bump x (x : E)
    rw [hbump x |>.2.2.2.2]
    norm_num
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => (bump x) ⁻¹' Ioi (1 / 2 : ℝ))
    (fun x => isOpen_Ioi.preimage (hbump x).2.2.1.continuous) hcover
  let C : Set E := ⋃ x : s, tsupport (bump (x : K))
  have hC : IsCompact C := by
    dsimp [C]
    exact isCompact_iUnion fun x => (hbump (x : K)).2.1
  have hCU : C ⊆ U := by
    intro y hy
    dsimp [C] at hy
    rcases mem_iUnion.1 hy with ⟨x, hxy⟩
    exact (hbump (x : K)).1 hxy
  let g : E → ℝ := fun y => 2 * (∑ x ∈ s, bump x y)
  have hg_support : support g ⊆ C := by
    intro y hy
    by_contra hnot
    apply hy
    have hsum : (∑ x ∈ s, bump x y) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      apply image_eq_zero_of_notMem_tsupport
      intro hxy
      apply hnot
      dsimp [C]
      exact mem_iUnion.2 ⟨⟨x, hx⟩, hxy⟩
    simp [g, hsum]
  have hg_smooth : ContDiff ℝ ∞ g := by
    dsimp [g]
    apply contDiff_const.mul
    apply ContDiff.sum
    intro x hx
    exact (hbump (x : K)).2.2.1
  have hg_gt_one {y : E} (hy : y ∈ K) : 1 < g y := by
    rcases mem_iUnion₂.1 (hs hy) with ⟨x, hx, hxy⟩
    -- Unpack preimage membership; the index `x : K` is coerced when applying `bump x` to `y`.
    change (1 / 2 : ℝ) < bump x y at hxy
    have hsum : bump x y ≤ ∑ z ∈ s, bump z y :=
      Finset.single_le_sum (fun z hz => hbump_nonneg z y) hx
    dsimp [g]
    nlinarith
  let ψ : E → ℝ := Real.smoothTransition ∘ g
  have hψ_smooth : ContDiff ℝ ∞ ψ := by
    dsimp [ψ]
    exact Real.smoothTransition.contDiff.comp hg_smooth
  have hψ_range : range ψ ⊆ Icc 0 1 := by
    rintro t ⟨y, rfl⟩
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hψ_eq_one : EqOn ψ 1 K := by
    intro y hy
    dsimp [ψ]
    rw [Real.smoothTransition.one_of_one_le (hg_gt_one hy).le]
  have hψ_eq_one_nhds : K ⊆ interior (ψ ⁻¹' {1}) := by
    intro y hy
    apply mem_interior_iff_mem_nhds.mpr
    have h_open : IsOpen {z : E | 1 < g z} :=
      isOpen_lt continuous_const hg_smooth.continuous
    refine Filter.mem_of_superset (h_open.mem_nhds (hg_gt_one hy)) ?_
    intro z hz
    have h_eq : Real.smoothTransition (g z) = 1 :=
      Real.smoothTransition.one_of_one_le hz.le
    simpa [ψ] using h_eq
  have hψ_support : support ψ ⊆ C := by
    intro y hy
    have hgy : g y ≠ 0 := by
      intro hgy
      apply hy
      dsimp [ψ]
      rw [hgy, Real.smoothTransition.zero]
    exact hg_support hgy
  have hψ_compact : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact hC hψ_support
  have hψ_tsupp : tsupport ψ ⊆ U := by
    rw [tsupport]
    exact (closure_minimal hψ_support hC.isClosed).trans hCU
  exact ⟨ψ, hψ_smooth, hψ_range, hψ_eq_one, hψ_eq_one_nhds, hψ_compact, hψ_tsupp⟩

namespace CompactExhaustion

/-- A compact-exhaustion term in an open set admits a smooth cutoff supported in the interior of
the next term. -/
theorem exists_contDiff_cutoff {Omega : Opens E} (K : CompactExhaustion Omega) (n : ℕ) :
    ∃ ψ : E → ℝ,
      ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
        EqOn ψ 1 ((Subtype.val : Omega → E) '' K n) ∧
        (Subtype.val : Omega → E) '' K n ⊆ interior (ψ ⁻¹' {1}) ∧
        HasCompactSupport ψ ∧
          tsupport ψ ⊆ (Subtype.val : Omega → E) '' interior (K (n + 1)) := by
  have hK : IsCompact ((Subtype.val : Omega → E) '' K n) :=
    (K.isCompact n).image continuous_subtype_val
  have hU : IsOpen ((Subtype.val : Omega → E) '' interior (K (n + 1))) :=
    Omega.isOpen.isOpenMap_subtype_val _ isOpen_interior
  have hKU :
      (Subtype.val : Omega → E) '' K n ⊆ (Subtype.val : Omega → E) '' interior (K (n + 1)) :=
    image_mono (K.subset_interior_succ n)
  exact TauCeti.exists_contDiff_cutoff hK hU hKU

end CompactExhaustion

end TauCeti
