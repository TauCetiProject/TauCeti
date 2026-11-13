/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Crosscut.TwoSides
public import TauCeti.Analysis.Complex.PlaneSeparation.Inside
public import TauCeti.Topology.JordanCurve.Path
import TauCeti.Analysis.Normed.Module.FilledHull
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Cutting a closed Jordan domain along a crosscut

Let `τ` be a crosscut of a bounded open set `U ⊆ ℂ` whose frontier is a Jordan curve.
The endpoints split the frontier into two arcs `α` and `β`. The sets
`range τ ∪ range α` and `range τ ∪ range β` are Jordan curves; their filled hulls cover
`closure U` and meet exactly along `range τ`. Each hull meets `frontier U` in its original
boundary arc. This gives the single-cut step for subdividing discs into closed cells with
identified common edges and boundary arcs. Schoenflies identifies each cell with a closed disc.

## The argument

Each inside is a connected component of `U \ range τ`, by the Jordan complementary-component
theorem. Their closures meet the original frontier in different arcs, so they are distinct.
The crosscut two-side theorem then shows that they exhaust `U \ range τ`.

## Main results

* `Path.IsCrosscut.filledHull_range_union_range_inter_frontier`: intersection with the old
  frontier, for any boundary path.
* `Path.IsCrosscut.filledHull_union_filledHull_eq_closure` and
  `Path.IsCrosscut.filledHull_inter_filledHull_eq_range`: decomposition for given complementary
  injective boundary paths.
* `Path.IsCrosscut.exists_filledHull_union_filledHull_eq_closure`: existence of such paths.
* `Path.IsCrosscut.exists_filledHull_union_filledHull_eq_closedBall`: the disc specialization.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Chapter 2.
* M. H. A. Newman, *Elements of the Topology of Plane Sets of Points*, Chapter V.
-/

public section

open Function Metric Set TauCeti

namespace Path

variable {x y : ℂ} {τ : Path x y} {U : Set ℂ}

/-- An injective frontier path closes a crosscut to a Jordan curve. -/
theorem IsCrosscut.isJordanCurve_range_union_range (hτ : IsCrosscut τ U) (hUo : IsOpen U)
    {α : Path x y} (hα : Injective α) (hαf : range α ⊆ frontier U) :
    IsJordanCurve (range τ ∪ range α) :=
  isJordanCurve_range_union_range_of_inter_eq_pair hτ.injective hα
    (hτ.range_inter_range_eq_pair hUo hαf)

private theorem filledHull_subset_closure (hτ : IsCrosscut τ U) (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUJ : IsJordanCurve (frontier U)) {α : Path x y}
    (hαf : range α ⊆ frontier U) : filledHull (range τ ∪ range α) ⊆ closure U := by
  have hcl : closure U = filledHull (frontier U) := by
    exact (congrArg closure (hUJ.eq_filledHull_sdiff_of_isOpen_of_isBounded hUo hUb)).trans
      hUJ.closure_filledHull_sdiff
  have hconn : IsPreconnected (closure U)ᶜ := by
    rw [hcl]
    have hrank : 1 < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      exact Cardinal.one_lt_two
    exact (isConnected_compl_filledHull hrank hUJ.isCompact.isBounded).isPreconnected
  have hunb : ¬ Bornology.IsBounded (closure U)ᶜ := by
    intro hb
    exact NormedSpace.unbounded_univ ℂ ℂ (by
      simpa using hUb.closure.union hb)
  have hsub : range τ ∪ range α ⊆ closure U :=
    union_subset hτ.range_subset_closure (hαf.trans frontier_subset_closure)
  exact (filledHull_mono hsub).trans_eq (filledHull_eq_self hconn hunb)

private theorem filledHull_sdiff_subset (hτ : IsCrosscut τ U) (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUJ : IsJordanCurve (frontier U)) {α : Path x y}
    (hαf : range α ⊆ frontier U) :
    filledHull (range τ ∪ range α) \ (range τ ∪ range α) ⊆ U \ range τ := by
  have hW : filledHull (range τ ∪ range α) \ (range τ ∪ range α) ⊆ U := by
    have hclosed := (isCompact_range τ.continuous).isClosed.union
      (isCompact_range α.continuous).isClosed
    have hreg : interior (closure U) = U := by
      rw [hUJ.eq_filledHull_sdiff_of_isOpen_of_isBounded hUo hUb,
        hUJ.closure_filledHull_sdiff, hUJ.interior_filledHull]
    rw [← hreg]
    exact hclosed.isOpen_filledHull_sdiff.subset_interior_iff.mpr
      (sdiff_subset.trans (filledHull_subset_closure hτ hUo hUb hUJ hαf))
  exact fun p hp ↦ ⟨hW hp, fun h ↦ hp.2 (Or.inl h)⟩

private theorem sdiff_range_subset_compl (hUo : IsOpen U) {α : Path x y}
    (hαf : range α ⊆ frontier U) : U \ range τ ⊆ (range τ ∪ range α)ᶜ :=
  fun _ hp h ↦ h.elim hp.2 fun ha ↦
    (disjoint_frontier_iff_isOpen.mpr hUo).notMem_of_mem_left (hαf ha) hp.1

private theorem mem_filledHull_sdiff_of_mem (hUo : IsOpen U) {α : Path x y}
    (hαf : range α ⊆ frontier U) {p : ℂ} (hp : p ∈ filledHull (range τ ∪ range α))
    (hpU : p ∈ U \ range τ) :
    p ∈ filledHull (range τ ∪ range α) \ (range τ ∪ range α) :=
  ⟨hp, sdiff_range_subset_compl hUo hαf hpU⟩

/-- The filled hull of a crosscut together with any path in the frontier meets the frontier
exactly in the range of that boundary path. No injectivity of the boundary path is needed. -/
theorem IsCrosscut.filledHull_range_union_range_inter_frontier (hτ : IsCrosscut τ U)
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUJ : IsJordanCurve (frontier U))
    {α : Path x y} (hαf : range α ⊆ frontier U) :
    filledHull (range τ ∪ range α) ∩ frontier U = range α := by
  refine Subset.antisymm (fun p ⟨hp, hpf⟩ ↦ ?_) fun p hp ↦
    ⟨subset_filledHull (Or.inr hp), hαf hp⟩
  by_cases hpJ : p ∈ range τ ∪ range α
  · rcases hpJ with h | h
    · rcases (hτ.range_inter_frontier hUo ▸ ⟨h, hpf⟩ : p ∈ ({x, y} : Set ℂ)) with rfl | rfl
      exacts [α.source_mem_range, α.target_mem_range]
    · exact h
  · exact ((disjoint_frontier_iff_isOpen.mpr hUo).notMem_of_mem_left hpf
      (filledHull_sdiff_subset hτ hUo hUb hUJ hαf ⟨hp, hpJ⟩).1).elim

private theorem connectedComponentIn_eq_filledHull_sdiff (hτ : IsCrosscut τ U)
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUJ : IsJordanCurve (frontier U))
    {α : Path x y} (hαf : range α ⊆ frontier U) (hJ : IsJordanCurve (range τ ∪ range α))
    {z : ℂ} (hz : z ∈ filledHull (range τ ∪ range α) \ (range τ ∪ range α)) :
    connectedComponentIn (U \ range τ) z =
      filledHull (range τ ∪ range α) \ (range τ ∪ range α) := by
  refine Subset.antisymm ?_
    (hJ.isConnected_filledHull_sdiff.isPreconnected.subset_connectedComponentIn hz
      (filledHull_sdiff_subset hτ hUo hUb hUJ hαf))
  rw [hJ.filledHull_sdiff_eq_connectedComponentIn hz]
  exact connectedComponentIn_mono _ (sdiff_range_subset_compl hUo hαf)

private theorem disjoint_and_union_filledHull_sdiff (hτ : IsCrosscut τ U)
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUJ : IsJordanCurve (frontier U))
    {α β : Path x y} (hα : Injective α) (hαf : range α ⊆ frontier U)
    (hβf : range β ⊆ frontier U) (hαβ : range α ∩ range β = {x, y})
    (hJα : IsJordanCurve (range τ ∪ range α)) (hJβ : IsJordanCurve (range τ ∪ range β)) :
    Disjoint (filledHull (range τ ∪ range α) \ (range τ ∪ range α))
        (filledHull (range τ ∪ range β) \ (range τ ∪ range β)) ∧
      (filledHull (range τ ∪ range α) \ (range τ ∪ range α)) ∪
        (filledHull (range τ ∪ range β) \ (range τ ∪ range β)) = U \ range τ := by
  set W₁ := filledHull (range τ ∪ range α) \ (range τ ∪ range α)
  set W₂ := filledHull (range τ ∪ range β) \ (range τ ∪ range β)
  have hW₁ := filledHull_sdiff_subset hτ hUo hUb hUJ hαf
  have hW₂ := filledHull_sdiff_subset hτ hUo hUb hUJ hβf
  -- Equal insides would have equal closures and hence equal old boundary arcs.
  have hne : W₁ ≠ W₂ := by
    intro heq
    have hcl : filledHull (range τ ∪ range α) = filledHull (range τ ∪ range β) := by
      rw [← hJα.closure_filledHull_sdiff, ← hJβ.closure_filledHull_sdiff]
      exact congrArg closure heq
    have hab : range α = range β := by
      rw [← hτ.filledHull_range_union_range_inter_frontier hUo hUb hUJ hαf,
        ← hτ.filledHull_range_union_range_inter_frontier hUo hUb hUJ hβf, hcl]
    have hhalf : α ⟨1 / 2, by norm_num, by norm_num⟩ ∈ ({x, y} : Set ℂ) := by
      rw [← hαβ, ← hab, inter_self]
      exact mem_range_self _
    rcases hhalf with h | h
    · have := congrArg Subtype.val (hα (h.trans α.source.symm))
      norm_num at this
    · have := congrArg Subtype.val (hα (h.trans α.target.symm))
      norm_num at this
  obtain ⟨z, hz⟩ := hJα.nonempty_filledHull_sdiff
  obtain ⟨w, hw⟩ := hJβ.nonempty_filledHull_sdiff
  have hc₁ := connectedComponentIn_eq_filledHull_sdiff hτ hUo hUb hUJ hαf hJα hz
  have hc₂ := connectedComponentIn_eq_filledHull_sdiff hτ hUo hUb hUJ hβf hJβ hw
  -- Distinct components are disjoint; the crosscut has at most two sides.
  have hdisj : Disjoint W₁ W₂ := by
    refine Set.disjoint_left.mpr fun v hv₁ hv₂ ↦ hne ?_
    have h₁ := connectedComponentIn_eq (hc₁.symm.subset hv₁)
    have h₂ := connectedComponentIn_eq (hc₂.symm.subset hv₂)
    exact hc₁.symm.trans (h₁.trans (h₂.symm.trans hc₂))
  have hsep : τ.SeparatesIn U z w := by
    refine (separatesIn_def τ _ z w).2 ⟨hW₁ hz, hW₂ hw, ?_⟩
    rwa [hc₁, hc₂]
  refine ⟨hdisj, Subset.antisymm (union_subset hW₁ hW₂) fun v hv ↦ ?_⟩
  have hv' := mem_connectedComponentIn hv
  rcases hτ.connectedComponentIn_eq_or_eq_of_separatesIn hUo
    (hUJ.isConnected_of_isOpen_of_isBounded hUo hUb).isPreconnected hsep hv with h | h
  · rw [h, hc₁] at hv'
    exact Or.inl hv'
  · rw [h, hc₂] at hv'
    exact Or.inr hv'

private theorem decomposition_of_arcs (hτ : IsCrosscut τ U)
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUJ : IsJordanCurve (frontier U))
    {α β : Path x y} (hα : Injective α) (hβ : Injective β)
    (hαβu : range α ∪ range β = frontier U) (hαβi : range α ∩ range β = {x, y}) :
    filledHull (range τ ∪ range α) ∪ filledHull (range τ ∪ range β) = closure U ∧
      filledHull (range τ ∪ range α) ∩ filledHull (range τ ∪ range β) = range τ := by
  have hαf : range α ⊆ frontier U := hαβu ▸ subset_union_left
  have hβf : range β ⊆ frontier U := hαβu ▸ subset_union_right
  obtain ⟨hdisj, hunion⟩ := disjoint_and_union_filledHull_sdiff hτ hUo hUb hUJ hα hαf hβf hαβi
    (hτ.isJordanCurve_range_union_range hUo hα hαf)
    (hτ.isJordanCurve_range_union_range hUo hβ hβf)
  have hfront {p : ℂ} (hp : p ∈ closure U) (hpU : p ∉ U) : p ∈ frontier U := by
    rw [hUo.frontier_eq]
    exact ⟨hp, hpU⟩
  constructor
  · refine Subset.antisymm (union_subset
      (filledHull_subset_closure hτ hUo hUb hUJ hαf)
      (filledHull_subset_closure hτ hUo hUb hUJ hβf)) fun p hp ↦ ?_
    by_cases hpτ : p ∈ range τ
    · exact Or.inl (subset_filledHull (Or.inl hpτ))
    by_cases hpU : p ∈ U
    · have h : p ∈ U \ range τ := ⟨hpU, hpτ⟩
      rw [← hunion] at h
      exact h.elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)
    · rcases (hαβu ▸ hfront hp hpU : p ∈ range α ∪ range β) with h | h
      exacts [Or.inl (subset_filledHull (Or.inr h)), Or.inr (subset_filledHull (Or.inr h))]
  · refine Subset.antisymm (fun p ⟨hpα, hpβ⟩ ↦ ?_) fun p hp ↦
      ⟨subset_filledHull (Or.inl hp), subset_filledHull (Or.inl hp)⟩
    by_contra hpτ
    by_cases hpU : p ∈ U
    · exact hdisj.ne_of_mem (mem_filledHull_sdiff_of_mem hUo hαf hpα ⟨hpU, hpτ⟩)
        (mem_filledHull_sdiff_of_mem hUo hβf hpβ ⟨hpU, hpτ⟩) rfl
    · have hpf := hfront (filledHull_subset_closure hτ hUo hUb hUJ hαf hpα) hpU
      have hp2 : p ∈ ({x, y} : Set ℂ) := by
        rw [← hαβi, ← hτ.filledHull_range_union_range_inter_frontier hUo hUb hUJ hαf,
          ← hτ.filledHull_range_union_range_inter_frontier hUo hUb hUJ hβf]
        exact ⟨⟨hpα, hpf⟩, hpβ, hpf⟩
      rcases hp2 with rfl | rfl
      exacts [hpτ τ.source_mem_range, hpτ τ.target_mem_range]

/-- Complementary injective frontier paths close a crosscut to two filled hulls covering
the closed Jordan domain. -/
theorem IsCrosscut.filledHull_union_filledHull_eq_closure (hτ : IsCrosscut τ U)
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUJ : IsJordanCurve (frontier U))
    {α β : Path x y} (hα : Injective α) (hβ : Injective β)
    (hαβu : range α ∪ range β = frontier U) (hαβi : range α ∩ range β = {x, y}) :
    filledHull (range τ ∪ range α) ∪ filledHull (range τ ∪ range β) = closure U :=
  (decomposition_of_arcs hτ hUo hUb hUJ hα hβ hαβu hαβi).1

/-- The two filled hulls determined by a crosscut and complementary injective frontier paths
meet exactly along the crosscut. -/
theorem IsCrosscut.filledHull_inter_filledHull_eq_range (hτ : IsCrosscut τ U)
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUJ : IsJordanCurve (frontier U))
    {α β : Path x y} (hα : Injective α) (hβ : Injective β)
    (hαβu : range α ∪ range β = frontier U) (hαβi : range α ∩ range β = {x, y}) :
    filledHull (range τ ∪ range α) ∩ filledHull (range τ ∪ range β) = range τ :=
  (decomposition_of_arcs hτ hUo hUb hUJ hα hβ hαβu hαβi).2

/-- A crosscut splits a closed Jordan domain into the filled hulls of two Jordan curves.
The boundary paths cover the old frontier and meet exactly at the crosscut endpoints. -/
theorem IsCrosscut.exists_filledHull_union_filledHull_eq_closure (hτ : IsCrosscut τ U)
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUJ : IsJordanCurve (frontier U)) :
    ∃ α β : Path x y, Injective α ∧ Injective β ∧ range α ∪ range β = frontier U ∧
      range α ∩ range β = {x, y} ∧ IsJordanCurve (range τ ∪ range α) ∧
      IsJordanCurve (range τ ∪ range β) ∧
      filledHull (range τ ∪ range α) ∪ filledHull (range τ ∪ range β) = closure U ∧
      filledHull (range τ ∪ range α) ∩ filledHull (range τ ∪ range β) = range τ := by
  obtain ⟨α, β, hα, hβ, hu, hi⟩ :=
    hUJ.exists_injective_path_range_union_eq_and_inter_eq_pair
      hτ.source_mem_frontier hτ.target_mem_frontier hτ.source_ne_target
  exact ⟨α, β, hα, hβ, hu, hi,
    hτ.isJordanCurve_range_union_range hUo hα (hu ▸ subset_union_left),
    hτ.isJordanCurve_range_union_range hUo hβ (hu ▸ subset_union_right),
    hτ.filledHull_union_filledHull_eq_closure hUo hUb hUJ hα hβ hu hi,
    hτ.filledHull_inter_filledHull_eq_range hUo hUb hUJ hα hβ hu hi⟩

private theorem radius_pos_of_isCrosscut {c : ℂ} {r : ℝ}
    (hτ : IsCrosscut τ (ball c r)) : 0 < r :=
  not_le.mp fun hr ↦ hτ.source_ne_target (subsingleton_sphere c hr
    (frontier_ball_subset_sphere hτ.source_mem_frontier)
    (frontier_ball_subset_sphere hτ.target_mem_frontier))

/-- The filled hull of a disc crosscut and a path in its boundary meets the circle exactly
in that boundary path. The crosscut hypothesis already forces the radius to be positive. -/
theorem IsCrosscut.filledHull_range_union_range_inter_sphere {c : ℂ} {r : ℝ}
    (hτ : IsCrosscut τ (ball c r)) {α : Path x y} (hαs : range α ⊆ sphere c r) :
    filledHull (range τ ∪ range α) ∩ sphere c r = range α := by
  have hr := radius_pos_of_isCrosscut hτ
  have hfr := frontier_ball c hr.ne'
  simpa only [hfr] using hτ.filledHull_range_union_range_inter_frontier isOpen_ball
    isBounded_ball (hfr.symm ▸ isJordanCurve_sphere c hr) (hfr.symm ▸ hαs)

/-- A crosscut splits a closed disc into the filled hulls of two Jordan curves, meeting
exactly along the crosscut. The statement applies to every centre and radius. -/
theorem IsCrosscut.exists_filledHull_union_filledHull_eq_closedBall {c : ℂ} {r : ℝ}
    (hτ : IsCrosscut τ (ball c r)) :
    ∃ α β : Path x y, Injective α ∧ Injective β ∧ range α ∪ range β = sphere c r ∧
      range α ∩ range β = {x, y} ∧ IsJordanCurve (range τ ∪ range α) ∧
      IsJordanCurve (range τ ∪ range β) ∧
      filledHull (range τ ∪ range α) ∪ filledHull (range τ ∪ range β) = closedBall c r ∧
      filledHull (range τ ∪ range α) ∩ filledHull (range τ ∪ range β) = range τ := by
  have hr := radius_pos_of_isCrosscut hτ
  have hfr := frontier_ball c hr.ne'
  simpa only [hfr, closure_ball c hr.ne'] using
    hτ.exists_filledHull_union_filledHull_eq_closure isOpen_ball isBounded_ball
      (hfr.symm ▸ isJordanCurve_sphere c hr)

end Path
