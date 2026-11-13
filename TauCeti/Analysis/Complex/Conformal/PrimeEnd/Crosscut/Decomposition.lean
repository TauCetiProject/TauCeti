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

* `Path.IsCrosscut.filledHull_range_union_range_inter_frontier`: for a bounded open Jordan
  domain, intersection with the old frontier for any frontier path between the crosscut endpoints.
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

/-- For an open set `U`, an injective path in `frontier U` with the same endpoints as a
crosscut closes it to a Jordan curve. -/
theorem IsCrosscut.isJordanCurve_range_union_range (hτ : IsCrosscut τ U) (hUo : IsOpen U)
    {α : Path x y} (hα : Injective α) (hαf : range α ⊆ frontier U) :
    IsJordanCurve (range τ ∪ range α) :=
  isJordanCurve_range_union_range_of_inter_eq_pair hτ.injective hα
    (hτ.range_inter_range_eq_pair hUo hαf)

/-- In a bounded open Jordan domain, the filled hull of a crosscut and a frontier path
between its endpoints lies in the domain's closure. -/
theorem IsCrosscut.filledHull_range_union_range_subset_closure (hτ : IsCrosscut τ U)
    (hUo : IsOpen U)
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

/-- In a bounded open Jordan domain, the filled hull of a crosscut and a frontier path
between its endpoints, with both path ranges removed, lies in the domain minus the crosscut. -/
theorem IsCrosscut.filledHull_sdiff_subset (hτ : IsCrosscut τ U) (hUo : IsOpen U)
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
      (sdiff_subset.trans (hτ.filledHull_range_union_range_subset_closure hUo hUb hUJ hαf))
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

/-- In a bounded open Jordan domain `U`, the filled hull of a crosscut and any path in
`frontier U` between its endpoints meets `frontier U` exactly in the range of that path.
No injectivity of the boundary path is needed. -/
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
      (hτ.filledHull_sdiff_subset hUo hUb hUJ hαf ⟨hp, hpJ⟩).1).elim

/-- In a bounded open Jordan domain, a crosscut and an injective frontier path between its
endpoints enclose a component of the domain minus the crosscut. -/
theorem IsCrosscut.connectedComponentIn_eq_filledHull_sdiff (hτ : IsCrosscut τ U)
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUJ : IsJordanCurve (frontier U))
    {α : Path x y} (hα : Injective α) (hαf : range α ⊆ frontier U)
    {z : ℂ} (hz : z ∈ filledHull (range τ ∪ range α) \ (range τ ∪ range α)) :
    connectedComponentIn (U \ range τ) z =
      filledHull (range τ ∪ range α) \ (range τ ∪ range α) := by
  have hJ := hτ.isJordanCurve_range_union_range hUo hα hαf
  refine Subset.antisymm ?_
    (hJ.isConnected_filledHull_sdiff.isPreconnected.subset_connectedComponentIn hz
      (hτ.filledHull_sdiff_subset hUo hUb hUJ hαf))
  rw [hJ.filledHull_sdiff_eq_connectedComponentIn hz]
  exact connectedComponentIn_mono _ (sdiff_range_subset_compl hUo hαf)

/-- In a bounded open Jordan domain, two injective frontier paths between a crosscut's
endpoints, meeting exactly there, enclose disjoint open cells covering the domain minus the
crosscut. -/
theorem IsCrosscut.disjoint_and_union_filledHull_sdiff (hτ : IsCrosscut τ U)
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUJ : IsJordanCurve (frontier U))
    {α β : Path x y} (hα : Injective α) (hβ : Injective β)
    (hαf : range α ⊆ frontier U) (hβf : range β ⊆ frontier U)
    (hαβ : range α ∩ range β = {x, y}) :
    Disjoint (filledHull (range τ ∪ range α) \ (range τ ∪ range α))
        (filledHull (range τ ∪ range β) \ (range τ ∪ range β)) ∧
      (filledHull (range τ ∪ range α) \ (range τ ∪ range α)) ∪
        (filledHull (range τ ∪ range β) \ (range τ ∪ range β)) = U \ range τ := by
  have hJα := hτ.isJordanCurve_range_union_range hUo hα hαf
  have hJβ := hτ.isJordanCurve_range_union_range hUo hβ hβf
  set W₁ := filledHull (range τ ∪ range α) \ (range τ ∪ range α)
  set W₂ := filledHull (range τ ∪ range β) \ (range τ ∪ range β)
  have hW₁ := hτ.filledHull_sdiff_subset hUo hUb hUJ hαf
  have hW₂ := hτ.filledHull_sdiff_subset hUo hUb hUJ hβf
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
  have hc₁ := hτ.connectedComponentIn_eq_filledHull_sdiff hUo hUb hUJ hα hαf hz
  have hc₂ := hτ.connectedComponentIn_eq_filledHull_sdiff hUo hUb hUJ hβ hβf hw
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
    (hαf : range α ⊆ frontier U) (hβf : range β ⊆ frontier U)
    (hαβi : range α ∩ range β = {x, y}) :
    filledHull (range τ ∪ range α) ∪ filledHull (range τ ∪ range β) = closure U ∧
      filledHull (range τ ∪ range α) ∩ filledHull (range τ ∪ range β) = range τ := by
  obtain ⟨hdisj, hunion⟩ :=
    hτ.disjoint_and_union_filledHull_sdiff hUo hUb hUJ hα hβ hαf hβf hαβi
  have hfront {p : ℂ} (hp : p ∈ closure U) (hpU : p ∉ U) : p ∈ frontier U := by
    rw [hUo.frontier_eq]
    exact ⟨hp, hpU⟩
  constructor
  · refine Subset.antisymm (union_subset
      (hτ.filledHull_range_union_range_subset_closure hUo hUb hUJ hαf)
      (hτ.filledHull_range_union_range_subset_closure hUo hUb hUJ hβf)) ?_
    refine closure_minimal (fun p hpU ↦ ?_)
      ((hτ.isJordanCurve_range_union_range hUo hα hαf).isClosed.isClosed_filledHull.union
        (hτ.isJordanCurve_range_union_range hUo hβ hβf).isClosed.isClosed_filledHull)
    by_cases hpτ : p ∈ range τ
    · exact Or.inl (subset_filledHull (Or.inl hpτ))
    have h : p ∈ U \ range τ := ⟨hpU, hpτ⟩
    rw [← hunion] at h
    exact h.elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)
  · refine Subset.antisymm (fun p ⟨hpα, hpβ⟩ ↦ ?_) fun p hp ↦
      ⟨subset_filledHull (Or.inl hp), subset_filledHull (Or.inl hp)⟩
    by_contra hpτ
    by_cases hpU : p ∈ U
    · exact hdisj.ne_of_mem (mem_filledHull_sdiff_of_mem hUo hαf hpα ⟨hpU, hpτ⟩)
        (mem_filledHull_sdiff_of_mem hUo hβf hpβ ⟨hpU, hpτ⟩) rfl
    · have hpf := hfront (hτ.filledHull_range_union_range_subset_closure hUo hUb hUJ hαf hpα) hpU
      have hp2 : p ∈ ({x, y} : Set ℂ) := by
        rw [← hαβi, ← hτ.filledHull_range_union_range_inter_frontier hUo hUb hUJ hαf,
          ← hτ.filledHull_range_union_range_inter_frontier hUo hUb hUJ hβf]
        exact ⟨⟨hpα, hpf⟩, hpβ, hpf⟩
      rcases hp2 with rfl | rfl
      exacts [hpτ τ.source_mem_range, hpτ τ.target_mem_range]

/-- In a bounded open Jordan domain, two injective frontier paths between a crosscut's
endpoints, meeting exactly there, close it to two filled hulls covering the domain's closure. -/
theorem IsCrosscut.filledHull_union_filledHull_eq_closure (hτ : IsCrosscut τ U)
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUJ : IsJordanCurve (frontier U))
    {α β : Path x y} (hα : Injective α) (hβ : Injective β)
    (hαf : range α ⊆ frontier U) (hβf : range β ⊆ frontier U)
    (hαβi : range α ∩ range β = {x, y}) :
    filledHull (range τ ∪ range α) ∪ filledHull (range τ ∪ range β) = closure U :=
  (decomposition_of_arcs hτ hUo hUb hUJ hα hβ hαf hβf hαβi).1

/-- In a bounded open Jordan domain, two injective frontier paths between a crosscut's
endpoints, meeting exactly there, determine filled hulls meeting exactly along the crosscut. -/
theorem IsCrosscut.filledHull_inter_filledHull_eq_range (hτ : IsCrosscut τ U)
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U) (hUJ : IsJordanCurve (frontier U))
    {α β : Path x y} (hα : Injective α) (hβ : Injective β)
    (hαf : range α ⊆ frontier U) (hβf : range β ⊆ frontier U)
    (hαβi : range α ∩ range β = {x, y}) :
    filledHull (range τ ∪ range α) ∩ filledHull (range τ ∪ range β) = range τ :=
  (decomposition_of_arcs hτ hUo hUb hUJ hα hβ hαf hβf hαβi).2

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
    hτ.filledHull_union_filledHull_eq_closure hUo hUb hUJ hα hβ
      (hu ▸ subset_union_left) (hu ▸ subset_union_right) hi,
    hτ.filledHull_inter_filledHull_eq_range hUo hUb hUJ hα hβ
      (hu ▸ subset_union_left) (hu ▸ subset_union_right) hi⟩

/-- The filled hull of a disc crosscut and a path in `sphere c r` with the same endpoints
meets `sphere c r` exactly in the range of that path. The crosscut forces the radius positive. -/
theorem IsCrosscut.filledHull_range_union_range_inter_sphere {c : ℂ} {r : ℝ}
    (hτ : IsCrosscut τ (ball c r)) {α : Path x y} (hαs : range α ⊆ sphere c r) :
    filledHull (range τ ∪ range α) ∩ sphere c r = range α := by
  have hr := hτ.radius_pos
  have hfr := frontier_ball c hr.ne'
  simpa only [hfr] using hτ.filledHull_range_union_range_inter_frontier isOpen_ball
    isBounded_ball (hfr.symm ▸ isJordanCurve_sphere c hr) (hfr.symm ▸ hαs)

/-- An injective path in `sphere c r` with the same endpoints as a crosscut of `ball c r`
closes it to a Jordan curve. The crosscut forces the radius positive. -/
theorem IsCrosscut.isJordanCurve_range_union_range_of_subset_sphere {c : ℂ} {r : ℝ}
    (hτ : IsCrosscut τ (ball c r)) {α : Path x y} (hα : Injective α)
    (hαs : range α ⊆ sphere c r) : IsJordanCurve (range τ ∪ range α) := by
  have hfr := frontier_ball c hτ.radius_pos.ne'
  exact hτ.isJordanCurve_range_union_range isOpen_ball hα (hfr.symm ▸ hαs)

/-- Two injective paths in `sphere c r` between a disc crosscut's endpoints, meeting
exactly there, close it to filled hulls covering `closedBall c r`.
No radius assumption is needed. -/
theorem IsCrosscut.filledHull_union_filledHull_eq_closedBall {c : ℂ} {r : ℝ}
    (hτ : IsCrosscut τ (ball c r)) {α β : Path x y} (hα : Injective α) (hβ : Injective β)
    (hαs : range α ⊆ sphere c r) (hβs : range β ⊆ sphere c r)
    (hαβi : range α ∩ range β = {x, y}) :
    filledHull (range τ ∪ range α) ∪ filledHull (range τ ∪ range β) = closedBall c r := by
  have hr := hτ.radius_pos
  have hfr := frontier_ball c hr.ne'
  simpa only [closure_ball c hr.ne'] using
    hτ.filledHull_union_filledHull_eq_closure isOpen_ball isBounded_ball
      (hfr.symm ▸ isJordanCurve_sphere c hr) hα hβ (hfr.symm ▸ hαs) (hfr.symm ▸ hβs) hαβi

/-- Two injective paths in `sphere c r` between a disc crosscut's endpoints, meeting
exactly there, determine filled hulls meeting along the crosscut. No radius assumption is needed. -/
theorem IsCrosscut.filledHull_inter_filledHull_eq_range_of_subset_sphere {c : ℂ} {r : ℝ}
    (hτ : IsCrosscut τ (ball c r)) {α β : Path x y} (hα : Injective α) (hβ : Injective β)
    (hαs : range α ⊆ sphere c r) (hβs : range β ⊆ sphere c r)
    (hαβi : range α ∩ range β = {x, y}) :
    filledHull (range τ ∪ range α) ∩ filledHull (range τ ∪ range β) = range τ := by
  have hr := hτ.radius_pos
  have hfr := frontier_ball c hr.ne'
  exact hτ.filledHull_inter_filledHull_eq_range isOpen_ball isBounded_ball
    (hfr.symm ▸ isJordanCurve_sphere c hr) hα hβ (hfr.symm ▸ hαs) (hfr.symm ▸ hβs) hαβi

/-- A crosscut splits a closed disc into the filled hulls of two Jordan curves, meeting
exactly along the crosscut. The statement applies to every centre and radius. -/
theorem IsCrosscut.exists_filledHull_union_filledHull_eq_closedBall {c : ℂ} {r : ℝ}
    (hτ : IsCrosscut τ (ball c r)) :
    ∃ α β : Path x y, Injective α ∧ Injective β ∧ range α ∪ range β = sphere c r ∧
      range α ∩ range β = {x, y} ∧ IsJordanCurve (range τ ∪ range α) ∧
      IsJordanCurve (range τ ∪ range β) ∧
      filledHull (range τ ∪ range α) ∪ filledHull (range τ ∪ range β) = closedBall c r ∧
      filledHull (range τ ∪ range α) ∩ filledHull (range τ ∪ range β) = range τ := by
  have hr := hτ.radius_pos
  have hfr := frontier_ball c hr.ne'
  simpa only [hfr, closure_ball c hr.ne'] using
    hτ.exists_filledHull_union_filledHull_eq_closure isOpen_ball isBounded_ball
      (hfr.symm ▸ isJordanCurve_sphere c hr)

end Path
