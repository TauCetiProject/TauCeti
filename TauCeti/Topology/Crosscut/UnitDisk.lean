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

/-!
# A crosscut cuts the closed unit disc into two closed discs

Let `τ` be a crosscut of the open unit disc `ball 0 1` of `ℂ`, from `x` to `y`: an injective path
whose endpoints lie on the unit circle and whose other points lie in the open disc. The two points
`x` and `y` cut the unit circle into two arcs `α` and `β`, and `range τ ∪ range α` and
`range τ ∪ range β` are Jordan curves. Their filled hulls are closed discs by the Schoenflies
theorem; this file shows that they cover the closed unit disc and meet exactly along the crosscut
(`Path.IsCrosscut.exists_filledHull_union_eq_closedBall`). The filled hull of
`range τ ∪ α` meets the unit circle exactly in the arc `α`
(`Path.IsCrosscut.filledHull_union_range_inter_sphere`).

## The argument

The inside `W` of `J = range τ ∪ range α` is open and contained in the closed disc, hence in the
open disc; it misses `range τ`. Its closure is `filledHull J`, which meets the open disc off the
crosscut only in `W`, so `W` is relatively clopen in `ball 0 1 \ range τ`. Being connected, it is a
connected component there. The insides of the two curves are distinct components, so the crosscut
separates them, and by `Path.IsCrosscut.connectedComponentIn_eq_or_eq_of_separatesIn` every point
of the open disc off the crosscut lies in one of them.

This is the topological single-cut step for the finite arc subdivisions in coordinate discs
required by GeometricTopology §1.7, Compact smooth surfaces, in
`TauCetiRoadmap/GeometricTopology/README.md`. The two filled hulls give the new closed cells;
the intersection and circle-intersection statements identify their common edge and their
remaining boundary arcs. Smooth compatibility and finite subdivision are subsequent steps.

## Main results

* `Path.IsCrosscut.filledHull_union_range_inter_sphere`: the filled hull of the crosscut together
  with an arc of the unit circle meets the circle in that arc.
* `Path.IsCrosscut.exists_filledHull_union_eq_closedBall`: a crosscut cuts the closed unit disc
  into the filled hulls of two Jordan curves, meeting along the crosscut.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Chapter 2.
* M. H. A. Newman, *Elements of the Topology of Plane Sets of Points*, Chapter V.
-/

public section

open Function Metric Set TauCeti

namespace Path

variable {x y : ℂ} {τ : Path x y}

private theorem exists_arcs_sphere (hx : x ∈ sphere (0 : ℂ) 1) (hy : y ∈ sphere (0 : ℂ) 1)
    (hxy : x ≠ y) :
    ∃ α β : Path x y, Injective α ∧ Injective β ∧ range α ∪ range β = sphere 0 1 ∧
      range α ∩ range β = {x, y} := by
  let u : Circle := ⟨x, hx⟩
  let v : Circle := ⟨y, hy⟩
  have huv : u ≠ v := fun h ↦ hxy (congrArg Subtype.val h)
  let c : Circle → ℂ := fun z ↦ z
  have hc : Continuous c := continuous_subtype_val
  have hci : Injective c := Circle.coe_injective
  let arc (p q : Circle) : Path (c p) (c q) := (Circle.path p q).map hc
  have harc (p q : Circle) : range (arc p q) = c '' range (Circle.path p q) :=
    range_comp c (Circle.path p q)
  refine ⟨arc u v, (arc v u).symm, hci.comp (Circle.path_injective_of_ne huv),
    (hci.comp (Circle.path_injective_of_ne huv.symm)).comp
      unitInterval.symm_involutive.injective, ?_, ?_⟩
  · rw [symm_range, harc, harc, ← image_union, Circle.range_path_union_range_path huv,
      image_univ]
    exact Subtype.range_coe
  · rw [symm_range, harc, harc, ← image_inter hci,
      Circle.range_path_inter_range_path huv, image_pair]

private theorem range_inter_sphere (hτ : IsCrosscut τ (ball 0 1)) :
    range τ ∩ sphere (0 : ℂ) 1 = {x, y} := by
  rw [← frontier_ball (0 : ℂ) one_ne_zero]
  exact hτ.range_inter_frontier isOpen_ball

private theorem range_subset_closedBall (hτ : IsCrosscut τ (ball 0 1)) :
    range τ ⊆ closedBall (0 : ℂ) 1 := by
  rw [← closure_ball (0 : ℂ) one_ne_zero]
  exact hτ.range_subset_closure

private theorem union_range_subset_closedBall (hτ : IsCrosscut τ (ball 0 1)) {α : Path x y}
    (hαs : range α ⊆ sphere 0 1) : range τ ∪ range α ⊆ closedBall 0 1 :=
  union_subset (range_subset_closedBall hτ) (hαs.trans sphere_subset_closedBall)

private theorem filledHull_subset_closedBall {α : Path x y}
    (hJ : range τ ∪ range α ⊆ closedBall 0 1) :
    filledHull (range τ ∪ range α) ⊆ closedBall 0 1 :=
  (filledHull_subset_closedConvexHull ⟨x, Or.inl τ.source_mem_range⟩).trans
    (closedConvexHull_min hJ (convex_closedBall 0 1) isClosed_closedBall)

private theorem range_inter_range_eq_pair (hτ : IsCrosscut τ (ball 0 1)) {α : Path x y}
    (hαs : range α ⊆ sphere 0 1) : range τ ∩ range α = {x, y} := by
  refine Subset.antisymm (fun z hz ↦ ?_) ?_
  · rw [← range_inter_sphere hτ]
    exact ⟨hz.1, hαs hz.2⟩
  · rintro z (rfl | rfl)
    · exact ⟨τ.source_mem_range, α.source_mem_range⟩
    · exact ⟨τ.target_mem_range, α.target_mem_range⟩

private theorem filledHull_sdiff_subset (hτ : IsCrosscut τ (ball 0 1)) {α : Path x y}
    (hαs : range α ⊆ sphere 0 1) (hJ : IsJordanCurve (range τ ∪ range α)) :
    filledHull (range τ ∪ range α) \ (range τ ∪ range α) ⊆ ball 0 1 \ range τ := by
  have hJb : range τ ∪ range α ⊆ closedBall 0 1 :=
    union_range_subset_closedBall hτ hαs
  have hW : filledHull (range τ ∪ range α) \ (range τ ∪ range α) ⊆ ball 0 1 := by
    rw [← interior_closedBall (0 : ℂ) one_ne_zero]
    exact hJ.isClosed.isOpen_filledHull_sdiff.subset_interior_iff.mpr
      (sdiff_subset.trans (filledHull_subset_closedBall hJb))
  exact fun p hp ↦ ⟨hW hp, fun h ↦ hp.2 (Or.inl h)⟩

private theorem mem_filledHull_sdiff_of_mem {α : Path x y} (hαs : range α ⊆ sphere 0 1) {p : ℂ}
    (hp : p ∈ filledHull (range τ ∪ range α)) (hpb : p ∈ ball 0 1 \ range τ) :
    p ∈ filledHull (range τ ∪ range α) \ (range τ ∪ range α) := by
  refine ⟨hp, fun h ↦ h.elim hpb.2 fun h ↦ ?_⟩
  have h1 := mem_sphere_zero_iff_norm.mp (hαs h)
  have h2 := mem_ball_zero_iff.mp hpb.1
  linarith

private theorem subset_filledHull_sdiff {α : Path x y}
    (hαs : range α ⊆ sphere 0 1) (hJ : IsJordanCurve (range τ ∪ range α)) {S : Set ℂ}
    (hS : IsPreconnected S) (hSτ : S ⊆ ball 0 1 \ range τ)
    (hSW : (S ∩ (filledHull (range τ ∪ range α) \ (range τ ∪ range α))).Nonempty) :
    S ⊆ filledHull (range τ ∪ range α) \ (range τ ∪ range α) := by
  refine hS.subset_left_of_subset_union hJ.isClosed.isOpen_filledHull_sdiff
    isClosed_closure.isOpen_compl (disjoint_compl_right_iff_subset.mpr subset_closure)
    (fun s hs ↦ ?_) hSW
  by_cases hsc : s ∈ closure (filledHull (range τ ∪ range α) \ (range τ ∪ range α))
  · rw [hJ.closure_filledHull_sdiff] at hsc
    exact Or.inl (mem_filledHull_sdiff_of_mem hαs hsc (hSτ hs))
  · exact Or.inr hsc

/-- The part of the unit circle filled in by the Jordan curve made of a crosscut `τ` of the open
unit disc and an arc `α` of the unit circle with the same endpoints is that arc. -/
theorem IsCrosscut.filledHull_union_range_inter_sphere (hτ : IsCrosscut τ (ball 0 1))
    {α : Path x y} (hαs : range α ⊆ sphere 0 1) (hJ : IsJordanCurve (range τ ∪ range α)) :
    filledHull (range τ ∪ range α) ∩ sphere 0 1 = range α := by
  refine Subset.antisymm (fun p ⟨hp, hps⟩ ↦ ?_) fun p hp ↦
    ⟨subset_filledHull (Or.inr hp), hαs hp⟩
  by_cases hpJ : p ∈ range τ ∪ range α
  · rcases hpJ with h | h
    · rcases (range_inter_sphere hτ ▸ ⟨h, hps⟩ : p ∈ ({x, y} : Set ℂ)) with rfl | rfl
      exacts [α.source_mem_range, α.target_mem_range]
    · exact h
  · have h1 := mem_ball_zero_iff.mp (filledHull_sdiff_subset hτ hαs hJ ⟨hp, hpJ⟩).1
    have h2 := mem_sphere_zero_iff_norm.mp hps
    linarith

private theorem disjoint_and_union_filledHull_sdiff (hτ : IsCrosscut τ (ball 0 1))
    {α β : Path x y} (hα : Injective α) (hαs : range α ⊆ sphere 0 1)
    (hβs : range β ⊆ sphere 0 1) (hαβ : range α ∩ range β = {x, y})
    (hJα : IsJordanCurve (range τ ∪ range α)) (hJβ : IsJordanCurve (range τ ∪ range β)) :
    Disjoint (filledHull (range τ ∪ range α) \ (range τ ∪ range α))
        (filledHull (range τ ∪ range β) \ (range τ ∪ range β)) ∧
      (filledHull (range τ ∪ range α) \ (range τ ∪ range α)) ∪
        (filledHull (range τ ∪ range β) \ (range τ ∪ range β)) = ball 0 1 \ range τ := by
  set W₁ := filledHull (range τ ∪ range α) \ (range τ ∪ range α)
  set W₂ := filledHull (range τ ∪ range β) \ (range τ ∪ range β)
  have hW₁ := filledHull_sdiff_subset hτ hαs hJα
  have hW₂ := filledHull_sdiff_subset hτ hβs hJβ
  have hdisj : Disjoint W₁ W₂ := by
    rw [Set.disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
    intro hne
    have h₂₁ := subset_filledHull_sdiff hαs hJα hJβ.isConnected_filledHull_sdiff.isPreconnected
      hW₂ (by rwa [inter_comm])
    have h₁₂ := subset_filledHull_sdiff hβs hJβ hJα.isConnected_filledHull_sdiff.isPreconnected
      hW₁ hne
    have hcl : filledHull (range τ ∪ range α) = filledHull (range τ ∪ range β) := by
      rw [← hJα.closure_filledHull_sdiff, ← hJβ.closure_filledHull_sdiff,
        Subset.antisymm h₁₂ h₂₁]
    have hab : range α = range β := by
      rw [← hτ.filledHull_union_range_inter_sphere hαs hJα,
        ← hτ.filledHull_union_range_inter_sphere hβs hJβ, hcl]
    have hhalf : α ⟨1 / 2, by norm_num, by norm_num⟩ ∈ ({x, y} : Set ℂ) := by
      rw [← hαβ, ← hab, inter_self]
      exact mem_range_self _
    rcases hhalf with h | h
    · have := congrArg Subtype.val (hα (h.trans α.source.symm))
      norm_num at this
    · have := congrArg Subtype.val (hα (h.trans α.target.symm))
      norm_num at this
  refine ⟨hdisj, Subset.antisymm (union_subset hW₁ hW₂) fun v hv ↦ ?_⟩
  obtain ⟨z, hz⟩ := hJα.nonempty_filledHull_sdiff
  obtain ⟨w, hw⟩ := hJβ.nonempty_filledHull_sdiff
  have hcomp {W : Set ℂ} (hWτ : W ⊆ ball 0 1 \ range τ) (hWc : IsPreconnected W)
      (hWmax : ∀ S, IsPreconnected S → S ⊆ ball 0 1 \ range τ → (S ∩ W).Nonempty → S ⊆ W)
      {z : ℂ} (hz : z ∈ W) : connectedComponentIn (ball 0 1 \ range τ) z = W :=
    Subset.antisymm (hWmax _ isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) ⟨z, mem_connectedComponentIn (hWτ hz), hz⟩)
      (hWc.subset_connectedComponentIn hz hWτ)
  have hc₁ := hcomp hW₁ hJα.isConnected_filledHull_sdiff.isPreconnected
    (fun S hS hSτ hSW ↦ subset_filledHull_sdiff hαs hJα hS hSτ hSW) hz
  have hc₂ := hcomp hW₂ hJβ.isConnected_filledHull_sdiff.isPreconnected
    (fun S hS hSτ hSW ↦ subset_filledHull_sdiff hβs hJβ hS hSτ hSW) hw
  have hsep : τ.SeparatesIn (ball 0 1) z w := by
    refine (separatesIn_def τ _ z w).2 ⟨hW₁ hz, hW₂ hw, ?_⟩
    rw [hc₁, hc₂]
    intro h
    apply Set.disjoint_left.mp hdisj hz
    have : z ∈ W₁ := hz
    rwa [show W₁ = W₂ from h] at this
  have hv' := mem_connectedComponentIn hv
  rcases hτ.connectedComponentIn_eq_or_eq_of_separatesIn isOpen_ball
    (convex_ball 0 1).isPreconnected hsep hv with h | h
  · rw [h, hc₁] at hv'
    exact Or.inl hv'
  · rw [h, hc₂] at hv'
    exact Or.inr hv'

private theorem exists_arcs_of_isCrosscut (hτ : IsCrosscut τ (ball 0 1)) :
    ∃ α β : Path x y, Injective α ∧ Injective β ∧ range α ∪ range β = sphere 0 1 ∧
      range α ∩ range β = {x, y} ∧ IsJordanCurve (range τ ∪ range α) ∧
      IsJordanCurve (range τ ∪ range β) ∧
      Disjoint (filledHull (range τ ∪ range α) \ (range τ ∪ range α))
        (filledHull (range τ ∪ range β) \ (range τ ∪ range β)) ∧
      (filledHull (range τ ∪ range α) \ (range τ ∪ range α)) ∪
        (filledHull (range τ ∪ range β) \ (range τ ∪ range β)) = ball 0 1 \ range τ := by
  have hfr := frontier_ball (0 : ℂ) one_ne_zero
  obtain ⟨α, β, hα, hβ, hαβu, hαβi⟩ := exists_arcs_sphere (hfr ▸ hτ.source_mem_frontier)
    (hfr ▸ hτ.target_mem_frontier) hτ.source_ne_target
  have hαs : range α ⊆ sphere 0 1 := hαβu ▸ subset_union_left
  have hβs : range β ⊆ sphere 0 1 := hαβu ▸ subset_union_right
  have hJα := isJordanCurve_range_union_range_of_inter_eq_pair hτ.injective hα
    (range_inter_range_eq_pair hτ hαs)
  have hJβ := isJordanCurve_range_union_range_of_inter_eq_pair hτ.injective hβ
    (range_inter_range_eq_pair hτ hβs)
  exact ⟨α, β, hα, hβ, hαβu, hαβi, hJα, hJβ,
    disjoint_and_union_filledHull_sdiff hτ hα hαs hβs hαβi hJα hJβ⟩

private theorem filledHull_union_filledHull (hτ : IsCrosscut τ (ball 0 1)) {α β : Path x y}
    (hαβu : range α ∪ range β = sphere 0 1)
    (hunion : (filledHull (range τ ∪ range α) \ (range τ ∪ range α)) ∪
        (filledHull (range τ ∪ range β) \ (range τ ∪ range β)) = ball 0 1 \ range τ) :
    filledHull (range τ ∪ range α) ∪ filledHull (range τ ∪ range β) = closedBall 0 1 := by
  refine Subset.antisymm (union_subset
    (filledHull_subset_closedBall (union_range_subset_closedBall hτ (hαβu ▸ subset_union_left)))
    (filledHull_subset_closedBall (union_range_subset_closedBall hτ
      (hαβu ▸ subset_union_right)))) fun p hp ↦ ?_
  by_cases hpτ : p ∈ range τ
  · exact Or.inl (subset_filledHull (Or.inl hpτ))
  by_cases hpb : p ∈ ball 0 1
  · have h : p ∈ ball 0 1 \ range τ := ⟨hpb, hpτ⟩
    rw [← hunion] at h
    rcases h with h | h
    exacts [Or.inl h.1, Or.inr h.1]
  · have hps : p ∈ sphere (0 : ℂ) 1 :=
      closedBall_sdiff_ball (x := (0 : ℂ)) (ε := 1) ▸ ⟨hp, hpb⟩
    rcases (hαβu ▸ hps : p ∈ range α ∪ range β) with h | h
    exacts [Or.inl (subset_filledHull (Or.inr h)), Or.inr (subset_filledHull (Or.inr h))]

/-- **A crosscut cuts the closed unit disc in two.** If `τ` is a crosscut of the open unit disc
from `x` to `y`, then the unit circle is the union of two arcs `α` and `β` from `x` to `y` meeting
only at `x` and `y`, the sets `range τ ∪ range α` and `range τ ∪ range β` are Jordan curves, and
their filled hulls cover the closed unit disc and meet exactly along the crosscut. -/
theorem IsCrosscut.exists_filledHull_union_eq_closedBall (hτ : IsCrosscut τ (ball 0 1)) :
    ∃ α β : Path x y, Injective α ∧ Injective β ∧ range α ∪ range β = sphere 0 1 ∧
      range α ∩ range β = {x, y} ∧ IsJordanCurve (range τ ∪ range α) ∧
      IsJordanCurve (range τ ∪ range β) ∧
      filledHull (range τ ∪ range α) ∪ filledHull (range τ ∪ range β) = closedBall 0 1 ∧
      filledHull (range τ ∪ range α) ∩ filledHull (range τ ∪ range β) = range τ := by
  obtain ⟨α, β, hα, hβ, hαβu, hαβi, hJα, hJβ, hdisj, hunion⟩ := exists_arcs_of_isCrosscut hτ
  have hαs : range α ⊆ sphere 0 1 := hαβu ▸ subset_union_left
  have hβs : range β ⊆ sphere 0 1 := hαβu ▸ subset_union_right
  refine ⟨α, β, hα, hβ, hαβu, hαβi, hJα, hJβ, filledHull_union_filledHull hτ hαβu hunion,
    Subset.antisymm (fun p ⟨hpα, hpβ⟩ ↦ ?_) fun p hp ↦
      ⟨subset_filledHull (Or.inl hp), subset_filledHull (Or.inl hp)⟩⟩
  by_contra hpτ
  have hpc : p ∈ closedBall (0 : ℂ) 1 :=
    filledHull_subset_closedBall (union_range_subset_closedBall hτ hαs) hpα
  by_cases hpb : p ∈ ball 0 1
  · exact hdisj.ne_of_mem (mem_filledHull_sdiff_of_mem hαs hpα ⟨hpb, hpτ⟩)
      (mem_filledHull_sdiff_of_mem hβs hpβ ⟨hpb, hpτ⟩) rfl
  · have hps : p ∈ sphere (0 : ℂ) 1 :=
      closedBall_sdiff_ball (x := (0 : ℂ)) (ε := 1) ▸ ⟨hpc, hpb⟩
    have hp2 : p ∈ ({x, y} : Set ℂ) := by
      rw [← hαβi, ← hτ.filledHull_union_range_inter_sphere hαs hJα,
        ← hτ.filledHull_union_range_inter_sphere hβs hJβ]
      exact ⟨⟨hpα, hps⟩, hpβ, hps⟩
    rcases hp2 with rfl | rfl
    exacts [hpτ τ.source_mem_range, hpτ τ.target_mem_range]

end Path
