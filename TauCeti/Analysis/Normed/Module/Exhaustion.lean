/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Topology.FilledIn
-- Provides `NormedSpace.toLocallyConvexSpace`, hence `LocallyConnectedSpace E`.
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Geometry.Manifold.Connected

/-!
# Filled compact exhaustions of open sets

The main theorem `IsOpen.exists_isFilledIn_compact_exhaustion` says that every open subset `Ω` of
a proper real normed space has an exhaustion by compact sets `K n ⊆ interior (K (n + 1))`, each of
which is filled in `Ω` in the sense of `TauCeti.IsFilledIn`: no connected component of `Ω \ K n`
is relatively compact in `Ω`. Such an exhaustion is the device which turns Runge approximation on
compact sets into the solution of an equation on all of `Ω`: successive local solutions are
corrected by global approximants with summable errors on the `K n`.

The explicit sequence `TauCeti.rungeExhaustion Ω n = closedBall 0 (n + 1) \ thickening (n + 1)⁻¹ Ωᶜ`
realizes this exhaustion: each stage is compact, lies in `Ω`, nests into the interior of the next
stage, and is filled in `Ω` by `IsOpen.isFilledIn_closedBall_sdiff_thickening`.

This file also provides two normed-space operations on sets filled in `Ω` used in Runge hull
arguments: compactness of the domain-relative fill of a compact set `K`
(`IsCompact.isCompact_union_setOf_isCompact_closure_connectedComponentIn`) and preservation of
`TauCeti.IsFilledIn` under inserting a point when `1 < Module.rank ℝ E`
(`TauCeti.IsFilledIn.insert`).

## Main declarations

* `IsOpen.isFilledIn_closedBall_sdiff_thickening`: a closed ball with a thickening of `Ωᶜ`
  removed is filled in `Ω`.
* `TauCeti.rungeExhaustion`: the explicit exhaustion
  `closedBall 0 (n + 1) \ thickening (n + 1)⁻¹ Ωᶜ`, with compactness, interior nesting,
  monotonicity, covering of `Ω`, compact cofinality, and filledness in `Ω`.
* `IsOpen.exists_isFilledIn_compact_exhaustion`: an open set in a proper real normed space has a
  compact exhaustion by sets filled in it.
* `IsCompact.isCompact_union_setOf_isCompact_closure_connectedComponentIn`: a compact set together
  with all relatively compact components of `Ω \ K` in `Ω` is compact.
* `TauCeti.IsFilledIn.insert`: inserting a point preserves `TauCeti.IsFilledIn` in real dimension
  greater than one.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
* A. Rainer, *Advanced Complex Analysis*, proof of Theorem 12.1.
-/

public section

open Metric Set
open scoped ENNReal

section ClosedBallThickening

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- **A closed ball minus a thickening of `Ωᶜ` is filled in `Ω`.** A point outside
`K = closedBall a r \ thickening δ Ωᶜ` either lies outside the ball, hence outside the filled hull
of the ball and so of `K`, or lies within `δ` of a point `y ∉ Ω`, to which the segment from it
leads without meeting `K`. -/
theorem IsOpen.isFilledIn_closedBall_sdiff_thickening {Ω : Set E} (hΩ : IsOpen Ω) (a : E)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    IsFilledIn (closedBall a r \ thickening δ Ωᶜ) Ω := by
  have hKΩ : closedBall a r \ thickening δ Ωᶜ ⊆ Ω := fun x hx => by
    by_contra hxΩ
    exact hx.2 (self_subset_thickening hδ _ hxΩ)
  rw [isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
    (isClosed_closedBall.sdiff isOpen_thickening) hΩ hKΩ]
  rintro x ⟨hxH, hxK⟩ hDΩ
  by_cases hx : x ∈ closedBall a r
  · -- `x` is within `δ` of a point `y ∉ Ω`; the segment `[x, y]` stays that close to `y`, so it
    -- avoids `K` and carries `y` into the component of `x` in `Kᶜ`.
    have hxt : x ∈ thickening δ Ωᶜ := by
      by_contra hxt
      exact hxK ⟨hx, hxt⟩
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hxt
    have hseg : segment ℝ x y ⊆ connectedComponentIn (closedBall a r \ thickening δ Ωᶜ)ᶜ x :=
      (convex_segment x y).isPreconnected.subset_connectedComponentIn (left_mem_segment ℝ x y)
        fun z hz hzK => hzK.2 <| mem_thickening_iff.mpr
          ⟨y, hy, (mem_closedBall.mp (segment_subset_closedBall_right x y hz)).trans_lt hxy⟩
    exact hy (hDΩ (hseg (right_mem_segment ℝ x y)))
  · -- The filled hull of `K` lies in that of the ball, hence in its closed convex hull: the ball.
    exact hx (closedConvexHull_min subset_rfl (convex_closedBall _ _) isClosed_closedBall
      (filledHull_subset_closedConvexHull (nonempty_closedBall.mpr hr)
        (filledHull_mono sdiff_subset hxH)))

/-- In a proper real normed space, a compact set `K` together with all connected components of
`Ω \ K` having compact closure inside an open set `Ω` is compact. -/
theorem IsCompact.isCompact_union_setOf_isCompact_closure_connectedComponentIn
    {K Ω : Set E} (hK : IsCompact K) (hΩ : IsOpen Ω) :
    IsCompact (K ∪ {z | z ∈ Ω \ K ∧ IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
      closure (connectedComponentIn (Ω \ K) z) ⊆ Ω}) :=
  isCompact_of_isClosed_isBounded
    (hK.isClosed.isClosed_union_setOf_isCompact_closure_connectedComponentIn hΩ)
    ((isBounded_filledHull.mpr hK.isBounded).subset
      (union_setOf_isCompact_closure_connectedComponentIn_subset_filledHull
        (hΩ.sdiff hK.isClosed)))

end ClosedBallThickening

namespace TauCeti

section RungeExhaustion

variable {E : Type*} [NormedAddCommGroup E]

/-- The explicit Runge exhaustion of an open subset `Ω` of a proper real normed space:
`rungeExhaustion Ω n = closedBall 0 (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ`, whose stages are filled
in `Ω` by `IsOpen.isFilledIn_closedBall_sdiff_thickening`. -/
noncomputable def rungeExhaustion (Ω : Set E) (n : ℕ) : Set E :=
  closedBall (0 : E) (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ

/-- Unfolding `TauCeti.rungeExhaustion`. -/
theorem rungeExhaustion_def (Ω : Set E) (n : ℕ) :
    rungeExhaustion Ω n = closedBall (0 : E) (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ :=
  (rfl)

/-- Membership in `TauCeti.rungeExhaustion`: `x ∈ rungeExhaustion Ω n` iff `‖x‖ ≤ n + 1` and the
extended distance from `x` to `Ωᶜ` is at least `(n + 1)⁻¹`. -/
theorem mem_rungeExhaustion_iff {Ω : Set E} {n : ℕ} {x : E} :
    x ∈ rungeExhaustion Ω n ↔
      ‖x‖ ≤ n + 1 ∧ ENNReal.ofReal (n + 1 : ℝ)⁻¹ ≤ infEDist x Ωᶜ := by
  rw [rungeExhaustion_def, mem_sdiff, mem_closedBall_zero_iff, mem_thickening_iff_infEDist_lt,
    not_lt]

/-- Each stage of `TauCeti.rungeExhaustion` is contained in `Ω`. -/
theorem rungeExhaustion_subset (Ω : Set E) (n : ℕ) : rungeExhaustion Ω n ⊆ Ω := fun _ hx => by
  by_contra hxΩ
  exact hx.2 (self_subset_thickening (by positivity) _ hxΩ)

/-- The Runge exhaustion of the empty set is empty at every stage. -/
@[simp]
theorem rungeExhaustion_empty (n : ℕ) : rungeExhaustion (∅ : Set E) n = ∅ :=
  eq_empty_of_subset (rungeExhaustion_subset ∅ n) rfl

/-- The Runge exhaustion of `Set.univ` is the sequence of closed balls `closedBall 0 (n + 1)`. -/
@[simp]
theorem rungeExhaustion_univ (n : ℕ) :
    rungeExhaustion (Set.univ : Set E) n = closedBall 0 (n + 1) := by
  simp [rungeExhaustion_def]

/-- Each stage of `TauCeti.rungeExhaustion` is compact. -/
theorem isCompact_rungeExhaustion [ProperSpace E] (Ω : Set E) (n : ℕ) :
    IsCompact (rungeExhaustion Ω n) :=
  (isCompact_closedBall (0 : E) _).diff isOpen_thickening

/-- Successive stages of `TauCeti.rungeExhaustion` nest into each other's interiors:
`rungeExhaustion Ω n ⊆ interior (rungeExhaustion Ω (n + 1))`. -/
theorem rungeExhaustion_subset_interior_succ (Ω : Set E) (n : ℕ) :
    rungeExhaustion Ω n ⊆ interior (rungeExhaustion Ω (n + 1)) := by
  have hopen : IsOpen (ball (0 : E) (n + 1 + 1) \ cthickening (n + 1 + 1 : ℝ)⁻¹ Ωᶜ) :=
    isOpen_ball.sdiff isClosed_cthickening
  refine Subset.trans ?_ (hopen.subset_interior_iff.mpr ?_)
  · rintro x ⟨hx₁, hx₂⟩
    refine ⟨mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx₁).trans_lt (by linarith)),
      fun h => hx₂ (cthickening_subset_thickening' (by positivity) ?_ _ h)⟩
    gcongr
    linarith
  · simp only [rungeExhaustion_def, Nat.cast_add, Nat.cast_one]
    exact sdiff_subset_sdiff ball_subset_closedBall (thickening_subset_cthickening _ _)

/-- Stagewise monotonicity of `TauCeti.rungeExhaustion`. -/
theorem rungeExhaustion_monotone (Ω : Set E) : Monotone (rungeExhaustion Ω) :=
  monotone_nat_of_le_succ fun n =>
    (rungeExhaustion_subset_interior_succ Ω n).trans interior_subset

/-- Monotonicity of `TauCeti.rungeExhaustion` in both the ambient set `Ω` and the stage `n`. -/
@[gcongr]
theorem rungeExhaustion_mono {Ω₁ Ω₂ : Set E} {m n : ℕ} (hΩ : Ω₁ ⊆ Ω₂) (hmn : m ≤ n) :
    rungeExhaustion Ω₁ m ⊆ rungeExhaustion Ω₂ n :=
  (sdiff_subset_sdiff Subset.rfl (thickening_subset_of_subset _ (compl_subset_compl.mpr hΩ))).trans
    (rungeExhaustion_monotone Ω₂ hmn)

/-- The stages of `TauCeti.rungeExhaustion` cover an open `Ω`. -/
theorem iUnion_rungeExhaustion {Ω : Set E} (hΩ : IsOpen Ω) :
    ⋃ n, rungeExhaustion Ω n = Ω := by
  refine Subset.antisymm (iUnion_subset (rungeExhaustion_subset Ω)) fun x hx => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  obtain ⟨n, hn⟩ := exists_nat_ge (max ‖x‖ ε⁻¹)
  have hn₁ : ‖x‖ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : ε⁻¹ < n + 1 := ((le_max_right _ _).trans hn).trans_lt (by linarith)
  refine mem_iUnion.mpr ⟨n, mem_closedBall_zero_iff.mpr (by linarith), fun h => ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp h
  refine hy (hball ?_)
  rw [mem_ball, dist_comm]
  exact hxy.trans (inv_lt_of_inv_lt₀ hε hn₂)

/-- Compact cofinality: every compact subset of an open `Ω` is contained in some stage of
`TauCeti.rungeExhaustion Ω`. -/
theorem exists_subset_rungeExhaustion_of_isCompact {Ω K : Set E} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) : ∃ n : ℕ, K ⊆ rungeExhaustion Ω n := by
  have hcov : K ⊆ ⋃ n, interior (rungeExhaustion Ω (n + 1)) := fun x hx => by
    obtain ⟨n, hn⟩ := mem_iUnion.mp ((iUnion_rungeExhaustion hΩ).symm ▸ hKΩ hx)
    exact mem_iUnion.mpr ⟨n, rungeExhaustion_subset_interior_succ Ω n hn⟩
  have hmono : Monotone fun n => interior (rungeExhaustion Ω (n + 1)) :=
    fun m n hmn => interior_mono (rungeExhaustion_monotone Ω (Nat.add_le_add_right hmn 1))
  obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n => interior (rungeExhaustion Ω (n + 1)))
    (fun _ => isOpen_interior) hcov hmono.directed_le
  exact ⟨n + 1, hn.trans interior_subset⟩

/-- Each stage of `TauCeti.rungeExhaustion` is filled in an open `Ω`. -/
theorem isFilledIn_rungeExhaustion [NormedSpace ℝ E] [ProperSpace E] {Ω : Set E} (hΩ : IsOpen Ω)
    (n : ℕ) : IsFilledIn (rungeExhaustion Ω n) Ω :=
  hΩ.isFilledIn_closedBall_sdiff_thickening 0 (by positivity) (by positivity)

/-- In a real normed space of dimension greater than one, inserting a point into `K` when `Ω \ K`
is open preserves `TauCeti.IsFilledIn K Ω`. -/
protected theorem IsFilledIn.insert [NormedSpace ℝ E] {K Ω : Set E} (h : IsFilledIn K Ω)
    (hrank : 1 < Module.rank ℝ E) (hΩK : IsOpen (Ω \ K)) (z : E) :
    IsFilledIn (insert z K) Ω := by
  refine isFilledIn_iff.mpr fun x hx ⟨hcpt, hsub⟩ => ?_
  have hxΩK : x ∈ Ω \ K := ⟨hx.1, fun hxK => hx.2 (mem_insert_of_mem z hxK)⟩
  have hxz : x ≠ z := fun hxz => hx.2 (hxz ▸ mem_insert z K)
  let C := connectedComponentIn (Ω \ K) x
  let C₁ := connectedComponentIn (Ω \ insert z K) x
  have hpre : IsPreconnected (C \ {z}) :=
    isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank (E := E) hrank
      hΩK.connectedComponentIn isPreconnected_connectedComponentIn
      isClosed_singleton (finite_singleton z).isDiscrete
  have hC_sub : C \ {z} ⊆ C₁ :=
    hpre.subset_connectedComponentIn ⟨mem_connectedComponentIn hxΩK, hxz⟩ fun w ⟨hwC, hwz⟩ =>
      ⟨(connectedComponentIn_subset _ _ hwC).1,
        fun hw_ins => hw_ins.elim hwz (connectedComponentIn_subset _ _ hwC).2⟩
  by_cases hzC : z ∈ C
  · have hzΩ : z ∈ Ω := (connectedComponentIn_subset _ _ hzC).1
    have hcl_sub : closure C ⊆ insert z (closure C₁) := by
      have hC_ins : C ⊆ insert z C₁ := fun w hw => by
        by_cases hwz : w = z
        · exact mem_insert_iff.mpr (Or.inl hwz)
        · exact mem_insert_of_mem z (hC_sub ⟨hw, hwz⟩)
      exact (closure_mono hC_ins).trans <| by
        rw [insert_eq, closure_union, isClosed_singleton.closure_eq, ← insert_eq]
    exact isFilledIn_iff.mp h x hxΩK
      ⟨(hcpt.insert z).of_isClosed_subset isClosed_closure hcl_sub,
        hcl_sub.trans (insert_subset_iff.mpr ⟨hzΩ, hsub⟩)⟩
  · have hC_eq : connectedComponentIn (Ω \ K) x = C₁ :=
      Subset.antisymm ((sdiff_singleton_eq_self hzC).symm.trans_subset hC_sub)
        (connectedComponentIn_mono x (sdiff_subset_sdiff Subset.rfl (subset_insert z K)))
    exact isFilledIn_iff.mp h x hxΩK ⟨hC_eq.symm ▸ hcpt, hC_eq.symm ▸ hsub⟩

end RungeExhaustion

end TauCeti

section Exhaustion

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- **Filled compact exhaustion.** Every open set `Ω` of a proper real normed space is the union of
compact sets `K n` with `K n ⊆ interior (K (n + 1))`, each of which is filled in `Ω`: no connected
component of `Ω \ K n` is relatively compact in `Ω`. -/
theorem IsOpen.exists_isFilledIn_compact_exhaustion {Ω : Set E} (hΩ : IsOpen Ω) :
    ∃ K : ℕ → Set E, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ interior (K (n + 1))) ∧
      ⋃ n, K n = Ω ∧ ∀ n, IsFilledIn (K n) Ω :=
  ⟨rungeExhaustion Ω, isCompact_rungeExhaustion Ω, rungeExhaustion_subset_interior_succ Ω,
    iUnion_rungeExhaustion hΩ, isFilledIn_rungeExhaustion hΩ⟩

end Exhaustion
