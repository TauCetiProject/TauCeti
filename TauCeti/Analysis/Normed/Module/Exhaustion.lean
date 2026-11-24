/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Thickening
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.Frontier
import TauCeti.Topology.MetricSpace.ProperSpace
import TauCeti.Topology.MetricSpace.Thickening

/-!
# Filled compact exhaustions of open sets

Every open subset `Ω` of a proper real seminormed space has an exhaustion by compact sets
`K n ⊆ interior (K (n + 1))`, each of which is filled in `Ω` in the sense of `TauCeti.IsFilledIn`:
no connected component of `Ω \ K n` is relatively compact in `Ω`
(`IsOpen.exists_isFilledIn_compact_exhaustion`). Such an exhaustion is the device which turns
Runge-type approximation on compact sets into global constructions and solutions of equations on
all of `Ω`: successive local solutions are corrected by global approximants with summable errors
on the stages `K n`.

For any subset `Ω` of a seminormed group `E`, `TauCeti.filledExhaustion Ω n` is the explicit stage

`K n = closedBall 0 (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ`,

consisting of the points of norm at most `n + 1` at extended distance at least `(n + 1)⁻¹` from
`Ωᶜ`. Each stage is closed and bounded, lies in `Ω`, and satisfies
`K n ⊆ interior (K (n + 1))`, with union `⋃ n, K n = interior Ω` (`= Ω` when `Ω` is open).
Consequently every compact subset of an open set `Ω` lies in `interior (K n)` for some `n`
(`IsOpen.exists_subset_interior_filledExhaustion`).

In a proper space each stage is compact (`TauCeti.isCompact_filledExhaustion`). In a real
seminormed space, `IsOpen.isFilledIn_closedBall_sdiff_thickening` shows without properness that
removing any thickening of `Ωᶜ` from a closed ball of nonnegative radius produces a set filled in
an open set `Ω`: a point outside the stage either lies outside the ball, hence outside the filled
hull of the ball and so of the stage, or is joined to a point of `Ωᶜ` by a short segment avoiding
the stage. Combining both properties yields `IsOpen.exists_isFilledIn_compact_exhaustion` on proper
real seminormed spaces.

## Main declarations

* `TauCeti.filledExhaustion`: the explicit exhaustion stages
  `closedBall 0 (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ`.
* `TauCeti.mem_filledExhaustion_iff`, `TauCeti.norm_le_of_mem_filledExhaustion`,
  `TauCeti.le_edist_of_mem_filledExhaustion`, and `TauCeti.le_dist_of_mem_filledExhaustion`:
  membership and norm/complement-distance bounds on each stage.
* `TauCeti.filledExhaustion_subset_interior_succ`, `TauCeti.filledExhaustion_subset_interior`,
  `TauCeti.filledExhaustion_monotone`, `TauCeti.filledExhaustion_mono`,
  `TauCeti.iUnion_filledExhaustion`, `IsOpen.iUnion_filledExhaustion`,
  `IsOpen.exists_subset_interior_filledExhaustion`, and `IsOpen.exists_subset_filledExhaustion`:
  monotonicity, interior nesting, union, and compact cofinality.
* `TauCeti.summable_of_forall_norm_le_filledExhaustion`: pointwise convergence of a series whose
  `k`-th term is bounded on the `k`-th stage by a summable sequence.
* `TauCeti.isCompact_filledExhaustion`: compactness of each stage in a proper space.
* `IsOpen.isFilledIn_closedBall_sdiff_thickening` and `IsOpen.isFilledIn_filledExhaustion`:
  filledness of `closedBall a r \ thickening δ Ωᶜ` and of each exhaustion stage in an open `Ω`.
* `IsOpen.exists_isFilledIn_compact_exhaustion`: an open set in a proper real seminormed space has
  a compact exhaustion by sets filled in it.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
* A. Rainer, *Advanced Complex Analysis*, Theorem 12.1.
-/

public section

open Bornology Metric Set

namespace TauCeti

section Stages

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The `n`th canonical filled-exhaustion stage of `Ω`:
`closedBall 0 (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ`, consisting of the points of norm at most
`n + 1` at extended distance at least `(n + 1)⁻¹` from `Ωᶜ`. -/
noncomputable def filledExhaustion (Ω : Set E) (n : ℕ) : Set E :=
  closedBall 0 (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ

theorem filledExhaustion_def (Ω : Set E) (n : ℕ) :
    filledExhaustion Ω n = closedBall 0 (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ :=
  (rfl)

/-- Membership in `filledExhaustion Ω n` in terms of norm and extended distance to `Ωᶜ`. -/
@[grind =]
theorem mem_filledExhaustion_iff {Ω : Set E} {n : ℕ} {x : E} :
    x ∈ filledExhaustion Ω n ↔
      ‖x‖ ≤ n + 1 ∧ ENNReal.ofReal (n + 1 : ℝ)⁻¹ ≤ infEDist x Ωᶜ := by
  rw [filledExhaustion_def, mem_sdiff, mem_closedBall_zero_iff, mem_thickening_iff_infEDist_lt,
    not_lt]

/-- Every point of `filledExhaustion Ω n` has norm at most `n + 1`. -/
theorem norm_le_of_mem_filledExhaustion {Ω : Set E} {n : ℕ} {x : E}
    (hx : x ∈ filledExhaustion Ω n) : ‖x‖ ≤ n + 1 :=
  (mem_filledExhaustion_iff.mp hx).1

/-- Every point of `filledExhaustion Ω n` is at extended distance at least
`ENNReal.ofReal (n + 1 : ℝ)⁻¹` from any point outside `Ω`. -/
theorem le_edist_of_mem_filledExhaustion {Ω : Set E} {n : ℕ} {x y : E}
    (hx : x ∈ filledExhaustion Ω n) (hy : y ∉ Ω) :
    ENNReal.ofReal (n + 1 : ℝ)⁻¹ ≤ edist x y :=
  (mem_filledExhaustion_iff.mp hx).2.trans (infEDist_le_edist_of_mem hy)

/-- Every point of `filledExhaustion Ω n` is at distance at least `(n + 1 : ℝ)⁻¹` from any point
outside `Ω`. -/
theorem le_dist_of_mem_filledExhaustion {Ω : Set E} {n : ℕ} {x y : E}
    (hx : x ∈ filledExhaustion Ω n) (hy : y ∉ Ω) :
    (n + 1 : ℝ)⁻¹ ≤ dist x y := by
  have h := le_edist_of_mem_filledExhaustion hx hy
  rw [edist_dist] at h
  exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp h

/-- Every stage `filledExhaustion Ω n` lies in `Ω`. -/
theorem filledExhaustion_subset (Ω : Set E) (n : ℕ) : filledExhaustion Ω n ⊆ Ω :=
  sdiff_thickening_compl_subset _ _ (by positivity)

@[simp]
theorem filledExhaustion_empty (n : ℕ) : filledExhaustion (∅ : Set E) n = ∅ :=
  subset_empty_iff.mp (filledExhaustion_subset ∅ n)

@[simp]
theorem filledExhaustion_univ (n : ℕ) :
    filledExhaustion (univ : Set E) n = closedBall 0 (n + 1) := by
  rw [filledExhaustion_def, compl_univ, thickening_empty, sdiff_empty]

/-- For `1 ≤ n`, `filledExhaustion Ω (n - 1)` is `closedBall 0 n \ thickening n⁻¹ Ωᶜ`. -/
theorem filledExhaustion_sub_one (Ω : Set E) {n : ℕ} (hn : 1 ≤ n) :
    filledExhaustion Ω (n - 1) = closedBall 0 n \ thickening (n : ℝ)⁻¹ Ωᶜ := by
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast Nat.sub_add_cancel hn
  rw [filledExhaustion_def, hcast]

/-- Every stage `filledExhaustion Ω n` lies in `closedBall 0 (n + 1)`. -/
theorem filledExhaustion_subset_closedBall (Ω : Set E) (n : ℕ) :
    filledExhaustion Ω n ⊆ closedBall 0 (n + 1) := fun _ hx ↦
  mem_closedBall_zero_iff.mpr (norm_le_of_mem_filledExhaustion hx)

/-- Every stage `filledExhaustion Ω n` is closed. -/
theorem isClosed_filledExhaustion (Ω : Set E) (n : ℕ) : IsClosed (filledExhaustion Ω n) := by
  rw [filledExhaustion_def]
  exact isClosed_closedBall.sdiff isOpen_thickening

/-- Every stage `filledExhaustion Ω n` is bounded. -/
theorem isBounded_filledExhaustion (Ω : Set E) (n : ℕ) : IsBounded (filledExhaustion Ω n) :=
  isBounded_closedBall.subset (filledExhaustion_subset_closedBall Ω n)

/-- Each stage `filledExhaustion Ω n` lies in the interior of the next stage
`filledExhaustion Ω (n + 1)`. -/
theorem filledExhaustion_subset_interior_succ (Ω : Set E) (n : ℕ) :
    filledExhaustion Ω n ⊆ interior (filledExhaustion Ω (n + 1)) := by
  simpa only [filledExhaustion_def, Nat.cast_add, Nat.cast_one] using
    closedBall_sdiff_thickening_subset_interior (0 : E) Ωᶜ
      (r₁ := (n : ℝ) + 1) (r₂ := (n : ℝ) + 1 + 1)
      (δ₁ := ((n : ℝ) + 1)⁻¹) (δ₂ := ((n : ℝ) + 1 + 1)⁻¹)
      (by linarith) (by positivity) (inv_strictAnti₀ (by positivity) (by linarith))

/-- The stages `filledExhaustion Ω n` increase with `n`. -/
theorem filledExhaustion_monotone (Ω : Set E) : Monotone (filledExhaustion Ω) :=
  monotone_nat_of_le_succ fun n ↦
    (filledExhaustion_subset_interior_succ Ω n).trans interior_subset

/-- Enlarging the stage index `n` enlarges `filledExhaustion Ω n`. -/
@[gcongr]
theorem filledExhaustion_mono {Ω : Set E} {m n : ℕ} (h : m ≤ n) :
    filledExhaustion Ω m ⊆ filledExhaustion Ω n :=
  filledExhaustion_monotone Ω h

/-- For `m < n`, `filledExhaustion Ω m` lies in `interior (filledExhaustion Ω n)`. -/
theorem filledExhaustion_subset_interior {Ω : Set E} {m n : ℕ} (h : m < n) :
    filledExhaustion Ω m ⊆ interior (filledExhaustion Ω n) :=
  (filledExhaustion_subset_interior_succ Ω m).trans (interior_mono (filledExhaustion_mono h))

/-- Enlarging the ambient set `Ω` enlarges each stage `filledExhaustion Ω n`. -/
@[gcongr]
theorem filledExhaustion_mono_left {Ω₁ Ω₂ : Set E} (h : Ω₁ ⊆ Ω₂) (n : ℕ) :
    filledExhaustion Ω₁ n ⊆ filledExhaustion Ω₂ n := by
  rw [filledExhaustion_def, filledExhaustion_def]
  exact sdiff_subset_sdiff Subset.rfl (thickening_subset_of_subset _ (compl_subset_compl.mpr h))

/-- For any set `Ω`, the union of the stages `filledExhaustion Ω n` is `interior Ω`. -/
theorem iUnion_filledExhaustion (Ω : Set E) : ⋃ n, filledExhaustion Ω n = interior Ω :=
  Metric.iUnion_closedBall_sdiff_thickening_compl 0 Ω

/-- For an open set `Ω`, the stages `filledExhaustion Ω n` have union `Ω`. -/
theorem _root_.IsOpen.iUnion_filledExhaustion {Ω : Set E} (hΩ : IsOpen Ω) :
    ⋃ n, filledExhaustion Ω n = Ω := by
  rw [TauCeti.iUnion_filledExhaustion, hΩ.interior_eq]

/-- **Compact cofinality in the interior.** Every compact subset `K ⊆ interior Ω` lies inside
`interior (filledExhaustion Ω n)` for some `n`. -/
theorem _root_.IsCompact.exists_subset_interior_filledExhaustion {Ω K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ interior Ω) :
    ∃ n, K ⊆ interior (filledExhaustion Ω n) := by
  refine hK.elim_directed_cover (fun n ↦ interior (filledExhaustion Ω n))
    (fun _ ↦ isOpen_interior) ?_
    (Monotone.directed_le fun _ _ h ↦ interior_mono (filledExhaustion_monotone Ω h))
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp ((iUnion_filledExhaustion Ω).symm ▸ hKΩ hx)
  exact mem_iUnion.mpr ⟨n + 1, filledExhaustion_subset_interior_succ Ω n hn⟩

/-- **Compact cofinality (strict).** Every compact subset `K` of an open set `Ω` lies inside
`interior (filledExhaustion Ω n)` for some `n`. -/
theorem _root_.IsOpen.exists_subset_interior_filledExhaustion {Ω K : Set E}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ n, K ⊆ interior (filledExhaustion Ω n) :=
  hK.exists_subset_interior_filledExhaustion (by rwa [hΩ.interior_eq])

/-- **Compact cofinality.** Every compact subset `K` of an open set `Ω` lies inside
`filledExhaustion Ω n` for some `n`. -/
theorem _root_.IsOpen.exists_subset_filledExhaustion {Ω K : Set E}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ n, K ⊆ filledExhaustion Ω n :=
  (hΩ.exists_subset_interior_filledExhaustion hK hKΩ).imp fun _ h ↦ h.trans interior_subset

/-- A series whose `k`-th term is bounded by `u k` on the stage `filledExhaustion Ω k`, for a
summable `u`, converges at every point of `interior Ω`: such a point lies in every stage from some
index on. -/
theorem summable_of_forall_norm_le_filledExhaustion {F : Type*} [NormedAddCommGroup F]
    [CompleteSpace F] {Ω : Set E} {t : ℕ → E → F} {u : ℕ → ℝ} (hu : Summable u)
    (hb : ∀ k, ∀ x ∈ filledExhaustion Ω k, ‖t k x‖ ≤ u k) {x : E} (hx : x ∈ interior Ω) :
    Summable fun k ↦ t k x := by
  obtain ⟨j, hj⟩ := mem_iUnion.1 ((iUnion_filledExhaustion Ω).symm ▸ hx)
  exact .of_norm_bounded_eventually_nat hu <|
    Filter.eventually_atTop.2 ⟨j, fun k hk ↦ hb k x (filledExhaustion_mono hk hj)⟩

end Stages

section Compact

variable {E : Type*} [SeminormedAddCommGroup E] [ProperSpace E]

/-- In a proper space, each stage `filledExhaustion Ω n` is compact. -/
theorem isCompact_filledExhaustion (Ω : Set E) (n : ℕ) : IsCompact (filledExhaustion Ω n) :=
  isCompact_closedBall_sdiff_thickening 0 (n + 1) (n + 1 : ℝ)⁻¹ Ωᶜ

end Compact

end TauCeti

section Filled

open TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A closed ball minus a thickening of `Ωᶜ` is filled in `Ω`.** In a real seminormed space, for
any open set `Ω`, radius `0 ≤ r`, and `δ : ℝ`, no connected component of
`Ω \ (closedBall a r \ thickening δ Ωᶜ)` has compact closure contained in `Ω`. -/
theorem IsOpen.isFilledIn_closedBall_sdiff_thickening {Ω : Set E} (hΩ : IsOpen Ω) (a : E)
    {r : ℝ} (hr : 0 ≤ r) (δ : ℝ) :
    IsFilledIn (closedBall a r \ thickening δ Ωᶜ) Ω := by
  set K := closedBall a r \ thickening δ Ωᶜ
  have hKclosed : IsClosed K := isClosed_closedBall.sdiff isOpen_thickening
  rw [isFilledIn_iff]
  rintro x hx ⟨hcpt, hcl⟩
  set C := connectedComponentIn (Ω \ K) x
  have hfrK : frontier C ⊆ K :=
    (hΩ.frontier_connectedComponentIn_sdiff_subset_closure hcl).trans hKclosed.closure_subset
  by_cases hxb : x ∈ closedBall a r
  · have hxt : x ∈ thickening δ Ωᶜ := by_contra fun hxt ↦ hx.2 ⟨hxb, hxt⟩
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hxt
    have hseg : segment ℝ x y ⊆ C :=
      (convex_segment x y).isPreconnected.subset_of_disjoint_frontier
        (disjoint_left.mpr fun z hzS hzfr ↦ (hfrK hzfr).2 <| mem_thickening_iff.mpr
          ⟨y, hy, (mem_closedBall.mp (segment_subset_closedBall_right x y hzS)).trans_lt hxy⟩)
        ⟨x, left_mem_segment ℝ x y, mem_connectedComponentIn hx⟩
    exact hy (hcl (subset_closure (hseg (right_mem_segment ℝ x y))))
  · exact hxb (closedConvexHull_min subset_rfl (convex_closedBall a r) isClosed_closedBall
      (filledHull_subset_closedConvexHull (nonempty_closedBall.mpr hr)
        (filledHull_mono sdiff_subset
          (subset_filledHull_of_frontier_subset (hcpt.isBounded.subset subset_closure) hfrK
            (mem_connectedComponentIn hx)))))

/-- Every stage `filledExhaustion Ω n` of an open set `Ω` in a real seminormed space is filled in
`Ω`. -/
theorem IsOpen.isFilledIn_filledExhaustion {Ω : Set E} (hΩ : IsOpen Ω) (n : ℕ) :
    IsFilledIn (filledExhaustion Ω n) Ω := by
  rw [filledExhaustion_def]
  exact hΩ.isFilledIn_closedBall_sdiff_thickening 0 (by positivity) _

end Filled

section Exhaustion

open TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- **Filled compact exhaustion.** Every open set `Ω` of a proper real seminormed space is the
union of compact sets `K n` with `K n ⊆ interior (K (n + 1))`, each of which is filled in `Ω`: no
connected component of `Ω \ K n` is relatively compact in `Ω`. -/
theorem IsOpen.exists_isFilledIn_compact_exhaustion {Ω : Set E} (hΩ : IsOpen Ω) :
    ∃ K : ℕ → Set E, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ interior (K (n + 1))) ∧
      ⋃ n, K n = Ω ∧ ∀ n, IsFilledIn (K n) Ω :=
  ⟨filledExhaustion Ω, isCompact_filledExhaustion Ω, filledExhaustion_subset_interior_succ Ω,
    hΩ.iUnion_filledExhaustion, hΩ.isFilledIn_filledExhaustion⟩

end Exhaustion
