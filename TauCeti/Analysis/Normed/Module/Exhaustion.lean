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
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Topology.Frontier

/-!
# Filled compact exhaustions of open sets

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
an open set `Ω` in the sense of `TauCeti.IsFilledIn` (no connected component of `Ω \ K` is
relatively compact in `Ω`): from a point outside `K`, either the segment to a nearby point of `Ωᶜ`
or the outward ray from the centre avoids `K`, so it cannot remain inside a component of `Ω \ K`
with compact closure in `Ω`. Combining both properties yields
`IsOpen.exists_isFilledIn_compact_exhaustion` on proper real seminormed spaces.

Also recorded here are `Metric.infEDist_frontier_of_mem_closure` and
`Metric.infDist_frontier_of_mem_closure`: from any point in `closure s` in a real seminormed space,
the distance to `frontier s` equals the distance to `sᶜ`, since the segment to any point of `sᶜ`
crosses `frontier s` no farther away.

## Main declarations

* `TauCeti.filledExhaustion`: the explicit exhaustion stages
  `closedBall 0 (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ`.
* `TauCeti.filledExhaustion_subset_interior_succ`, `TauCeti.iUnion_filledExhaustion`,
  `IsOpen.iUnion_filledExhaustion`, `IsOpen.exists_subset_interior_filledExhaustion`, and
  `IsOpen.exists_subset_filledExhaustion`: interior nesting, union, and compact cofinality.
* `TauCeti.isCompact_filledExhaustion`: compactness of each stage in a proper space.
* `Metric.infEDist_frontier_of_mem_closure` and `Metric.infDist_frontier_of_mem_closure`:
  distance to `frontier s` equals distance to `sᶜ` on `closure s`.
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
theorem mem_filledExhaustion_iff {Ω : Set E} {n : ℕ} {x : E} :
    x ∈ filledExhaustion Ω n ↔
      ‖x‖ ≤ n + 1 ∧ ENNReal.ofReal (n + 1 : ℝ)⁻¹ ≤ infEDist x Ωᶜ := by
  rw [filledExhaustion_def, mem_sdiff, mem_closedBall_zero_iff, mem_thickening_iff_infEDist_lt,
    not_lt]

/-- Every stage `filledExhaustion Ω n` lies in `Ω`. -/
theorem filledExhaustion_subset (Ω : Set E) (n : ℕ) : filledExhaustion Ω n ⊆ Ω := fun x hx ↦ by
  by_contra hxΩ
  exact hx.2 (self_subset_thickening (by positivity) _ hxΩ)

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
    filledExhaustion Ω n ⊆ closedBall 0 (n + 1) :=
  sdiff_subset

/-- Every stage `filledExhaustion Ω n` is closed. -/
theorem isClosed_filledExhaustion (Ω : Set E) (n : ℕ) : IsClosed (filledExhaustion Ω n) :=
  isClosed_closedBall.sdiff isOpen_thickening

/-- Every stage `filledExhaustion Ω n` is bounded. -/
theorem isBounded_filledExhaustion (Ω : Set E) (n : ℕ) : IsBounded (filledExhaustion Ω n) :=
  isBounded_closedBall.subset (filledExhaustion_subset_closedBall Ω n)

/-- Each stage `filledExhaustion Ω n` lies in the interior of the next stage
`filledExhaustion Ω (n + 1)`. -/
theorem filledExhaustion_subset_interior_succ (Ω : Set E) (n : ℕ) :
    filledExhaustion Ω n ⊆ interior (filledExhaustion Ω (n + 1)) := by
  -- `K n` lies in the open set `ball 0 (n + 2) \ cthickening (n + 2)⁻¹ Ωᶜ ⊆ K (n + 1)`.
  have hopen : IsOpen (ball (0 : E) (n + 1 + 1) \ cthickening (n + 1 + 1 : ℝ)⁻¹ Ωᶜ) :=
    isOpen_ball.sdiff isClosed_cthickening
  refine Subset.trans ?_ (hopen.subset_interior_iff.mpr ?_)
  · rintro x ⟨hx₁, hx₂⟩
    refine ⟨mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx₁).trans_lt (by linarith)),
      fun h ↦ hx₂ (cthickening_subset_thickening' (by positivity) ?_ _ h)⟩
    gcongr
    linarith
  · simp only [filledExhaustion_def, Nat.cast_add, Nat.cast_one]
    exact sdiff_subset_sdiff ball_subset_closedBall (thickening_subset_cthickening _ _)

/-- The stages `filledExhaustion Ω n` increase with `n`. -/
theorem monotone_filledExhaustion (Ω : Set E) : Monotone (filledExhaustion Ω) :=
  monotone_nat_of_le_succ fun n ↦
    (filledExhaustion_subset_interior_succ Ω n).trans interior_subset

/-- Enlarging the ambient set `Ω` enlarges each stage `filledExhaustion Ω n`. -/
@[gcongr]
theorem filledExhaustion_mono_left {Ω₁ Ω₂ : Set E} (h : Ω₁ ⊆ Ω₂) (n : ℕ) :
    filledExhaustion Ω₁ n ⊆ filledExhaustion Ω₂ n :=
  sdiff_subset_sdiff Subset.rfl (thickening_subset_of_subset _ (compl_subset_compl.mpr h))

/-- For any set `Ω`, the union of the stages `filledExhaustion Ω n` is `interior Ω`. -/
theorem iUnion_filledExhaustion (Ω : Set E) : ⋃ n, filledExhaustion Ω n = interior Ω := by
  refine Subset.antisymm (iUnion_subset fun n ↦ (filledExhaustion_subset_interior_succ Ω n).trans
    (interior_mono (filledExhaustion_subset Ω (n + 1)))) fun x hx ↦ ?_
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨n, hn⟩ := exists_nat_ge (max ‖x‖ ε⁻¹)
  have hn₁ : ‖x‖ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : ε⁻¹ < n + 1 := ((le_max_right _ _).trans hn).trans_lt (by linarith)
  refine mem_iUnion.mpr ⟨n, mem_closedBall_zero_iff.mpr (by linarith), fun h ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp h
  refine hy (hball ?_)
  rw [mem_ball, dist_comm]
  exact hxy.trans (inv_lt_of_inv_lt₀ hε hn₂)

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
    (Monotone.directed_le fun _ _ h ↦ interior_mono (monotone_filledExhaustion Ω h))
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

end Stages

section Compact

variable {E : Type*} [SeminormedAddCommGroup E] [ProperSpace E]

/-- In a proper space, each stage `filledExhaustion Ω n` is compact. -/
theorem isCompact_filledExhaustion (Ω : Set E) (n : ℕ) : IsCompact (filledExhaustion Ω n) :=
  (isCompact_closedBall _ _).diff isOpen_thickening

end Compact

end TauCeti

section FrontierDistance

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- From any point `x ∈ closure s` in a real seminormed space, the extended distance to
`frontier s` equals the extended distance to `sᶜ`. -/
theorem Metric.infEDist_frontier_of_mem_closure {s : Set E} {x : E} (hx : x ∈ closure s) :
    infEDist x (frontier s) = infEDist x sᶜ := by
  -- The segment from `x ∈ s` to any `y ∈ sᶜ` meets `frontier s` no farther from `x` than `y`.
  have hfr_compl : frontier s ⊆ closure sᶜ := by
    rw [frontier_eq_closure_inter_closure]
    exact inter_subset_right
  refine le_antisymm ?_ ?_
  · rw [closure_eq_self_union_frontier] at hx
    rcases hx with hxs | hxf
    · refine le_infEDist.mpr fun y hy ↦ ?_
      obtain ⟨z, hzseg, hzf⟩ := (convex_segment x y).isPreconnected.inter_frontier_nonempty
        ⟨x, left_mem_segment ℝ x y, hxs⟩ ⟨y, right_mem_segment ℝ x y, hy⟩
      refine (infEDist_le_edist_of_mem hzf).trans ?_
      rw [edist_dist, edist_dist]
      exact ENNReal.ofReal_le_ofReal <| by
        simpa [dist_comm] using mem_closedBall.mp (segment_subset_closedBall_left x y hzseg)
    · simp [infEDist_zero_of_mem hxf]
  · rw [← infEDist_closure]
    exact infEDist_anti hfr_compl

/-- From any point `x ∈ closure s` in a real seminormed space, the ordinary distance to
`frontier s` equals the ordinary distance to `sᶜ`. -/
theorem Metric.infDist_frontier_of_mem_closure {s : Set E} {x : E} (hx : x ∈ closure s) :
    infDist x (frontier s) = infDist x sᶜ :=
  congrArg ENNReal.toReal (Metric.infEDist_frontier_of_mem_closure hx)

end FrontierDistance

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
  have hfrK : frontier C ⊆ K := hKclosed.frontier_connectedComponentIn_sdiff_subset hΩ hcl
  -- Any preconnected set through `x` avoiding `K` misses `frontier C`, so it stays in `C`.
  have htrap {S : Set E} (hS : IsPreconnected S) (hxS : x ∈ S) (hSK : S ⊆ Kᶜ) : S ⊆ C :=
    hS.subset_of_disjoint_frontier
      (disjoint_left.mpr fun z hzS hzfr ↦ hSK hzS (hfrK hzfr))
      ⟨x, hxS, mem_connectedComponentIn hx⟩
  by_cases hxb : x ∈ closedBall a r
  · have hxt : x ∈ thickening δ Ωᶜ := by_contra fun hxt ↦ hx.2 ⟨hxb, hxt⟩
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hxt
    have hseg : segment ℝ x y ⊆ C :=
      htrap (convex_segment x y).isPreconnected (left_mem_segment ℝ x y) fun z hz hzK ↦
        hzK.2 <| mem_thickening_iff.mpr
          ⟨y, hy, (mem_closedBall.mp (segment_subset_closedBall_right x y hz)).trans_lt hxy⟩
    exact hy (hcl (subset_closure (hseg (right_mem_segment ℝ x y))))
  · rw [mem_closedBall, dist_eq_norm, not_le] at hxb
    have hxa : 0 < ‖x - a‖ := hr.trans_lt hxb
    have hdist (t : ℝ) : dist (a + t • (x - a)) a = |t| * ‖x - a‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    set ray := (fun t : ℝ ↦ a + t • (x - a)) '' Ici 1
    have hrayC : ray ⊆ C := by
      refine htrap (isPreconnected_Ici.image _ (by fun_prop)) ⟨1, self_mem_Ici, by simp⟩ ?_
      rintro _ ⟨t, ht, rfl⟩ hzK
      have hmem := hzK.1
      rw [mem_closedBall, hdist, abs_of_pos (by linarith [mem_Ici.mp ht])] at hmem
      linarith [le_mul_of_one_le_left hxa.le (mem_Ici.mp ht)]
    obtain ⟨R, hR⟩ := (hcpt.isBounded.subset (hrayC.trans subset_closure)).subset_closedBall a
    set t := (|R| + 1) / ‖x - a‖ + 1
    have ht : 1 ≤ t := le_add_of_nonneg_left (by positivity)
    have hmem := mem_closedBall.mp (hR ⟨t, ht, rfl⟩)
    rw [hdist, abs_of_pos (by linarith), add_mul, div_mul_cancel₀ _ hxa.ne'] at hmem
    linarith [le_abs_self R]

/-- Every stage `filledExhaustion Ω n` of an open set `Ω` in a real seminormed space is filled in
`Ω`. -/
theorem IsOpen.isFilledIn_filledExhaustion {Ω : Set E} (hΩ : IsOpen Ω) (n : ℕ) :
    IsFilledIn (filledExhaustion Ω n) Ω :=
  hΩ.isFilledIn_closedBall_sdiff_thickening 0 (by positivity) _

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
