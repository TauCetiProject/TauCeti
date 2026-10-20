/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Normed.Module.Convex
public import TauCeti.Topology.FilledHull
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import TauCeti.Topology.ConnectedComponents

/-!
# Filled compact exhaustions of open sets

A set `K` is *filled in* a set `Ω` (`TauCeti.IsFilledIn K Ω`) if no connected component of
`Ω \ K` is relatively compact in `Ω`, that is, has compact closure contained in `Ω`. This is the
topological hypothesis of Runge-type approximation theorems, under which functions holomorphic, or
harmonic, near a compact set `K ⊆ Ω` are uniform limits on `K` of functions holomorphic, or
harmonic, on all of `Ω`.

The main theorem `IsOpen.exists_isFilledIn_compact_exhaustion` says that every open subset `Ω` of
a proper real normed space has an exhaustion by compact sets `K n ⊆ interior (K (n + 1))`, each of
which is filled in `Ω`. Such an exhaustion is the device which turns Runge approximation on compact
sets into the solution of an equation on all of `Ω`: successive local solutions are corrected by
global approximants with summable errors on the `K n`. The sets are
`K n = closedBall 0 (n + 1) \ thickening (n + 1)⁻¹ Ωᶜ`: a point outside `K n` is joined, outside
`K n`, either to infinity by a ray, or to a point of `Ωᶜ` by a short segment.

In a proper, locally connected metric space, `TauCeti.isFilledIn_iff_forall_mem_filledHull`
recasts the condition through the bounded components of `Kᶜ`, which make up the filled hull
`TauCeti.filledHull K \ K`: for closed `K ⊆ Ω`, the set `K` is filled in `Ω` exactly when every
bounded connected component of `Kᶜ` meets `Ωᶜ`. This is the form in which the condition enters
unique-continuation arguments on the complement of `K`: each component of `Kᶜ` is unbounded or
reaches a point outside `Ω`.
For `Ω` the whole space, being filled in it means being equal to the filled hull
(`TauCeti.isFilledIn_univ_iff`).

## Main declarations

* `IsPreconnected.subset_connectedComponentIn_of_inter_closure_subset`: a preconnected set through
  a point of an open set `U` lies in the component of that point in `U`, as soon as it meets the
  closure of that component only inside `U`.
* `TauCeti.IsFilledIn`: no connected component of `Ω \ K` is relatively compact in `Ω`.
* `TauCeti.isFilledIn_iff_forall_mem_filledHull`: the same condition through the bounded components
  of `Kᶜ`.
* `IsOpen.exists_isFilledIn_compact_exhaustion`: an open set in a proper real normed space has a
  compact exhaustion by sets filled in it.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
-/

public section

open Bornology Metric Set

/-- **Trapping a preconnected set in a component of an open set.** Let `U` be open in a locally
connected space and let `C` be the connected component of `x ∈ U` in `U`. A preconnected set `A`
through `x` lies in `C` as soon as it meets the closure of `C` only inside `U`. This weakens the
hypothesis `A ⊆ U` of `IsPreconnected.subset_connectedComponentIn`. -/
theorem IsPreconnected.subset_connectedComponentIn_of_inter_closure_subset {X : Type*}
    [TopologicalSpace X] [LocallyConnectedSpace X] {A U : Set X} {x : X} (hA : IsPreconnected A)
    (hU : IsOpen U) (hxA : x ∈ A) (hxU : x ∈ U)
    (h : A ∩ closure (_root_.connectedComponentIn U x) ⊆ U) :
    A ⊆ _root_.connectedComponentIn U x := by
  refine hA.subset_of_closure_inter_subset hU.connectedComponentIn
    ⟨x, hxA, mem_connectedComponentIn hxU⟩ fun y hy => ?_
  by_contra hyC
  have hfr : y ∈ frontier (_root_.connectedComponentIn U x) :=
    ⟨hy.1, by rwa [hU.connectedComponentIn.interior_eq]⟩
  exact TauCeti.frontier_connectedComponentIn_subset_compl hU x hfr (h ⟨hy.2, hy.1⟩)

namespace TauCeti

section Topology

variable {X : Type*} [TopologicalSpace X] {K Ω : Set X}

/-- A set `K` is **filled in** a set `Ω` if no connected component of `Ω \ K` is relatively compact
in `Ω`: the closure of each such component is noncompact or leaves `Ω`. -/
def IsFilledIn (K Ω : Set X) : Prop :=
  ∀ x ∈ Ω \ K,
    ¬ (IsCompact (closure (connectedComponentIn (Ω \ K) x)) ∧
      closure (connectedComponentIn (Ω \ K) x) ⊆ Ω)

/-- Unfolding `TauCeti.IsFilledIn`. -/
theorem isFilledIn_iff :
    IsFilledIn K Ω ↔ ∀ x ∈ Ω \ K,
      ¬ (IsCompact (closure (connectedComponentIn (Ω \ K) x)) ∧
        closure (connectedComponentIn (Ω \ K) x) ⊆ Ω) :=
  Iff.rfl

end Topology

section MetricSpace

variable {X : Type*} [PseudoMetricSpace X] [ProperSpace X] [LocallyConnectedSpace X] {K Ω : Set X}

/-- **Filledness through the filled hull.** For a closed set `K` inside an open set `Ω` of a proper,
locally connected metric space, `K` is filled in `Ω` exactly when no bounded connected component
of `Kᶜ` lies in `Ω`, i.e. every bounded component of `Kᶜ` meets `Ωᶜ`. -/
theorem isFilledIn_iff_forall_mem_filledHull (hK : IsClosed K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔ ∀ x ∈ filledHull K \ K, ¬ connectedComponentIn Kᶜ x ⊆ Ω := by
  constructor
  · -- The component `C` of `x` in `Ω \ K` lies in the component `D` of `x` in `Kᶜ`, whose closure
    -- is compact and adds to `D` only points of `K ⊆ Ω`.
    rintro h x ⟨hxH, hxK⟩ hDΩ
    have hCD : connectedComponentIn (Ω \ K) x ⊆ connectedComponentIn Kᶜ x :=
      connectedComponentIn_mono x (sdiff_subset_compl _ _)
    have hclD : closure (connectedComponentIn Kᶜ x) ⊆ Ω := by
      rw [closure_eq_self_union_frontier]
      exact union_subset hDΩ <| (frontier_connectedComponentIn_subset_compl hK.isOpen_compl x).trans
        (by rwa [compl_compl])
    exact h x ⟨hDΩ (mem_connectedComponentIn hxK), hxK⟩
      ⟨(mem_filledHull_iff.mp hxH).isCompact_closure.of_isClosed_subset isClosed_closure
        (closure_mono hCD), (closure_mono hCD).trans hclD⟩
  · -- A relatively compact component of `Ω \ K` would contain the whole component of `x` in `Kᶜ`.
    rintro h x ⟨hxΩ, hxK⟩ ⟨hcpt, hsub⟩
    have hD : connectedComponentIn Kᶜ x ⊆ connectedComponentIn (Ω \ K) x :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn_of_inter_closure_subset
        (hΩ.sdiff hK) (mem_connectedComponentIn hxK) ⟨hxΩ, hxK⟩
        fun y hy => ⟨hsub hy.2, connectedComponentIn_subset _ _ hy.1⟩
    exact h x ⟨mem_filledHull_iff.mpr (hcpt.isBounded.subset (hD.trans subset_closure)), hxK⟩
      (hD.trans (subset_closure.trans hsub))

/-- A closed set is filled in the whole space exactly when it equals its filled hull, i.e. its
complement has no bounded connected component. -/
theorem isFilledIn_univ_iff (hK : IsClosed K) : IsFilledIn K univ ↔ filledHull K = K := by
  rw [isFilledIn_iff_forall_mem_filledHull hK isOpen_univ (subset_univ K)]
  exact ⟨fun h => Subset.antisymm
      (fun x hx => by_contra fun hxK => h x ⟨hx, hxK⟩ (subset_univ _)) subset_filledHull,
    fun h x hx _ => hx.2 (h ▸ hx.1)⟩

end MetricSpace

end TauCeti

section Exhaustion

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- **Filled compact exhaustion.** Every open set `Ω` of a proper real normed space is the union of
compact sets `K n` with `K n ⊆ interior (K (n + 1))`, each of which is filled in `Ω`: no connected
component of `Ω \ K n` is relatively compact in `Ω`. -/
theorem IsOpen.exists_isFilledIn_compact_exhaustion {Ω : Set E} (hΩ : IsOpen Ω) :
    ∃ K : ℕ → Set E, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ interior (K (n + 1))) ∧
      ⋃ n, K n = Ω ∧ ∀ n, IsFilledIn (K n) Ω := by
  set K : ℕ → Set E := fun n => closedBall 0 (n + 1) \ thickening (n + 1 : ℝ)⁻¹ Ωᶜ
  have hKcpt : ∀ n, IsCompact (K n) := fun n => (isCompact_closedBall _ _).diff isOpen_thickening
  have hKΩ : ∀ n, K n ⊆ Ω := fun n x hx => by
    by_contra hxΩ
    exact hx.2 (self_subset_thickening (by positivity) _ hxΩ)
  refine ⟨K, hKcpt, fun n => ?_, ?_, fun n => ?_⟩
  · -- `K n` lies in the open set `ball 0 (n + 2) \ cthickening (n + 2)⁻¹ Ωᶜ ⊆ K (n + 1)`.
    have hopen : IsOpen (ball (0 : E) (n + 1 + 1) \ cthickening (n + 1 + 1 : ℝ)⁻¹ Ωᶜ) :=
      isOpen_ball.sdiff isClosed_cthickening
    refine Subset.trans ?_ (hopen.subset_interior_iff.mpr ?_)
    · rintro x ⟨hx₁, hx₂⟩
      refine ⟨mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx₁).trans_lt (by linarith)),
        fun h => hx₂ (cthickening_subset_thickening' (by positivity) ?_ _ h)⟩
      gcongr
      linarith
    · simp only [K, Nat.cast_add, Nat.cast_one]
      exact sdiff_subset_sdiff ball_subset_closedBall (thickening_subset_cthickening _ _)
  · refine Subset.antisymm (iUnion_subset hKΩ) fun x hx => ?_
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
    obtain ⟨n, hn⟩ := exists_nat_ge (max ‖x‖ ε⁻¹)
    have hn₁ : ‖x‖ ≤ n := (le_max_left _ _).trans hn
    have hn₂ : ε⁻¹ < n + 1 := ((le_max_right _ _).trans hn).trans_lt (by linarith)
    refine mem_iUnion.mpr ⟨n, mem_closedBall_zero_iff.mpr (by linarith), fun h => ?_⟩
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp h
    refine hy (hball ?_)
    rw [mem_ball, dist_comm]
    exact hxy.trans (inv_lt_of_inv_lt₀ hε hn₂)
  · rw [isFilledIn_iff_forall_mem_filledHull (hKcpt n).isClosed hΩ (hKΩ n)]
    rintro x ⟨hxH, hxK⟩ hDΩ
    have hbdd := mem_filledHull_iff.mp hxH
    by_cases hx : ‖x‖ ≤ n + 1
    · -- `x` is within `(n + 1)⁻¹` of a point `y ∉ Ω`; the segment `[x, y]` stays that close to
      -- `y`, so it avoids `K n` and carries `y` into the component of `x` in `(K n)ᶜ`.
      have hxt : x ∈ thickening (n + 1 : ℝ)⁻¹ Ωᶜ := by
        by_contra hxt
        exact hxK ⟨mem_closedBall_zero_iff.mpr hx, hxt⟩
      obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hxt
      have hseg : segment ℝ x y ⊆ connectedComponentIn (K n)ᶜ x := by
        refine (convex_segment x y).isPreconnected.subset_connectedComponentIn
          (left_mem_segment ℝ x y) fun z hz hzK => hzK.2 (mem_thickening_iff.mpr ⟨y, hy, ?_⟩)
        have hzy : z ∈ closedBall y (dist x y) :=
          (convex_closedBall y (dist x y)).segment_subset (mem_closedBall.mpr le_rfl)
            (mem_closedBall_self dist_nonneg) hz
        exact (mem_closedBall.mp hzy).trans_lt hxy
      exact hy (hDΩ (hseg (right_mem_segment ℝ x y)))
    · -- The ray `{t • x | 1 ≤ t}` stays outside `closedBall 0 (n + 1) ⊇ K n`, so the component of
      -- `x` in `(K n)ᶜ` is unbounded.
      replace hx := not_le.mp hx
      have hx₀ : 0 < ‖x‖ := lt_trans (by positivity) hx
      have hray : (fun t : ℝ => t • x) '' Ici 1 ⊆ connectedComponentIn (K n)ᶜ x := by
        refine (isPreconnected_Ici.image (fun t : ℝ => t • x)
          (continuous_id.smul continuous_const).continuousOn)
          |>.subset_connectedComponentIn ⟨1, self_mem_Ici, one_smul ℝ x⟩ ?_
        rintro _ ⟨t, ht, rfl⟩ hK
        have h₁ := mem_closedBall_zero_iff.mp hK.1
        rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ht)] at h₁
        nlinarith [mem_Ici.mp ht]
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (hbdd.subset hray)
      set t := max 1 ((C + 1) / ‖x‖)
      have ht : 1 ≤ t := le_max_left _ _
      have h₁ := hC _ ⟨t, ht, rfl⟩
      rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ht)] at h₁
      have h₂ : (C + 1) / ‖x‖ * ‖x‖ ≤ t * ‖x‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hx₀.le
      rw [div_mul_cancel₀ _ hx₀.ne'] at h₂
      linarith

end Exhaustion
