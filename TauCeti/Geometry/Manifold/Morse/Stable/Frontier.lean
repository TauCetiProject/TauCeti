/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Manifold
import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Existence
import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Local.Basic
import TauCeti.Geometry.Manifold.Morse.Stable.Embedding

/-!
# Trajectories into a critical point of index `n - 1` from every critical point of index `n`

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, and `X` a
pseudo-gradient adapted to `f`. The unstable manifold `W^u(m)` of a critical point `m` of index
`n` is an open subset of `M`
(`TauCeti.IsAdaptedPseudoGradient.isOpen_unstableSet_of_manifoldMorseIndex_eq_finrank`), and
that of a critical point of index `0` is the point itself
(`TauCeti.IsAdaptedPseudoGradient.unstableSet_eq_singleton_of_manifoldMorseIndex_eq_zero`).

This file studies a critical point `q` of index `n - 1` when every other critical point has
index `0` or `n`, as for the function `hᵤ² + t hᵥ` on the sphere, with two maxima, a saddle and a
minimum. The question is which critical points of index `n` send a trajectory to `q`. The local
theory does not decide it: the stable manifold `W^s(q)` is `q` together with two trajectories,
and these may come from the same critical point of index `n`, as on the torus with one maximum.
The answer here is global.

* **Near `q`**
  (`TauCeti.IsAdaptedPseudoGradient.exists_mem_unstableSet_inter_stableSet_ne_of_mem_closure`). In a
  Morse chart at `q` in which `X` is linear, there is a single coordinate `x` of positive weight,
  and near `q` the unstable manifold `W^u(q)` is the hyperplane `x = 0`. Each of the two half-balls
  `x > 0` and `x < 0` is connected and avoids `W^u(q)` and the other critical points, so it lies in
  the union of the open unstable manifolds of the critical points of index `n`, and hence in a
  single one of them
  (`TauCeti.IsAdaptedPseudoGradient.subset_unstableSet_of_isPreconnected`). Its points on the
  axis of `x` are points of `W^s(q)`. So if `q` lies in the closure of `W^u(m)`, then some
  trajectory runs from `m` to `q`.
* **Globally**
  (`TauCeti.IsAdaptedPseudoGradient.exists_mem_unstableSet_inter_stableSet_ne_of_isPreconnected`).
  Suppose that no trajectory runs from a critical point `m` of index `n` to `q`. Then `q` is not in
  the closure of `W^u(m)`, and neither is any point of `W^u(q)`, since that closure is closed and
  invariant under the flow. The unstable manifolds of the other critical points of index `n` are
  open and disjoint from `W^u(m)`, and those of index `0` are points. So, away from the critical
  points of index `0`, the closure of `W^u(m)` is `W^u(m)` itself: removing the critical points of
  index `0` from `M` leaves the disjoint union of the open sets `W^u(m)` and the complement of its
  closure. Both are nonempty, the second containing the points of `W^s(q)` other than `q`. So if
  `M` minus its critical points of index `0` is connected, as it is for a sphere of dimension at
  least two with a unique minimum, every critical point of index `n` sends a trajectory to `q`.

When there are exactly two critical points of index `n`, the two trajectories into `q` therefore
come one from each of them (`TauCeti.Geometry.Manifold.Morse.Boundary.OneTrajectory`). This is the
trajectory count behind the Morse complex of the sphere with two maxima, where each maximum has
boundary `±` the saddle.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `subset_unstableSet_of_isPreconnected`: a connected set covered by the unstable manifolds of
  critical points of index `n` lies in one of them.
* `exists_mem_unstableSet_inter_stableSet_ne_of_mem_closure`: if `q` lies in the closure of
  `W^u(m)`, a trajectory runs from `m` to `q`.
* `exists_mem_unstableSet_inter_stableSet_ne_of_isPreconnected`: every critical point of index `n`
  sends a trajectory to `q` when `M` minus its critical points of index `0` is connected.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (the Morse complex of the sphere with two maxima, a saddle
  and a minimum).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1 (stable and unstable manifolds) and Chapter 4 (the Morse complex).
-/

public section

open Filter Function Metric Module Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- **A connected set covered by unstable manifolds of top index lies in one of them.** If every
point of a preconnected set `S` lies on the unstable manifold of a critical point of index `n`,
then `S` lies on the unstable manifold of a single one: these unstable manifolds are open and
pairwise disjoint. -/
theorem subset_unstableSet_of_isPreconnected (hf : IsMorse 𝓘(ℝ, E) f) {S : Set M}
    (hS : IsPreconnected S)
    (hcover : ∀ y ∈ S, ∃ c, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f c = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f c = finrank ℝ E ∧ y ∈ hX.flow.unstableSet c)
    {m y : M} (hyS : y ∈ S) (hym : y ∈ hX.flow.unstableSet m) : S ⊆ hX.flow.unstableSet m := by
  obtain ⟨c, hc, hcind, hyc⟩ := hcover y hyS
  obtain rfl : c = m := by
    by_contra hcm
    exact disjoint_left.1 (Flow.disjoint_unstableSet hcm) hyc hym
  set U := ⋃ c' ∈ {c' : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f c' = 0 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f c' = finrank ℝ E ∧ c' ≠ c}, hX.flow.unstableSet c'
  have hU : IsOpen U := isOpen_biUnion fun c' hc' ↦
    hX.isOpen_unstableSet_of_manifoldMorseIndex_eq_finrank hf hc'.1 hc'.2.1
  have hdisj : Disjoint (hX.flow.unstableSet c) U :=
    disjoint_iUnion₂_right.2 fun c' hc' ↦ Flow.disjoint_unstableSet hc'.2.2.symm
  refine hS.subset_left_of_subset_union
    (hX.isOpen_unstableSet_of_manifoldMorseIndex_eq_finrank hf hc hcind) hU hdisj
    (fun z hz ↦ ?_) ⟨y, hyS, hyc⟩
  obtain ⟨c', hc', hc'ind, hzc'⟩ := hcover z hz
  by_cases hcc : c' = c
  · exact Or.inl (hcc ▸ hzc')
  · exact Or.inr (mem_iUnion₂.2 ⟨c', ⟨hc', hc'ind, hcc⟩, hzc'⟩)

/-- If every critical point other than `q` has index `0` or `n`, then a point which lies neither on
`W^u(q)` nor at a critical point other than `q` lies on the unstable manifold of a critical point
of index `n`. -/
private theorem exists_mem_unstableSet_of_notMem (hf : IsMorse 𝓘(ℝ, E) f) {q y : M}
    (hcrit : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → y ≠ q →
      manifoldMorseIndex 𝓘(ℝ, E) f y = 0 ∨ manifoldMorseIndex 𝓘(ℝ, E) f y = finrank ℝ E)
    (hyu : y ∉ hX.flow.unstableSet q) (hy : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → y = q) :
    ∃ c, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f c = 0 ∧ manifoldMorseIndex 𝓘(ℝ, E) f c = finrank ℝ E ∧
      y ∈ hX.flow.unstableSet c := by
  obtain ⟨c, hc, hyc⟩ := hX.exists_mem_unstableSet hf y
  have hcq : c ≠ q := by
    rintro rfl
    exact hyu hyc
  refine ⟨c, hc, (hcrit c hc hcq).resolve_left fun h0 ↦ ?_, hyc⟩
  rw [hX.unstableSet_eq_singleton_of_manifoldMorseIndex_eq_zero hf hc h0, mem_singleton_iff] at hyc
  subst hyc
  exact hcq (hy hc)

/-- The coordinate ball of a Morse chart at a critical point `q` of index `n - 1` in which `X` is
linear, with `j` the coordinate of positive weight. On a small ball of coordinates `z`, the point
`g z` of the chart with coordinates `z` depends continuously on `z`, lies on `W^u(q)` exactly when
`z j = 0`, lies on `W^s(q)` when its coordinates of negative weight vanish, and is not a critical
point other than `q`. -/
private theorem exists_pos_forall_norm_lt (hf : IsMorse 𝓘(ℝ, E) f) {q : M}
    (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0) {φ : MorseChart E f q}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {j : Fin (finrank ℝ E)} (hj : φ.weight j = 1) (hneg : ∀ i, i ≠ j → φ.weight i < 0) :
    ∃ r > 0, ContinuousOn (fun z ↦ φ.toChart.symm (φ.coord.symm z)) (ball 0 r) ∧
      ∀ z : Fin (finrank ℝ E) → ℝ, ‖z‖ < r →
        (φ.toChart.symm (φ.coord.symm z) ∈ φ.toChart.source ∧
          φ.coord (φ.toChart (φ.toChart.symm (φ.coord.symm z))) = z) ∧
        (φ.toChart.symm (φ.coord.symm z) ∈ hX.flow.unstableSet q ↔ z j = 0) ∧
        ((∀ i, φ.weight i < 0 → z i = 0) → φ.toChart.symm (φ.coord.symm z) ∈ hX.flow.stableSet q) ∧
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (φ.toChart.symm (φ.coord.symm z)) = 0 →
          φ.toChart.symm (φ.coord.symm z) = q) := by
  have hnd := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hq
  -- Near `q`, `W^s(q)` is cut out by the coordinates of negative weight, and `W^u(q)`, the stable
  -- manifold of `-X`, by the coordinate `j` of positive weight.
  obtain ⟨εs, hεs, hs⟩ := hX.exists_forall_mem_stableSet_iff φ hφ
  obtain ⟨εu, hεu, hu⟩ := (hX.neg hf).exists_forall_mem_stableSet_iff (φ.neg hnd)
    (φ.coord_mfderiv_neg hφ hnd)
  obtain ⟨rT, hrT, hT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  have hgcont : ContinuousOn (fun z ↦ φ.toChart.symm (φ.coord.symm z)) (ball 0 rT) := fun z hz ↦
    ((φ.toChart.continuousAt_symm (hT z (mem_ball_zero_iff.1 hz))).comp
      (φ.coord.symm.toContinuousLinearEquiv.continuous.continuousAt)).continuousWithinAt
  -- Near `q` there is no other critical point.
  have hfin : {y : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ∧ y ≠ q}.Finite :=
    (by simpa only [criticalPoints_eq_setOf_mfderiv_eq_zero] using hf.finite_criticalPoints :
      {y : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0}.Finite).subset fun y hy ↦ hy.1
  have hW : {y : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ∧ y ≠ q}ᶜ ∈
      𝓝 (φ.toChart.symm (φ.coord.symm 0)) := by
    rw [map_zero, φ.toChart_symm_zero]
    exact hfin.isClosed.isOpen_compl.mem_nhds fun h ↦ h.2 rfl
  obtain ⟨r₀, hr₀, hr₀W⟩ := Metric.eventually_nhds_iff.1
    ((hgcont.continuousAt (ball_mem_nhds 0 hrT)).eventually hW)
  refine ⟨min (min rT r₀) (min εs εu), by positivity,
    hgcont.mono (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))),
    fun z hz ↦ ?_⟩
  simp only [lt_min_iff] at hz
  have hsrc : φ.toChart.symm (φ.coord.symm z) ∈ φ.toChart.source :=
    φ.toChart.map_target (hT z hz.1.1)
  have hcoord : φ.coord (φ.toChart (φ.toChart.symm (φ.coord.symm z))) = z := by
    rw [φ.toChart.right_inv (hT z hz.1.1), LinearEquiv.apply_symm_apply]
  refine ⟨⟨hsrc, hcoord⟩, ?_, fun h0 ↦ (hs _ hsrc (by rw [hcoord]; exact hz.2.1)).2
      (by rw [hcoord]; exact h0),
    fun hcrit ↦ by_contra fun hzq ↦ hr₀W (by simpa using hz.1.2) ⟨hcrit, hzq⟩⟩
  rw [hX.unstableSet_eq_stableSet_neg hf]
  refine (hu _ (by simpa using hsrc) (by simpa [hcoord] using hz.2.2)).trans
    ⟨fun h ↦ ?_, fun h i hi ↦ ?_⟩
  · simpa [hcoord] using h j (by simp [hj])
  · have hij : i = j := by
      by_contra hij
      have := hneg i hij
      simp only [MorseChart.neg_weight, Pi.neg_apply, neg_lt_zero] at hi
      linarith
    simpa [hij, hcoord] using h

/-- **A trajectory from the closure.** Let `q` be a critical point of index `n - 1` such that every
other critical point has index `0` or `n`. If `q` lies in the closure of the unstable manifold of a
point `m ≠ q`, then some trajectory runs from `m` to `q`: a point of `W^u(m) ∩ W^s(q)` other than
`q`. -/
theorem exists_mem_unstableSet_inter_stableSet_ne_of_mem_closure (hf : IsMorse 𝓘(ℝ, E) f)
    {q m : M} (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hqind : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = finrank ℝ E)
    (hcrit : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → y ≠ q →
      manifoldMorseIndex 𝓘(ℝ, E) f y = 0 ∨ manifoldMorseIndex 𝓘(ℝ, E) f y = finrank ℝ E)
    (hmq : m ≠ q) (hm : q ∈ closure (hX.flow.unstableSet m)) :
    ∃ y ∈ hX.flow.unstableSet m ∩ hX.flow.stableSet q, y ≠ q := by
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart q hq
  obtain ⟨j, hj, hneg⟩ := φ.exists_weight_eq_one_of_add_one_eq_finrank hqind
  obtain ⟨r, hrpos, hgcont, hr⟩ := hX.exists_pos_forall_norm_lt hf hq hφ hj hneg
  set g : (Fin (finrank ℝ E) → ℝ) → M := fun z ↦ φ.toChart.symm (φ.coord.symm z)
  -- A point `y = g z` of `W^u(m)` close to `q`; it is off `W^u(q)`, so `z j ≠ 0`.
  have hN : φ.toChart.source ∩ φ.toChart ⁻¹' (φ.coord ⁻¹' ball 0 r) ∈ 𝓝 q :=
    (φ.toChart.continuousOn.isOpen_inter_preimage φ.toChart.open_source
      (isOpen_ball.preimage φ.continuous_coord)).mem_nhds ⟨φ.mem_source, by simpa using hrpos⟩
  obtain ⟨y, ⟨hyN, hyN'⟩, hym⟩ := mem_closure_iff_nhds.1 hm _ hN
  set z := φ.coord (φ.toChart y)
  have hzr : ‖z‖ < r := mem_ball_zero_iff.1 hyN'
  have hgz : g z = y := φ.toChart_symm_coord_symm_coord hyN
  have hzj : z j ≠ 0 := fun h ↦ disjoint_left.1 (Flow.disjoint_unstableSet hmq) hym
    (hgz ▸ ((hr z hzr).2.1.2 h))
  -- The half-ball on the side of `y`, along the coordinate `j`.
  set K : Set (Fin (finrank ℝ E) → ℝ) := ball 0 r ∩ {w | 0 < z j * w j}
  have hKconv : Convex ℝ K := (convex_ball 0 r).inter
    (convex_halfSpace_gt (f := fun w : Fin (finrank ℝ E) → ℝ ↦ z j * w j)
      ⟨fun a b ↦ by simp [mul_add], fun c a ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring⟩ 0)
  have hKr (w) (hw : w ∈ K) : ‖w‖ < r := mem_ball_zero_iff.1 hw.1
  have hH : IsPreconnected (g '' K) := hKconv.isPreconnected.image g (hgcont.mono inter_subset_left)
  -- The half-ball avoids `W^u(q)` and the other critical points, so it lies in `W^u(m)`.
  have hzK : z ∈ K := ⟨mem_ball_zero_iff.2 hzr, mul_self_pos.2 hzj⟩
  have hHm : g '' K ⊆ hX.flow.unstableSet m := by
    refine hX.subset_unstableSet_of_isPreconnected hf hH ?_ ⟨z, hzK, hgz⟩ hym
    rintro _ ⟨w, hw, rfl⟩
    have hwj : w j ≠ 0 := fun h ↦ by simpa [h] using hw.2
    exact hX.exists_mem_unstableSet_of_notMem hf hcrit (fun h ↦ hwj ((hr w (hKr w hw)).2.1.1 h))
      (hr w (hKr w hw)).2.2.2
  -- The point of the half-ball on the axis of `j` lies on `W^s(q)`.
  set w₀ : Fin (finrank ℝ E) → ℝ := Pi.single j (z j) with hw₀
  have hw₀r : ‖w₀‖ < r := by
    rw [hw₀, Pi.norm_single]
    exact (norm_le_pi_norm z j).trans_lt hzr
  have hw₀K : w₀ ∈ K := ⟨mem_ball_zero_iff.2 hw₀r, by simpa [hw₀] using mul_self_pos.2 hzj⟩
  refine ⟨g w₀, ⟨hHm ⟨w₀, hw₀K, rfl⟩, (hr w₀ hw₀r).2.2.1 fun i hi ↦ ?_⟩, fun h ↦ hzj ?_⟩
  · have hij : i ≠ j := by
      rintro rfl
      rw [hj] at hi
      norm_num at hi
    rw [hw₀, Pi.single_eq_of_ne hij]
  · have h0 : φ.coord (φ.toChart (g w₀)) = w₀ := (hr w₀ hw₀r).1.2
    rw [h, φ.apply_self, map_zero] at h0
    simpa [hw₀] using congr_fun h0.symm j

/-- **Every critical point of top index sends a trajectory to `q`.** Let `q` be a critical point
of index `n - 1` such that every other critical point has index `0` or `n`, and suppose that `M`
minus its critical points of index `0` is connected. Then for every critical point `m` of index
`n` some trajectory runs from `m` to `q`: a point of `W^u(m) ∩ W^s(q)` other than `q`. -/
theorem exists_mem_unstableSet_inter_stableSet_ne_of_isPreconnected (hf : IsMorse 𝓘(ℝ, E) f)
    {q m : M} (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hqind : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = finrank ℝ E)
    (hcrit : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → y ≠ q →
      manifoldMorseIndex 𝓘(ℝ, E) f y = 0 ∨ manifoldMorseIndex 𝓘(ℝ, E) f y = finrank ℝ E)
    (hconn : IsPreconnected {y : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f y = 0}ᶜ)
    (hm : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f m = 0) (hmind : manifoldMorseIndex 𝓘(ℝ, E) f m = finrank ℝ E) :
    ∃ y ∈ hX.flow.unstableSet m ∩ hX.flow.stableSet q, y ≠ q := by
  -- Otherwise `M` minus its critical points of index `0` splits into the open set `W^u(m)` and the
  -- complement of its closure, the second containing the points of `W^s(q)` other than `q`.
  by_contra hno
  have hmq : m ≠ q := by
    rintro rfl
    omega
  have hqcl : q ∉ closure (hX.flow.unstableSet m) := fun h ↦
    hno (hX.exists_mem_unstableSet_inter_stableSet_ne_of_mem_closure hf hq hqind hcrit hmq h)
  set A := hX.flow.unstableSet m with hAdef
  have hA : IsOpen A := hX.isOpen_unstableSet_of_manifoldMorseIndex_eq_finrank hf hm hmind
  -- Away from the critical points of index `0`, the closure of `A` adds no point to `A`.
  have hsub : {y : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f y = 0}ᶜ ⊆ A ∪ (closure A)ᶜ := by
    intro y hy
    by_cases hyA : y ∈ closure A
    swap
    · exact Or.inr hyA
    left
    obtain ⟨c, hc, hyc⟩ := hX.exists_mem_unstableSet hf y
    by_cases hcq : c = q
    · -- The closure of `A` is closed and invariant, so it contains the backward limit `q` of `y`.
      subst hcq
      refine absurd (isClosed_closure.mem_of_tendsto (Flow.mem_unstableSet.1 hyc)
        (Eventually.of_forall fun t ↦ ?_)) hqcl
      exact map_mem_closure (hX.flow.continuous continuous_const continuous_id) hyA
        fun a ha ↦ (Flow.apply_mem_unstableSet_iff _ t).2 ha
    rcases hcrit c hc hcq with h0 | hn
    · rw [hX.unstableSet_eq_singleton_of_manifoldMorseIndex_eq_zero hf hc h0, mem_singleton_iff]
        at hyc
      exact absurd ⟨hyc ▸ hc, hyc ▸ h0⟩ hy
    · by_cases hcm : c = m
      · rw [hAdef, ← hcm]
        exact hyc
      · exact absurd hyA (disjoint_left.1 ((Flow.disjoint_unstableSet hcm).closure_right
          (hX.isOpen_unstableSet_of_manifoldMorseIndex_eq_finrank hf hc hn)) hyc)
  have hmA : m ∈ A := (hX.mem_unstableSet_inter_stableSet_self hm).1
  have hYA := hconn.subset_left_of_subset_union hA isClosed_closure.isOpen_compl
    (disjoint_compl_right_iff_subset.2 subset_closure) hsub
    ⟨m, fun h ↦ by have := h.2; omega, hmA⟩
  -- A point of `W^s(q)` other than `q` is not critical, so it lies in `A`.
  obtain ⟨y, hys, hyq⟩ := hX.exists_mem_stableSet_ne hq (by omega)
  refine hno ⟨y, ⟨hYA fun h ↦ hyq ?_, hys⟩, hyq⟩
  by_contra hyq'
  exact disjoint_left.1 (Flow.disjoint_stableSet hyq')
    (hX.mem_unstableSet_inter_stableSet_self h.1).2 hys

end IsAdaptedPseudoGradient

end TauCeti
