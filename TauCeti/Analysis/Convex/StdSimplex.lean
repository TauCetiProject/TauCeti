/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Join
public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The standard simplex as a join with its barycentre or a vertex

Over a linearly ordered field `R`, the standard simplex, the set of weight vectors of
`Convexity.StdSimplex R ι`, is the convex join of its relative boundary, the points with some
vanishing coordinate, and its barycentre, the constant point `(card ι)⁻¹`. Along the segment from
a boundary point to the barycentre, the position is recovered as `card ι` times the least
coordinate. So the segments meet only at the barycentre, and every point of the simplex other than
the barycentre lies on exactly one of them.

This is pseudo-radial projection of a simplex from its barycentre onto its boundary. It identifies
the cone on the boundary of a simplex, with apex at the barycentre, with the whole simplex; this is
the local model of a closed vertex star whose link is a combinatorial sphere.

Similarly, the standard simplex is the convex join of the facet opposite a vertex `i` with that
vertex, the `i`-th coordinate recovering the position along each segment. This is the local model
of a closed vertex star whose link is a combinatorial ball.

The faces of the standard simplex, the convex hulls of sets of vertices `Pi.single i 1`, are
described in coordinates. A point of one face is moved into its intersection with a second face
by transferring the coordinates outside the intersection to a common vertex; the distance moved
is at most `card ι` times the distance to any point of the second face. Disjoint faces are
likewise separated by at least `(card ι)⁻¹`.

## Main results

* `Convexity.StdSimplex.mem_range_toFun_comp_weights_iff`: the weight vectors of the standard
  simplex are the vectors with nonnegative coordinates summing to one.
* `Convexity.StdSimplex.convex_range_toFun_comp_weights`: the weight vectors of the standard
  simplex form a convex set.
* `Convexity.StdSimplex.norm_toLp_weights_le_one`: each weight vector has ℓᵖ norm at most one.
* `LinearMap.sum_apply_eq_of_mapsTo_range_weights`: a linear map carrying the standard simplex
  into a standard simplex preserves coordinate sums.
* `TauCeti.stdSimplexBoundary`, `TauCeti.isCompact_stdSimplexBoundary`: the relative boundary of
  the standard simplex, the points with some vanishing coordinate, and its compactness.
* `TauCeti.mem_convexHull_pi_single_iff`: the face of the standard simplex spanned by a set of
  vertices consists of the points of the simplex whose coordinates vanish off that set.
* `TauCeti.norm_sub_le_one_of_mem_convexHull_pi_single`: points of faces of the standard
  simplex are within distance one.
* `TauCeti.exists_mem_convexHull_inter_norm_sub_le`: a point `x` of one coordinate face has a
  point of its intersection with a second face within `card ι * ‖x - y‖`, for any `y` in the
  second face.
* `TauCeti.one_le_card_mul_norm_sub_of_disjoint`: disjoint coordinate faces are at distance at
  least `(card ι)⁻¹`.
* `TauCeti.card_mul_inf'_smul_add_smul_barycenter`: `card ι` times the least coordinate recovers
  the parameter along a segment from a boundary point to the barycentre.
* `TauCeti.convexJoin_boundary_stdSimplex_barycenter`: the standard simplex is the convex join of
  its relative boundary with its barycentre.
* `TauCeti.convexJoin_facet_stdSimplex_single`: the standard simplex is the convex join of a facet
  with the opposite vertex.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2, “Pseudo-Radial Projection”, pp. 20–21.
-/

public section

open Set Finset Convexity

namespace Convexity.StdSimplex

/-- A vector is a weight vector of the standard simplex if and only if its coordinates are
nonnegative and sum to one. -/
theorem mem_range_toFun_comp_weights_iff {R : Type*} [Semiring R] [PartialOrder R]
    {X : Type*} [Fintype X] {x : X → R} :
    x ∈ (range fun t : StdSimplex R X => ⇑t.weights) ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 := by
  rw [range_toFun_comp_weights]
  simp

/-- The weight vectors of the standard simplex form a convex set. -/
theorem convex_range_toFun_comp_weights (R : Type*) [Semiring R] [PartialOrder R]
    [IsOrderedRing R] (X : Type*) :
    Convex R (range fun t : StdSimplex R X => ⇑t.weights) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ a b ha hb hab
  refine ⟨⟨a • s.weights + b • t.weights, ?_, ?_⟩, rfl⟩
  · intro x
    simpa using add_nonneg (mul_nonneg ha (s.nonneg x)) (mul_nonneg hb (t.nonneg x))
  · simp [Finsupp.sum_add_index', Finsupp.sum_smul_index', ← Finsupp.mul_sum, s.total, t.total,
      hab]

/-- The ℓᵖ norm of the weights of a standard simplex point is at most one for `1 ≤ p`. -/
theorem norm_toLp_weights_le_one {ι : Type*} [Fintype ι] {p : ENNReal} [Fact (1 ≤ p)]
    (t : StdSimplex ℝ ι) : ‖WithLp.toLp p (t.weights : ι → ℝ)‖ ≤ 1 := by
  classical
  conv_lhs => rw [pi_eq_sum_univ' (t.weights : ι → ℝ)]
  rw [WithLp.toLp_sum]
  simpa [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg (t.weights_nonneg _)] using
    norm_sum_le (Finset.univ : Finset ι)
      (fun i ↦ t.weights i • PiLp.single p i (1 : ℝ))

/-- A coordinate of a point of the standard simplex is less than one if some other coordinate
is positive. -/
theorem apply_lt_one_of_mem_range_weights {R : Type*} [Semiring R] [PartialOrder R]
    [AddLeftStrictMono R] {ι : Type*} {x : ι → R}
    (hx : x ∈ range fun s : StdSimplex R ι => ⇑s.weights) {i j : ι} (hij : j ≠ i)
    (hxj : 0 < x j) : x i < 1 := by
  classical
  have := addLeftMono_of_addLeftStrictMono R
  obtain ⟨s, rfl⟩ := hx
  -- The total weight is the sum over any finite set containing the support, here one that also
  -- contains `i` and `j`.
  have hsupp : s.weights.support ⊆ s.weights.support ∪ {i, j} := subset_union_left
  have hij' : ({i, j} : Finset ι) ⊆ s.weights.support ∪ {i, j} := subset_union_right
  have htotal := s.total
  rw [s.weights.sum_of_support_subset hsupp _ fun _ _ => rfl] at htotal
  have hle := sum_le_sum_of_subset_of_nonneg hij' fun k _ _ => s.weights_nonneg k
  rw [sum_pair hij.symm, htotal] at hle
  exact (lt_add_of_pos_right _ hxj).trans_le hle

/-- The weight vector of a convex combination of two points of the standard simplex lies on the
segment between their weight vectors. -/
theorem weights_convexCombPair_mem_segment {R : Type*} [Semiring R] [PartialOrder R]
    [IsStrictOrderedRing R] {ι : Type*} {p q : R} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (u v : StdSimplex R ι) :
    ⇑(convexCombPair p q hp hq hpq u v).weights ∈ segment R ⇑u.weights ⇑v.weights :=
  ⟨p, q, hp, hq, hpq, by simp⟩

/-- A point of the standard simplex with no weight away from `x` is the vertex `x`. -/
theorem eq_single_of_forall_ne_weights_eq_zero {R : Type*} [Semiring R] [PartialOrder R]
    [IsStrictOrderedRing R] {ι : Type*} {w : StdSimplex R ι} {x : ι}
    (h : ∀ y ≠ x, w.weights y = 0) : w = single x :=
  support_weights_eq_singleton.mp <| w.support_weights_nonempty.subset_singleton_iff.mp
    fun y hy => mem_singleton.mpr <| by_contra fun hyx => Finsupp.mem_support_iff.mp hy (h y hyx)

end Convexity.StdSimplex

/-- A linear map carrying the weight vectors of the standard simplex on `α` into those of the
standard simplex on `β` preserves coordinate sums: it sends every vertex to a vector of coordinate
sum one. -/
theorem LinearMap.sum_apply_eq_of_mapsTo_range_weights {R α β : Type*} [Semiring R]
    [PartialOrder R] [ZeroLEOneClass R] [Fintype α] [Fintype β] (L : (α → R) →ₗ[R] (β → R))
    (hL : MapsTo L (Set.range fun t : StdSimplex R α => ⇑t.weights)
      (Set.range fun t : StdSimplex R β => ⇑t.weights)) (v : α → R) :
    ∑ b, L v b = ∑ a, v a := by
  classical
  have hvert (a : α) : ∑ b, L (Pi.single a 1) b = 1 := by
    have ha : Pi.single a 1 ∈ Set.range fun t : StdSimplex R α => ⇑t.weights :=
      StdSimplex.mem_range_toFun_comp_weights_iff.2 ⟨Pi.single_nonneg.2 zero_le_one, by simp⟩
    exact (StdSimplex.mem_range_toFun_comp_weights_iff.1 (hL ha)).2
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp_rw [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hvert, mul_one]

namespace TauCeti

variable {R ι : Type*}

section Boundary

variable (R ι) in
/-- The relative boundary of the standard simplex: its points with some vanishing coordinate. -/
def stdSimplexBoundary [Semiring R] [PartialOrder R] : Set (ι → R) :=
  {y ∈ (range fun s : StdSimplex R ι => ⇑s.weights) | ∃ i, y i = 0}

variable (R ι) in
/-- The relative boundary of the standard simplex is the set of its points with some vanishing
coordinate. -/
theorem stdSimplexBoundary_def [Semiring R] [PartialOrder R] :
    stdSimplexBoundary R ι = {y ∈ (range fun s : StdSimplex R ι => ⇑s.weights) | ∃ i, y i = 0} :=
  (rfl)

/-- Membership in the relative boundary of the standard simplex. -/
@[simp]
theorem mem_stdSimplexBoundary [Semiring R] [PartialOrder R] {x : ι → R} :
    x ∈ stdSimplexBoundary R ι ↔
      x ∈ (range fun s : StdSimplex R ι => ⇑s.weights) ∧ ∃ i, x i = 0 :=
  Iff.rfl

/-- The relative boundary lies in the standard simplex. -/
theorem stdSimplexBoundary_subset [Semiring R] [PartialOrder R] :
    stdSimplexBoundary R ι ⊆ range fun s : StdSimplex R ι => ⇑s.weights :=
  fun _ hx => (mem_stdSimplexBoundary.mp hx).1

/-- A point of the standard simplex lies on its relative boundary or in its open part. -/
theorem mem_stdSimplexBoundary_or_forall_pos [Semiring R] [PartialOrder R] {x : ι → R}
    (hx : x ∈ range fun s : StdSimplex R ι => ⇑s.weights) :
    x ∈ stdSimplexBoundary R ι ∨ ∀ i, 0 < x i := by
  refine or_iff_not_imp_left.2 fun h i => ?_
  obtain ⟨s, rfl⟩ := hx
  exact (s.weights_nonneg i).lt_of_ne' fun h0 =>
    h (mem_stdSimplexBoundary.mpr ⟨mem_range_self s, i, h0⟩)

variable [Finite ι]

/-- The relative boundary of the standard simplex over an ordered semiring with continuous
addition, closed points and compact closed intervals, such as `ℝ`, is compact. -/
theorem isCompact_stdSimplexBoundary [Semiring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [TopologicalSpace R] [ContinuousAdd R] [CompactIccSpace R] [T1Space R] :
    IsCompact (stdSimplexBoundary R ι) := by
  have := Fintype.ofFinite ι
  -- The boundary is the intersection of the unit cube with a closed set.
  have hC : IsClosed
      ((fun y : ι → R => ∑ i, y i) ⁻¹' {1} ∩ ⋃ i, (fun y : ι → R => y i) ⁻¹' {0}) :=
    (isClosed_singleton.preimage (continuous_finsetSum _ fun i _ => continuous_apply i)).inter
      (isClosed_iUnion_of_finite fun i => isClosed_singleton.preimage (continuous_apply i))
  convert (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : R)) (b := 1)).inter_right hC
    using 1
  ext y
  simp only [mem_stdSimplexBoundary, StdSimplex.mem_range_toFun_comp_weights_iff, mem_inter_iff,
    mem_univ_pi, Set.mem_Icc, Set.mem_preimage, mem_singleton_iff, mem_iUnion]
  constructor
  · rintro ⟨⟨h0, h1⟩, hz⟩
    exact ⟨fun i => ⟨h0 i, h1 ▸ single_le_sum (fun j _ => h0 j) (mem_univ i)⟩, h1, hz⟩
  · rintro ⟨hI, h1, hz⟩
    exact ⟨⟨fun i => (hI i).1, h1⟩, hz⟩

end Boundary

/-- A face of the standard simplex, the convex hull of a set of vertices `Pi.single i 1`,
consists of weight vectors of `Convexity.StdSimplex`. -/
theorem convexHull_pi_single_subset_range_toFun_comp_weights [Semiring R] [PartialOrder R]
    [IsOrderedRing R] [DecidableEq ι] (s : Set ι) :
    convexHull R ((fun i : ι => Pi.single i (1 : R)) '' s) ⊆
      range fun t : StdSimplex R ι => ⇑t.weights := by
  refine convexHull_min (fun _ hi => ?_) (StdSimplex.convex_range_toFun_comp_weights R ι)
  obtain ⟨i, _, rfl⟩ := hi
  exact ⟨⟨.single i 1, by simp, by simp⟩, Finsupp.single_eq_pi_single i 1⟩

/-- Membership in a face of the standard simplex, the convex hull of a set of vertices
`Pi.single i 1`, is membership in the standard simplex together with vanishing of the coordinates
outside the face. The empty face has empty convex hull. -/
@[simp]
theorem mem_convexHull_pi_single_iff [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq ι] {s : Set ι} {x : ι → R} :
    x ∈ convexHull R ((fun i : ι => Pi.single i (1 : R)) '' s) ↔
      x ∈ (range fun t : StdSimplex R ι => ⇑t.weights) ∧ ∀ i ∉ s, x i = 0 := by
  constructor
  · intro hx
    refine ⟨convexHull_pi_single_subset_range_toFun_comp_weights s hx, fun i hi => ?_⟩
    apply convexHull_min (fun _ hz => ?_) (convex_hyperplane (LinearMap.proj i).isLinear 0) hx
    obtain ⟨j, hj, rfl⟩ := hz
    simp [ne_of_mem_of_not_mem hj hi]
  · rintro ⟨⟨t, rfl⟩, hsupp⟩
    classical
    -- Split off one vertex at a time, by induction on the number of vertices carrying weight.
    induction hn : #t.weights.support using Nat.strong_induction_on generalizing t with
    | _ n ih =>
    obtain ⟨a, ha⟩ := t.support_weights_nonempty
    have has : a ∈ s := by_contra fun h => Finsupp.mem_support_iff.mp ha (hsupp a h)
    have hva : (Pi.single a 1 : ι → R) ∈ convexHull R ((fun i : ι => Pi.single i (1 : R)) '' s) :=
      subset_convexHull R _ ⟨a, has, rfl⟩
    by_cases hs' : ∃ j ∈ ({a}ᶜ : Set ι), t.weights j ≠ 0
    · -- `t` lies on the segment from the vertex `a` to its restriction away from `a`.
      rw [← t.convexCombPair_restrict_restrict_compl {a} ⟨a, rfl, Finsupp.mem_support_iff.mp ha⟩
        hs']
      refine (convex_convexHull R _).segment_subset ?_ ?_
        (StdSimplex.weights_convexCombPair_mem_segment ..)
      · simpa [Finsupp.single_eq_pi_single] using hva
      · refine ih _ ?_ _ (fun j hj => ?_) rfl
        · rw [← hn, StdSimplex.support_weights_restrict]
          exact card_lt_card (filter_ssubset.mpr ⟨a, ha, by simp⟩)
        · exact Finsupp.notMem_support_iff.mp (by simp [hsupp j hj])
    · -- Otherwise `t` is the vertex `a`.
      push Not at hs'
      simpa [StdSimplex.eq_single_of_forall_ne_weights_eq_zero hs', Finsupp.single_eq_pi_single]
        using hva

variable [Fintype ι]

section Faces

variable [DecidableEq ι]

/-- Two points of faces of the standard simplex are within distance one in the sup norm. -/
theorem norm_sub_le_one_of_mem_convexHull_pi_single {s t : Set ι} {x y : ι → ℝ}
    (hx : x ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' s))
    (hy : y ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' t)) :
    ‖x - y‖ ≤ 1 := by
  rw [← dist_eq_norm]
  exact (Metric.dist_le_diam_of_mem (StdSimplex.isBounded_range_toFun_comp_weights ι)
    (convexHull_pi_single_subset_range_toFun_comp_weights s hx)
    (convexHull_pi_single_subset_range_toFun_comp_weights t hy)).trans
    (StdSimplex.diam_range_toFun_comp_weights_subset_closedBall ι)

/-- For points `x` and `y` of the faces spanned by `s` and `t`, every coordinate of `x` outside
`s ∩ t` is at most `‖x - y‖`: either it vanishes, or the corresponding coordinate of `y` does. -/
theorem apply_le_norm_sub_of_notMem_inter {s t : Set ι} {x y : ι → ℝ}
    (hx : x ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' s))
    (hy : y ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' t)) {i : ι}
    (hi : i ∉ s ∩ t) : x i ≤ ‖x - y‖ := by
  obtain ⟨hxS, hsupp⟩ := mem_convexHull_pi_single_iff.mp hx
  have hnonneg := (StdSimplex.mem_range_toFun_comp_weights_iff.mp hxS).1
  by_cases his : i ∈ s
  · have hyi := (mem_convexHull_pi_single_iff.mp hy).2 i fun hit => hi ⟨his, hit⟩
    simpa [hyi, abs_of_nonneg (hnonneg i)] using norm_le_pi_norm (x - y) i
  · rw [hsupp i his]
    exact norm_nonneg _

/-- Two intersecting coordinate faces admit a short route through their intersection.
The point in the intersection is within `card ι * ‖x - y‖` of `x`, including at the boundary
of either face. No positive-coordinate hypothesis is needed. -/
theorem exists_mem_convexHull_inter_norm_sub_le {σ τ : Finset ι} {x y : ι → ℝ}
    (hx : x ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (σ : Set ι)))
    (hy : y ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (τ : Set ι)))
    (hστ : (σ ∩ τ).Nonempty) :
    ∃ z ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (σ ∩ τ : Finset ι)),
      ‖x - z‖ ≤ (Fintype.card ι : ℝ) * ‖x - y‖ := by
  obtain ⟨v, hv⟩ := hστ
  obtain ⟨hnonneg, hsum⟩ := StdSimplex.mem_range_toFun_comp_weights_iff.mp
    (convexHull_pi_single_subset_range_toFun_comp_weights _ hx)
  -- Keep the coordinates in `σ ∩ τ`, and move every other coordinate to the vertex `v`.
  let r (i : ι) := if i ∈ σ ∩ τ then i else v
  have hr (i : ι) : r i ∈ σ ∩ τ := by
    simp only [r]
    split_ifs with hi
    exacts [hi, hv]
  refine ⟨∑ i, x i • Pi.single (r i) 1, (convex_convexHull ℝ _).sum_mem
    (fun i _ => hnonneg i) hsum (fun i _ => subset_convexHull ℝ _ ⟨r i, hr i, rfl⟩), ?_⟩
  have hterm (i : ι) : ‖x i • ((Pi.single i (1 : ℝ) : ι → ℝ) - Pi.single (r i) 1)‖ ≤ ‖x - y‖ := by
    by_cases hi : i ∈ σ ∩ τ
    · simp [r, Finset.mem_inter.mp hi]
    · have hxi : x i ≤ ‖x - y‖ :=
        apply_le_norm_sub_of_notMem_inter hx hy (by simpa only [← coe_inter, mem_coe] using hi)
      have he : ‖(Pi.single i (1 : ℝ) : ι → ℝ) - Pi.single (r i) 1‖ ≤ 1 :=
        norm_sub_le_one_of_mem_convexHull_pi_single (s := {i}) (t := {r i})
          (subset_convexHull ℝ _ ⟨i, rfl, rfl⟩) (subset_convexHull ℝ _ ⟨r i, rfl, rfl⟩)
      rw [norm_smul, Real.norm_of_nonneg (hnonneg i)]
      exact (mul_le_of_le_one_right (hnonneg i) he).trans hxi
  calc
    ‖x - ∑ i, x i • Pi.single (r i) 1‖ =
        ‖∑ i, x i • ((Pi.single i (1 : ℝ) : ι → ℝ) - Pi.single (r i) 1)‖ := by
      simp_rw [smul_sub]
      rw [sum_sub_distrib, ← pi_eq_sum_univ']
    _ ≤ ∑ i, ‖x i • ((Pi.single i (1 : ℝ) : ι → ℝ) - Pi.single (r i) 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖x - y‖ := sum_le_sum fun i _ => hterm i
    _ = (Fintype.card ι : ℝ) * ‖x - y‖ := by simp

/-- Disjoint coordinate faces are quantitatively separated, even if they are not maximal
faces of a complex. The estimate is uniform over all pairs of faces. -/
theorem one_le_card_mul_norm_sub_of_disjoint {σ τ : Finset ι} {x y : ι → ℝ}
    (hx : x ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (σ : Set ι)))
    (hy : y ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (τ : Set ι)))
    (hστ : Disjoint σ τ) :
    1 ≤ (Fintype.card ι : ℝ) * ‖x - y‖ := by
  calc
    1 = ∑ i, x i := (StdSimplex.mem_range_toFun_comp_weights_iff.mp
        (convexHull_pi_single_subset_range_toFun_comp_weights _ hx)).2.symm
    _ ≤ ∑ _i : ι, ‖x - y‖ := sum_le_sum fun i _ => apply_le_norm_sub_of_notMem_inter hx hy
        fun hi => disjoint_left.mp hστ hi.1 hi.2
    _ = (Fintype.card ι : ℝ) * ‖x - y‖ := by simp

end Faces

/-- Along the segment from a point `y` with nonnegative coordinates, one of them zero, to the
barycentre of the standard simplex, `card ι` times the least coordinate is the parameter `t`. -/
theorem card_mul_inf'_smul_add_smul_barycenter [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Nonempty ι] {y : ι → R} (hy : 0 ≤ y) {i : ι} (hi : y i = 0) {t : R} (ht : t ≤ 1) :
    (Fintype.card ι : R) * univ.inf' univ_nonempty
      ((1 - t) • y + t • ⇑(StdSimplex.barycenter : StdSimplex R ι).weights) = t := by
  have hc : (0 : R) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hinf : univ.inf' univ_nonempty
      ((1 - t) • y + t • ⇑(StdSimplex.barycenter : StdSimplex R ι).weights) =
      t * (Fintype.card ι : R)⁻¹ := by
    refine le_antisymm ((inf'_le _ (mem_univ i)).trans_eq
      (by simp [hi, StdSimplex.weights_barycenter_apply])) (le_inf' _ _ ?_)
    intro j _
    simpa [StdSimplex.weights_barycenter_apply] using mul_nonneg (sub_nonneg.mpr ht) (hy j)
  rw [hinf, mul_left_comm, mul_inv_cancel₀ hc.ne', mul_one]

/-- **Pseudo-radial decomposition of the standard simplex.** The standard simplex is the convex
join of its relative boundary, the points with some vanishing coordinate, with its barycentre. -/
theorem convexJoin_boundary_stdSimplex_barycenter [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Nontrivial ι] :
    convexJoin R (stdSimplexBoundary R ι) {⇑(StdSimplex.barycenter : StdSimplex R ι).weights} =
      range fun s : StdSimplex R ι => ⇑s.weights := by
  classical
  rw [stdSimplexBoundary_def]
  set c : R := (Fintype.card ι : R)
  have hc : 0 < c := Nat.cast_pos.mpr Fintype.card_pos
  have hS : (range fun s : StdSimplex R ι => ⇑s.weights) =
      {z | (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1} :=
    Set.ext fun _ => StdSimplex.mem_range_toFun_comp_weights_iff
  have hconv := StdSimplex.convex_range_toFun_comp_weights R ι
  have hbar : ⇑(StdSimplex.barycenter : StdSimplex R ι).weights = fun _ => c⁻¹ :=
    funext StdSimplex.weights_barycenter_apply
  rw [hS] at hconv
  rw [hbar, hS]
  have hb : (fun _ => c⁻¹) ∈ {z : ι → R | (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1} :=
    hbar ▸ hS ▸ mem_range_self _
  refine Subset.antisymm (convexJoin_subset (fun y hy => hy.1)
    (singleton_subset_iff.mpr hb) hconv) fun z hz => ?_
  -- Write `z` as the point at parameter `t = c * min z` on a segment from the boundary.
  set m := univ.inf' univ_nonempty z
  obtain ⟨i, -, hi⟩ := exists_mem_eq_inf' univ_nonempty z
  have hle (j : ι) : 0 ≤ z j - m := sub_nonneg.mpr (inf'_le _ (Finset.mem_univ j))
  have hsum : ∑ j, (z j - m) = 1 - c * m := by
    simp [sum_sub_distrib, hz.2, c]
  have ht : c * m ≤ 1 := by linarith [sum_nonneg fun j (_ : j ∈ Finset.univ) => hle j]
  rcases ht.lt_or_eq with ht | ht
  · have hpos : 0 < 1 - c * m := sub_pos.mpr ht
    refine mem_convexJoin.mpr ⟨(1 - c * m)⁻¹ • (z - fun _ => m), ⟨⟨fun j => ?_, ?_⟩, i, ?_⟩,
      _, rfl, 1 - c * m, c * m, hpos.le, mul_nonneg hc.le (le_inf' _ _ fun j _ => hz.1 j),
      by ring, ?_⟩
    · simpa using mul_nonneg (inv_nonneg.mpr hpos.le) (hle j)
    · simp [← mul_sum, hsum, inv_mul_cancel₀ hpos.ne']
    · simp [m, hi]
    · ext j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
  · -- At `t = 1` every coordinate is the least one, so `z` is the barycentre.
    have hzero := (sum_eq_zero_iff_of_nonneg fun j (_ : j ∈ Finset.univ) => hle j).mp (by linarith)
    have hm : m = c⁻¹ := (inv_eq_of_mul_eq_one_right ht).symm
    have hzb : z = fun _ => c⁻¹ := funext fun j => by
      linarith [hzero j (Finset.mem_univ j)]
    obtain ⟨j, k, hjk⟩ := exists_pair_ne ι
    have hj : ⇑(StdSimplex.single j : StdSimplex R ι).weights ∈
        {y ∈ {z : ι → R | (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1} | ∃ i, y i = 0} :=
      ⟨hS ▸ mem_range_self _, k, by simp [hjk]⟩
    rw [hzb]
    exact subset_convexJoin_right ⟨_, hj⟩ (mem_singleton _)

omit [Fintype ι] in
/-- **The standard simplex as a cone on a facet.** The standard simplex is the convex join of the
facet opposite a vertex `i`, the points with vanishing `i`-th coordinate, with that vertex. Along
the segment from a point of the facet to the vertex, the `i`-th coordinate is the parameter. -/
theorem convexJoin_facet_stdSimplex_single [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [Nontrivial ι] [DecidableEq ι] (i : ι) :
    convexJoin R {y ∈ range fun s : StdSimplex R ι => ⇑s.weights | y i = 0} {Pi.single i 1} =
      range fun s : StdSimplex R ι => ⇑s.weights := by
  have hb : (Pi.single i 1 : ι → R) ∈ range fun s : StdSimplex R ι => ⇑s.weights :=
    ⟨StdSimplex.single i, Finsupp.single_eq_pi_single i 1⟩
  refine Subset.antisymm (convexJoin_subset (fun y hy => hy.1) (singleton_subset_iff.mpr hb)
    (StdSimplex.convex_range_toFun_comp_weights R ι)) ?_
  rintro _ ⟨w, rfl⟩
  dsimp only
  classical
  by_cases hwi : w.weights i = 0
  · -- `w` already lies on the facet.
    exact subset_convexJoin_left (Set.singleton_nonempty _) ⟨mem_range_self w, hwi⟩
  by_cases hs : ∃ j ∈ ({i}ᶜ : Set ι), w.weights j ≠ 0
  · -- `w` lies on the segment from its restriction away from `i` to the vertex.
    rw [← w.convexCombPair_restrict_restrict_compl {i} ⟨i, rfl, hwi⟩ hs]
    have hv : ⇑(w.restrict {i} ⟨i, rfl, hwi⟩).weights ∈ ({Pi.single i 1} : Set (ι → R)) := by
      simp [Finsupp.single_eq_pi_single]
    have hf : ⇑(w.restrict {i}ᶜ hs).weights ∈
        {y ∈ range fun s : StdSimplex R ι => ⇑s.weights | y i = 0} :=
      ⟨mem_range_self _, Finsupp.notMem_support_iff.mp (by simp)⟩
    refine segment_subset_convexJoin hf hv ?_
    rw [segment_symm]
    exact StdSimplex.weights_convexCombPair_mem_segment ..
  · -- With no weight away from `i`, `w` is the vertex.
    push Not at hs
    obtain ⟨j, hj⟩ := exists_ne i
    have hj' : (Pi.single j 1 : ι → R) ∈
        {y ∈ range fun s : StdSimplex R ι => ⇑s.weights | y i = 0} :=
      ⟨⟨StdSimplex.single j, Finsupp.single_eq_pi_single j 1⟩, by simp [hj.symm]⟩
    rw [StdSimplex.eq_single_of_forall_ne_weights_eq_zero hs, StdSimplex.weights_single,
      Finsupp.single_eq_pi_single]
    exact subset_convexJoin_right ⟨_, hj'⟩ (mem_singleton _)

end TauCeti
