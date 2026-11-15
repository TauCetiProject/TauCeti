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
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The standard simplex as a join with its barycentre or a vertex

The standard simplex, the set of weight vectors of `Convexity.StdSimplex ℝ ι`, is the convex join
of its relative boundary, the points with some vanishing coordinate, and its barycentre, the
constant point `(card ι)⁻¹`. Along the segment from a boundary point to the barycentre, the
position is recovered as `card ι` times the least coordinate. So the segments meet only at the
barycentre, and every point of the simplex other than the barycentre lies on exactly one of them.

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
* `TauCeti.stdSimplexBoundary`, `TauCeti.isCompact_stdSimplexBoundary`: the relative boundary of
  the standard simplex, the points with some vanishing coordinate, and its compactness.
* `TauCeti.mem_convexHull_pi_single_iff`: membership in the face of the standard simplex spanned
  by a set of vertices, in coordinates.
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

/-- A coordinate of a point of the standard simplex is less than one if some other coordinate
is positive. -/
theorem apply_lt_one_of_mem_range_weights {R : Type*} [Semiring R] [LinearOrder R]
    [IsStrictOrderedRing R] {ι : Type*} [Finite ι] {x : ι → R}
    (hx : x ∈ range fun s : StdSimplex R ι => ⇑s.weights) {i j : ι} (hij : j ≠ i)
    (hxj : 0 < x j) : x i < 1 := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨hx0, hx1⟩ := mem_range_toFun_comp_weights_iff.1 hx
  have := sum_le_sum_of_subset_of_nonneg (subset_univ {i, j}) fun k _ _ => hx0 k
  rw [sum_pair hij.symm, hx1] at this
  exact (lt_add_of_pos_right (x i) hxj).trans_le this

end Convexity.StdSimplex

namespace TauCeti

variable {ι : Type*}

section Boundary

variable (ι) in
/-- The relative boundary of the standard simplex: its points with some vanishing coordinate. -/
def stdSimplexBoundary : Set (ι → ℝ) :=
  {y ∈ (range fun s : StdSimplex ℝ ι => ⇑s.weights) | ∃ i, y i = 0}

variable (ι) in
/-- The relative boundary of the standard simplex is the set of its points with some vanishing
coordinate. -/
theorem stdSimplexBoundary_def :
    stdSimplexBoundary ι = {y ∈ (range fun s : StdSimplex ℝ ι => ⇑s.weights) | ∃ i, y i = 0} :=
  (rfl)

/-- Membership in the relative boundary of the standard simplex. -/
@[simp]
theorem mem_stdSimplexBoundary {x : ι → ℝ} :
    x ∈ stdSimplexBoundary ι ↔ x ∈ (range fun s : StdSimplex ℝ ι => ⇑s.weights) ∧ ∃ i, x i = 0 :=
  Iff.rfl

/-- The relative boundary lies in the standard simplex. -/
theorem stdSimplexBoundary_subset :
    stdSimplexBoundary ι ⊆ range fun s : StdSimplex ℝ ι => ⇑s.weights :=
  fun _ hx => hx.1

variable [Finite ι]

/-- The relative boundary of the standard simplex is compact. -/
theorem isCompact_stdSimplexBoundary : IsCompact (stdSimplexBoundary ι) := by
  have hZ : IsClosed {y : ι → ℝ | ∃ i, y i = 0} := by
    simpa only [ofPred_exists] using
      isClosed_iUnion_of_finite fun i => isClosed_eq (continuous_apply i) continuous_const
  exact (isCompact_range (StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous).inter_right
    hZ

/-- A point of the standard simplex lies on its relative boundary or in its open part. -/
theorem mem_stdSimplexBoundary_or_forall_pos {x : ι → ℝ}
    (hx : x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) :
    x ∈ stdSimplexBoundary ι ∨ ∀ i, 0 < x i := by
  have := Fintype.ofFinite ι
  by_cases h : ∀ i, 0 < x i
  · exact Or.inr h
  · obtain ⟨i, hi⟩ := not_forall.1 h
    exact Or.inl ⟨hx, i,
      le_antisymm (not_lt.1 hi) ((StdSimplex.mem_range_toFun_comp_weights_iff.1 hx).1 i)⟩

end Boundary

/-- A face of the standard simplex, the convex hull of a set of vertices `Pi.single i 1`,
consists of weight vectors of `Convexity.StdSimplex`. -/
theorem convexHull_pi_single_subset_range_toFun_comp_weights [DecidableEq ι] (s : Set ι) :
    convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' s) ⊆
      range fun t : StdSimplex ℝ ι => ⇑t.weights := by
  refine convexHull_min (fun _ hi => ?_) (StdSimplex.convex_range_toFun_comp_weights ℝ ι)
  obtain ⟨i, _, rfl⟩ := hi
  exact ⟨StdSimplex.single i, by
    ext j
    simp [Finsupp.single_apply, Pi.single_apply, eq_comm]⟩

variable [Fintype ι]

/-- Membership in a face of the standard simplex is nonnegativity, total mass one,
and vanishing of the coordinates outside the face. The empty face has empty convex hull. -/
@[simp]
theorem mem_convexHull_pi_single_iff [DecidableEq ι] {s : Set ι} {x : ι → ℝ} :
    x ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' s) ↔
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ ∀ i ∉ s, x i = 0 := by
  constructor
  · intro hx
    have hsimplex : (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 :=
      StdSimplex.mem_range_toFun_comp_weights_iff.1
        (convexHull_pi_single_subset_range_toFun_comp_weights s hx)
    refine ⟨hsimplex.1, hsimplex.2, fun i hi => ?_⟩
    apply convexHull_min (fun _ hz => ?_) (convex_hyperplane (LinearMap.proj i).isLinear 0) hx
    obtain ⟨j, hj, rfl⟩ := hz
    simp [ne_of_mem_of_not_mem hj hi]
  · rintro ⟨hnonneg, hsum, hsupp⟩
    classical
    have hmem (i : ι) (hi : x i ≠ 0) : i ∈ s := by_contra fun his => hi (hsupp i his)
    have hsums : ∑ i ∈ univ with i ∈ s, x i = 1 := by
      rw [sum_filter_of_ne fun i _ => hmem i, hsum]
    have hrepr : ∑ i ∈ univ with i ∈ s, x i • Pi.single i (1 : ℝ) = x := by
      rw [sum_filter_of_ne fun i _ hi => hmem i (left_ne_zero_of_smul hi), ← pi_eq_sum_univ']
    rw [← hrepr]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hnonneg i) hsums
      (fun i hi => subset_convexHull ℝ _ ⟨i, (mem_filter.mp hi).2, rfl⟩)

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
  obtain ⟨hnonneg, -, hsupp⟩ := mem_convexHull_pi_single_iff.mp hx
  by_cases his : i ∈ s
  · have hyi := (mem_convexHull_pi_single_iff.mp hy).2.2 i fun hit => hi ⟨his, hit⟩
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
  obtain ⟨hnonneg, hsum, -⟩ := mem_convexHull_pi_single_iff.mp hx
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
    1 = ∑ i, x i := (mem_convexHull_pi_single_iff.mp hx).2.1.symm
    _ ≤ ∑ _i : ι, ‖x - y‖ := sum_le_sum fun i _ => apply_le_norm_sub_of_notMem_inter hx hy
        fun hi => disjoint_left.mp hστ hi.1 hi.2
    _ = (Fintype.card ι : ℝ) * ‖x - y‖ := by simp

end Faces

/-- Along the segment from a point `y` with nonnegative coordinates, one of them zero, to the
barycentre of the standard simplex, `card ι` times the least coordinate is the parameter `t`. -/
theorem card_mul_inf'_smul_add_smul_barycenter [Nonempty ι] {y : ι → ℝ} (hy : 0 ≤ y) {i : ι}
    (hi : y i = 0) {t : ℝ} (ht : t ≤ 1) :
    (Fintype.card ι : ℝ) * univ.inf' univ_nonempty
      ((1 - t) • y + t • ⇑(StdSimplex.barycenter : StdSimplex ℝ ι).weights) = t := by
  have hc : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hinf : univ.inf' univ_nonempty
      ((1 - t) • y + t • ⇑(StdSimplex.barycenter : StdSimplex ℝ ι).weights) =
      t * (Fintype.card ι : ℝ)⁻¹ := by
    refine le_antisymm ((inf'_le _ (mem_univ i)).trans_eq
      (by simp [hi, StdSimplex.weights_barycenter_apply])) (le_inf' _ _ ?_)
    intro j _
    simpa [StdSimplex.weights_barycenter_apply] using mul_nonneg (sub_nonneg.mpr ht) (hy j)
  rw [hinf, mul_left_comm, mul_inv_cancel₀ hc.ne', mul_one]

/-- **Pseudo-radial decomposition of the standard simplex.** The standard simplex is the convex
join of its relative boundary, the points with some vanishing coordinate, with its barycentre. -/
theorem convexJoin_boundary_stdSimplex_barycenter [Nontrivial ι] :
    convexJoin ℝ (stdSimplexBoundary ι) {⇑(StdSimplex.barycenter : StdSimplex ℝ ι).weights} =
      range fun s : StdSimplex ℝ ι => ⇑s.weights := by
  classical
  rw [stdSimplexBoundary_def]
  set c : ℝ := (Fintype.card ι : ℝ)
  have hc : 0 < c := Nat.cast_pos.mpr Fintype.card_pos
  have hS : (range fun s : StdSimplex ℝ ι => ⇑s.weights) =
      {z | (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1} := by
    rw [StdSimplex.range_toFun_comp_weights]
    ext z
    simp
  have hconv := StdSimplex.convex_range_toFun_comp_weights ℝ ι
  have hbar : ⇑(StdSimplex.barycenter : StdSimplex ℝ ι).weights = fun _ => c⁻¹ :=
    funext StdSimplex.weights_barycenter_apply
  rw [hS] at hconv
  rw [hbar, hS]
  have hb : (fun _ => c⁻¹) ∈ {z : ι → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1} :=
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
    have hj : ⇑(StdSimplex.single j : StdSimplex ℝ ι).weights ∈
        {y ∈ {z : ι → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1} | ∃ i, y i = 0} :=
      ⟨hS ▸ mem_range_self _, k, by simp [hjk]⟩
    rw [hzb]
    exact subset_convexJoin_right ⟨_, hj⟩ (mem_singleton _)

omit [Fintype ι] in
/-- **The standard simplex as a cone on a facet.** The standard simplex is the convex join of the
facet opposite a vertex `i`, the points with vanishing `i`-th coordinate, with that vertex. Along
the segment from a point of the facet to the vertex, the `i`-th coordinate is the parameter. -/
theorem convexJoin_facet_stdSimplex_single {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [Finite ι] [Nontrivial ι] [DecidableEq ι] (i : ι) :
    convexJoin R {y ∈ range fun s : StdSimplex R ι => ⇑s.weights | y i = 0} {Pi.single i 1} =
      range fun s : StdSimplex R ι => ⇑s.weights := by
  have := Fintype.ofFinite ι
  have hS : (range fun s : StdSimplex R ι => ⇑s.weights) =
      {z | (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1} := by
    rw [StdSimplex.range_toFun_comp_weights]
    ext z
    simp
  have hconv := StdSimplex.convex_range_toFun_comp_weights R ι
  rw [hS] at hconv
  rw [hS]
  have hb : (Pi.single i 1 : ι → R) ∈ {z : ι → R | (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1} :=
    ⟨fun j => by rcases eq_or_ne j i with rfl | hj <;> simp [*], by simp⟩
  refine Subset.antisymm (convexJoin_subset (fun y hy => hy.1)
    (singleton_subset_iff.mpr hb) hconv) fun z hz => ?_
  have hle : z i ≤ 1 := by
    rw [← hz.2]
    exact single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ i)
  rcases hle.lt_or_eq with ht | ht
  · -- Write `z` as the point at parameter `z i` on a segment from the facet.
    have hpos : 0 < 1 - z i := sub_pos.mpr ht
    refine mem_convexJoin.mpr ⟨(1 - z i)⁻¹ • (z - z i • Pi.single i 1), ⟨⟨fun j => ?_, ?_⟩, ?_⟩,
      _, rfl, 1 - z i, z i, hpos.le, hz.1 i, by ring, ?_⟩
    · rcases eq_or_ne j i with rfl | hj
      · simp
      · simpa [hj] using mul_nonneg (inv_nonneg.mpr hpos.le) (hz.1 j)
    · simp [← mul_sum, sum_sub_distrib, hz.2, inv_mul_cancel₀ hpos.ne']
    · simp
    · ext j
      rcases eq_or_ne j i with rfl | hj
      · simp
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_eq_of_ne hj]
        field_simp
        ring
  · -- At parameter one every other coordinate vanishes, so `z` is the vertex.
    have hzero : ∀ j ∈ univ.erase i, z j = 0 := by
      refine (sum_eq_zero_iff_of_nonneg fun j _ => hz.1 j).mp ?_
      linarith [add_sum_erase univ z (Finset.mem_univ i), hz.2]
    have hzi : z = Pi.single i 1 := funext fun j => by
      rcases eq_or_ne j i with rfl | hj
      · simp [ht]
      · simp [hj, hzero j (mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)]
    obtain ⟨j, hj⟩ := exists_ne i
    have hj' : (Pi.single j 1 : ι → R) ∈
        {y ∈ {z : ι → R | (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1} | y i = 0} :=
      ⟨⟨fun k => by rcases eq_or_ne k j with rfl | hk <;> simp [*], by simp⟩, by simp [hj.symm]⟩
    rw [hzi]
    exact subset_convexJoin_right ⟨_, hj'⟩ (mem_singleton _)

end TauCeti
