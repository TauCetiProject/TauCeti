/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Join
public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
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

## Main results

* `Convexity.StdSimplex.convex_range_toFun_comp_weights`: the weight vectors of the standard
  simplex form a convex set.
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

/-- The weight vectors of the standard simplex on a finite type form a convex set. -/
theorem convex_range_toFun_comp_weights (R : Type*) [Semiring R] [PartialOrder R]
    [IsOrderedRing R] (X : Type*) [Finite X] :
    Convex R (range fun t : StdSimplex R X => ⇑t.weights) := by
  have := Fintype.ofFinite X
  rw [range_toFun_comp_weights]
  exact (convex_iInter fun i => convex_halfSpace_ge (LinearMap.proj i).isLinear 0).inter
    (by simpa using
      convex_hyperplane (∑ i, LinearMap.proj (R := R) (φ := fun _ : X => R) i).isLinear 1)

end Convexity.StdSimplex

namespace TauCeti

variable {ι : Type*} [Fintype ι]

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
    convexJoin ℝ {y ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights | ∃ i, y i = 0}
      {⇑(StdSimplex.barycenter : StdSimplex ℝ ι).weights} =
      range fun s : StdSimplex ℝ ι => ⇑s.weights := by
  classical
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
