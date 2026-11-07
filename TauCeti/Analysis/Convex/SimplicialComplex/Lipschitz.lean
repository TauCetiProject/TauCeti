/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

/-!
# Lipschitz estimates across coordinate simplices

A common Lipschitz bound on the closed faces of a finite coordinate complex gives a global
bound for a map which vanishes at the vertices. The constant loses only a factor depending
on the number of ambient vertices, independently of the number and sizes of the faces.
This applies to interpolation errors: the interpolant and the original map agree at vertices.
In particular, it allows error estimates to cross the original faces of a complex, where a
single convex-domain pasting argument does not apply.

The geometric ingredient moves a point of one face into its intersection with another face,
by transferring the coordinates outside the second face to a common vertex. The distance
moved is bounded by the number of coordinates times the distance between the original points.

## References

* J. Munkres, *Elementary Differential Topology*, Chapter II, Section 9 (secant approximation)
  and Theorems 10.5–10.6 (smooth triangulations).
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public section

open Set Finset
open scoped NNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Membership in a face of the barycentric simplex is nonnegativity, total mass one,
and vanishing of the coordinates outside the face. The empty face has empty convex hull. -/
@[simp]
theorem mem_convexHull_pi_single_iff {σ : Finset ι} {x : ι → ℝ} :
    x ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (σ : Set ι)) ↔
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ ∀ i ∉ σ, x i = 0 := by
  constructor
  · intro hx
    have hsimplex : (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 := by
      have hr : x ∈ range (fun t : Convexity.StdSimplex ℝ ι => ⇑t.weights) := by
        apply convexHull_min (fun _ hi => ?_)
          (Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ ι) hx
        obtain ⟨i, _, rfl⟩ := hi
        exact ⟨Convexity.StdSimplex.single i, by
          ext j
          simp [Finsupp.single_apply, Pi.single_apply, eq_comm]⟩
      obtain ⟨t, rfl⟩ := hr
      exact ⟨t.weights_nonneg, t.total_of_fintype⟩
    refine ⟨hsimplex.1, hsimplex.2, fun i hi => ?_⟩
    apply convexHull_min (fun _ hz => ?_) (convex_hyperplane (LinearMap.proj i).isLinear 0) hx
    obtain ⟨j, hj, rfl⟩ := hz
    simp [ne_of_mem_of_not_mem hj hi]
  · rintro ⟨hnonneg, hsum, hsupp⟩
    have hsumσ : ∑ i ∈ σ, x i = 1 := by
      rwa [← Finset.sum_subset (Finset.subset_univ σ) (fun i _ hi => hsupp i hi)] at hsum
    have hrepr : ∑ i ∈ σ, x i • Pi.single i (1 : ℝ) = x := by
      calc
        _ = ∑ i, x i • Pi.single i (1 : ℝ) :=
          Finset.sum_subset (Finset.subset_univ σ) (fun i _ hi => by simp [hsupp i hi])
        _ = x := (pi_eq_sum_univ' x).symm
    rw [← hrepr]
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hnonneg i) hsumσ
      (fun i hi => subset_convexHull ℝ _ ⟨i, hi, rfl⟩)

private theorem norm_sub_pi_single_le_one {σ : Finset ι} {x : ι → ℝ}
    (hx : x ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (σ : Set ι))) (v : ι) :
    ‖x - Pi.single v 1‖ ≤ 1 := by
  have hmem : x ∈ range (fun t : Convexity.StdSimplex ℝ ι => ⇑t.weights) := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    simpa only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] using
      (mem_convexHull_pi_single_iff.mp hx).imp_right And.left
  have hv : Pi.single v (1 : ℝ) ∈
      range (fun t : Convexity.StdSimplex ℝ ι => ⇑t.weights) :=
    ⟨Convexity.StdSimplex.single v, by ext j; simp [Finsupp.single_apply, Pi.single_apply, eq_comm]⟩
  exact (Metric.dist_le_diam_of_mem
    (Convexity.StdSimplex.isBounded_range_toFun_comp_weights ι) hmem hv).trans
      (Convexity.StdSimplex.diam_range_toFun_comp_weights_subset_closedBall ι)

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
  obtain ⟨hvσ, hvτ⟩ := Finset.mem_inter.mp hv
  obtain ⟨hnonneg, hsum, hsupp⟩ := mem_convexHull_pi_single_iff.mp hx
  have hysupp := (mem_convexHull_pi_single_iff.mp hy).2.2
  let r (i : ι) := if i ∈ τ then i else v
  let z : ι → ℝ := ∑ i ∈ σ, x i • Pi.single (r i) 1
  have hsumσ : ∑ i ∈ σ, x i = 1 := by
    rwa [← Finset.sum_subset (Finset.subset_univ σ) (fun i _ hi => hsupp i hi)] at hsum
  refine ⟨z, (convex_convexHull ℝ _).sum_mem (fun i _ => hnonneg i) hsumσ ?_, ?_⟩
  · intro i hi
    apply subset_convexHull ℝ _
    exact ⟨r i, by by_cases hit : i ∈ τ <;> simp [r, hit, hi, hvσ, hvτ], rfl⟩
  · have hrepr : ∑ i ∈ σ, x i • Pi.single i (1 : ℝ) = x := by
      calc
        _ = ∑ i, x i • Pi.single i (1 : ℝ) :=
          Finset.sum_subset (Finset.subset_univ σ) (fun i _ hi => by simp [hsupp i hi])
        _ = x := (pi_eq_sum_univ' x).symm
    have hterm (i : ι) : ‖x i • ((Pi.single i (1 : ℝ) : ι → ℝ) - Pi.single (r i) 1)‖ ≤ ‖x - y‖ := by
      by_cases hit : i ∈ τ
      · simp [r, hit]
      · have hxi : x i ≤ ‖x - y‖ := by
          have h := norm_le_pi_norm (x - y) i
          simpa [hysupp i hit, abs_of_nonneg (hnonneg i)] using h
        have he : ‖(Pi.single i (1 : ℝ) : ι → ℝ) - Pi.single (r i) 1‖ ≤ 1 :=
          norm_sub_pi_single_le_one (σ := {i})
            (subset_convexHull ℝ _ ⟨i, by simp, rfl⟩) (r i)
        rw [norm_smul, Real.norm_of_nonneg (hnonneg i)]
        exact (mul_le_mul_of_nonneg_left he (hnonneg i)).trans (by simpa using hxi)
    calc
      ‖x - z‖ = ‖∑ i ∈ σ, x i • ((Pi.single i (1 : ℝ) : ι → ℝ) - Pi.single (r i) 1)‖ := by
        simp_rw [smul_sub]
        rw [sum_sub_distrib, hrepr]
      _ ≤ ∑ i ∈ σ, ‖x i • ((Pi.single i (1 : ℝ) : ι → ℝ) - Pi.single (r i) 1)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ σ, ‖x - y‖ := sum_le_sum fun i _ => hterm i
      _ ≤ (Fintype.card ι : ℝ) * ‖x - y‖ := by
        simpa using mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr (card_le_univ σ) : (σ.card : ℝ) ≤ Fintype.card ι) (norm_nonneg _)

/-- Disjoint coordinate faces are quantitatively separated, even if they are not maximal
faces of a complex. The estimate is uniform over all pairs of faces. -/
theorem one_le_card_mul_norm_sub_of_disjoint {σ τ : Finset ι} {x y : ι → ℝ}
    (hx : x ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (σ : Set ι)))
    (hy : y ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (τ : Set ι)))
    (hστ : Disjoint σ τ) :
    1 ≤ (Fintype.card ι : ℝ) * ‖x - y‖ := by
  obtain ⟨hnn, hsum, hsupp⟩ := mem_convexHull_pi_single_iff.mp hx
  have hysupp := (mem_convexHull_pi_single_iff.mp hy).2.2
  have hle (i : ι) : x i ≤ ‖x - y‖ := by
    by_cases hi : i ∈ σ
    · have hyi := hysupp i (Finset.disjoint_left.mp hστ hi)
      simpa [hyi, abs_of_nonneg (hnn i)] using norm_le_pi_norm (x - y) i
    · rw [hsupp i hi]
      exact norm_nonneg _
  calc
    1 = ∑ i, x i := hsum.symm
    _ ≤ ∑ i : ι, ‖x - y‖ := sum_le_sum fun i _ => hle i
    _ = (Fintype.card ι : ℝ) * ‖x - y‖ := by simp

private theorem dist_le_lipschitz_constant {Y : Type*} [PseudoMetricSpace Y]
    {f : (ι → ℝ) → Y} {C : ℝ≥0} {b : Y} {σ : Finset ι} {x : ι → ℝ}
    (hx : x ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (σ : Set ι)))
    (hf : LipschitzOnWith C f
      (convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (σ : Set ι))))
    (hb : ∀ i ∈ σ, f (Pi.single i 1) = b) : dist (f x) b ≤ C := by
  obtain ⟨v, hv⟩ := (convexHull_nonempty_iff.mp ⟨x, hx⟩)
  obtain ⟨i, hi, rfl⟩ := hv
  have h := hf.dist_le_mul x hx (Pi.single i 1) (subset_convexHull ℝ _ ⟨i, hi, rfl⟩)
  rw [hb i hi] at h
  exact h.trans (mul_le_of_le_one_right C.coe_nonneg
    (by simpa only [dist_eq_norm] using norm_sub_pi_single_le_one hx i))

/-- A common facewise Lipschitz bound gives a global bound on a union of coordinate faces
for maps taking the same value at all vertices. The loss depends only on the ambient vertex
count, and the union need not be connected, pure, or closed under taking faces. This is useful
for interpolation errors, whose vertex values are zero. -/
theorem lipschitzOnWith_iUnion_convexHull_pi_single {Y : Type*} [PseudoMetricSpace Y]
    {S : Set (Finset ι)} {f : (ι → ℝ) → Y} {C : ℝ≥0} {b : Y}
    (hf : ∀ σ ∈ S, LipschitzOnWith C f
      (convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (σ : Set ι))))
    (hb : ∀ σ ∈ S, ∀ i ∈ σ, f (Pi.single i 1) = b) :
    LipschitzOnWith ((2 * Fintype.card ι + 1 : ℝ≥0) * C) f
      (⋃ σ ∈ S, convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (σ : Set ι))) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro x hx y hy
  obtain ⟨σ, hσ, hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨τ, hτ, hy⟩ := mem_iUnion₂.mp hy
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_ofNat,
    NNReal.coe_one, dist_eq_norm]
  rcases (σ ∩ τ).eq_empty_or_nonempty with hdis | hinter
  · have hsep := one_le_card_mul_norm_sub_of_disjoint hx hy
      (Finset.disjoint_iff_inter_eq_empty.mpr hdis)
    have hxbound := dist_le_lipschitz_constant hx (hf σ hσ) (hb σ hσ)
    have hybound := dist_le_lipschitz_constant hy (hf τ hτ) (hb τ hτ)
    have htriangle := dist_triangle (f x) b (f y)
    rw [dist_comm b] at htriangle
    nlinarith [C.coe_nonneg, norm_nonneg (x - y)]
  · obtain ⟨z, hz, hxz⟩ := exists_mem_convexHull_inter_norm_sub_le hx hy hinter
    have hzσ := convexHull_mono (image_mono (Finset.coe_subset.mpr Finset.inter_subset_left)) hz
    have hzτ := convexHull_mono (image_mono (Finset.coe_subset.mpr Finset.inter_subset_right)) hz
    have hxbound := (hf σ hσ).dist_le_mul x hx z hzσ
    have hybound := (hf τ hτ).dist_le_mul z hzτ y hy
    have hzy : ‖z - y‖ ≤ (Fintype.card ι + 1 : ℝ) * ‖x - y‖ := by
      have h := norm_sub_le_norm_sub_add_norm_sub z x y
      rw [norm_sub_rev z x] at h
      nlinarith
    have htriangle := dist_triangle (f x) (f z) (f y)
    simp only [dist_eq_norm] at hxbound hybound
    nlinarith [mul_le_mul_of_nonneg_left hxz C.coe_nonneg,
      mul_le_mul_of_nonneg_left hzy C.coe_nonneg]

end TauCeti
