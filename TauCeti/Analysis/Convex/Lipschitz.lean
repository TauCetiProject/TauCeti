/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import TauCeti.Analysis.Convex.StdSimplex

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.IntermediateValue

/-!
# Lipschitz estimates across a finite closed cover and across coordinate faces

A common Lipschitz bound on the members of a finite closed cover of a convex set holds
on the whole set. The covering sets need not themselves be convex. This permits estimates
for piecewise smooth maps to pass across the boundaries of their pieces without a loss
in the constant. In particular, derivative estimates on the simplices of a subdivision
give a Lipschitz estimate for the assembled secant error.

The local-to-global argument uses continuous induction along a line segment. The local
hypothesis only compares nearby points with the centre of each neighbourhood; it does not
require a Lipschitz estimate between every pair in that neighbourhood.

A union of closed coordinate faces of the standard simplex need not be convex. Still, a common
Lipschitz bound on the faces gives a global bound for a map which takes one common value at
the vertices. The constant loses only a factor depending on the number of ambient vertices,
independently of the number and sizes of the faces. This applies to interpolation errors: the
interpolant and the original map agree at vertices. In particular, it allows error estimates to
cross the original faces of a complex, where a single convex-domain pasting argument does not
apply. The geometric ingredient moves a point of one face into its intersection with another
face, by transferring the coordinates outside the intersection to a common vertex. The distance
moved is bounded by the number of coordinates times the distance between the original points.

## References

* J. Munkres, *Elementary Differential Topology*, Chapter II, Section 9, for the use of
  piecewise derivative estimates in secant approximation, and Theorems 10.5–10.6 (smooth
  triangulations).
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public section

open Set Filter Topology
open scoped NNReal

namespace Convex

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [PseudoMetricSpace Y] {s : Set E} {f : E → Y} {K : ℝ≥0}

/-- A uniform local bound on distances from each centre gives the same global Lipschitz
bound on a convex set. -/
theorem lipschitzOnWith_of_locally_dist_le (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, ∀ᶠ y in 𝓝[s] x, dist (f y) (f x) ≤ K * dist y x) :
    LipschitzOnWith K f s := by
  have hcont : ContinuousOn f s := fun x hx =>
    tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero'
      (Eventually.of_forall fun _ => dist_nonneg) (hf x hx) (by
        simpa using (tendsto_const_nhds.mul
          ((continuous_id.dist continuous_const).continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds) :
          Tendsto (fun y : E => (K : ℝ) * dist y x) (𝓝[s] x) (𝓝 ((K : ℝ) * dist x x))))
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  let γ : ℝ → E := AffineMap.lineMap x y
  have hγ : Continuous γ := (lipschitzWith_lineMap x y).continuous
  have hγs : MapsTo γ (Icc 0 1) s := fun _ ht => hs.lineMap_mem hx hy ht
  let A : Set ℝ := {t | dist (f (γ t)) (f x) ≤ (K : ℝ) * t * dist x y}
  have hclosed : IsClosed (A ∩ Icc 0 1) := by
    have hdist : ContinuousOn (fun t => dist (f (γ t)) (f x)) (Icc 0 1) :=
      continuous_dist.comp_continuousOn
        ((hcont.comp hγ.continuousOn hγs).prodMk continuousOn_const)
    convert isClosed_Icc.isClosed_le hdist
      (by fun_prop : ContinuousOn (fun t : ℝ => (K : ℝ) * t * dist x y) (Icc 0 1)) using 1
    ext t
    exact and_comm
  have hzero : (0 : ℝ) ∈ A := by simp [A, γ]
  have hstep : ∀ t ∈ A ∩ Ico 0 1, A ∈ 𝓝[>] t := by
    rintro t ⟨htA, ht⟩
    have hlocal := (hγ.continuousWithinAt.tendsto_nhdsWithin hγs).eventually
      (hf (γ t) (hγs (Ico_subset_Icc_self ht)))
    have hlocal' : ∀ᶠ u in 𝓝[>] t,
        dist (f (γ u)) (f (γ t)) ≤ K * dist (γ u) (γ t) :=
      nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ht) hlocal
    filter_upwards [hlocal', self_mem_nhdsWithin] with u hu htu
    have hd : dist (γ u) (γ t) = (u - t) * dist x y := by
      simp only [γ, dist_lineMap_lineMap, Real.dist_eq,
        abs_of_pos (sub_pos.mpr htu)]
    have htri := dist_triangle (f (γ u)) (f (γ t)) (f x)
    simp only [A, mem_ofPred_eq] at htA ⊢
    rw [hd] at hu
    nlinarith
  have hone := hclosed.Icc_subset_of_forall_mem_nhdsWithin hzero hstep
    (right_mem_Icc.mpr zero_le_one)
  simpa [A, γ, dist_comm] using hone

/-- Lipschitz estimates with the same constant on a finite closed cover of a convex set
glue with no loss in that constant. Neither the pieces nor their intersections with the
convex set are required to be convex. -/
theorem lipschitzOnWith_of_finite_closed_cover {ι : Type*} [Finite ι]
    (hs : Convex ℝ s) (C : ι → Set E) (hC : ∀ i, IsClosed (C i))
    (hcover : s ⊆ ⋃ i, C i) (hf : ∀ i, LipschitzOnWith K f (s ∩ C i)) :
    LipschitzOnWith K f s := by
  classical
  refine hs.lipschitzOnWith_of_locally_dist_le fun x hx => ?_
  have hnear : ∀ᶠ y in 𝓝 x, ∀ i, y ∈ C i → x ∈ C i :=
    eventually_all.mpr fun i => by
      by_cases hi : x ∈ C i
      · exact Eventually.of_forall fun _ _ => hi
      · filter_upwards [(hC i).isOpen_compl.mem_nhds hi] with y hy hmem
        exact (hy hmem).elim
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hys
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hys)
  exact (hf i).dist_le_mul y ⟨hys, hi⟩ x ⟨hx, hy i hi⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Piecewise derivative bounds relative to a fixed linear map give a global linear
approximation on a convex set. The map need not be differentiable across the seams of
the finite closed convex cover. -/
theorem approximatesLinearOn_of_finite_closed_cover {ι : Type*} [Finite ι]
    {g : E → F} {A : E →L[ℝ] F} {ε : ℝ≥0}
    (hs : Convex ℝ s) (C : ι → Set E) (hC : ∀ i, IsClosed (C i))
    (hconv : ∀ i, Convex ℝ (s ∩ C i)) (hcover : s ⊆ ⋃ i, C i)
    (D : ι → E → E →L[ℝ] F)
    (hg : ∀ i, ∀ x ∈ s ∩ C i, HasFDerivWithinAt g (D i x) (s ∩ C i) x)
    (hbound : ∀ i, ∀ x ∈ s ∩ C i, ‖D i x - A‖₊ ≤ ε) :
    ApproximatesLinearOn g A s ε := by
  apply LipschitzOnWith.approximatesLinearOn
  refine hs.lipschitzOnWith_of_finite_closed_cover C hC hcover fun i => ?_
  exact (hconv i).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (hg i x hx).sub A.hasFDerivWithinAt) (hbound i)

end Convex

namespace TauCeti

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem norm_sub_pi_single_le_one {s : Set ι} {x : ι → ℝ}
    (hx : x ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' s)) (v : ι) :
    ‖x - Pi.single v 1‖ ≤ 1 := by
  have hmem {s : Set ι} {x : ι → ℝ}
      (hx : x ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' s)) :
      x ∈ range (fun t : Convexity.StdSimplex ℝ ι => ⇑t.weights) := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    simpa only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] using
      (mem_convexHull_pi_single_iff.mp hx).imp_right And.left
  exact (Metric.dist_le_diam_of_mem (Convexity.StdSimplex.isBounded_range_toFun_comp_weights ι)
    (hmem hx) (hmem (s := {v}) (subset_convexHull ℝ _ ⟨v, rfl, rfl⟩))).trans
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
  obtain ⟨hnonneg, hsum, hsupp⟩ := mem_convexHull_pi_single_iff.mp hx
  have hysupp := (mem_convexHull_pi_single_iff.mp hy).2.2
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
    · simp [show r i = i from ite_eq_left hi]
    · have hxi : x i ≤ ‖x - y‖ := by
        by_cases hiσ : i ∈ σ
        · have hiτ : i ∉ τ := fun hiτ => hi (mem_inter.mpr ⟨hiσ, hiτ⟩)
          simpa [hysupp i hiτ, abs_of_nonneg (hnonneg i)] using norm_le_pi_norm (x - y) i
        · rw [hsupp i hiσ]
          exact norm_nonneg _
      have he : ‖(Pi.single i (1 : ℝ) : ι → ℝ) - Pi.single (r i) 1‖ ≤ 1 :=
        norm_sub_pi_single_le_one (s := {i}) (subset_convexHull ℝ _ ⟨i, rfl, rfl⟩) (r i)
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
    linarith [mul_le_mul_of_nonneg_left hsep C.coe_nonneg,
      mul_nonneg C.coe_nonneg (norm_nonneg (x - y))]
  · obtain ⟨z, hz, hxz⟩ := exists_mem_convexHull_inter_norm_sub_le hx hy hinter
    have hzσ := convexHull_mono (image_mono (Finset.coe_subset.mpr Finset.inter_subset_left)) hz
    have hzτ := convexHull_mono (image_mono (Finset.coe_subset.mpr Finset.inter_subset_right)) hz
    have hxbound := (hf σ hσ).dist_le_mul x hx z hzσ
    have hybound := (hf τ hτ).dist_le_mul z hzτ y hy
    have hzy : ‖z - y‖ ≤ (Fintype.card ι + 1 : ℝ) * ‖x - y‖ := by
      have h := norm_sub_le_norm_sub_add_norm_sub z x y
      rw [norm_sub_rev z x] at h
      linarith [hxz]
    have htriangle := dist_triangle (f x) (f z) (f y)
    simp only [dist_eq_norm] at hxbound hybound
    linarith [mul_le_mul_of_nonneg_left hxz C.coe_nonneg,
      mul_le_mul_of_nonneg_left hzy C.coe_nonneg]

end TauCeti
