/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import TauCeti.Analysis.Convex.StdSimplex
import Mathlib.Tactic.Linarith

/-!
# Lipschitz estimates across coordinate faces of the standard simplex

A union of closed coordinate faces of the standard simplex need not be convex, so the
finite-closed-cover gluing of `TauCeti.Analysis.Convex.Lipschitz` does not apply to it. Still, a
common Lipschitz bound on the faces gives a global bound for a map which takes one common value
at the vertices (`TauCeti.lipschitzOnWith_biUnion_convexHull_pi_single`). The constant loses only
a factor depending on the number of ambient vertices, independently of the number and sizes of
the faces. This applies to interpolation errors: the interpolant and the original map agree at
vertices. In particular, it allows error estimates to cross the original faces of a complex.

Points of intersecting faces are compared through a nearby point of the common face
(`TauCeti.exists_mem_convexHull_inter_norm_sub_le`); points of disjoint faces are at least
`(card ι)⁻¹` apart (`TauCeti.one_le_card_mul_norm_sub_of_disjoint`), so there the vertex value
controls both images.

## References

* J. Munkres, *Elementary Differential Topology*, Chapter II, Section 9, for the use of
  piecewise derivative estimates in secant approximation, and Theorems 10.5–10.6 (smooth
  triangulations).
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public section

open Set
open scoped NNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem dist_le_lipschitz_constant {Y : Type*} [PseudoMetricSpace Y]
    {f : (ι → ℝ) → Y} {C : ℝ≥0} {b : Y} {σ : Finset ι} {x : ι → ℝ}
    (hx : x ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (σ : Set ι)))
    (hf : LipschitzOnWith C f
      (convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (σ : Set ι))))
    (hb : ∀ i ∈ σ, f (Pi.single i 1) = b) : dist (f x) b ≤ C := by
  obtain ⟨v, hv⟩ := (convexHull_nonempty_iff.mp ⟨x, hx⟩)
  obtain ⟨i, hi, rfl⟩ := hv
  have hi' : Pi.single i 1 ∈ convexHull ℝ ((fun i : ι => Pi.single i (1 : ℝ)) '' (σ : Set ι)) :=
    subset_convexHull ℝ _ ⟨i, hi, rfl⟩
  have h := hf.dist_le_mul x hx (Pi.single i 1) hi'
  rw [hb i hi] at h
  exact h.trans (mul_le_of_le_one_right C.coe_nonneg
    (by simpa only [dist_eq_norm] using norm_sub_le_one_of_mem_convexHull_pi_single hx hi'))

/-- A common facewise Lipschitz bound gives a global bound on a union of coordinate faces
for maps taking the same value at all vertices. The loss depends only on the ambient vertex
count, and the union need not be connected, pure, or closed under taking faces. This is useful
for interpolation errors, whose vertex values are zero. -/
theorem lipschitzOnWith_biUnion_convexHull_pi_single {Y : Type*} [PseudoMetricSpace Y]
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
