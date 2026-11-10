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

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# Lipschitz estimates across a finite closed cover

A common Lipschitz bound on the members of a finite closed cover of a convex set holds
on the whole set. The covering sets need not themselves be convex. This permits estimates
for piecewise smooth maps to pass across the boundaries of their pieces without a loss
in the constant. In particular, derivative estimates on the simplices of a subdivision
give a Lipschitz estimate for the assembled secant error.

The local-to-global argument uses continuous induction along a line segment. The local
hypothesis only compares nearby points with the centre of each neighbourhood; it does not
require a Lipschitz estimate between every pair in that neighbourhood.

## References

* J. Munkres, *Elementary Differential Topology*, Chapter II, Section 9, for the use of
  piecewise derivative estimates in secant approximation.
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
