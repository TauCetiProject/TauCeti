/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Basic
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Uniform ellipticity on compact sets

A coefficient field `a : X → Matrix n n ℝ` that is continuous on a compact set `K` and positive
definite at every point of `K` is uniformly elliptic on `K`
(`TauCeti.PDE.exists_uniformlyEllipticOn_of_isCompact`). The lower constant is a positive uniform
lower bound for the continuous function `(x, ξ) ↦ ξ ⬝ a(x) ξ` on the compact set `K × S`, with `S`
the unit sphere. The upper constant bounds the operator norms of the bilinear forms of `a(x)`,
which vary continuously on `K`. No nonemptiness assumption on `K × S` is needed.

This is how a smooth coefficient field, such as a Riemannian metric read in a chart, gives a
uniformly elliptic operator on every open set with compact closure in its domain.

Adapted from Giada Franz's formalization in
[`ColdingMinicozziTheory`](https://github.com/riccardobrasca/ColdingMinicozziTheory), module
`ForTauCeti/Analysis/PDE/Ellipticity/Compact.lean`, revision
`6b89bc4abbf989319947d24d776114611027f224`.
-/

public section

open Matrix Metric Set

namespace TauCeti

namespace PDE

variable {X : Type*} [TopologicalSpace X] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Pointwise positivity on a compact set is uniform ellipticity.** A coefficient field that is
continuous on a compact set `K`, and positive definite at every point of `K`, is uniformly
elliptic on `K`. -/
theorem exists_uniformlyEllipticOn_of_isCompact {K : Set X} (hK : IsCompact K)
    {a : X → Matrix n n ℝ} (ha : ContinuousOn a K)
    (hpos : ∀ x ∈ K, ∀ ξ : EuclideanSpace ℝ n, ξ ≠ 0 → 0 < ξ ⬝ᵥ (a x *ᵥ ξ)) :
    ∃ lam Lam, UniformlyEllipticOn K a lam Lam := by
  have hB : ContinuousOn (fun x ↦ matrixBilinearForm (a x)) K :=
    continuous_matrixBilinearForm.comp_continuousOn ha
  obtain ⟨lam, hlam, hlower⟩ := hK.exists_pos_forall_mul_norm_sq_le hB
    (by simpa only [matrixBilinearForm_apply] using hpos)
  have hsum : ContinuousOn (fun x ↦ ∑ i, ∑ j, |a x i j|) K :=
    continuousOn_finsetSum _ fun i _ ↦ continuousOn_finsetSum _ fun j _ ↦
      ((continuous_id.matrix_elem i j).comp_continuousOn ha).abs
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hsum
  refine ⟨lam, max lam C, UniformlyEllipticOn.of_bounds hlam (le_max_left _ _)
    (fun x hx ξ ↦ by simpa only [matrixBilinearForm_self] using hlower x hx ξ)
    fun x hx η ξ ↦ ?_⟩
  rw [← matrixBilinearForm_apply, ← Real.norm_eq_abs]
  exact (matrixBilinearForm (a x)).le_of_opNorm₂_le_of_le
    (((norm_matrixBilinearForm_le_sum_abs _).trans ((le_abs_self _).trans (hC x hx))).trans
      (le_max_right _ _)) le_rfl le_rfl

end PDE

end TauCeti
