/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Holder.Iterated
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Laplacian of a bounded `C^{k,α}` map

For a bounded `C^{k,α}` map `f` on a finite-dimensional real inner product space `E`, the
Laplacian `Δ f` is controlled by the second derivative: pointwise
`‖Δ f x‖ ≤ dim E * ‖D²f‖_∞` when `k ≥ 2`, and for `k = 2` the Laplacian is `α`-Hölder with
`dim E` times the Hölder seminorm of `D²f`. These are the bounds on the Laplacian of an initial
datum in parabolic Schauder theory.

## Main declarations

* `TauCeti.CkHolderSpace.norm_laplacian_le_iteratedFDeriv_two`: the supremum bound.
* `TauCeti.CkHolderSpace.holderWith_laplacian`: the Hölder bound.
-/

public section

namespace TauCeti.CkHolderSpace

open InnerProductSpace Laplacian
open scoped NNReal

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Laplacian of a bounded `C^{k+2,α}` map is bounded by `dim E` times the supremum norm of
its second derivative field. -/
theorem norm_laplacian_le_iteratedFDeriv_two (f : CkHolderSpace (k + 2) α E F) (x : E) :
    ‖Δ (f : E → F) x‖ ≤ Module.finrank ℝ E * ‖f.iteratedFDeriv 2‖ :=
  (norm_laplacian_le _ x).trans (mul_le_mul_of_nonneg_left
    (f.norm_fderiv_fderiv_le_iteratedFDeriv_two x) (Nat.cast_nonneg _))

/-- The Laplacian of a bounded `C^{2,α}` map is `α`-Hölder with `dim E` times the Hölder seminorm
of `D²f`. -/
theorem holderWith_laplacian (f : CkHolderSpace 2 α E F) :
    HolderWith (Module.finrank ℝ E * nnHolderNorm α (_root_.iteratedFDeriv ℝ 2 f)) α
      (Δ (f : E → F)) := by
  rw [← holderOnWith_univ]
  refine HolderOnWith.of_dist_le fun x _ y _ ↦ ?_
  rw [dist_eq_norm]
  refine (norm_laplacian_sub_laplacian_le _ x y).trans ?_
  rw [NNReal.coe_mul, NNReal.coe_natCast, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (by simpa [dist_eq_norm] using f.holderWith_fderiv_fderiv.dist_le x y) (Nat.cast_nonneg _)

end TauCeti.CkHolderSpace
