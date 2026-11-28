/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
import TauCeti.Analysis.Calculus.DifferentialForm.Basic

/-!
# The curl of a one-form as a two-vector

On a finite-dimensional real inner product space `V`, the exterior derivative of a one-form `b'`
is a two-form, read as a two-vector through `TauCeti.alternatingFormEquiv`. Paired with a bivector
`u ∧ v`, the two-vector `F' = -db'` is the curl of `b'` in the plane of `u` and `v`: the derivative
of `b'(u)` along `v` minus that of `b'(v)` along `u`.

## Main results

* `TauCeti.inner_alternatingFormEquiv_symm_neg_extDeriv`: the curl identity
  `⟪F', u ∧ v⟫ = ∂_v b'(u) - ∂_u b'(v)` for a one-form differentiable at the base point.
-/

public section

open exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti

/-- The two-vector `F' = -db'` of a one-form `b'` differentiable at `y`, paired with a bivector
`u ∧ v`: the derivative of `b'(u)` along `v` minus that of `b'(v)` along `u`. -/
theorem inner_alternatingFormEquiv_symm_neg_extDeriv {b' : V → V [⋀^Fin 1]→L[ℝ] ℝ} {y : V}
    (hb' : DifferentiableAt ℝ b' y) (u v : V) :
    ⟪(alternatingFormEquiv V 2).symm (-extDeriv b' y), ιMulti ℝ 2 ![u, v]⟫ =
      fderiv ℝ (fun y' ↦ b' y' (fun _ ↦ u)) y v - fderiv ℝ (fun y' ↦ b' y' (fun _ ↦ v)) y u := by
  rw [inner_alternatingFormEquiv_symm_ιMulti, ContinuousAlternatingMap.neg_apply,
    extDeriv_apply_pair_of_differentiableAt hb']
  ring

end TauCeti
