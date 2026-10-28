/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Linear isometries as isometries of quadratic forms

A real quadratic form `Q` on a normed space is a fixed multiple of the squared norm when
`Q v = c * ‖v‖²` for all `v`; for example the form `Q v = -‖v‖²` of the Clifford algebras of the
Seiberg–Witten equations. A linear isometry equivalence preserves the norm, so it is an isometry
equivalence between two such forms with the same constant `c`.

## Main definitions

* `LinearIsometryEquiv.toQuadraticIsometryEquiv`: a linear isometry equivalence `f : V ≃ V'` as an
  isometry equivalence `Q ≃ Q'` of quadratic forms with `Q v = c * ‖v‖²` and `Q' v = c * ‖v‖²`.
-/

public section

namespace LinearIsometryEquiv

variable {V V' : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
  [SeminormedAddCommGroup V'] [NormedSpace ℝ V'] {Q : QuadraticForm ℝ V}
  {Q' : QuadraticForm ℝ V'} {c : ℝ}

/-- A linear isometry equivalence is an isometry equivalence between quadratic forms that are the
same multiple of the squared norm, `Q v = c * ‖v‖²` and `Q' v = c * ‖v‖²`. -/
@[expose] def toQuadraticIsometryEquiv (f : V ≃ₗᵢ[ℝ] V') (hQ : ∀ v, Q v = c * ‖v‖ ^ 2)
    (hQ' : ∀ v, Q' v = c * ‖v‖ ^ 2) : Q.IsometryEquiv Q' :=
  { f.toLinearEquiv with map_app' v := by simp [hQ, hQ'] }

/-- The isometry equivalence of quadratic forms induced by `f` is `f`. -/
@[simp]
theorem coe_toQuadraticIsometryEquiv (f : V ≃ₗᵢ[ℝ] V') (hQ : ∀ v, Q v = c * ‖v‖ ^ 2)
    (hQ' : ∀ v, Q' v = c * ‖v‖ ^ 2) : ⇑(f.toQuadraticIsometryEquiv hQ hQ') = f :=
  rfl

end LinearIsometryEquiv
