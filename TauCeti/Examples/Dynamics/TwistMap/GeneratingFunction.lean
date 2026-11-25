/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.TwistMap.GeneratingFunction
public import TauCeti.Examples.Dynamics.TwistMap.Exact
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Checks for the generating function of the shear

The shear `F(x, y) = (x + y, y)` of the plane is exact for `λ = y dx` with `S = y²/2`. Its
twist coordinates are `Q(x, y) = (x, x + y)` and its generating function is
`h(x, X) = (X − x)²/2`. At `(x, X) = (1, 2) = Q(1, 1)`: `S(1, 1) = h(1, 2) = 1/2`, and
`dh = dX − dx`, that is `−∂₁h = ∂₂h = 1`.
-/

open Set

public noncomputable section

namespace TauCeti.Examples.TwistGeneratingFunction

open TauCeti.Examples.ExactTwistMap

/-- The shear `(x, y) ↦ (x + y, y)` as an open partial homeomorphism. -/
abbrev shear : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
  (shiftedShear 0).toOpenPartialHomeomorph

/-- The primitive `S = y²/2` of `F*(y dx) − y dx = y dy` for the shear. -/
theorem hasFDerivAt_primitive (p : ℝ × ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => p.2 ^ 2 / 2) ((shear p).2 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (fderiv ℝ shear p) - p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2 / 2) p.2 p.2 :=
    (HasDerivAt.div_const (hasDerivAt_pow 2 p.2) 2).congr_deriv (by norm_num)
  have h : HasFDerivAt (fun p : ℝ × ℝ => p.2 ^ 2 / 2)
      (p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hsq.comp_hasFDerivAt p hasFDerivAt_snd
  convert h using 1
  rw [Homeomorph.toOpenPartialHomeomorph_apply, fst_comp_fderiv_shiftedShear]
  ext <;> simp [shiftedShear_apply]

/-- `h(1, 2) = S(1, 1) = 1/2`. -/
example : stripBandGeneratingFunction shear univ (fun p => p.2 ^ 2 / 2) (1, 2) = 1 / 2 := by
  have h := stripBandGeneratingFunction_stripTwistCoord (S := fun p : ℝ × ℝ => p.2 ^ 2 / 2)
    (isMonotoneTwistMap_shiftedShear 0).injOn_stripTwistCoord (q := (1, 1)) (mem_univ _)
  rw [stripTwistCoord_apply] at h
  norm_num [shiftedShear_apply] at h
  exact h

/-- `dh = dX − dx` at `(1, 2)`: `−∂₁h(1, 2) = ∂₂h(1, 2) = 1`. -/
example : HasFDerivAt (stripBandGeneratingFunction shear univ fun p => p.2 ^ 2 / 2)
    (ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) (1, 2) := by
  have h := (isMonotoneTwistMap_shiftedShear 0).hasFDerivAt_stripBandGeneratingFunction
    (g := fun p => p.2) (fun p _ => hasFDerivAt_primitive p) (p := (1, 1))
    ⟨mem_univ _, mem_univ _⟩
  rw [stripTwistCoord_apply] at h
  norm_num [shiftedShear_apply] at h
  exact h

end TauCeti.Examples.TwistGeneratingFunction
