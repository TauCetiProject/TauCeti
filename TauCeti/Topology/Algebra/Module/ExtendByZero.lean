/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Continuous linear extension of coordinate functions by zero

Mathlib's `Function.ExtendByZero.linearMap` is continuous for the product topologies:
each output coordinate is either a fixed input coordinate or zero. No finiteness
assumption on the coordinate types is needed. For an injective index map, restriction
recovers the original function, including when the target has unused coordinates.

This construction lets affine coordinate formulas pass to enlarged vertex sets of
simplicial complexes. It uses Mathlib's existing extension by zero rather than choosing
a different extension on unused coordinates.
-/

public section

namespace Function.ExtendByZero

variable {ι κ : Type*} (R : Type*) [Semiring R] [TopologicalSpace R] (e : ι → κ)

/-- Extension by zero as a continuous linear map between product spaces of coordinates. -/
noncomputable def continuousLinearMap : (ι → R) →L[R] (κ → R) :=
  { linearMap R e with
    cont := by
      classical
      have h : Continuous (fun x : ι → R => Function.extend e x 0) := by
        apply continuous_pi
        intro j
        by_cases hj : ∃ i, e i = j
        · simpa only [Function.extend_def, dite_eq_left hj] using
            (continuous_apply (Classical.choose hj) : Continuous fun x : ι → R =>
              x (Classical.choose hj))
        · simpa only [Function.extend_apply' _ _ _ hj, Pi.zero_apply] using
            (continuous_const : Continuous fun _ : ι → R => (0 : R))
      exact h }

/-- The continuous linear extension uses `Function.extend` with zero outside the image. -/
@[simp]
theorem continuousLinearMap_apply (x : ι → R) :
    continuousLinearMap R e x = Function.extend e x 0 := (rfl)

/-- Restrict coordinate functions along an index map, as a continuous linear map. -/
def restriction : (κ → R) →L[R] (ι → R) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (e i)

/-- Coordinate restriction is precomposition with the index map. -/
@[simp]
theorem restriction_apply (x : κ → R) : restriction R e x = x ∘ e := by
  ext i
  simp [restriction]

/-- Restriction recovers every function extended along an injective index map. -/
theorem restriction_leftInverse (he : Function.Injective e) :
    Function.LeftInverse (restriction R e) (continuousLinearMap R e) := by
  intro x
  ext i
  simp [he]

end Function.ExtendByZero
