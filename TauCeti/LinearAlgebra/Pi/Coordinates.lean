/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis

/-!
# Semilinear maps on a product along one coordinate

A nonzero semilinear map `f : (ι → R) →ₛₗ[σ] M` on a finite product is nonzero at some coordinate
vector. Setting one coordinate of its argument to `t` adds `σ t` times its value at that coordinate
vector to its value with the coordinate zeroed. Hence, over a semiring with left-cancellative
addition, replacing the coordinate `i` of `v` by the value `f v` of a semilinear functional
`f : (ι → R) →ₛₗ[τ] R` is injective if `t ↦ τ t * f (Pi.single i 1)` is injective, for a linear
functional if its coefficient `f (Pi.single i 1)` is right-regular.

## Main results

* `LinearMap.exists_apply_single_ne_zero`: a nonzero semilinear map on a finite product `ι → R`
  is nonzero at some coordinate vector.
* `LinearMap.apply_update_eq_add_smul`: for a semilinear map `f : (ι → R) →ₛₗ[σ] M`, setting the
  coordinate `i` of `x` to `t` adds `σ t` times the value at `Pi.single i 1` to the value at `x`
  with that coordinate zeroed.
* `LinearMap.update_with_apply_injective`: over a semiring with left-cancellative addition,
  replacing one coordinate `i` of `v` by the value of a semilinear functional
  `f : (ι → R) →ₛₗ[τ] R` is injective if `t ↦ τ t * f (Pi.single i 1)` is injective; for a linear
  functional, if the coefficient `f (Pi.single i 1)` is right-regular.

These coordinate arguments are adapted from [KLS](https://github.com/human-ai-mathematics/kls-lean),
commit `65810c73f9dd7945fc646ab484cb19d673f5291d`,
`formalization/FunctionalInequalities/Analysis/`, files `PiCoordinates.lean` and
`Sard/CoordinateChange.lean`.
-/

public section

namespace LinearMap

variable {ι R S M : Type*} [DecidableEq ι] [Semiring R] [Semiring S] [AddCommMonoid M] [Module S M]
  {σ : R →+* S}

/-- A nonzero semilinear map on a finite product `ι → R` is nonzero on some coordinate vector. -/
theorem exists_apply_single_ne_zero [Finite ι] (f : (ι → R) →ₛₗ[σ] M) (hf : f ≠ 0) :
    ∃ i : ι, f (Pi.single i 1) ≠ 0 := by
  by_contra! h
  exact hf <| (Pi.basisFun R ι).ext fun i ↦ by simpa using h i

/-- The value of a semilinear map `f : (ι → R) →ₛₗ[σ] M` after setting the coordinate `i` of `x`
to `t` is its value with that coordinate set to zero, plus `σ t` times its value at the coordinate
vector `Pi.single i 1`. -/
theorem apply_update_eq_add_smul (f : (ι → R) →ₛₗ[σ] M) (x : ι → R) (i : ι) (t : R) :
    f (Function.update x i t) = f (Function.update x i 0) + σ t • f (Pi.single i 1) := by
  -- `Function.update_add` splits the update as `update x i 0 + update 0 i t`, and
  -- `update 0 i t` is `Pi.single i t = t • Pi.single i 1` by the definition of `Pi.single`.
  have hsplit : Function.update x i t = Function.update x i 0 + t • Pi.single i 1 := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one, Pi.single]
    simpa using Function.update_add x 0 i 0 t
  simp [hsplit]

/-- Over a semiring with left-cancellative addition, replacing the coordinate `i` of `v` by the
value `f v` of a semilinear functional `f : (ι → R) →ₛₗ[τ] R` is injective when `t ↦ τ t * c` is
injective, where `c = f (Pi.single i 1)`. For a linear functional this says that `c` is
right-regular. -/
theorem update_with_apply_injective [IsLeftCancelAdd R] {τ : R →+* R} (f : (ι → R) →ₛₗ[τ] R)
    (i : ι) (hf : Function.Injective fun t ↦ τ t * f (Pi.single i 1)) :
    Function.Injective fun v ↦ Function.update v i (f v) := by
  intro v w h
  have hrest : Function.update v i 0 = Function.update w i 0 := by
    simpa only [Function.update_idem] using congrArg (fun x : ι → R ↦ Function.update x i 0) h
  -- Split off the coordinate `i` on both sides of `f v = f w` and cancel the common summand.
  have hsplit (x : ι → R) : f x = f (Function.update x i 0) + τ (x i) * f (Pi.single i 1) := by
    simpa only [Function.update_eq_self, smul_eq_mul] using apply_update_eq_add_smul f x i (x i)
  have hfvw : f v = f w := by simpa using congrFun h i
  rw [hsplit v, hsplit w, hrest] at hfvw
  have hvw : v i = w i := hf (add_left_cancel hfvw)
  calc v = Function.update (Function.update v i 0) i (v i) := by simp
    _ = w := by simp [hrest, hvw]

end LinearMap
