/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Continuous linear maps on products and Pi types

This file collects supplementary results about continuous linear maps on indexed products `ι → R`.

## Main results

* `ContinuousLinearMap.eq_smul_id_of_unique`: every continuous linear endomorphism of a
  one-coordinate space `ι → R` over a topological commutative semiring `R` with continuous scalar
  multiplication is a scalar multiple of the identity.
* `ContinuousLinearMap.update_proj_apply`: the family `Function.update (fun m ↦ proj m) i α`,
  which replaces the projection to the coordinate `i` by `α`, evaluates at `j` and `v` to the
  coordinate `j` of `Function.update v i (α v)`.
-/

public section

namespace ContinuousLinearMap

section CommSemiring

variable {R : Type*} [CommSemiring R] [TopologicalSpace R]

/-- Every continuous linear endomorphism of a one-coordinate space `ι → R` is a scalar multiple of
the identity. -/
theorem eq_smul_id_of_unique {ι : Type*} [Unique ι] [ContinuousConstSMul R R]
    (T : (ι → R) →L[R] (ι → R)) :
    T = T (fun _ ↦ 1) default • ContinuousLinearMap.id R (ι → R) := by
  ext v i
  have hv : v = v default • (fun _ : ι ↦ (1 : R)) := by
    ext j
    simp [Unique.eq_default j]
  conv_lhs => rw [hv]
  simp [Unique.eq_default i, mul_comm]

end CommSemiring

/-- Evaluating the family `Function.update (fun m ↦ proj m) i α`, which replaces the projection to
the coordinate `i` by the continuous linear map `α`, at `j` and `v` gives the coordinate `j` of
`Function.update v i (α v)`. With `ContinuousLinearMap.coe_pi'`, `simp` uses it to evaluate
`pi (Function.update (fun m ↦ proj m) i α) v`. -/
@[simp]
theorem update_proj_apply {ι R : Type*} [DecidableEq ι] [Semiring R]
    {φ : ι → Type*} [∀ m, TopologicalSpace (φ m)] [∀ m, AddCommMonoid (φ m)] [∀ m, Module R (φ m)]
    (i : ι) (α : (∀ m, φ m) →L[R] φ i) (j : ι) (v : ∀ m, φ m) :
    Function.update (fun m ↦ proj m) i α j v = Function.update v i (α v) j :=
  Function.apply_update (fun _ g ↦ g v) (fun m ↦ proj m) i α j

end ContinuousLinearMap
