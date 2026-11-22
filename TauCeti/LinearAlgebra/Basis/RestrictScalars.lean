/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Submodule

/-!
# Coordinates in a basis with restricted scalars

Let `b` be a finite basis of an `S`-module `M`, and `R` a subring of `S` (an `R`-algebra `S`
without `R`-torsion). Mathlib's `Module.Basis.restrictScalars` makes `b` a basis over `R` of the
`R`-span of its vectors. The vector of that span with coordinates `n : ι → R` is, in `M`, the
vector with coordinates `fun i ↦ algebraMap R S (n i)` in `b`. This is how a sum over integer
coordinates is reindexed as a sum over the lattice `span ℤ (range b)`.

## Main results

* `Module.Basis.repr_restrictScalars_equivFun_symm`: the `b`-coordinates of the vector with
  coordinates `n` in `b.restrictScalars R` are `algebraMap R S (n i)`.
* `Module.Basis.coe_restrictScalars_equivFun_symm`: that vector, in `M`, is
  `b.equivFun.symm fun i ↦ algebraMap R S (n i)`.
-/

public section

namespace Module.Basis

variable {ι R S M : Type*} [Finite ι] [CommRing R] [IsDomain R] [Ring S] [Nontrivial S]
  [AddCommGroup M] [Algebra R S] [Module S M] [Module R M] [IsScalarTower R S M]
  [IsTorsionFree R S] (b : Basis ι S M)

/-- The `b`-coordinates of the vector with coordinates `n` in `b.restrictScalars R` are the
images `algebraMap R S (n i)` of its coordinates. -/
@[simp]
theorem repr_restrictScalars_equivFun_symm (n : ι → R) (i : ι) :
    b.repr ((b.restrictScalars R).equivFun.symm n : M) i = algebraMap R S (n i) := by
  rw [← b.restrictScalars_repr_apply R, ← equivFun_apply, LinearEquiv.apply_symm_apply]

/-- The vector with coordinates `n` in `b.restrictScalars R` is, in `M`, the vector with
coordinates `fun i ↦ algebraMap R S (n i)` in `b`. -/
theorem coe_restrictScalars_equivFun_symm (n : ι → R) :
    ((b.restrictScalars R).equivFun.symm n : M) = b.equivFun.symm fun i ↦ algebraMap R S (n i) :=
  b.equivFun.eq_symm_apply.2 <| funext fun i ↦ by
    rw [equivFun_apply, repr_restrictScalars_equivFun_symm]

end Module.Basis
