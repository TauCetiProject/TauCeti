/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Ranges after extension of scalars

If the coefficient algebra is faithfully flat, membership of a vector in the range of a linear map
can be checked after extension of scalars.  This is the linear-algebraic descent step used when an
equation acquires a solution after passing to a larger field.

Membership in a submodule is the case of a cyclic submodule in `Submodule.baseChange_le_iff` from
`Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean`: faithfully flat extension of scalars reflects
inclusions of submodules.  The statement for ranges follows because extension of scalars commutes
with ranges, `LinearMap.baseChange_range`.

## Main results

* `Submodule.one_tmul_mem_baseChange_iff`: a vector belongs to a submodule exactly when its
  canonical image belongs to the extended submodule, for a faithfully flat coefficient algebra.
* `LinearMap.one_tmul_mem_range_baseChange_iff`: a vector belongs to a range exactly when its
  canonical image belongs to the extended range, for a faithfully flat coefficient algebra.
-/

public section

open TensorProduct

namespace Submodule

universe u v w

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [Ring A] [Algebra R A]
variable [AddCommGroup M] [Module R M]

/-- Over a faithfully flat coefficient algebra, a vector belongs to a submodule exactly when its
canonical image belongs to the extension of that submodule. -/
@[simp]
theorem one_tmul_mem_baseChange_iff [Module.FaithfullyFlat R A]
    (p : Submodule R M) (m : M) :
    (1 : A) ⊗ₜ[R] m ∈ p.baseChange A ↔ m ∈ p := by
  simpa using baseChange_le_iff (A := A) (p := span R {m}) (q := p)

end Submodule

namespace LinearMap

universe u v w x

variable {R : Type u} {A : Type v} {M : Type w} {N : Type x}

section Descent

variable [CommRing R] [Ring A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Over a faithfully flat coefficient algebra, a vector belongs to the range of a linear map if
and only if its canonical image belongs to the range after extension of scalars. -/
theorem one_tmul_mem_range_baseChange_iff [Module.FaithfullyFlat R A]
    (f : M →ₗ[R] N) (y : N) :
    (1 : A) ⊗ₜ[R] y ∈ range (f.baseChange A) ↔ y ∈ range f := by
  rw [← baseChange_range, Submodule.one_tmul_mem_baseChange_iff]

end Descent

end LinearMap
