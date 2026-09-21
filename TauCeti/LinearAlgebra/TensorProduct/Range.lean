/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Ranges after extension of scalars

Extension of scalars carries the range of a linear map to the extension of its range.  If the
coefficient algebra is faithfully flat, membership of a vector in that range can be checked after
extension of scalars.  This is the linear-algebraic descent step used when an equation acquires a
solution after passing to a larger field.

This builds on `Submodule.baseChange` from
`Mathlib/LinearAlgebra/TensorProduct/Tower.lean` and
`Module.FaithfullyFlat.one_tmul_eq_zero_iff` from
`Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean`.

## Main results

* `LinearMap.range_baseChange`: the range of an extended linear map is the extension of its range.
* `LinearMap.one_tmul_mem_range_baseChange_iff`: a vector belongs to a range exactly when its
  canonical image belongs to the extended range, for a faithfully flat coefficient algebra.
-/

public section

open TensorProduct
open scoped TensorProduct

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
  constructor
  · intro hm
    have hzero : LinearMap.lTensor A p.mkQ ((1 : A) ⊗ₜ[R] m) = 0 := by
      rw [← LinearMap.mem_ker, lTensor_mkQ]
      exact hm
    have hzero' : (1 : A) ⊗ₜ[R] p.mkQ m = 0 := by
      simpa only [LinearMap.lTensor_tmul] using hzero
    have : p.mkQ m = 0 :=
      (Module.FaithfullyFlat.one_tmul_eq_zero_iff R _ (p.mkQ m)).mp hzero'
    rw [← p.ker_mkQ]
    exact LinearMap.mem_ker.mpr this
  · intro hm
    exact Submodule.tmul_mem_baseChange_of_mem 1 hm

end Submodule

namespace LinearMap

universe u v w x

variable {R : Type u} {A : Type v} {M : Type w} {N : Type x}

section Range

variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Extension of scalars carries the range of a linear map to the extension of its range. -/
@[simp]
theorem range_baseChange (f : M →ₗ[R] N) :
    range (f.baseChange A) = (range f).baseChange A := by
  calc
    range (f.baseChange A) =
        range (((range f).subtype.comp f.rangeRestrict).baseChange A) := by
      rw [f.subtype_comp_rangeRestrict]
    _ = range ((range f).subtype.baseChange A ∘ₗ f.rangeRestrict.baseChange A) := by
      rw [baseChange_comp]
    _ = range ((range f).subtype.baseChange A) := by
      apply range_comp_of_range_eq_top
      rw [range_eq_top]
      exact baseChange_surjective A f.surjective_rangeRestrict
    _ = (range f).baseChange A := by rw [Submodule.baseChange]

end Range

section Descent

variable [CommRing R] [Ring A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Over a faithfully flat coefficient algebra, a vector belongs to the range of a linear map if
and only if its canonical image belongs to the range after extension of scalars. -/
theorem one_tmul_mem_range_baseChange_iff [Module.FaithfullyFlat R A]
    (f : M →ₗ[R] N) (y : N) :
    (1 : A) ⊗ₜ[R] y ∈ range (f.baseChange A) ↔ y ∈ range f := by
  rw [range_baseChange, Submodule.one_tmul_mem_baseChange_iff]

end Descent

end LinearMap
