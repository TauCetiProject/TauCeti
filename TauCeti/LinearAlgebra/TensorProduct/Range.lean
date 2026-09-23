/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Images and ranges after extension of scalars

Extending scalars along an algebra `A` turns a linear map `f` into `f.baseChange A` and a submodule
`p` into `p.baseChange A`.  The two operations commute: the image of an extended submodule is the
extension of the image, with no hypothesis on `A` at all, because both sides are generated over `A`
by the canonical images `1 ⊗ₜ m` of elements of `p`.

If the coefficient algebra is moreover faithfully flat, membership of a vector in the range of a
linear map can be checked after extension of scalars.  This is the linear-algebraic descent step
used when an equation acquires a solution after passing to a larger field.

This builds on `Submodule.baseChange` from
`Mathlib/LinearAlgebra/TensorProduct/Tower.lean` and
`lTensor_mkQ` and `LinearMap.lTensor_range` from
`Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean`, as well as
`Module.FaithfullyFlat.one_tmul_eq_zero_iff` from
`Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean`.

## Main results

* `LinearMap.map_baseChange`: the image of an extended submodule under an extended linear map is
  the extension of the image.
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

variable [CommRing R] [Ring A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

section Image

/-- Extension of scalars commutes with taking the image of a submodule: both sides are spanned
over the extended coefficients by the canonical images of the elements of `f '' p`. -/
theorem map_baseChange (f : M →ₗ[R] N) (p : Submodule R M) :
    Submodule.map (f.baseChange A) (p.baseChange A) = (p.map f).baseChange A := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.baseChange_eq_span]
  congr 1
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map, TensorProduct.mk_apply]
  constructor
  · rintro ⟨-, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp⟩
  · rintro ⟨-, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(1 : A) ⊗ₜ[R] x, ⟨x, hx, rfl⟩, by simp⟩

end Image

section Descent

/-- Over a faithfully flat coefficient algebra, a vector belongs to the range of a linear map if
and only if its canonical image belongs to the range after extension of scalars. -/
theorem one_tmul_mem_range_baseChange_iff [Module.FaithfullyFlat R A]
    (f : M →ₗ[R] N) (y : N) :
    (1 : A) ⊗ₜ[R] y ∈ range (f.baseChange A) ↔ y ∈ range f := by
  calc
    _ ↔ (1 : A) ⊗ₜ[R] y ∈ range ((range f).subtype.baseChange A) := by
      simpa only [mem_range, baseChange_eq_ltensor] using
        SetLike.ext_iff.mp (lTensor_range (Q := A) (g := f)) ((1 : A) ⊗ₜ[R] y)
    _ ↔ y ∈ range f := by
      rw [← Submodule.baseChange, Submodule.one_tmul_mem_baseChange_iff]

end Descent

end LinearMap
