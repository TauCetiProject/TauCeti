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
extension of the image, with no hypothesis on `A` at all.  In particular a containment of the image
of a submodule in another submodule ascends to the extensions.

If the coefficient algebra is moreover faithfully flat, all of this is reversible: membership of a
vector in a submodule or in the range of a linear map, a containment of the image of a submodule in
another, and a containment of a range in a submodule may each be checked after extension of
scalars.  This is the linear-algebraic descent step used when an equation acquires a solution, or a
structural statement becomes available, after passing to a larger field.

This builds on `Submodule.baseChange` from
`Mathlib/LinearAlgebra/TensorProduct/Tower.lean` and
`lTensor_mkQ` and `LinearMap.lTensor_range` from
`Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean`, as well as
`Module.FaithfullyFlat.one_tmul_eq_zero_iff` and `Submodule.baseChange_le_iff` from
`Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean`.

## Main results

* `LinearMap.map_baseChange`: the image of an extended submodule under an extended linear map is
  the extension of the image.
* `LinearMap.mapsTo_baseChange`: a containment of the image of a submodule in another ascends to
  the extensions, with no hypothesis on the coefficient algebra.
* `LinearMap.mapsTo_baseChange_iff` and `LinearMap.range_baseChange_le_baseChange_iff`: over a
  faithfully flat coefficient algebra, such a containment, respectively a containment of the whole
  range in a submodule, may be checked after extension of scalars.
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

section Image

variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Extension of scalars commutes with taking the image of a submodule: the image of the extension
of `p` under the extension of `f` is the extension of the image of `p` under `f`. -/
@[simp]
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

/-- **Ascent of a containment along extension of scalars.**  If `f` maps `p` into `q`, then the
extended map sends the extension of `p` into the extension of `q`.  This direction asks nothing of
the coefficient algebra. -/
theorem mapsTo_baseChange (f : M →ₗ[R] N) {p : Submodule R M} {q : Submodule R N}
    (h : ∀ x ∈ p, f x ∈ q) {z : A ⊗[R] M} (hz : z ∈ p.baseChange A) :
    f.baseChange A z ∈ q.baseChange A := by
  have hz' : f.baseChange A z ∈ Submodule.map (f.baseChange A) (p.baseChange A) := ⟨z, hz, rfl⟩
  rw [map_baseChange] at hz'
  refine Submodule.baseChange_mono A ?_ hz'
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

end Image

section Descent

variable [CommRing R] [Ring A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [Module.FaithfullyFlat R A]

/-- **A containment of submodules under a linear map may be checked after extending scalars.**
Over a faithfully flat coefficient algebra, the extended map sends the extension of `p` into the
extension of `q` exactly when `f` maps `p` into `q`. -/
theorem mapsTo_baseChange_iff (f : M →ₗ[R] N) (p : Submodule R M) (q : Submodule R N) :
    (∀ z ∈ p.baseChange A, f.baseChange A z ∈ q.baseChange A) ↔ ∀ x ∈ p, f x ∈ q := by
  refine ⟨fun h x hx => ?_, fun h _ hz => mapsTo_baseChange f h hz⟩
  have hmem := h ((1 : A) ⊗ₜ[R] x) (Submodule.tmul_mem_baseChange_of_mem (1 : A) hx)
  rwa [baseChange_tmul, Submodule.one_tmul_mem_baseChange_iff] at hmem

/-- **A containment of the range of a linear map in a submodule may be checked after extending
scalars.** -/
theorem range_baseChange_le_baseChange_iff (f : M →ₗ[R] N) (q : Submodule R N) :
    range (f.baseChange A) ≤ q.baseChange A ↔ range f ≤ q := by
  have h := map_baseChange (A := A) f ⊤
  rw [Submodule.baseChange_top, Submodule.map_top, Submodule.map_top] at h
  rw [h, Submodule.baseChange_le_iff]

/-- Over a faithfully flat coefficient algebra, a vector belongs to the range of a linear map if
and only if its canonical image belongs to the range after extension of scalars. -/
theorem one_tmul_mem_range_baseChange_iff (f : M →ₗ[R] N) (y : N) :
    (1 : A) ⊗ₜ[R] y ∈ range (f.baseChange A) ↔ y ∈ range f := by
  calc
    _ ↔ (1 : A) ⊗ₜ[R] y ∈ range ((range f).subtype.baseChange A) := by
      simpa only [mem_range, baseChange_eq_ltensor] using
        SetLike.ext_iff.mp (lTensor_range (Q := A) (g := f)) ((1 : A) ⊗ₜ[R] y)
    _ ↔ y ∈ range f := by
      rw [← Submodule.baseChange, Submodule.one_tmul_mem_baseChange_iff]

end Descent

end LinearMap
