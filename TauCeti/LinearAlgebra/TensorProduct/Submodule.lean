/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Scalar extension of images and powers of submodules

Extension of scalars commutes with taking images of submodules under linear maps, and preserves
powers of submodules of an algebra. The latter applies, in particular, to the homogeneous pieces of
tensor and exterior algebras, defined as powers of their generators.

For submodules `p` and `q`, every element of `(p ⊔ q) ⊗[R] M` is the sum of images of elements of
`p ⊗[R] M` and `q ⊗[R] M` under the maps induced by the inclusions
(`Submodule.exists_eq_rTensor_inclusion_add`).

Multiplication of tensor products of submodules is compatible with multiplication in each
factor (`Submodule.map₂_tmul_mul_le`).
-/

public section

open scoped TensorProduct Pointwise

namespace Submodule

section Map

variable {R A M N : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Extension of scalars commutes with taking the image of a submodule under a linear map. -/
@[simp]
theorem baseChange_map (f : M →ₗ[R] N) (p : Submodule R M) :
    (p.map f).baseChange A = (p.baseChange A).map (f.baseChange A) := by
  rw [baseChange_eq_span, baseChange_eq_span, map_span, map_coe, map_coe, map_coe,
    Set.image_image, Set.image_image]
  simp

/-- Extension of scalars commutes with taking the range of a linear map. -/
@[simp]
theorem _root_.LinearMap.baseChange_range (f : M →ₗ[R] N) :
    (LinearMap.range f).baseChange A = LinearMap.range (f.baseChange A) := by
  rw [← Submodule.map_top, baseChange_map, baseChange_top, Submodule.map_top]

end Map

section Inclusion

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The images of `p ⊗[R] M` and `q ⊗[R] M` span `(p ⊔ q) ⊗[R] M`. -/
theorem exists_eq_rTensor_inclusion_add (p q : Submodule R N) (t : ↥(p ⊔ q) ⊗[R] M) :
    ∃ a b, t = (inclusion le_sup_left).rTensor M a + (inclusion le_sup_right).rTensor M b := by
  induction t with
  | tmul x m =>
    obtain ⟨y, hy, z, hz, hyz⟩ := mem_sup.mp x.2
    refine ⟨⟨y, hy⟩ ⊗ₜ m, ⟨z, hz⟩ ⊗ₜ m, ?_⟩
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, ← TensorProduct.add_tmul]
    exact congrArg (· ⊗ₜ m) (Subtype.ext hyz.symm)
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨a₁, b₁, rfl⟩ := h₁
    obtain ⟨a₂, b₂, rfl⟩ := h₂
    exact ⟨a₁ + a₂, b₁ + b₂, by rw [map_add, map_add, add_add_add_comm]⟩

end Inclusion

section Multiplication

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

/-- Products of tensor products of submodules lie in the tensor product of their products. -/
theorem map₂_tmul_mul_le (P S : Submodule R A) (Q T : Submodule R B) :
    map₂ (TensorProduct.mk R A B) P Q * map₂ (TensorProduct.mk R A B) S T ≤
      map₂ (TensorProduct.mk R A B) (P * S) (Q * T) := by
  apply mul_le.mpr
  intro x hx y hy
  rw [← TensorProduct.range_mapIncl] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  induction a with
  | tmul p q =>
    induction b with
    | tmul s t =>
      simpa using apply_mem_map₂ (TensorProduct.mk R A B)
        (mul_mem_mul p.2 s.2) (mul_mem_mul q.2 t.2)
    | add b c hb hc => simpa [mul_add] using Submodule.add_mem _ hb hc
  | add a c ha hc => simpa [add_mul] using Submodule.add_mem _ ha hc

end Multiplication

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [Semiring B]
variable [Algebra R A] [Algebra R B]

/-- Extension of scalars preserves powers of submodules of an algebra. -/
@[simp]
theorem baseChange_pow (p : Submodule R B) (n : ℕ) :
    (p ^ n).baseChange A = p.baseChange A ^ n := by
  conv_lhs => rw [← p.span_eq, span_pow, baseChange_span]
  rw [baseChange_eq_span, map_coe, span_pow]
  exact congrArg (span A) (Set.image_pow
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) (p : Set B) n)

end Submodule
