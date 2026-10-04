/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Operations

/-!
# Scalar extension of images and powers of submodules

Extension of scalars commutes with taking images of submodules under linear maps, and preserves
powers of submodules of an algebra. The latter applies, in particular, to the homogeneous pieces of
tensor and exterior algebras, defined as powers of their generators.
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

end Map

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
