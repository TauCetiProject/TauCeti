/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Symmetrized
public import TauCeti.Algebra.Algebra.Complex
public import TauCeti.Algebra.Star.SelfAdjoint.LinearMap

/-!
# Self-adjoint squares and symmetrized multiplication

For complex algebras, the self-adjoint square law for a complex linear map is equivalent
to multiplicativity on Mathlib's `SymAlg`. The inverse of two identifies each symmetrized
product with half its anticommutator.
-/

public section

namespace LinearMap

/-- For a complex linear map on a complex star module, preserving self-adjoint squares
is equivalent to preserving multiplication in the symmetrized algebra.
The codomain does not need an involution. -/
theorem map_mul_self_of_isSelfAdjoint_iff_sym_map_unsym_sym_mul_sym
    {A B : Type*} [Ring A] [StarAddMonoid A] [Algebra ℂ A] [StarModule ℂ A]
    [Ring B] [Algebra ℂ B] [Invertible (2 : A)] [Invertible (2 : B)]
    (f : A →ₗ[ℂ] B) :
    (∀ x, IsSelfAdjoint x → f (x * x) = f x * f x) ↔
      (∀ x y, SymAlg.sym (f (SymAlg.unsym (SymAlg.sym x * SymAlg.sym y))) =
        SymAlg.sym (f x) * SymAlg.sym (f y)) := by
  constructor
  · intro hf x y
    simp only [SymAlg.sym_mul_sym, SymAlg.unsym_sym, TauCeti.ComplexAlgebra.invOf_two_eq,
      ← Algebra.smul_def, map_smul, f.map_mul_add_mul_of_map_mul_self_of_isSelfAdjoint hf]
  · intro h x _
    simpa only [← SymAlg.sym_mul_self, SymAlg.unsym_sym, SymAlg.sym_inj] using h x x

end LinearMap
