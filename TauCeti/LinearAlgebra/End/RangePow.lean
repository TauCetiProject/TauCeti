/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Stabilising ranges of iterates

Once the decreasing chain `range f ⊇ range f² ⊇ ⋯` of an endomorphism `f` stops at stage `n`, the
kernel and the range of `f ^ n` together span the module. This is the case `g = f ^ n` of the
fact that the kernel and the range of any endomorphism `g` with `range (g ^ 2) = range g` together
span the module. Unlike Mathlib's `LinearMap.eventually_codisjoint_ker_pow_range_pow`, no Artinian
hypothesis is needed: it only serves to make the chain stop.
-/

public section

namespace LinearMap

variable {R M : Type*} [Semiring R]

section AddCommMonoid

variable [AddCommMonoid M] [Module R M] {f : Module.End R M} {n : ℕ}

/-- If the range of `f ^ (n + 1)` equals that of `f ^ n`, the ranges of all higher powers of `f`
equal it too. -/
theorem range_pow_add_eq_of_range_pow_succ_eq (h : range (f ^ (n + 1)) = range (f ^ n)) (m : ℕ) :
    range (f ^ (n + m)) = range (f ^ n) := by
  have hrec : ∀ k, range (f ^ (k + 1)) = (range (f ^ k)).map f := fun k => by
    rw [pow_succ', Module.End.mul_eq_comp, range_comp]
  induction m with
  | zero => rfl
  | succ m ih => rw [← add_assoc, hrec, ih, ← hrec, h]

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [Module R M] {f : Module.End R M} {n : ℕ}

/-- If the range of `f ^ 2` equals that of `f`, the kernel and the range of `f` together span the
module. -/
theorem codisjoint_ker_range_of_range_sq_eq (h : range (f ^ 2) = range f) :
    Codisjoint (ker f) (range f) := by
  refine Submodule.codisjoint_iff_exists_add_eq.mpr fun x => ?_
  obtain ⟨z, hz⟩ : f x ∈ range (f ^ 2) := h ▸ mem_range_self f x
  rw [sq, mul_apply_eq_comp] at hz
  exact ⟨x - f z, f z, by simp [hz], mem_range_self f z, sub_add_cancel x _⟩

/-- If the range of `f ^ (n + 1)` equals that of `f ^ n`, the kernel and the range of `f ^ n`
together span the module. -/
theorem codisjoint_ker_pow_range_pow_of_range_pow_succ_eq
    (h : range (f ^ (n + 1)) = range (f ^ n)) :
    Codisjoint (ker (f ^ n)) (range (f ^ n)) :=
  codisjoint_ker_range_of_range_sq_eq <| by
    rw [← pow_mul, mul_two, range_pow_add_eq_of_range_pow_succ_eq h]

end AddCommGroup

end LinearMap

end
