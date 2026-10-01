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
kernel and the range of `f ^ n` together span the module. Unlike Mathlib's
`LinearMap.eventually_codisjoint_ker_pow_range_pow`, no Artinian hypothesis is needed: it only
serves to make the chain stop.
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
  induction m with
  | zero => rfl
  | succ m ih => rw [← add_assoc, pow_succ', Module.End.mul_eq_comp, range_comp, ih,
      ← range_comp, ← Module.End.mul_eq_comp, ← pow_succ', h]

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [Module R M] {f : Module.End R M} {n : ℕ}

/-- If the range of `f ^ (n + 1)` equals that of `f ^ n`, the kernel and the range of `f ^ n`
together span the module. -/
theorem codisjoint_ker_pow_range_pow_of_range_pow_succ_eq
    (h : range (f ^ (n + 1)) = range (f ^ n)) :
    Codisjoint (ker (f ^ n)) (range (f ^ n)) := by
  refine codisjoint_iff.mpr (Submodule.eq_top_iff'.mpr fun x => ?_)
  obtain ⟨z, hz⟩ : (f ^ n) x ∈ range (f ^ (n + n)) := by
    rw [range_pow_add_eq_of_range_pow_succ_eq h]
    exact mem_range_self _ x
  rw [pow_add, Module.End.mul_apply] at hz
  exact Submodule.mem_sup.mpr
    ⟨x - (f ^ n) z, by simp [hz], (f ^ n) z, mem_range_self _ z, sub_add_cancel x _⟩

end AddCommGroup

end LinearMap

end
