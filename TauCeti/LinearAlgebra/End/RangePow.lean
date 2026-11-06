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
hypothesis is needed: it only serves to make the chain stop. If the kernel chain has also
stopped, the endomorphism restricts to a bijection on the stable range, giving the invertible
part of the Fitting splitting without finite-length assumptions.
-/

public section

namespace LinearMap

variable {R M : Type*}

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M] {f : Module.End R M} {n : ℕ}

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

variable [Semiring R] [AddCommGroup M] [Module R M] {f : Module.End R M} {n : ℕ}

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

section Ring

variable [Ring R] [AddCommGroup M] [Module R M]

/-- If both the kernel and range chains stop at `n`, the endomorphism restricts to a
bijection on the stable range. This is the invertible part of the Fitting decomposition;
no finite-length hypothesis is required once stabilization is known. -/
theorem bijective_restrict_range_pow_of_stable (f : Module.End R M) (n : ℕ)
    (hk : ker (f ^ (n + 1)) = ker (f ^ n))
    (hr : range (f ^ (n + 1)) = range (f ^ n))
    (h : ∀ x ∈ range (f ^ n), f x ∈ range (f ^ n) := by
      rintro x ⟨y, rfl⟩
      exact ⟨f y, LinearMap.congr_fun (Commute.self_pow f n).eq.symm y⟩) :
    Function.Bijective (f.restrict h : range (f ^ n) →ₗ[R] range (f ^ n)) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨y, hy⟩ := x.property
    have hfy : (f ^ (n + 1)) y = 0 := by
      simpa only [pow_succ', mul_apply_eq_comp, hy,
        LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] using
        congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    have hy0 := LinearMap.mem_ker.mp (hk ▸ LinearMap.mem_ker.mpr hfy)
    exact Subtype.ext (hy ▸ hy0)
  · intro x
    have hx : (x : M) ∈ range (f ^ (n + 1)) := by
      rw [hr]
      exact x.property
    obtain ⟨y, hy⟩ := hx
    refine ⟨⟨(f ^ n) y, mem_range_self _ _⟩, Subtype.ext ?_⟩
    simpa only [LinearMap.restrict_apply, pow_succ', mul_apply_eq_comp] using hy

end Ring

end LinearMap

end
