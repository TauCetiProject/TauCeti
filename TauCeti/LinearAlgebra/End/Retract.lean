/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Spectral kernels along a linear retract

For a retract `r ∘ i = id`, extending an endomorphism `f` by `i ∘ f ∘ r` adds only a
zero block. The inclusion therefore identifies the kernels of every power of `1 - f`
and `1 - i ∘ f ∘ r`. The inverse is the restriction of `r`. This comparison does not
require a field, finite generation, or a choice of complement, and includes exponent zero.
It allows generalized eigenspaces at nonzero spectral values to be computed in a retract
presentation.
-/

public section

namespace LinearMap

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {i : M →ₗ[R] N} {r : N →ₗ[R] M}

/-- Extending `f` along a retract adds only a zero block: a vector killed by a power of
`1 - i ∘ f ∘ r` belongs to the image of the inclusion. -/
theorem comp_apply_eq_self_of_mem_ker_one_sub_pow (f : Module.End R M)
    (hri : r.comp i = .id) (n : ℕ)
    {x : N} (hx : x ∈ ker ((1 - i.comp (f.comp r)) ^ n)) : i (r x) = x := by
  have hri' (y : M) : r (i y) = y := DFunLike.congr_fun hri y
  let g : Module.End R N := 1 - i.comp (f.comp r)
  let q : Module.End R N := 1 - i.comp r
  have hq (y : N) : q (g y) = q y := by
    simp [q, g, hri']
  have hpow (k : ℕ) (y : N) : q ((g ^ k) y) = q y := by
    induction k with
    | zero => simp
    | succ k ih => simpa only [pow_succ', mul_apply_eq_comp, hq] using ih
  have hz := hpow n x
  rw [mem_ker] at hx
  rw [hx, map_zero] at hz
  dsimp only [q] at hz
  exact (sub_eq_zero.mp hz.symm).symm

/-- The inclusion and retraction identify the kernels of powers of `1 - f` and of
`1 - i ∘ f ∘ r`, including exponent zero. -/
def kerOneSubPowEquivOfRetract (f : Module.End R M) (hri : r.comp i = .id) (n : ℕ) :
    ker ((1 - f) ^ n) ≃ₗ[R] ker ((1 - i.comp (f.comp r)) ^ n) := by
  have hri' (y : M) : r (i y) = y := DFunLike.congr_fun hri y
  have hi : Function.Semiconj i (1 - f : Module.End R M)
      (1 - i.comp (f.comp r) : Module.End R N) := by
    intro y
    simp [hri']
  have hr : Function.Semiconj r (1 - i.comp (f.comp r) : Module.End R N)
      (1 - f : Module.End R M) := by
    intro y
    simp [hri']
  have hi_pow : Function.Semiconj i ((1 - f) ^ n : Module.End R M)
      ((1 - i.comp (f.comp r)) ^ n : Module.End R N) := by
    simpa only [FunLike.coe_pow_eq_iterate] using hi.iterate_right n
  have hr_pow : Function.Semiconj r ((1 - i.comp (f.comp r)) ^ n : Module.End R N)
      ((1 - f) ^ n : Module.End R M) := by
    simpa only [FunLike.coe_pow_eq_iterate] using hr.iterate_right n
  refine LinearEquiv.ofLinearMap
    ((i.comp (ker ((1 - f) ^ n)).subtype).codRestrict _ ?_)
    ((r.comp (ker ((1 - i.comp (f.comp r)) ^ n)).subtype).codRestrict _ ?_)
    ?_ ?_
  · intro x
    exact mem_ker.mpr ((hi_pow x).symm.trans (by simp [mem_ker.mp x.property]))
  · intro x
    exact mem_ker.mpr ((hr_pow x).symm.trans (by simp [mem_ker.mp x.property]))
  · ext x
    exact comp_apply_eq_self_of_mem_ker_one_sub_pow f hri n x.property
  · ext x
    exact hri' x

/-- The spectral-kernel equivalence applies the inclusion. -/
@[simp]
theorem coe_kerOneSubPowEquivOfRetract_apply (f : Module.End R M)
    (hri : r.comp i = .id) (n : ℕ) (x : ker ((1 - f) ^ n)) :
    (kerOneSubPowEquivOfRetract f hri n x : N) = i x :=
  (rfl)

/-- The inverse spectral-kernel equivalence applies the retraction. -/
@[simp]
theorem coe_kerOneSubPowEquivOfRetract_symm_apply (f : Module.End R M)
    (hri : r.comp i = .id) (n : ℕ) (x : ker ((1 - i.comp (f.comp r)) ^ n)) :
    ((kerOneSubPowEquivOfRetract f hri n).symm x : M) = r x :=
  (rfl)

end LinearMap
