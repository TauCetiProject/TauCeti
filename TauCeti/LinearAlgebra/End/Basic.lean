/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Module.LinearMap.End

/-!
# Basic facts about module endomorphisms

A nontrivial endomorphism semiring forces the underlying module to be nontrivial. Together with
Mathlib's converse instance, this identifies nontriviality on the two sides without assumptions on
the endomorphism semiring beyond nontriviality itself.

A vector on which every endomorphism of a list acts by the same scalar `z` is acted on by their
product through `z ^ l.length` (`Module.End.list_prod_apply_eq_pow_smul`).

The powers of `-f` act as the powers of `f` up to the sign `(-1) ^ n`
(`Module.End.neg_pow_apply`).
-/

public section

namespace TauCeti

/-- A module with nontrivial endomorphism semiring is nontrivial. -/
theorem nontrivial_of_nontrivial_end {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Nontrivial (Module.End R M)] : Nontrivial M := by
  have : Nontrivial (M → M) := (DFunLike.coe_injective (F := Module.End R M)).nontrivial
  exact Function.nontrivial_of_nontrivial M M

end TauCeti

namespace Module.End

/-- A product of endomorphisms each of which acts on `s` by the scalar `z` acts on `s` by
`z ^ l.length`. -/
theorem list_prod_apply_eq_pow_smul {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {l : List (Module.End R M)} {z : R} {s : M} (h : ∀ a ∈ l, a s = z • s) :
    l.prod s = z ^ l.length • s := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, Module.End.mul_apply, ih fun a ha ↦ h a (List.mem_cons_of_mem _ ha),
      map_smul, h a List.mem_cons_self, smul_smul, List.length_cons, pow_succ]

/-- The powers of `-f` are the powers of `f` up to sign. -/
theorem neg_pow_apply {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]
    (f : Module.End R M) (n : ℕ) (x : M) : ((-f) ^ n) x = ((-1 : ℤ) ^ n) • (f ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, LinearMap.neg_apply, map_zsmul, pow_succ' f,
      Module.End.mul_apply, pow_succ' (-1 : ℤ), neg_one_mul, neg_smul]

end Module.End
