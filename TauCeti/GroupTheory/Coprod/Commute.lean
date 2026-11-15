/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.Coprod.Basic

/-!
# Commuting elements of the two factors of a free product

In the free product `M ∗ N` of two monoids, an element of `M` and an element of `N` commute only
when one of them is trivial. This is the basic obstruction to writing a commutative group as a
free product of two nontrivial subgroups.

## Main results

* `Monoid.Coprod.commute_inl_inr_iff`, `Monoid.Coprod.commute_inr_inl_iff`: `inl a` and `inr b`
  commute in `M ∗ N` if and only if `a = 1` or `b = 1`.
-/

public section

namespace Monoid.Coprod

variable {M N : Type*} [Monoid M] [Monoid N]

/-! The proof lets `M ∗ N` act on the set `M × N`: an element `a` of `M` multiplies on the left the
first coordinate of the pairs whose second coordinate is `1` and fixes the other pairs, and
symmetrically for `N`. On `(1, 1)`, `inl a * inr b` and `inr b * inl a` give `(1, b)` and `(a, 1)`
when `a ≠ 1` and `b ≠ 1`. -/

private def fstFun [DecidableEq N] (a : M) : Function.End (M × N) :=
  fun p => if p.2 = 1 then (a * p.1, p.2) else p

private theorem fstFun_apply [DecidableEq N] (a : M) (p : M × N) :
    fstFun (N := N) a p = if p.2 = 1 then (a * p.1, p.2) else p :=
  rfl

private def sndFun [DecidableEq M] (b : N) : Function.End (M × N) :=
  fun p => if p.1 = 1 then (p.1, b * p.2) else p

private theorem sndFun_apply [DecidableEq M] (b : N) (p : M × N) :
    sndFun (M := M) b p = if p.1 = 1 then (p.1, b * p.2) else p :=
  rfl

private def fstAct [DecidableEq N] : M →* Function.End (M × N) where
  toFun := fstFun
  map_one' := FaithfulSMul.eq_of_smul_eq_smul fun (p : M × N) => by simp [fstFun_apply]
  map_mul' a a' := FaithfulSMul.eq_of_smul_eq_smul fun (p : M × N) => by
    rw [mul_smul]; by_cases h : p.2 = 1 <;> simp [fstFun_apply, h, mul_assoc]

private def sndAct [DecidableEq M] : N →* Function.End (M × N) where
  toFun := sndFun
  map_one' := FaithfulSMul.eq_of_smul_eq_smul fun (p : M × N) => by simp [sndFun_apply]
  map_mul' b b' := FaithfulSMul.eq_of_smul_eq_smul fun (p : M × N) => by
    rw [mul_smul]; by_cases h : p.1 = 1 <;> simp [sndFun_apply, h, mul_assoc]

/-- An element of `M` commutes with an element of `N` in the free product `M ∗ N` if and only if
one of them is trivial. -/
@[simp]
theorem commute_inl_inr_iff {a : M} {b : N} : Commute (inl a : M ∗ N) (inr b) ↔ a = 1 ∨ b = 1 := by
  classical
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> simp⟩
  by_contra! hab
  have := congr(lift (fstAct (N := N)) (sndAct (M := M)) $h.eq • ((1 : M), (1 : N)))
  simp_all [mul_smul, fstAct, sndAct, fstFun_apply, sndFun_apply]

/-- An element of `N` commutes with an element of `M` in the free product `M ∗ N` if and only if
one of them is trivial. -/
@[simp]
theorem commute_inr_inl_iff {a : M} {b : N} : Commute (inr b : M ∗ N) (inl a) ↔ a = 1 ∨ b = 1 :=
  Commute.symm_iff.trans commute_inl_inr_iff

end Monoid.Coprod
