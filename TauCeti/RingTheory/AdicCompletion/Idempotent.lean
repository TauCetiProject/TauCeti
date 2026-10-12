/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Idempotents
import Mathlib.Tactic.NoncommRing
import TauCeti.RingTheory.Ideal.Extended

/-!
# Lifting idempotents in adically complete algebras

Let `R` be a commutative ring, `I` an ideal of `R`, and `S` an `R`-algebra, possibly
noncommutative, that is `I`-adically complete as an `R`-module. Then idempotents lift along any
ring homomorphism `f : S →+* T` whose kernel is `I • S`: every idempotent of `T` in the range of
`f` is the image of an idempotent of `S`.

Mathlib lifts idempotents along a ring homomorphism whose kernel is nil
(`exists_isIdempotentElem_eq_of_ker_isNilpotent`), which covers a quotient by a nilpotent ideal.
The kernel `I • S` is not nil in general, for instance `p • ℤ_p[G]` in the group algebra of a
finite group over `ℤ_p`, and completeness replaces nilpotence. For commutative `S` the statement
also follows from Hensel's lemma (`TauCeti.HenselianRing.exists_isIdempotentElem_sub_mem`); the
point here is that `S` may be noncommutative, such as a matrix algebra or the endomorphism ring
of a module.

The proof is Newton's iteration for the polynomial `X ^ 2 - X`. If `a = x ^ 2 - x`, then
`x' = x + a * (1 - 2 * x)` satisfies `x' ^ 2 - x' = a ^ 2 * (4 * a - 3)`, so the defect `a` is
squared at each step while `x' - x` is a multiple of `a`. Starting from any lift of the
idempotent, the iterates form an `I`-adic Cauchy sequence, and its limit is an idempotent lift.
Every element involved is a polynomial in a single element of `S`, so noncommutativity of `S`
plays no role.

## Main results

* `TauCeti.IsAdicComplete.exists_isIdempotentElem_eq`: idempotents lift along a ring homomorphism
  with kernel `I • S` out of an `I`-adically complete `R`-algebra `S`.

## References

* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §6.
* T. Y. Lam, *A First Course in Noncommutative Rings*, §21.
-/

public section

namespace TauCeti

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] (I : Ideal R)

/-- One step of Newton's iteration for `X ^ 2 - X`. -/
private def newtonIdempotent (x : S) : S :=
  x + (x * x - x) * (1 - 2 * x)

private theorem newtonIdempotent_sub (x : S) :
    newtonIdempotent x - x = (x * x - x) * (1 - 2 * x) := by
  rw [newtonIdempotent, add_sub_cancel_left]

/-- The defect `x ^ 2 - x` is squared by a Newton step. -/
private theorem newtonIdempotent_mul_self_sub (x : S) :
    newtonIdempotent x * newtonIdempotent x - newtonIdempotent x =
      (x * x - x) * ((x * x - x) * (4 * (x * x - x) - 3)) := by
  simp only [newtonIdempotent]
  noncomm_ring

/-- **Idempotents lift modulo `I • S` in an `I`-adically complete algebra.** Let `S` be an
`R`-algebra, possibly noncommutative, which is `I`-adically complete as an `R`-module, and let
`f : S →+* T` be a ring homomorphism whose kernel is `I • S`. Every idempotent of `T` in the range
of `f` is the image of an idempotent of `S`.

This is the complete analogue of `exists_isIdempotentElem_eq_of_ker_isNilpotent`, which asks the
kernel to be nil instead. -/
theorem IsAdicComplete.exists_isIdempotentElem_eq [IsAdicComplete I S] {T : Type*} [Ring T]
    (f : S →+* T) (hf : ∀ x, f x = 0 ↔ x ∈ I • (⊤ : Submodule R S)) {e : T} (he : e ∈ f.range)
    (he' : IsIdempotentElem e) : ∃ e' : S, IsIdempotentElem e' ∧ f e' = e := by
  obtain ⟨x₀, hx₀⟩ := he
  -- The Newton iterates of a lift of `e`: all lift `e`, and the `n`-th has defect in `I ^ (n + 1)`.
  let x : ℕ → S := fun n ↦ newtonIdempotent^[n] x₀
  have hx_succ (n : ℕ) : x (n + 1) = newtonIdempotent (x n) :=
    Function.iterate_succ_apply' _ _ _
  have hfx (n : ℕ) : f (x n) = e := by
    induction n with
    | zero => exact hx₀
    | succ n ih =>
      rw [hx_succ, newtonIdempotent, map_add, map_mul, map_sub, map_mul, ih, he'.eq, sub_self,
        zero_mul, add_zero]
  have hdefect (n : ℕ) : x n * x n - x n ∈ I ^ (n + 1) • (⊤ : Submodule R S) := by
    induction n with
    | zero => rw [zero_add, pow_one, ← hf, map_sub, map_mul, hfx 0, he'.eq, sub_self]
    | succ n ih =>
      rw [hx_succ, newtonIdempotent_mul_self_sub]
      rw [← Ideal.mem_map_algebraMap_iff] at ih ⊢
      refine Ideal.map_mono (Ideal.pow_le_pow_right (by omega : n + 1 + 1 ≤ n + 1 + (n + 1))) ?_
      rw [pow_add, Ideal.map_algebraMap_mul]
      exact Ideal.mul_mem_mul ih (Ideal.mul_mem_right _ _ ih)
  have hstep (n : ℕ) : x (n + 1) - x n ∈ I ^ (n + 1) • (⊤ : Submodule R S) := by
    rw [hx_succ, newtonIdempotent_sub, ← Ideal.mem_map_algebraMap_iff]
    exact Ideal.mul_mem_right _ _ ((Ideal.mem_map_algebraMap_iff _).mpr (hdefect n))
  -- The iterates form a Cauchy sequence, whose limit is the required idempotent.
  have hcauchy {m n : ℕ} (hmn : m ≤ n) : x m ≡ x n [SMOD (I ^ m • ⊤ : Submodule R S)] := by
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      refine ih.trans (SModEq.sub_mem.mpr ?_)
      rw [← neg_sub, neg_mem_iff]
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (hstep n)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) x hcauchy
  refine ⟨L, ?_, ?_⟩
  · refine sub_eq_zero.mp <| IsHausdorff.haus' (I := I) (L * L - L) fun n ↦
      SModEq.sub_mem.mpr ?_
    -- Writing `d = L - x n`, the defect of `L` is that of `x n` plus `x n * d + d * L - d`.
    have hd : L - x n ∈ I ^ n • (⊤ : Submodule R S) := by
      rw [← neg_sub, neg_mem_iff]
      exact SModEq.sub_mem.mp (hL n)
    have hsplit : L * L - L - 0 =
        (x n * x n - x n) + x n * (L - x n) + (L - x n) * L - (L - x n) := by
      noncomm_ring
    rw [hsplit]
    rw [← Ideal.mem_map_algebraMap_iff] at hd ⊢
    refine sub_mem (add_mem (add_mem ?_ (Ideal.mul_mem_left _ _ hd))
      (Ideal.mul_mem_right _ _ hd)) hd
    exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega))
      ((Ideal.mem_map_algebraMap_iff _).mpr (hdefect n))
  · have h1 : x 1 - L ∈ I • (⊤ : Submodule R S) := by
      simpa using SModEq.sub_mem.mp (hL 1)
    rw [← hfx 1, ← sub_eq_zero, ← map_sub, ← neg_sub, map_neg, neg_eq_zero, hf]
    exact h1

end TauCeti
