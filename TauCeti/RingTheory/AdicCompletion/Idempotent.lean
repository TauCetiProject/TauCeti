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
noncommutative, that is `I`-adically complete as an `R`-module. Every element idempotent modulo
`I • S` is congruent modulo `I • S` to an idempotent of `S`. Consequently, idempotents lift along
any ring homomorphism `f : S →+* T` whose kernel is `I • S`: every idempotent of `T` in the range of
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
plays no role. The polynomials have no constant term, so the iterates stay in every corner `cSd`
containing the starting point, and so does their limit.

## Main results

* `IsAdicComplete.exists_isIdempotentElem_sub_mem_of_mul_eq`: an element idempotent modulo
  `I • S` is congruent to an idempotent of `S`, which can be chosen in any corner `cSd` that
  contains the element, for instance in `eSe` for an idempotent `e`.
* `IsAdicComplete.exists_isIdempotentElem_sub_mem`: an element idempotent modulo `I • S` is
  congruent to an idempotent of `S`.
* `IsAdicComplete.exists_isIdempotentElem_eq`: idempotents lift along a ring homomorphism
  with kernel `I • S` out of an `I`-adically complete `R`-algebra `S`.

## References

* C. W. Curtis, I. Reiner, *Methods of Representation Theory, Vol. I*, §6.
* T. Y. Lam, *A First Course in Noncommutative Rings*, §21.
-/

public section

namespace IsAdicComplete

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] (I : Ideal R)

variable {S : Type*} [NonAssocRing S] in
/-- One step of Newton's iteration for `X ^ 2 - X`. -/
private def newtonIdempotent (x : S) : S :=
  x + (x * x - x) * (1 - 2 * x)

variable {S : Type*} [NonAssocRing S] in
private theorem newtonIdempotent_sub (x : S) :
    newtonIdempotent x - x = (x * x - x) * (1 - 2 * x) := by
  rw [newtonIdempotent, add_sub_cancel_left]

/-- The defect `x ^ 2 - x` is squared by a Newton step. -/
private theorem newtonIdempotent_mul_self_sub (x : S) :
    newtonIdempotent x * newtonIdempotent x - newtonIdempotent x =
      (x * x - x) * ((x * x - x) * (4 * (x * x - x) - 3)) := by
  simp only [newtonIdempotent]
  noncomm_ring

/-- A Newton step stays in every left corner `cS` containing its argument. -/
private theorem mul_newtonIdempotent {c x : S} (hc : c * x = x) :
    c * newtonIdempotent x = newtonIdempotent x := by
  have h : c * (x * x - x) = x * x - x := by rw [mul_sub, ← mul_assoc, hc]
  rw [newtonIdempotent, mul_add, hc, ← mul_assoc, h]

/-- A Newton step stays in every right corner `Sd` containing its argument. -/
private theorem newtonIdempotent_mul {d x : S} (hd : x * d = x) :
    newtonIdempotent x * d = newtonIdempotent x := by
  have h1 : (x * x - x) * d = x * x - x := by rw [sub_mul, mul_assoc, hd]
  have h2 : (1 - 2 * x) * d = d - 2 * x := by rw [sub_mul, one_mul, mul_assoc, hd]
  rw [newtonIdempotent, add_mul, hd, mul_assoc, h2, mul_sub, h1, mul_sub (x * x - x) 1, mul_one]

/-- The `n`-th Newton iterate of an element idempotent modulo `I • S` has defect in
`I ^ (n + 1) • S`. -/
private theorem iterate_newtonIdempotent_defect_mem {x₀ : S}
    (hx₀ : x₀ * x₀ - x₀ ∈ I • (⊤ : Submodule R S)) (n : ℕ) :
    newtonIdempotent^[n] x₀ * newtonIdempotent^[n] x₀ - newtonIdempotent^[n] x₀ ∈
      I ^ (n + 1) • (⊤ : Submodule R S) := by
  induction n with
  | zero => simpa only [zero_add, pow_one, Function.iterate_zero_apply] using hx₀
  | succ n ih =>
    rw [Function.iterate_succ_apply', newtonIdempotent_mul_self_sub]
    rw [← Ideal.mem_map_algebraMap_iff] at ih ⊢
    refine Ideal.map_mono (Ideal.pow_le_pow_right (by omega : n + 1 + 1 ≤ n + 1 + (n + 1))) ?_
    rw [pow_add, Ideal.map_algebraMap_mul]
    exact Ideal.mul_mem_mul ih (Ideal.mul_mem_right _ _ ih)

/-- The `I`-adic limit of a sequence in a left corner `cS` lies in it. -/
private theorem mul_eq_of_forall_sub_mem [IsHausdorff I S] {c L : S} {x : ℕ → S}
    (hx : ∀ n, c * x n = x n) (hL : ∀ n, L - x n ∈ I ^ n • (⊤ : Submodule R S)) : c * L = L := by
  refine sub_eq_zero.mp <| IsHausdorff.haus' (I := I) (c * L - L) fun n ↦ SModEq.sub_mem.mpr ?_
  have hLn := hL n
  have hsplit : c * L - L - 0 = c * (L - x n) - (L - x n) := by
    rw [mul_sub, hx n, sub_zero, sub_sub_sub_cancel_right]
  rw [hsplit]
  rw [← Ideal.mem_map_algebraMap_iff] at hLn ⊢
  exact sub_mem (Ideal.mul_mem_left _ _ hLn) hLn

/-- The `I`-adic limit of a sequence in a right corner `Sd` lies in it. -/
private theorem mul_eq_of_forall_sub_mem' [IsHausdorff I S] {d L : S} {x : ℕ → S}
    (hx : ∀ n, x n * d = x n) (hL : ∀ n, L - x n ∈ I ^ n • (⊤ : Submodule R S)) : L * d = L := by
  refine sub_eq_zero.mp <| IsHausdorff.haus' (I := I) (L * d - L) fun n ↦ SModEq.sub_mem.mpr ?_
  have hLn := hL n
  have hsplit : L * d - L - 0 = (L - x n) * d - (L - x n) := by
    rw [sub_mul, hx n, sub_zero, sub_sub_sub_cancel_right]
  rw [hsplit]
  rw [← Ideal.mem_map_algebraMap_iff] at hLn ⊢
  exact sub_mem (Ideal.mul_mem_right _ _ hLn) hLn

/-- An element of an `I`-adically complete, possibly noncommutative `R`-algebra that is
idempotent modulo `I • S` is congruent modulo `I • S` to an idempotent, which lies in every
corner `cSd` containing the element: if `c * x₀ = x₀` and `x₀ * d = x₀`, then also
`c * e = e` and `e * d = e`. Taking `c = d` an idempotent, the lift lies in the corner ring. -/
theorem exists_isIdempotentElem_sub_mem_of_mul_eq [IsAdicComplete I S] {x₀ c d : S}
    (hx₀ : x₀ * x₀ - x₀ ∈ I • (⊤ : Submodule R S)) (hc : c * x₀ = x₀) (hd : x₀ * d = x₀) :
    ∃ e : S, IsIdempotentElem e ∧ e - x₀ ∈ I • (⊤ : Submodule R S) ∧ c * e = e ∧ e * d = e := by
  let x : ℕ → S := fun n ↦ newtonIdempotent^[n] x₀
  have hx_zero : x 0 = x₀ := rfl
  have hx_succ (n : ℕ) : x (n + 1) = newtonIdempotent (x n) :=
    Function.iterate_succ_apply' _ _ _
  have hdefect := iterate_newtonIdempotent_defect_mem I hx₀
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
  have hLx (n : ℕ) : L - x n ∈ I ^ n • (⊤ : Submodule R S) := by
    rw [← neg_sub, neg_mem_iff]
    exact SModEq.sub_mem.mp (hL n)
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · refine sub_eq_zero.mp <| IsHausdorff.haus' (I := I) (L * L - L) fun n ↦
      SModEq.sub_mem.mpr ?_
    -- Writing `d = L - x n`, the defect of `L` is that of `x n` plus `x n * d + d * L - d`.
    have hd := hLx n
    have hsplit : L * L - L - 0 =
        (x n * x n - x n) + x n * (L - x n) + (L - x n) * L - (L - x n) := by
      noncomm_ring
    rw [hsplit]
    rw [← Ideal.mem_map_algebraMap_iff] at hd ⊢
    refine sub_mem (add_mem (add_mem ?_ (Ideal.mul_mem_left _ _ hd))
      (Ideal.mul_mem_right _ _ hd)) hd
    exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega))
      ((Ideal.mem_map_algebraMap_iff _).mpr (hdefect n))
  · have h1 : L - x 1 ∈ I • (⊤ : Submodule R S) := by
      simpa only [pow_one, neg_sub] using neg_mem (SModEq.sub_mem.mp (hL 1))
    have h01 : x 1 - x₀ ∈ I • (⊤ : Submodule R S) := by
      simpa only [zero_add, pow_one, hx_zero] using hstep 0
    simpa only [sub_add_sub_cancel] using add_mem h1 h01
  -- The iterates stay in the corner `cSd`, and hence so does their limit.
  · exact mul_eq_of_forall_sub_mem I (fun n ↦ Set.MapsTo.iterate (s := {y | c * y = y})
      (fun _ hy ↦ mul_newtonIdempotent hy) n hc) hLx
  · exact mul_eq_of_forall_sub_mem' I (fun n ↦ Set.MapsTo.iterate (s := {y | y * d = y})
      (fun _ hy ↦ newtonIdempotent_mul hy) n hd) hLx

/-- An element of an `I`-adically complete, possibly noncommutative `R`-algebra that is
idempotent modulo `I • S` is congruent modulo `I • S` to an idempotent. -/
theorem exists_isIdempotentElem_sub_mem [IsAdicComplete I S] {x₀ : S}
    (hx₀ : x₀ * x₀ - x₀ ∈ I • (⊤ : Submodule R S)) :
    ∃ e : S, IsIdempotentElem e ∧ e - x₀ ∈ I • (⊤ : Submodule R S) :=
  (exists_isIdempotentElem_sub_mem_of_mul_eq I hx₀ (one_mul x₀) (mul_one x₀)).imp
    fun _ h ↦ ⟨h.1, h.2.1⟩

/-- **Idempotents lift modulo `I • S` in an `I`-adically complete algebra.** Let `S` be an
`R`-algebra, possibly noncommutative, which is `I`-adically complete as an `R`-module, and let
`f : S →+* T` be a ring homomorphism whose kernel is `I • S`. Every idempotent of `T` in the range
of `f` is the image of an idempotent of `S`. The target `T` need not be associative.

This is the complete analogue of `exists_isIdempotentElem_eq_of_ker_isNilpotent`, which asks the
kernel to be nil instead. -/
theorem exists_isIdempotentElem_eq [IsAdicComplete I S] {T : Type*} [NonAssocRing T]
    (f : S →+* T) (hf : ∀ x, f x = 0 ↔ x ∈ I • (⊤ : Submodule R S)) {e : T} (he : e ∈ f.range)
    (he' : IsIdempotentElem e) : ∃ e' : S, IsIdempotentElem e' ∧ f e' = e := by
  obtain ⟨x, rfl⟩ := he
  obtain ⟨e', he', hx⟩ := exists_isIdempotentElem_sub_mem I (x₀ := x)
    ((hf _).mp (by simp [he'.eq]))
  exact ⟨e', he', sub_eq_zero.mp (by simpa using (hf _).mpr hx)⟩

end IsAdicComplete
