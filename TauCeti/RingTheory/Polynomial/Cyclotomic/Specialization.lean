/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# Specialization of roots of unity at prime level

If two integer polynomials agree at a `p`-th root of unity in characteristic zero, then their
values at `1` are congruent modulo the prime `p`. The primitive-root case uses
`Polynomial.cyclotomic_eq_minpoly` and `Polynomial.eval_one_cyclotomic_prime`.

For an array of integer coefficients, if all but one row vanish under cyclotomic evaluation
and the distinguished row has value `e * ζ ^ k`, the weighted sum of the ordinary row sums is
congruent to `e` times
that row's weight. In a prime-index character expansion, the cyclotomic evaluations are the
coefficients on the generator coset, whereas the ordinary row sums are the coefficients on
the subgroup. A zero weight on the surviving row therefore forces divisibility by `p`.
-/

public section

open scoped BigOperators nonZeroDivisors

namespace Polynomial

private theorem eval_one_modEq_of_aeval_eq_of_pow_eq_one_field {K : Type*}
    [Field K] [CharZero K] (P Q : ℤ[X]) {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : ζ ^ p = 1)
    (h : aeval ζ P = aeval ζ Q) : P.eval 1 ≡ Q.eval 1 [ZMOD (p : ℤ)] := by
  by_cases hz : ζ = 1
  · have hc (T : ℤ[X]) : aeval (1 : K) T = Int.cast (R := K) (T.eval 1) := by
      simpa only [map_one, algebraMap_int_eq, Int.coe_castRingHom] using
        (aeval_algebraMap_apply_eq_algebraMap_eval (A := K) (1 : ℤ) T)
    rw [hz, hc, hc] at h
    rw [Int.cast_injective h]
  have : Fact p.Prime := ⟨hp⟩
  have hprim : IsPrimitiveRoot ζ p := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hζ hz)
  have hd : cyclotomic p ℤ ∣ Q - P := by
    rw [cyclotomic_eq_minpoly hprim hp.pos]
    exact minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hp.pos) (by rw [map_sub, h, sub_self])
  have he := _root_.map_dvd (evalRingHom (1 : ℤ)) hd
  exact Int.modEq_of_dvd (by simpa only [coe_evalRingHom, eval_one_cyclotomic_prime, eval_sub]
    using he)

/-- If two integer polynomials agree at a `p`-th root of unity in a characteristic-zero ring,
their values at `1` agree modulo `p`. The root need not be primitive. -/
theorem eval_one_modEq_of_aeval_eq_of_pow_eq_one {A : Type*} [CommRing A] [CharZero A]
    (P Q : ℤ[X]) {p : ℕ} (hp : p.Prime) {ζ : A} (hζ : ζ ^ p = 1)
    (h : aeval ζ P = aeval ζ Q) : P.eval 1 ≡ Q.eval 1 [ZMOD (p : ℤ)] := by
  -- A prime avoiding the nonzero integers gives a characteristic-zero field specialization.
  let S := (ℤ⁰).map (Int.castRingHom A)
  have hS : Disjoint ((⊥ : Ideal A) : Set A) S := by
    refine Set.disjoint_left.2 ?_
    rintro x hx ⟨m, hm, rfl⟩
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hm) (Int.cast_eq_zero.mp (Ideal.mem_bot.mp hx))
  obtain ⟨I, hI, _, hIS⟩ := (⊥ : Ideal A).exists_le_prime_disjoint S hS
  have : CharZero (A ⧸ I) := charZero_of_inj_zero fun n hn ↦ by
    by_contra hn'
    exact Set.disjoint_left.mp hIS (Ideal.Quotient.eq_zero_iff_mem.mp hn)
      ⟨n, mem_nonZeroDivisors_iff_ne_zero.mpr (Int.natCast_ne_zero.mpr hn'), by simp⟩
  let K := FractionRing (A ⧸ I)
  let f : A →+* K := (algebraMap (A ⧸ I) K).comp (Ideal.Quotient.mk I)
  apply eval_one_modEq_of_aeval_eq_of_pow_eq_one_field P Q hp (ζ := f ζ)
  · simpa only [map_pow, map_one] using congrArg f hζ
  · simpa only [aeval_def, algebraMap_int_eq, ringHom_eval₂_intCastRingHom] using congrArg f h

end Polynomial

namespace Nat.Prime

open Polynomial

/-- If the cyclotomic evaluations of the rows `a i` vanish off `i₀`, and the row at `i₀`
evaluates to `e * ζ ^ k`, then the sum of their ordinary row sums weighted by `w` is
congruent to `e * w i₀` modulo `p`. In particular, if `w i₀ = 0`, the sum is divisible by `p`. -/
theorem sum_mul_sum_modEq_of_sum_mul_pow_eq_single {A ι : Type*} [CommRing A] [CharZero A]
    {p : ℕ} (hp : p.Prime) {ζ : A} (hζ : ζ ^ p = 1) (s : Finset ι) {i₀ : ι}
    (hi₀ : i₀ ∈ s) (a : ι → Fin p → ℤ) (w : ι → ℤ) {e : ℤ} {k : ℕ}
    (h₀ : ∑ j : Fin p, (a i₀ j : A) * ζ ^ j.val = (e : A) * ζ ^ k)
    (h : ∀ i ∈ s, i ≠ i₀ → ∑ j : Fin p, (a i j : A) * ζ ^ j.val = 0) :
    (∑ i ∈ s, w i * ∑ j : Fin p, a i j) ≡ e * w i₀ [ZMOD (p : ℤ)] := by
  let P : ℤ[X] := ∑ i ∈ s, C (w i) * ∑ j : Fin p, C (a i j) * X ^ j.val
  let Q : ℤ[X] := C (e * w i₀) * X ^ k
  have hPQ : aeval ζ P = aeval ζ Q := by
    simp only [P, Q, map_sum, map_mul, map_pow, aeval_C, aeval_X, algebraMap_int_eq,
      Int.coe_castRingHom]
    rw [Finset.sum_eq_single_of_mem i₀ hi₀ (fun i hi hne ↦ by rw [h i hi hne, mul_zero]), h₀]
    ring
  simpa only [P, Q, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one] using
    P.eval_one_modEq_of_aeval_eq_of_pow_eq_one Q hp hζ hPQ

end Nat.Prime
