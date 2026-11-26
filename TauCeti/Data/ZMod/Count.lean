/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.Harmonic.Defs

import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.Data.ZMod.FinEquiv
import TauCeti.GroupTheory.Coset.Fiber

/-!
# Counting residues by a condition on their reduction

A condition on `x : ZMod n` that only reads the reduction of `x` modulo a divisor of `n` can be
counted after reducing. This file records the two counting laws that result.

Reducing along a single divisor `m ∣ n` multiplies the count: the reduction `ZMod n → ZMod m`,
written here as `fun x ↦ (x.val : ZMod m)`, is a surjective additive homomorphism, so all of its
fibres have the same size and a condition pulled back along it holds proportionally often. The
identity is stated as `m * (count over ZMod n) = n * (count over ZMod m)`, which carries the same
information as a division by `m` without a quotient appearing.

Splitting a modulus into pairwise coprime factors multiplies the counts: conditions imposed on
the separate factors are independent, so the number of residues satisfying all of them is the
product of the individual counts. This is the Chinese remainder theorem `ZMod.prodEquivPi` in
counting form. In particular the number of roots modulo `n` of an integer polynomial is the product
of its numbers of roots modulo the prime powers exactly dividing `n`, by `ZMod.equivPi`.

Sums over the residues modulo `n` of a function of the least nonnegative representative are sums
over `range n`, and sums over `ZMod n` coincide with sums over the positive representatives
`Icc 1 n`; summed over the representatives that are multiples of `n / m`, for `m ∣ n`, they
become sums over the residues modulo `m`. As a special case of the first identity, the reciprocals
of the representatives sum to the harmonic number `H_{n-1}`.

## Main results

* `ZMod.mul_card_filter_natCast_val`: counting a condition on the reduction modulo `m ∣ n`.
* `ZMod.sum_comp_natCast_val`: summing a function of the reduction modulo `m ∣ n`.
* `ZMod.sum_val_eq_sum_range`: summing a function of the representatives over `range n`.
* `ZMod.sum_eq_sum_Icc`: summing a function on `ZMod n` over the positive representatives
  `Icc 1 n`.
* `ZMod.sum_val_filter_castHom_eq_sum_range`: summing a function of the representatives over a
  fibre of the reduction `ZMod (k * m) → ZMod m`.
* `ZMod.sum_inv_val_eq_harmonic`: the reciprocals of the representatives sum to `H_{n-1}`.
* `ZMod.sum_inv_val_le_one_add_log`: a logarithmic bound for reciprocal representatives.
* `ZMod.sum_Ico_mul`: splitting an integer interval into complete residue blocks.
* `ZMod.sum_ite_dvd_val`: summing over the representatives that are multiples of `n / m`.
* `ZMod.card_filter_forall_natCast_val`: counting independent conditions on coprime factors.
* `ZMod.natCard_aeval_eq_zero_eq_prod_primeFactors`: the number of roots of an integer polynomial
  modulo `n` is multiplicative over the prime-power factorization of `n`.
* `ZMod.natCard_aeval_eq_zero_eq_zero_of_dvd`: an integer polynomial with no roots modulo `m` has
  none modulo any multiple of `m`.
* `ZMod.card_filter_not_self_dvd_val`: the residues whose representative the modulus does not
  divide, the base case of such a count.
-/

public section

open Finset

open scoped Function -- for the `on` notation in `Pairwise (Nat.Coprime on a)`

namespace ZMod

variable {m n : ℕ}

/-- **Summing a function of the reduction modulo a divisor.** For `m ∣ n`, a function of the
reduction modulo `m` summed over the residues modulo `n` is `n / m` times its sum over the residues
modulo `m`: every fibre of the reduction has `n / m` elements. -/
theorem sum_comp_natCast_val {M : Type*} [AddCommMonoid M] [NeZero m] [NeZero n] (hmn : m ∣ n)
    (f : ZMod m → M) : ∑ x : ZMod n, f (x.val : ZMod m) = (n / m) • ∑ y : ZMod m, f y := by
  have hφ : Function.Surjective (castHom hmn (ZMod m) : ZMod n →+ ZMod m) :=
    castHom_surjective hmn
  -- summing `1` along the reduction shows that its kernel has `n / m` elements
  have hker := AddMonoidHom.sum_comp_of_surjective _ hφ fun _ ↦ (1 : ℕ)
  simp only [sum_const, card_univ, ZMod.card, smul_eq_mul, mul_one] at hker
  simpa only [AddMonoidHom.coe_ofClass, castHom_apply, natCast_val,
    Nat.eq_div_of_mul_eq_left (NeZero.ne m) hker.symm] using
    AddMonoidHom.sum_comp_of_surjective _ hφ f

/-- **Counting a condition on the reduction modulo a divisor.** For `m ∣ n`, the residues modulo
`n` whose reduction modulo `m` satisfies `Q` are `n / m` times as many as the residues modulo `m`
satisfying `Q`, stated without the quotient. -/
theorem mul_card_filter_natCast_val [NeZero m] [NeZero n] (hmn : m ∣ n)
    (Q : ZMod m → Prop) [DecidablePred Q] :
    m * #{x : ZMod n | Q (x.val : ZMod m)} = n * #{y : ZMod m | Q y} := by
  rw [card_filter, card_filter, sum_comp_natCast_val hmn fun y ↦ if Q y then 1 else 0,
    smul_eq_mul, ← mul_assoc, Nat.mul_div_cancel' hmn]

/-- **Summing over the representatives.** A function of the least nonnegative representative
summed over the residues modulo `n` is its sum over `range n`. -/
theorem sum_val_eq_sum_range {M : Type*} [AddCommMonoid M] [NeZero n] (f : ℕ → M) :
    ∑ x : ZMod n, f x.val = ∑ i ∈ range n, f i := by
  rw [Finset.sum_range, ← (finEquiv n).symm.toEquiv.sum_comp]
  simp

/-- **Summing over positive residue representatives.** For `n ≠ 0`, a sum over `ZMod n` equals
the sum over `Finset.Icc 1 n` obtained by replacing `0` with `n`. -/
theorem sum_eq_sum_Icc {A : Type*} [AddCommMonoid A] [NeZero n] (f : ZMod n → A) :
    ∑ x : ZMod n, f x = ∑ a ∈ Icc 1 n, f a := by
  have hval : ∑ x : ZMod n, f x = ∑ x : ZMod n, f (x.val : ZMod n) :=
    Finset.sum_congr rfl fun x _ => by rw [ZMod.natCast_zmod_val]
  have h0n : f (0 : ℕ) = f (n : ℕ) := by simp
  rw [hval, sum_val_eq_sum_range (fun a => f a), Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (NeZero.pos n), h0n,
    add_comm, ← Finset.sum_Ico_succ_top (NeZero.pos n), Finset.Ico_add_one_right_eq_Icc]

/-- **Summing over a fibre of the reduction.** The residues modulo `k * m` that reduce to
`x : ZMod m` have the representatives `x.val + m * j` for `j < k`, so a function of the
representative summed over them is its sum over these. -/
theorem sum_val_filter_castHom_eq_sum_range {M : Type*} [AddCommMonoid M] {k : ℕ} [NeZero k]
    [NeZero m] (x : ZMod m) (f : ℕ → M) :
    ∑ y : ZMod (k * m) with castHom (dvd_mul_left m k) (ZMod m) y = x, f y.val =
      ∑ j ∈ range k, f (x.val + m * j) := by
  have hm : 0 < m := NeZero.pos m
  have hcast (y : ZMod (k * m)) :
      castHom (dvd_mul_left m k) (ZMod m) y = x ↔ y.val % m = x.val := by
    rw [castHom_apply, cast_eq_val, ← (val_injective m).eq_iff, val_natCast]
  simp_rw [hcast]
  rw [sum_filter, sum_val_eq_sum_range (fun i ↦ if i % m = x.val then f i else 0), ← sum_filter]
  -- `i ↦ i / m` is a bijection from the representatives `i ≡ x.val` below `k m` onto `range k`.
  refine sum_nbij' (· / m) (x.val + m * ·) (fun i hi ↦ ?_) (fun j hj ↦ ?_) (fun i hi ↦ ?_)
    (fun j _ ↦ ?_) (fun i hi ↦ ?_)
  · simp only [mem_filter, mem_range] at hi
    simpa only [mem_range] using Nat.div_lt_of_lt_mul (by linarith [hi.1])
  · simp only [mem_range] at hj
    simp only [mem_filter, mem_range, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.val_lt,
      and_true]
    nlinarith [x.val_lt]
  · rw [← (mem_filter.1 hi).2, Nat.mod_add_div]
  · rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt x.val_lt, zero_add]
  · rw [← (mem_filter.1 hi).2, Nat.mod_add_div]

/-- **Summing the reciprocals of the representatives.** The reciprocals of the least nonnegative
representatives of the residues modulo `n` sum to the harmonic number `H_{n-1}`; the residue `0`
contributes `0⁻¹ = 0`. -/
theorem sum_inv_val_eq_harmonic {K : Type*} [DivisionRing K] [CharZero K] [NeZero n] :
    ∑ x : ZMod n, ((x.val : ℕ) : K)⁻¹ = harmonic (n - 1) := by
  rw [sum_val_eq_sum_range (fun i ↦ ((i : ℕ) : K)⁻¹)]
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [sum_range_succ', harmonic]
  push_cast
  simp

/-- The sum of reciprocal least nonnegative representatives of the nonzero residues is
bounded by one plus the logarithm of the modulus. -/
theorem sum_inv_val_le_one_add_log {N : ℕ} [NeZero N] :
    ∑ k ∈ univ.erase (0 : ZMod N), (k.val : ℝ)⁻¹ ≤ 1 + Real.log N := by
  have hh : ∑ j ∈ range N, (j : ℝ)⁻¹ ≤ (harmonic N : ℝ) := by
    rw [sum_range_eq_add_Ico _ (NeZero.pos N), harmonic_eq_sum_Icc]
    simp only [Nat.cast_zero, _root_.inv_zero, zero_add, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    exact sum_le_sum_of_subset_of_nonneg Ico_subset_Icc_self fun j _ _ ↦ by positivity
  have he : ∑ k ∈ univ.erase (0 : ZMod N), (k.val : ℝ)⁻¹ =
      ∑ k : ZMod N, (k.val : ℝ)⁻¹ := by
    rw [← sum_erase_add _ _ (mem_univ (0 : ZMod N))]
    simp
  rw [he, ZMod.sum_val_eq_sum_range (fun j ↦ (j : ℝ)⁻¹)]
  exact hh.trans (harmonic_le_one_add_log N)

/-- Split a sum over an integer interval with endpoints divisible by the modulus into
complete residue blocks. The summand need not be periodic. -/
theorem sum_Ico_mul {A : Type*} [AddCommMonoid A] [NeZero n] (l u : ℤ) (f : ℤ → A) :
    ∑ z ∈ Ico l u, ∑ a : ZMod n, f ((a.val : ℤ) + n * z) =
      ∑ k ∈ Ico (n * l) (n * u), f k := by
  classical
  rw [← sum_product' (Ico l u) univ (fun z (a : ZMod n) ↦ f ((a.val : ℤ) + n * z))]
  refine sum_bij (fun p _ ↦ (p.2.val : ℤ) + n * p.1) ?_ ?_ ?_ (by intros; rfl)
  · rintro ⟨z, a⟩ hp
    have hz := mem_Ico.mp (mem_product.mp hp).1
    have ha := a.val_lt
    simp only [mem_Ico]
    constructor <;> nlinarith
  · rintro ⟨z, a⟩ _ ⟨w, b⟩ hq hab
    have hab' := congrArg (fun k : ℤ ↦ (k : ZMod n)) hab
    simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_mul,
      ZMod.natCast_self, zero_mul, add_zero] at hab'
    subst b
    have hn : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have : z = w := mul_left_cancel₀ hn (add_left_cancel hab)
    simp [this]
  · intro k hk
    obtain ⟨z, hz⟩ := (ZMod.intCast_eq_iff n k (k : ZMod n)).mp rfl
    refine ⟨(z, k), mem_product.mpr ⟨?_, mem_univ _⟩, hz.symm⟩
    have ha := (k : ZMod n).val_lt
    have hk := mem_Ico.mp hk
    simp only [mem_Ico]
    constructor <;> nlinarith

/-- **Summing over the multiples of `n / m`.** For `m ∣ n`, the representatives modulo `n` that
are multiples of `n / m` are the `(n / m) y` with `y < m`, so a function of the quotient summed
over them is its sum over the residues modulo `m`. -/
theorem sum_ite_dvd_val {M : Type*} [AddCommMonoid M] [NeZero m] [NeZero n] (hmn : m ∣ n)
    (f : ℕ → M) :
    ∑ x : ZMod n, (if n / m ∣ x.val then f (x.val / (n / m)) else 0) = ∑ y : ZMod m, f y.val := by
  obtain ⟨L, rfl⟩ := hmn
  have hL : 0 < L := Nat.pos_of_mul_pos_left (NeZero.pos (m * L))
  rw [Nat.mul_div_cancel_left _ (NeZero.pos m),
    sum_val_eq_sum_range (fun i ↦ if L ∣ i then f (i / L) else 0), sum_val_eq_sum_range f,
    ← sum_filter, eq_comm]
  -- the multiples of `L` below `m * L` are the `q * L` with `q < m`
  refine sum_nbij' (· * L) (· / L) (fun q hq ↦ ?_) (fun i hi ↦ ?_)
    (fun q _ ↦ Nat.mul_div_cancel q hL) (fun i hi ↦ Nat.div_mul_cancel (mem_filter.mp hi).2)
    fun q _ ↦ congrArg f (Nat.mul_div_cancel q hL).symm
  · exact mem_filter.mpr
      ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_right (mem_range.mp hq) hL), dvd_mul_left L q⟩
  · exact mem_range.mpr (Nat.div_lt_of_lt_mul (mul_comm m L ▸ mem_range.mp (mem_filter.mp hi).1))

/-- **All residues but zero have a representative the modulus does not divide.** A representative
is smaller than the modulus, so the modulus divides it exactly when it vanishes. -/
@[simp]
theorem card_filter_not_self_dvd_val [NeZero m] : #{z : ZMod m | ¬m ∣ z.val} = m - 1 := by
  -- the modulus divides a representative exactly when the residue vanishes
  simp only [← natCast_eq_zero_iff, natCast_zmod_val]
  rw [filter_ne', card_erase_of_mem (mem_univ 0), card_univ, ZMod.card]

/-- **Counting independent conditions on coprime factors.** If the moduli `a i` are pairwise
coprime, the residues modulo `∏ i, a i` whose reduction modulo each `a i` satisfies `Q i` are
counted by the product over `i` of the residues modulo `a i` satisfying `Q i`. -/
theorem card_filter_forall_natCast_val {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (hcop : Pairwise (Nat.Coprime on a)) [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (Q : ∀ i, ZMod (a i) → Prop) [∀ i, DecidablePred (Q i)] :
    #{x : ZMod (∏ i, a i) | ∀ i, Q i (x.val : ZMod (a i))}
      = ∏ i, #{y : ZMod (a i) | Q i y} := by
  classical
  have hval : ∀ (x : ZMod (∏ i, a i)) (i : ι),
      ((x.val : ZMod (a i))) = prodEquivPi a hcop x i := fun x i => by
    rw [prodEquivPi_apply, castHom_apply, natCast_val]
  have e : {x : ZMod (∏ i, a i) // ∀ i, Q i (x.val : ZMod (a i))} ≃
      ∀ i, {y : ZMod (a i) // Q i y} :=
    ((prodEquivPi a hcop).toEquiv.subtypeEquiv fun x => by simp only [hval]; rfl).trans
      Equiv.subtypePiEquivPi
  simpa only [Fintype.card_subtype, Fintype.card_pi] using Fintype.card_congr e

/-- **Counting roots prime power by prime power.** For `n ≠ 0`, the number of roots modulo `n` of
an integer polynomial `P` is the product, over the primes `p ∣ n`, of its numbers of roots modulo
the exact prime powers `p ^ vₚ(n)`. -/
theorem natCard_aeval_eq_zero_eq_prod_primeFactors (hn : n ≠ 0) (P : Polynomial ℤ) :
    Nat.card {x : ZMod n // Polynomial.aeval x P = 0} =
      ∏ p ∈ n.primeFactors,
        Nat.card {x : ZMod (p ^ n.factorization p) // Polynomial.aeval x P = 0} := by
  let e := equivPi n hn
  have he (x : ZMod n) (p : n.primeFactors) :
      Polynomial.aeval (e x p) P = e (Polynomial.aeval x P) p :=
    Polynomial.aeval_algHom_apply ((Pi.evalRingHom _ p).comp e.toRingHom).toIntAlgHom x P
  have e' : {x : ZMod n // Polynomial.aeval x P = 0} ≃
      ∀ p : n.primeFactors, {y : ZMod (p ^ n.factorization p) // Polynomial.aeval y P = 0} :=
    (e.toEquiv.subtypeEquiv fun x ↦ by
      rw [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_eq_zero_iff e e.injective,
        funext_iff]
      simp only [he, Pi.zero_apply]).trans Equiv.subtypePiEquivPi
  rw [Nat.card_congr e', Nat.card_pi, Finset.prod_coe_sort n.primeFactors
    (fun p ↦ Nat.card {y : ZMod (p ^ n.factorization p) // Polynomial.aeval y P = 0})]

/-- **No roots modulo a divisor.** If an integer polynomial `P` has no roots modulo `m`, then it
has none modulo any multiple `n` of `m`, since a root modulo `n` reduces to one modulo `m`. -/
theorem natCard_aeval_eq_zero_eq_zero_of_dvd (hmn : m ∣ n) {P : Polynomial ℤ}
    (hP : ∀ y : ZMod m, Polynomial.aeval y P ≠ 0) :
    Nat.card {x : ZMod n // Polynomial.aeval x P = 0} = 0 := by
  refine Nat.card_eq_zero.mpr (.inl ⟨fun ⟨x, hx⟩ ↦ hP (castHom hmn (ZMod m) x) ?_⟩)
  have h := Polynomial.aeval_algHom_apply (castHom hmn (ZMod m)).toIntAlgHom x P
  rwa [hx, map_zero] at h

end ZMod
