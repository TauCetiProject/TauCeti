/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Index
import TauCeti.FieldTheory.Finite.Card
import TauCeti.SetTheory.Cardinal.Finite

/-!
# The fibres of `b ↦ b ^ q + b` over a field with `q²` elements

Let `K` be a field with `Nat.card K = q ^ 2`. For `q ≠ 0` it is a finite field with `q²`
elements, and `q = p ^ n` is a power of its characteristic `p`. The statements take only `q`,
with no characteristic assumed; the proof of the count recovers `p` and `n`. The map
`T b = b ^ q + b` is additive, and it is the trace from `K` to its subfield with `q` elements,
although that subfield plays no role in the statement here. For `q ≠ 0`, every `c` with
`c ^ q = c` has exactly `q` preimages under `T`.

The kernel of `T` consists of roots of `X ^ q + X`, and its image of roots of `X ^ q - X`, since
`(b ^ q + b) ^ q = b ^ (q²) + b ^ q = b + b ^ q`. So both have at most `q` elements. Their
product is `|K| = q²`, so both have exactly `q` elements. The image is then the whole root set
of `X ^ q - X` in `K`, and each fibre over it is a coset of the kernel.

This is the count behind the order `q³` of the translation group of the Hermitian function
field: for `a ∈ K`, the element `c = a ^ (q + 1)` satisfies `c ^ q = c`.

For `ε = ±1` the twisted trace `b ↦ b + ε b ^ q` is then onto the elements `c` with
`c ^ q = ε c`, and has a nonzero kernel element. For `ε = 1` this is the count above; for
`ε = -1` the element `1` is in the kernel, and `b = c b₁` with `b₁ ^ q + b₁ = 1` is a preimage of
`c`. These are the two conditions on the form of the finite unitary groups under which their
action on isotropic points is transitive with central kernel.

## Main results

* `TauCeti.FiniteField.natCard_pow_add_self_eq`: `#{b | b ^ q + b = c} = q` whenever
  `c ^ q = c`.
* `TauCeti.FiniteField.exists_pow_add_self_eq`: every `c` with `c ^ q = c` is of the form
  `b ^ q + b`.
* `TauCeti.FiniteField.exists_add_neg_one_pow_mul_pow_eq`: for `ε = (-1) ^ k`, every `c` with
  `c ^ q = ε c` is of the form `b + ε b ^ q`.
* `TauCeti.FiniteField.exists_ne_zero_add_neg_one_pow_mul_pow_eq_zero`: for `ε = (-1) ^ k`, some
  nonzero `b` satisfies `b + ε b ^ q = 0`.
-/

public section

open Polynomial

namespace TauCeti

namespace FiniteField

variable {K : Type*} [Field K] {p n : ℕ} [ExpChar K p]

/-- The count of `natCard_pow_add_self_eq` with `q = p ^ n` written as a power of the exponential
characteristic `p`, the form in which the Frobenius `iterateFrobenius K p n` computes `b ^ q`. -/
private theorem natCard_pow_pow_add_self_eq (hK : Nat.card K = (p ^ n) ^ 2) {c : K}
    (hc : c ^ p ^ n = c) : Nat.card {b : K // b ^ p ^ n + b = c} = p ^ n := by
  classical
  have := finite_of_natCard_eq_pow (expChar_pow_pos K p n).ne' hK
  have := Fintype.ofFinite K
  have hq := one_lt_of_natCard_eq_pow (expChar_pow_pos K p n).ne' hK
  set q := p ^ n with hqdef
  -- The additive maps `T b = b ^ q + b` and `T' c = c ^ q - c`.
  let T : K →+ K := (iterateFrobenius K p n).toAddMonoidHom + .id K
  let T' : K →+ K := (iterateFrobenius K p n).toAddMonoidHom - .id K
  have hT (b : K) : T b = b ^ q + b := by simp [T, iterateFrobenius_def, hqdef]
  have hT' (c : K) : T' c = c ^ q - c := by simp [T', iterateFrobenius_def, hqdef]
  have hpow (b : K) : b ^ q ^ 2 = b := by rw [← hK]; exact pow_natCard b
  -- The image of `T` lies in the kernel of `T'`, since `(b ^ q + b) ^ q = b + b ^ q`.
  have hle : T.range ≤ T'.ker := by
    rintro _ ⟨b, rfl⟩
    rw [AddMonoidHom.mem_ker, hT', hT, hqdef, add_pow_expChar_pow]
    -- `(b ^ q) ^ q = b ^ q ^ 2 = b`, as `K` has `q ^ 2` elements.
    rw [← pow_mul, ← sq, hpow]
    ring
  -- The kernels of `T` and `T'` consist of roots of `X ^ q + X` and `X ^ q - X`.
  have hX1 : (X ^ q + X : K[X]).natDegree = q := by
    rw [natDegree_add_eq_left_of_degree_lt] <;> simp [hq]
  have hker : Nat.card T.ker ≤ q := by
    rw [← SetLike.coe_sort_coe, Nat.card_eq_card_toFinset]
    refine (card_le_degree_of_subset_roots fun b hb ↦ ?_).trans hX1.le
    rw [mem_roots (ne_zero_of_natDegree_gt (hX1 ▸ hq))]
    simpa [hT] using hb
  have hker' : Nat.card T'.ker ≤ q := by
    rw [← SetLike.coe_sort_coe, Nat.card_eq_card_toFinset]
    refine (card_le_degree_of_subset_roots fun c hc ↦ ?_).trans
      (natDegree_X_pow_sub_X (R := K) hq).le
    rw [mem_roots (X_pow_sub_X_ne_zero hq)]
    simpa [hT'] using hc
  -- `|ker T| · |im T| = q²` and both factors are at most `q`, so both are `q`.
  have hmul : Nat.card T.ker * Nat.card T.range = q ^ 2 := by
    rw [AddSubgroup.card_ker_mul_card_range, hK]
  have hrange : Nat.card T.range ≤ q := (AddSubgroup.card_le_of_le hle).trans hker'
  have hkerq : Nat.card T.ker = q := by nlinarith
  have hrangeq : Nat.card T.range = q := by nlinarith
  -- Hence the image of `T` is the whole kernel of `T'`, which contains `c`.
  have hcmem : c ∈ T.range := by
    rw [AddSubgroup.eq_of_le_of_card_ge hle (hker'.trans hrangeq.ge), AddMonoidHom.mem_ker, hT',
      hc, sub_self]
  -- The fibre over `c = T b₀` is in bijection with the kernel of `T`.
  obtain ⟨b₀, rfl⟩ := hcmem
  refine (Nat.card_congr ?_).trans hkerq
  exact (Equiv.subtypeEquivRight fun b ↦ by simp [hT]).trans (T.fiberEquivKer b₀)

/-- In a field `K` with `Nat.card K = q ^ 2` for some `q ≠ 0`, every `c` with `c ^ q = c` is of the
form `b ^ q + b` for exactly `q` elements `b`. No characteristic is assumed: `K` is then finite of
order `q²`, so `q` is a power `p ^ n` of its characteristic, which the proof recovers. The
hypothesis `q ≠ 0` is needed: over `ℚ`, where `Nat.card ℚ = 0 = 0 ^ 2`, the element `c = 1` has
`c ^ 0 = c` and the single preimage `0` under `b ↦ b ^ 0 + b`. -/
theorem natCard_pow_add_self_eq {q : ℕ} (hq : q ≠ 0) (hK : Nat.card K = q ^ 2) {c : K}
    (hc : c ^ q = c) : Nat.card {b : K // b ^ q + b = c} = q := by
  have := finite_of_natCard_eq_pow hq hK
  have := Fintype.ofFinite K
  -- `q` divides the order `p ^ m` of `K`, so it is a power `p ^ n` of the characteristic `p`.
  obtain ⟨p, hchar, m, hprime, hcard⟩ := _root_.FiniteField.card' K
  let : CharP K p := hchar
  let : Fact p.Prime := ⟨hprime⟩
  have hdvd : q ∣ p ^ (m : ℕ) := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨n, -, rfl⟩ := (Nat.dvd_prime_pow hprime).mp hdvd
  exact natCard_pow_pow_add_self_eq hK hc

/-- In a field `K` with `Nat.card K = q ^ 2`, every `c` with `c ^ q = c` is of the form
`b ^ q + b`. At `q = 0` the field is infinite, `c ^ 0 = c` forces `c = 1`, and `b = 0` works. -/
theorem exists_pow_add_self_eq {q : ℕ} (hK : Nat.card K = q ^ 2) {c : K}
    (hc : c ^ q = c) : ∃ b : K, b ^ q + b = c := by
  rcases eq_or_ne q 0 with rfl | hq
  · exact ⟨0, by simpa using hc⟩
  have hpos : 0 < Nat.card {b : K // b ^ q + b = c} := by
    rw [natCard_pow_add_self_eq hq hK hc]
    exact Nat.pos_of_ne_zero hq
  obtain ⟨⟨b, hb⟩⟩ := Nat.card_pos_iff.mp hpos |>.1
  exact ⟨b, hb⟩

/-- **The twisted trace is onto.** In a field `K` with `Nat.card K = q ^ 2`, and for
`ε = (-1) ^ k`, every `c` with `c ^ q = ε c` is of the form `b + ε b ^ q`. -/
theorem exists_add_neg_one_pow_mul_pow_eq {q : ℕ} (hK : Nat.card K = q ^ 2) (k : ℕ)
    {c : K} (hc : c ^ q = (-1) ^ k * c) : ∃ b : K, b + (-1) ^ k * b ^ q = c := by
  rcases neg_one_pow_eq_or K k with h | h <;> rw [h] at hc ⊢
  · obtain ⟨b, hb⟩ := exists_pow_add_self_eq hK (one_mul c ▸ hc)
    exact ⟨b, by rw [one_mul, add_comm, hb]⟩
  · -- Scale a preimage `b₁` of `1` under `b ↦ b ^ q + b` by `c`.
    obtain ⟨b, hb⟩ := exists_pow_add_self_eq hK (one_pow q)
    refine ⟨c * b, ?_⟩
    rw [mul_pow, hc]
    linear_combination c * hb

/-- **The twisted trace has a nonzero kernel element.** In a field `K` with `Nat.card K = q ^ 2`,
and for `ε = (-1) ^ k`, some nonzero `b` satisfies `b + ε b ^ q = 0`. At `q = 0` this is
`b + ε = 0`, solved by `b = -ε`. -/
theorem exists_ne_zero_add_neg_one_pow_mul_pow_eq_zero {q : ℕ}
    (hK : Nat.card K = q ^ 2) (k : ℕ) : ∃ b ≠ (0 : K), b + (-1) ^ k * b ^ q = 0 := by
  rcases neg_one_pow_eq_or K k with h | h <;> rw [h]
  · rcases eq_or_ne q 0 with rfl | hq0
    · exact ⟨-1, neg_ne_zero.mpr one_ne_zero, by simp⟩
    -- The `q` roots of `b ^ q + b = 0` are not all zero.
    have hq := one_lt_of_natCard_eq_pow hq0 hK
    have hcard : 1 < {b : K | b ^ q + b = 0}.ncard := by
      rwa [← Nat.card_coe_set_eq, Set.coe_ofPred, natCard_pow_add_self_eq hq0 hK (zero_pow hq0)]
    obtain ⟨b, hb, hne⟩ := Set.exists_ne_of_one_lt_ncard hcard 0
    refine ⟨b, hne, ?_⟩
    rw [one_mul, add_comm]
    exact hb
  · exact ⟨1, one_ne_zero, by simp⟩

/-- The quadratic finite-field involution admits an element of trace one, in every
characteristic. -/
theorem exists_add_iterateFrobenius_eq_one (hK : Nat.card K = (p ^ n) ^ 2) :
    ∃ t : K, t + iterateFrobenius K p n t = 1 := by
  obtain ⟨t, ht⟩ := exists_pow_add_self_eq hK (one_pow (p ^ n))
  exact ⟨t, by simpa [iterateFrobenius_def, add_comm] using ht⟩

/-- Over a field of order `q²`, the affine trace equation
`z + z ^ q = x ^ q * x` has exactly `q³` solutions `(z, x)`. -/
theorem natCard_add_pow_eq_pow_mul {q : ℕ} (hK : Nat.card K = q ^ 2) :
    Nat.card {c : K × K // c.1 + c.1 ^ q = c.2 ^ q * c.2} = q ^ 3 := by
  classical
  by_cases hq : q = 0
  · subst q
    let e : {c : K × K // c.1 + c.1 ^ 0 = c.2 ^ 0 * c.2} ≃ K :=
      { toFun c := c.val.1
        invFun z := ⟨(z, z + 1), by simp⟩
        left_inv c := by
          apply Subtype.ext
          exact Prod.ext rfl (by simpa using c.property)
        right_inv z := rfl }
    simpa using (Nat.card_congr e).trans hK
  have := finite_of_natCard_eq_pow hq hK
  let := Fintype.ofFinite K
  have hpow (a : K) : a ^ q ^ 2 = a := by rw [← hK]; exact pow_natCard a
  have hfib (x : K) : Nat.card {z : K // z ^ q + z = x ^ q * x} = q := by
    apply natCard_pow_add_self_eq hq hK
    rw [mul_pow, ← pow_mul, ← sq, hpow, mul_comm]
  let e : {c : K × K // c.1 + c.1 ^ q = c.2 ^ q * c.2} ≃
      {c : K × K // c.2 ^ q + c.2 = c.1 ^ q * c.1} :=
    Equiv.subtypeEquiv (Equiv.prodComm K K) (by intro c; simp [add_comm])
  rw [Nat.card_congr e,
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      fun x z : K => z ^ q + z = x ^ q * x), Nat.card_sigma]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, hK]
  ring

end FiniteField

end TauCeti
