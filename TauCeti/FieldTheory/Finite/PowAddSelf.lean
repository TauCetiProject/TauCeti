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

/-!
# The fibres of `b ↦ b ^ q + b` over a field with `q²` elements

Let `K` be a finite field with `q²` elements, where `q = p ^ n` is a power of the
characteristic. The map `T b = b ^ q + b` is additive, and it is the trace from `K` to its
subfield with `q` elements, although that subfield plays no role in the statement here. Every
`c` with `c ^ q = c` has exactly `q` preimages under `T`.

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

/-- In a field with `q²` elements, `q = p ^ n` a power of the exponential characteristic, every
`c` with `c ^ q = c` is of the form `b ^ q + b` for exactly `q` elements `b`. -/
theorem natCard_pow_add_self_eq (hK : Nat.card K = (p ^ n) ^ 2) {c : K}
    (hc : c ^ p ^ n = c) : Nat.card {b : K // b ^ p ^ n + b = c} = p ^ n := by
  classical
  have : Finite K :=
    Nat.finite_of_card_ne_zero
      (by rw [hK]; exact pow_ne_zero 2 (pow_ne_zero n (expChar_pos K p).ne'))
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hK
  set q := p ^ n with hqdef
  -- A field has at least two elements, so `q > 1`.
  have hq : 1 < q := (Nat.one_lt_pow_iff two_ne_zero).mp (hK ▸ Fintype.one_lt_card)
  -- The additive maps `T b = b ^ q + b` and `T' c = c ^ q - c`.
  let T : K →+ K := (iterateFrobenius K p n).toAddMonoidHom + .id K
  let T' : K →+ K := (iterateFrobenius K p n).toAddMonoidHom - .id K
  have hT (b : K) : T b = b ^ q + b := by simp [T, iterateFrobenius_def, hqdef]
  have hT' (c : K) : T' c = c ^ q - c := by simp [T', iterateFrobenius_def, hqdef]
  have hpow (b : K) : b ^ q ^ 2 = b := by rw [← hK]; exact FiniteField.pow_card b
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
    rw [AddSubgroup.card_ker_mul_card_range, Nat.card_eq_fintype_card, hK]
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

/-- In a field with `q²` elements, every `c` with `c ^ q = c` is of the form `b ^ q + b`. -/
theorem exists_pow_add_self_eq [Finite K] (hK : Nat.card K = (p ^ n) ^ 2) {c : K}
    (hc : c ^ p ^ n = c) : ∃ b : K, b ^ p ^ n + b = c := by
  have : Finite {b : K // b ^ p ^ n + b = c} := Subtype.finite
  have hpos : 0 < Nat.card {b : K // b ^ p ^ n + b = c} := by
    rw [natCard_pow_add_self_eq hK hc]
    exact pow_pos (expChar_pos K p) n
  obtain ⟨⟨b, hb⟩⟩ := Nat.card_pos_iff.mp hpos |>.1
  exact ⟨b, hb⟩

/-- **The twisted trace is onto.** In a field with `q²` elements, `q = p ^ n` a power of the
exponential characteristic, and for `ε = (-1) ^ k`, every `c` with `c ^ q = ε c` is of the form
`b + ε b ^ q`. -/
theorem exists_add_neg_one_pow_mul_pow_eq [Finite K] (hK : Nat.card K = (p ^ n) ^ 2) (k : ℕ)
    {c : K} (hc : c ^ p ^ n = (-1) ^ k * c) : ∃ b : K, b + (-1) ^ k * b ^ p ^ n = c := by
  rcases neg_one_pow_eq_or K k with h | h <;> rw [h] at hc ⊢
  · obtain ⟨b, hb⟩ := exists_pow_add_self_eq hK (one_mul c ▸ hc)
    exact ⟨b, by rw [one_mul, add_comm, hb]⟩
  · -- Scale a preimage `b₁` of `1` under `b ↦ b ^ q + b` by `c`.
    obtain ⟨b, hb⟩ := exists_pow_add_self_eq hK (one_pow (p ^ n))
    refine ⟨c * b, ?_⟩
    rw [mul_pow, hc]
    linear_combination c * hb

/-- **The twisted trace has a nonzero kernel element.** In a field with `q²` elements, `q = p ^ n`
a power of the exponential characteristic, and for `ε = (-1) ^ k`, some nonzero `b` satisfies
`b + ε b ^ q = 0`. -/
theorem exists_ne_zero_add_neg_one_pow_mul_pow_eq_zero [Finite K]
    (hK : Nat.card K = (p ^ n) ^ 2) (k : ℕ) : ∃ b ≠ (0 : K), b + (-1) ^ k * b ^ p ^ n = 0 := by
  rcases neg_one_pow_eq_or K k with h | h <;> rw [h]
  · -- The `q` roots of `b ^ q + b = 0` are not all zero.
    have : Finite {b : K // b ^ p ^ n + b = 0} := Subtype.finite
    have hq : 1 < p ^ n := (Nat.one_lt_pow_iff two_ne_zero).mp (hK ▸ Finite.one_lt_card)
    have hcard : 1 < Nat.card {b : K // b ^ p ^ n + b = 0} := by
      rwa [natCard_pow_add_self_eq hK (zero_pow (pow_pos (expChar_pos K p) n).ne')]
    have : Nontrivial {b : K // b ^ p ^ n + b = 0} := Finite.one_lt_card_iff_nontrivial.mp hcard
    have hzero : (0 : K) ^ p ^ n + 0 = 0 := by
      rw [zero_pow (pow_pos (expChar_pos K p) n).ne', add_zero]
    obtain ⟨⟨b, hb⟩, hne⟩ := exists_ne (⟨0, hzero⟩ : {b : K // b ^ p ^ n + b = 0})
    refine ⟨b, fun hb0 ↦ hne (Subtype.ext hb0), ?_⟩
    rw [one_mul, add_comm, hb]
  · exact ⟨1, one_ne_zero, by simp⟩

end FiniteField

end TauCeti
