/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import TauCeti.FieldTheory.Finite.PowNeOne

/-!
# The fibres of `b ↦ b ^ q * b` over a field with `q²` elements

Let `K` be a finite field with `q²` elements. The multiplicative map `N b = b ^ q * b = b ^ (q + 1)`
is the norm from `K` to its subfield with `q` elements, although that subfield plays no role in the
statements here. Every nonzero `c` with `c ^ q = c` has `c ^ (q - 1) = 1` and has exactly `q + 1`
preimages under `N`.

On `Kˣ`, the kernel of `b ↦ b ^ (q + 1)` has at most `q + 1` elements and its image lies in the
kernel of `c ↦ c ^ (q - 1)`, which has at most `q - 1` elements because `Kˣ` is cyclic. Their
product is `|Kˣ| = q² - 1 = (q + 1)(q - 1)`, so both bounds are equalities: the image is the whole
fixed unit group `{c ∈ Kˣ | c ^ q = c}`, and each fibre over it is a coset of the kernel of size
`q + 1`. Including `c = 0` makes `b ↦ b ^ q * b` onto all elements `c` with `c ^ q = c` without
introducing an `Algebra` structure over the fixed subfield (unlike Mathlib's
`FiniteField.norm_surjective`, which quantifies over an explicit base field).

When `q ≥ 3`, the unit group of `K` has `q² - 1 > q + 2` elements, so `b ^ (q + 1)` is not
identically one on `Kˣ`; its value at a witness `b` is a fixed element `c = b ^ q * b` distinct
from `0` and `1`. Together with `TauCeti.FiniteField.exists_pow_mul_self_eq`, this supplies the
rank-one unitary generation and commutator inputs for `SU₃(q)` when `q ≥ 3`.

## Main results

* `TauCeti.FiniteField.natCard_pow_mul_self_eq`: `#{b | b ^ q * b = c} = q + 1` whenever `q ≠ 0`,
  `c ≠ 0`, and `c ^ q = c`.
* `TauCeti.FiniteField.exists_pow_mul_self_eq`: every `c` with `c ^ q = c` is of the form
  `b ^ q * b`.
* `TauCeti.FiniteField.exists_pow_eq_self_and_ne_zero_and_ne_one`: when `3 ≤ q`, some `c` satisfies
  `c ^ q = c`, `c ≠ 0`, and `c ≠ 1`.
-/

public section

namespace TauCeti.FiniteField

variable {K : Type*} [Field K]

/-- In a field with `q²` elements (`q ≠ 0`), every nonzero `c` with `c ^ q = c` is of the form
`b ^ q * b` for exactly `q + 1` elements `b`. -/
theorem natCard_pow_mul_self_eq {q : ℕ} (hq : q ≠ 0) (hK : Nat.card K = q ^ 2) {c : K}
    (hc0 : c ≠ 0) (hc : c ^ q = c) : Nat.card {b : K // b ^ q * b = c} = q + 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (hK ▸ pow_ne_zero 2 hq)
  let := Fintype.ofFinite K
  let := Fintype.ofFinite Kˣ
  have hq1 : 1 < q := (Nat.one_lt_pow_iff two_ne_zero).mp (hK ▸ Finite.one_lt_card)
  have hqsub : 0 < q - 1 := Nat.sub_pos_of_lt hq1
  have hqsq : (q + 1) * (q - 1) = q ^ 2 - 1 := by rw [← Nat.sq_sub_sq, one_pow]
  let N : Kˣ →* Kˣ := powMonoidHom (q + 1)
  let M : Kˣ →* Kˣ := powMonoidHom (q - 1)
  -- Every `(b ^ (q + 1)) ^ (q - 1) = b ^ (q² - 1) = 1` in `Kˣ`.
  have hle : N.range ≤ M.ker := by
    rintro _ ⟨b, rfl⟩
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    simp only [N, M, powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_one, ← pow_mul, hqsq]
    rw [← hK, Nat.card_eq_fintype_card]
    exact _root_.FiniteField.pow_card_sub_one_eq_one (b : K) b.ne_zero
  -- In the cyclic group `Kˣ`, `x ^ k = 1` has at most `k` solutions for `k > 0`.
  have hkerN : Nat.card N.ker ≤ q + 1 := by
    rw [← SetLike.coe_sort_coe, Nat.card_eq_card_toFinset]
    exact (Finset.card_le_card fun x hx ↦ by simpa [N] using hx).trans
      (IsCyclic.card_pow_eq_one_le (α := Kˣ) (Nat.succ_pos q))
  have hkerM : Nat.card M.ker ≤ q - 1 := by
    rw [← SetLike.coe_sort_coe, Nat.card_eq_card_toFinset]
    exact (Finset.card_le_card fun x hx ↦ by simpa [M] using hx).trans
      (IsCyclic.card_pow_eq_one_le (α := Kˣ) hqsub)
  have hmul : Nat.card N.ker * Nat.card N.range = (q + 1) * (q - 1) := by
    rw [Subgroup.card_ker_mul_card_range, Nat.card_units, hK, hqsq]
  have hrange : Nat.card N.range ≤ q - 1 := (Subgroup.card_le_of_le hle).trans hkerM
  have hkerNq : Nat.card N.ker = q + 1 := by nlinarith
  have hrangeq : Nat.card N.range = q - 1 := by nlinarith
  -- `u = c` satisfies `u ^ (q - 1) = 1`, so `u` lies in `M.ker = N.range`.
  let u : Kˣ := Units.mk0 c hc0
  have humem : u ∈ N.range := by
    rw [Subgroup.eq_of_le_of_card_ge hle (hkerM.trans hrangeq.ge), MonoidHom.mem_ker]
    refine Units.ext (mul_left_cancel₀ hc0 ?_)
    calc c * ((M u : Kˣ) : K) = c ^ (1 + (q - 1)) := by simp [M, u, pow_add, pow_one]
      _ = c * 1 := by rw [Nat.add_sub_of_le hq1.le, hc, mul_one]
  obtain ⟨b₀, hb₀⟩ := humem
  -- Every solution `b : K` of `b ^ q * b = c ≠ 0` is a unit in the `N`-fibre over `N b₀ = u`.
  let e : {b : K // b ^ q * b = c} ≃ (N ⁻¹' {N b₀}) :=
    { toFun b := ⟨Units.mk0 b.1 (fun h ↦ hc0 (by rw [← b.2, h, mul_zero])),
        (Units.ext (by simp [N, u, pow_succ, b.2]) : _ = u).trans hb₀.symm⟩
      invFun b := ⟨b.1, by simpa [N, u, pow_succ] using congrArg Units.val (b.2.trans hb₀)⟩
      left_inv _ := Subtype.ext rfl
      right_inv _ := Subtype.ext (Units.ext rfl) }
  exact (Nat.card_congr (e.trans (N.fiberEquivKer b₀))).trans hkerNq

/-- In a field with `q²` elements, every `c` with `c ^ q = c` is of the form `b ^ q * b`. -/
theorem exists_pow_mul_self_eq {q : ℕ} (hK : Nat.card K = q ^ 2) {c : K}
    (hc : c ^ q = c) : ∃ b : K, b ^ q * b = c := by
  by_cases hq : q = 0
  · subst q
    exact ⟨1, by simpa using hc⟩
  by_cases hc0 : c = 0
  · subst c
    exact ⟨0, by simp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (hK ▸ pow_ne_zero 2 hq)
  have hpos : 0 < Nat.card {b : K // b ^ q * b = c} := by
    rw [natCard_pow_mul_self_eq hq hK hc0 hc]
    exact Nat.succ_pos q
  obtain ⟨⟨b, hb⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  exact ⟨b, hb⟩

/-- In a field with `q²` elements and `3 ≤ q`, some element `c` satisfies `c ^ q = c`, `c ≠ 0`,
and `c ≠ 1`. -/
theorem exists_pow_eq_self_and_ne_zero_and_ne_one {q : ℕ} (hq : 3 ≤ q) (hK : Nat.card K = q ^ 2) :
    ∃ c : K, c ^ q = c ∧ c ≠ 0 ∧ c ≠ 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  let := Fintype.ofFinite K
  obtain ⟨b, hb0, hb1⟩ := exists_ne_zero_pow_ne_one (F := K) (k := q + 1) (by omega)
    (by rw [hK]; nlinarith)
  refine ⟨b ^ q * b, ?_, mul_ne_zero (pow_ne_zero q hb0) hb0, ?_⟩
  · rw [mul_pow, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, _root_.FiniteField.pow_card,
      mul_comm]
  · rwa [← pow_succ]

end TauCeti.FiniteField
