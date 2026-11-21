/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.FieldTheory.Finite.EulerCriterion
import TauCeti.FieldTheory.Finite.PowNeOne
import TauCeti.GroupTheory.SpecificGroups.Cyclic.PowMonoidHom

/-!
# The quadratic norm `b ↦ b ^ q * b` over a field with `q²` elements

Let `K` be a finite field with `q²` elements. The map `b ↦ b ^ q * b = b ^ (q + 1)` is the
quadratic field norm from `K` to its fixed subfield `{c : K | c ^ q = c}` of `q` elements, written
without requiring an explicit `Algebra` structure over the fixed subfield. On the cyclic unit group
`Kˣ` of order `q² - 1 = (q + 1)(q - 1)`, the `(q + 1)`-th power map has kernel of order `q + 1`
(`IsCyclic.card_powMonoidHom_ker`) and image `{c ∈ Kˣ | c ^ (q - 1) = 1}`
(`IsCyclic.mem_range_powMonoidHom_iff`, equivalently Euler's criterion
`TauCeti.FiniteField.exists_pow_eq_iff_pow_card_sub_one_div_eq_one`). Thus every nonzero fixed
element has exactly `q + 1` preimages, and including `0` shows that the norm is surjective onto
`{c : K | c ^ q = c}`. When `3 ≤ q`, `q² - 1 > q + 1` yields a fixed element distinct from `0`
and `1`, which supplies the `|𝔽_q| ≥ 3` condition (excluding `SU₃(2)`) for the finite unitary
groups `SU_{r+1}(q)` / `²A_r(q)`.

## Main results

* `TauCeti.FiniteField.natCard_pow_mul_self_eq`: `#{b | b ^ q * b = c} = q + 1` whenever `c ≠ 0`
  and `c ^ q = c`.
* `TauCeti.FiniteField.exists_pow_mul_self_eq`: every `c` with `c ^ q = c` is of the form
  `b ^ q * b`.
* `TauCeti.FiniteField.exists_pow_eq_self_and_ne_zero_and_ne_one`: when `3 ≤ q`, some `c` satisfies
  `c ^ q = c`, `c ≠ 0`, and `c ≠ 1`.

## References

The file layout and statement style follow the additive trace companion
`TauCeti.FieldTheory.Finite.PowAddSelf` (`TauCeti.FiniteField.natCard_pow_add_self_eq` and
`TauCeti.FiniteField.exists_pow_add_self_eq`); surjectivity for an explicit `Algebra` structure is
Mathlib's `FiniteField.norm_surjective`.
-/

public section

namespace TauCeti.FiniteField

variable {K : Type*} [Field K]

/-- In a field with `q²` elements, every nonzero `c` with `c ^ q = c` is of the form `b ^ q * b`
for exactly `q + 1` elements `b`. -/
theorem natCard_pow_mul_self_eq {q : ℕ} (hK : Nat.card K = q ^ 2) {c : K}
    (hc0 : c ≠ 0) (hc : c ^ q = c) : Nat.card {b : K // b ^ q * b = c} = q + 1 := by
  by_cases hq : q = 0
  · subst hq
    have hc1 : c = 1 := by simpa using hc.symm
    have : Unique {b : K // b ^ 0 * b = c} :=
      { default := ⟨1, by simp [hc1]⟩
        uniq := fun ⟨b, hb⟩ ↦ Subtype.ext (by simpa [hc1] using hb) }
    exact Nat.card_unique
  have : Finite K := Nat.finite_of_card_ne_zero (hK ▸ pow_ne_zero 2 hq)
  have hq1 : 1 < q := (Nat.one_lt_pow_iff two_ne_zero).mp (hK ▸ Finite.one_lt_card)
  have hqsq : (q + 1) * (q - 1) = q ^ 2 - 1 := by rw [← Nat.sq_sub_sq, one_pow]
  have hcard : Nat.card Kˣ = (q + 1) * (q - 1) := by rw [Nat.card_units, hK, hqsq]
  have hdvd : q + 1 ∣ Nat.card Kˣ := ⟨q - 1, hcard⟩
  let N : Kˣ →* Kˣ := powMonoidHom (q + 1)
  have hkerN : Nat.card N.ker = q + 1 := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hdvd]
  let u : Kˣ := Units.mk0 c hc0
  have humem : u ∈ N.range := by
    rw [IsCyclic.mem_range_powMonoidHom_iff, Nat.gcd_eq_right hdvd, hcard,
      Nat.mul_div_cancel_left _ (Nat.succ_pos q)]
    refine Units.ext (mul_left_cancel₀ hc0 ?_)
    calc c * ((u ^ (q - 1) : Kˣ) : K) = c ^ (1 + (q - 1)) := by simp [u, pow_add, pow_one]
      _ = c * 1 := by rw [Nat.add_sub_of_le hq1.le, hc, mul_one]
  obtain ⟨b₀, hb₀⟩ := humem
  let e : {b : K // b ^ q * b = c} ≃ (N ⁻¹' {N b₀}) :=
    { toFun b := ⟨Units.mk0 b.val (fun h ↦ hc0 (by rw [← b.property, h, mul_zero])),
        (Units.ext (by simp [N, u, pow_succ, b.property]) : _ = u).trans hb₀.symm⟩
      invFun b :=
        ⟨b.val, by simpa [N, u, pow_succ] using congrArg Units.val (b.property.trans hb₀)⟩
      left_inv _ := Subtype.ext rfl
      right_inv _ := Subtype.ext (Units.ext rfl) }
  exact (Nat.card_congr (e.trans (N.fiberEquivKer b₀))).trans hkerN

/-- In a field with `q²` elements, every `c` with `c ^ q = c` is of the form `b ^ q * b`. -/
theorem exists_pow_mul_self_eq {q : ℕ} (hK : Nat.card K = q ^ 2) {c : K}
    (hc : c ^ q = c) : ∃ b : K, b ^ q * b = c := by
  by_cases hq : q = 0
  · exact ⟨1, by subst q; simpa using hc⟩
  by_cases hc0 : c = 0
  · exact ⟨0, by subst c; simp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (hK ▸ pow_ne_zero 2 hq)
  have hq1 : 1 < q := (Nat.one_lt_pow_iff two_ne_zero).mp (hK ▸ Finite.one_lt_card)
  have hqsq : (q + 1) * (q - 1) = q ^ 2 - 1 := by rw [← Nat.sq_sub_sq, one_pow]
  have hdvd : q + 1 ∣ Nat.card K - 1 := ⟨q - 1, by rw [hK, hqsq]⟩
  obtain ⟨b, hb⟩ := (exists_pow_eq_iff_pow_card_sub_one_div_eq_one hdvd hc0).mpr (by
    rw [hK, ← hqsq, Nat.mul_div_cancel_left _ (Nat.succ_pos q)]
    refine mul_left_cancel₀ hc0 ?_
    calc c * c ^ (q - 1) = c ^ (1 + (q - 1)) := by rw [pow_add, pow_one]
      _ = c * 1 := by rw [Nat.add_sub_of_le hq1.le, hc, mul_one])
  exact ⟨b, by simpa [pow_succ] using hb⟩

/-- In a field with `q²` elements and `3 ≤ q`, some element `c` satisfies `c ^ q = c`, `c ≠ 0`,
and `c ≠ 1`. -/
theorem exists_pow_eq_self_and_ne_zero_and_ne_one {q : ℕ} (hq : 3 ≤ q) (hK : Nat.card K = q ^ 2) :
    ∃ c : K, c ^ q = c ∧ c ≠ 0 ∧ c ≠ 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  let := Fintype.ofFinite K
  obtain ⟨b, hb0, hb1⟩ := exists_ne_zero_pow_ne_one (F := K) (k := q + 1) (by omega)
    (by rw [hK]; nlinarith)
  refine ⟨b ^ q * b, ?_, mul_ne_zero (pow_ne_zero q hb0) hb0, by rwa [← pow_succ]⟩
  rw [mul_pow, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, _root_.FiniteField.pow_card,
    mul_comm]

end TauCeti.FiniteField
