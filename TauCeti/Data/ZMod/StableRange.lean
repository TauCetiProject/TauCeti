/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Stable range one for `ZMod n`

For every nonzero modulus `n`, the ring `ZMod n` has Bass stable range one: two residues `a` and
`b` generate the unit ideal if and only if some `ZMod n`-multiple shift `a + k * b` is a unit.
This is the unimodular row-shifting step behind transvection and normal-closure decompositions in
`SL(2, ZMod n)` when the upper-left entry of a matrix is not yet invertible.

The hypothesis `NeZero n` is essential: at `n = 0`, `ZMod 0 = ℤ` has stable range two rather than
one, since `5` and `7` are coprime in `ℤ` while `5 + 7 * k` is never `±1`.

## Main results

* `ZMod.exists_isUnit_add_mul`, `ZMod.exists_isUnit_add_mul_left`: if `IsCoprime a b` in `ZMod n`
  with `n ≠ 0`, there exists `k : ZMod n` such that `a + k * b` (respectively `a + b * k`) is a
  unit.
* `ZMod.isCoprime_iff_exists_isUnit_add_mul`, `ZMod.isCoprime_iff_exists_isUnit_add_mul_left`:
  characterizations of `IsCoprime a b` in `ZMod n` via unit shifts.

## References

* H. Bass, *`K`-theory and stable algebra*, Publ. Math. Inst. Hautes Études Sci. 22 (1964), 5–60,
  §4 (stable range one for semilocal rings).
-/

public section

namespace ZMod

/-- **Bass stable range one for `ZMod n`.** For `n ≠ 0`, if `a` and `b` are coprime in `ZMod n`,
some shift `a + k * b` is a unit. -/
theorem exists_isUnit_add_mul {n : ℕ} [NeZero n] {a b : ZMod n} (h : IsCoprime a b) :
    ∃ k : ZMod n, IsUnit (a + k * b) := by
  let P : Finset ℕ := n.primeFactors.filter fun p ↦ ¬ p ∣ a.val
  let k : ℕ := ∏ p ∈ P, p
  refine ⟨(k : ZMod n), ?_⟩
  have hval : a + (k : ZMod n) * b = ((a.val + k * b.val : ℕ) : ZMod n) := by
    push_cast
    rw [natCast_zmod_val, natCast_zmod_val]
  rw [hval, isUnit_iff_coprime]
  refine Nat.coprime_of_dvd' fun p hp hsum hpn ↦ ?_
  by_cases hpa : p ∣ a.val
  · have hpkb : p ∣ k * b.val := (Nat.dvd_add_right hpa).mp hsum
    have hpk : ¬ p ∣ k := by
      intro hpk
      obtain ⟨q, hqP, hpq⟩ := Prime.exists_mem_finset_dvd hp.prime hpk
      obtain ⟨hq_mem, hqa⟩ := Finset.mem_filter.mp hqP
      have hqp : p = q :=
        (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq_mem)).mp hpq
      exact hqa (hqp ▸ hpa)
    have hpb : p ∣ b.val := (hp.dvd_mul.mp hpkb).resolve_left hpk
    obtain ⟨u, v, huv⟩ := h
    have hp1 := congrArg (castHom hpn (ZMod p)) huv
    have ha0 : castHom hpn (ZMod p) a = 0 := by
      rw [castHom_apply, cast_eq_val, natCast_eq_zero_iff]
      exact hpa
    have hb0 : castHom hpn (ZMod p) b = 0 := by
      rw [castHom_apply, cast_eq_val, natCast_eq_zero_iff]
      exact hpb
    simp only [map_add, map_mul, map_one, ha0, hb0, mul_zero, add_zero] at hp1
    have : Fact p.Prime := ⟨hp⟩
    exact absurd hp1 zero_ne_one
  · have hpP : p ∈ P :=
      Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpn, NeZero.ne n⟩, hpa⟩
    have hpkb : p ∣ k * b.val := dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hpP) _
    exact False.elim (hpa ((Nat.dvd_add_left hpkb).mp hsum))

/-- Left-multiplied variant of `ZMod.exists_isUnit_add_mul`: if `IsCoprime a b` in `ZMod n` with
`n ≠ 0`, some shift `a + b * k` is a unit. -/
theorem exists_isUnit_add_mul_left {n : ℕ} [NeZero n] {a b : ZMod n} (h : IsCoprime a b) :
    ∃ k : ZMod n, IsUnit (a + b * k) := by
  obtain ⟨k, hk⟩ := exists_isUnit_add_mul h
  exact ⟨k, mul_comm k b ▸ hk⟩

/-- In `ZMod n` for `n ≠ 0`, two residues are coprime if and only if some shift `a + k * b` is a
unit. -/
theorem isCoprime_iff_exists_isUnit_add_mul {n : ℕ} [NeZero n] {a b : ZMod n} :
    IsCoprime a b ↔ ∃ k : ZMod n, IsUnit (a + k * b) := by
  refine ⟨exists_isUnit_add_mul, ?_⟩
  rintro ⟨k, u, hu⟩
  refine ⟨↑u⁻¹, ↑u⁻¹ * k, ?_⟩
  rw [mul_assoc, ← mul_add, ← hu, Units.inv_mul]

/-- Left-multiplied variant of `ZMod.isCoprime_iff_exists_isUnit_add_mul`. -/
theorem isCoprime_iff_exists_isUnit_add_mul_left {n : ℕ} [NeZero n] {a b : ZMod n} :
    IsCoprime a b ↔ ∃ k : ZMod n, IsUnit (a + b * k) := by
  simp_rw [mul_comm b, isCoprime_iff_exists_isUnit_add_mul]

end ZMod
