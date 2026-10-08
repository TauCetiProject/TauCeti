/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.ZMod.Units
public import Mathlib.Data.ZMod.QuotientRing

/-!
# Divisibility read off congruences modulo `n`

Facts about integers read off congruences in `ZMod n`, and divisibility inside the ring `ZMod n`
itself.

A linear congruence with unit coefficient is solvable: if `b` is a unit modulo `n`, then some
residue `j : ZMod n` satisfies `n ∣ a - j.val * b` over `ℤ`. The solution is `j = a b⁻¹`, and it
is returned as a residue class together with its canonical representative `j.val`, which is the
form a coset representative indexed by `Fin n` needs.

`ZMod.exists_dvd_sub_val_mul` was extracted from
`TauCeti/NumberTheory/ModularForms/CongruenceSubgroups.lean`, where it was private; that index
calculation was ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/CongruenceIndex.lean`, Chris Birkbeck, Apache-2.0). The lemma is
consumed there and in `HeckeRing/GL2/Gamma1/CoprimeCosets.lean`.

`ZMod.natCast_dvd_val_sub_of_unitsMap_eq` is adapted from the same project (Chris Birkbeck,
`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `2baa76f74`, file
`projects/LeanModularForms/LeanModularForms/Eigenforms/ConductorTheorem.lean`, declaration
`natCast_val_sub_dvd_of_unitsMap_eq` (:665). Two departures from the source: it is stated for an
arbitrary divisor `d ∣ N` rather than only for the reduction modulo `N / l`, which is all its
proof uses, and the name places the divisibility in Mathlib's operand order.

## Main results

* `ZMod.exists_dvd_sub_val_mul`: the congruence `j b ≡ a (mod n)` has a solution `j : ZMod n`
  whenever `b` is a unit modulo `n`.
* `ZMod.natCast_dvd_val_sub_of_unitsMap_eq`: two units with the same image under `ZMod.unitsMap`
  along `d ∣ N` have representatives congruent modulo `d`, as integers.
* `ZMod.intCast_lcm_eq_of_eq_of_eq`: one residue modulo `lcm a b` from the residues modulo `a`
  and `b` — the Chinese remainder theorem for a single integer.
* `ZMod.natCast_natAbs_eq_of_mul_nonneg`: congruent integers with nonnegative product have
  congruent absolute values.
* `ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd`: a residue modulo `n` is determined by its
  reductions modulo the prime powers dividing `n`.
* `ZMod.equivPi_apply`: the components of Mathlib's Chinese remainder isomorphism `ZMod.equivPi`
  are the reductions modulo the prime powers exactly dividing `n`.
* `ZMod.dvd_of_forall_mul_eq_zero`: divisibility inside `ZMod n` from annihilators: if every `r`
  with `r d = 0` has `r x = 0`, then `d ∣ x`.
-/

public section

namespace ZMod

/-- **A linear congruence with unit coefficient is solvable.** If `b` is a unit modulo `n`, then
`n ∣ a - j.val * b` for some `j : ZMod n`, namely `j = a b⁻¹`. -/
lemma exists_dvd_sub_val_mul (n : ℕ) [NeZero n] (a b : ℤ)
    (hb : IsUnit ((b : ℤ) : ZMod n)) : ∃ j : ZMod n, (n : ℤ) ∣ a - (j.val : ℤ) * b := by
  obtain ⟨u, hu⟩ := hb
  refine ⟨(a : ZMod n) * ↑u⁻¹, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, mul_assoc]
  -- the coerced product collapses: `↑b = ↑u` by `hu`, and `u⁻¹ * u = 1` in the units
  have hunit : (↑u⁻¹ * ((b : ℤ) : ZMod n) : ZMod n) = 1 := by rw [← hu, Units.inv_mul]
  rw [hunit, mul_one, sub_self]

/-- **From equal reductions to an integer congruence.** Two units with the same image under the
reduction `(ZMod N)ˣ → (ZMod d)ˣ` along `d ∣ N` have representatives congruent modulo `d`, as
integers. This is the bridge from unit bookkeeping to statements about integer matrix entries. -/
theorem natCast_dvd_val_sub_of_unitsMap_eq {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N)
    (u u' : (ZMod N)ˣ) (h_eq : unitsMap hd u = unitsMap hd u') :
    (d : ℤ) ∣ (((u : ZMod N).val : ℤ) - ((u' : ZMod N).val : ℤ)) := by
  have h_cast : castHom hd (ZMod d) (u : ZMod N) = castHom hd (ZMod d) (u' : ZMod N) := by
    have hh := congr_arg Units.val h_eq
    rwa [unitsMap_val, unitsMap_val] at hh
  rw [← intCast_eq_intCast_iff_dvd_sub]
  push_cast
  rw [natCast_val (u' : ZMod N), natCast_val (u : ZMod N),
    ← castHom_apply (h := hd) (u' : ZMod N), ← castHom_apply (h := hd) (u : ZMod N), h_cast]

/-- **One residue modulo a least common multiple** from the residues modulo the two moduli: the
Chinese remainder theorem `Int.modEq_and_modEq_iff_modEq_lcm`, read in `ZMod`. -/
theorem intCast_lcm_eq_of_eq_of_eq {a b : ℕ} {x y : ℤ} (ha : (x : ZMod a) = y)
    (hb : (x : ZMod b) = y) : (x : ZMod (Nat.lcm a b)) = y := by
  rw [ZMod.intCast_eq_intCast_iff] at ha hb ⊢
  have hlcm : (↑(Nat.lcm a b) : ℤ) = ↑(Int.lcm (a : ℤ) (b : ℤ)) := by simp [Int.lcm, Nat.lcm]
  rw [hlcm, ← Int.modEq_and_modEq_iff_modEq_lcm]
  exact ⟨ha, hb⟩

/-- **Congruent integers with nonnegative product have congruent absolute values.** If
`z * w ≥ 0` and `z ≡ w` modulo `m`, then `|z| ≡ |w|` modulo `m`. -/
theorem natCast_natAbs_eq_of_mul_nonneg {m : ℕ} {z w : ℤ} (hzw : 0 ≤ z * w)
    (h : (z : ZMod m) = w) : (z.natAbs : ZMod m) = w.natAbs := by
  rcases hzw.lt_or_eq with hzw | hzw
  · rcases pos_and_pos_or_neg_and_neg_of_mul_pos hzw with ⟨hz, hw⟩ | ⟨hz, hw⟩ <;>
      simp [← Int.cast_natCast (R := ZMod m), abs_of_pos, abs_of_neg, hz, hw, h]
  -- if one of them vanishes, both are divisible by `m`, and so are their absolute values
  rcases mul_eq_zero.mp hzw.symm with rfl | rfl
  · rw [Int.cast_zero, eq_comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    rw [Int.natAbs_zero, Nat.cast_zero, eq_comm, ZMod.natCast_eq_zero_iff]
    exact Int.natCast_dvd.mp h
  · rw [Int.cast_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    rw [Int.natAbs_zero, Nat.cast_zero, ZMod.natCast_eq_zero_iff]
    exact Int.natCast_dvd.mp h

/-- **A residue is determined by its reductions modulo prime powers.** Two residues modulo `n`
whose reductions modulo every prime power `p ^ k` dividing `n` agree are equal: the Chinese
remainder theorem in its uniqueness form, along the prime factorization of `n`. -/
theorem eq_of_forall_cast_eq_of_prime_pow_dvd {n : ℕ} [NeZero n] {x y : ZMod n}
    (h : ∀ p k : ℕ, p.Prime → k ≠ 0 → p ^ k ∣ n → (cast x : ZMod (p ^ k)) = cast y) : x = y := by
  -- The difference is the cast of its value, which `n` divides because every prime power
  -- dividing `n` does.
  rw [← sub_eq_zero, ← natCast_zmod_val (x - y), natCast_eq_zero_iff]
  refine (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr fun p k hp hpk ↦ ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  rw [← natCast_eq_zero_iff, natCast_val, cast_sub hpk, h p k hp hk hpk, sub_self]

/-- The component at `p` of the Chinese remainder isomorphism `ZMod.equivPi` is reduction modulo
`p ^ n.factorization p`. -/
@[simp]
theorem equivPi_apply (n : ℕ) (hn : n ≠ 0) (x : ZMod n) (p : n.primeFactors) :
    equivPi n hn x p = castHom (Nat.ordProj_dvd n p) (ZMod (p ^ n.factorization p)) x :=
  RingHom.congr_fun
    (Subsingleton.elim ((Pi.evalRingHom _ p).comp (equivPi n hn).toRingHom)
      (castHom (Nat.ordProj_dvd n p) (ZMod (p ^ n.factorization p)))) x

/-- **Divisibility in `ℤ/nℤ` from annihilators.** If every `r : ZMod n` with `r * d = 0` also has
`r * x = 0`, then `d ∣ x`. With `g = gcd(d, n)`, the element `n / g` kills `d`, hence `x`, so `g`
divides `x`; and `g = d * d⁻¹` is a multiple of `d` in `ZMod n` (`ZMod.mul_inv_eq_gcd`). -/
theorem dvd_of_forall_mul_eq_zero {n : ℕ} [NeZero n] {d x : ZMod n}
    (h : ∀ r : ZMod n, r * d = 0 → r * x = 0) : d ∣ x := by
  set g := Nat.gcd d.val n with hg
  obtain ⟨m, hm⟩ : g ∣ n := Nat.gcd_dvd_right _ _
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun h0 => NeZero.ne n (by rw [hm, h0, mul_zero])
  -- `m = n / g` kills `d`
  have hmd : (m : ZMod n) * d = 0 := by
    obtain ⟨k, hk⟩ : g ∣ d.val := Nat.gcd_dvd_left _ _
    rw [← natCast_zmod_val d, ← Nat.cast_mul, natCast_eq_zero_iff, hk]
    exact ⟨k, by rw [← mul_assoc, mul_comm m g, ← hm]⟩
  -- hence `m` kills `x`, so `g ∣ x.val`
  have hgx : g ∣ x.val := by
    have hmx := h _ hmd
    rw [← natCast_zmod_val x, ← Nat.cast_mul, natCast_eq_zero_iff] at hmx
    refine (Nat.mul_dvd_mul_iff_left hmpos).1 ?_
    rwa [mul_comm m g, ← hm]
  calc d ∣ (g : ZMod n) := ⟨d⁻¹, (mul_inv_eq_gcd d).symm⟩
    _ ∣ (x.val : ZMod n) := Nat.cast_dvd_cast hgx
    _ = x := natCast_zmod_val x

end ZMod
