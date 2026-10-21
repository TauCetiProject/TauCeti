/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.ModEq

import Mathlib.Tactic.Ring

/-!
# The Chinese remainder theorem for arbitrary integer moduli

Two integer congruences have a common solution precisely when their residues agree modulo the
greatest common divisor of their moduli. The statement includes negative and zero moduli; in
particular, congruence modulo zero is equality.

Mathlib's `Int.modEq_and_modEq_iff_modEq_lcm` then describes the solution set, when nonempty, as
one congruence class modulo the least common multiple.

## Reference

Victor Shoup, *A Computational Introduction to Number Theory and Algebra*, Exercise 2.18.

## Provenance

The constructive proof was extracted from the principal-congruence-subgroup argument in
`TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic`. That argument was ported from
Chris Birkbeck's AINTLIB project (Apache-2.0), file
`LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Foundation.lean`.
-/

public section

namespace Int

/-- **Compatible integer congruences have a common solution.** If `x` and `y` agree modulo
`gcd(m, n)`, then some integer agrees with `x` modulo `m` and with `y` modulo `n`.

The formula from Bézout coefficients works without sign or nonzero hypotheses on the moduli. -/
theorem exists_modEq_and_modEq_of_modEq_gcd {m n x y : ℤ}
    (h : x ≡ y [ZMOD ↑(Int.gcd m n)]) :
    ∃ z : ℤ, z ≡ x [ZMOD m] ∧ z ≡ y [ZMOD n] := by
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨x + m * (Int.gcdA m n * k), ?_, ?_⟩
  · exact Int.modEq_iff_dvd.mpr ⟨-(Int.gcdA m n * k), by ring⟩
  · refine Int.modEq_iff_dvd.mpr ⟨Int.gcdB m n * k, ?_⟩
    have hy : y = x + (↑(Int.gcd m n) : ℤ) * k := by
      calc
        y = (y - x) + x := by ring
        _ = (↑(Int.gcd m n) : ℤ) * k + x := by rw [hk]
        _ = x + (↑(Int.gcd m n) : ℤ) * k := by ring
    rw [hy, Int.gcd_eq_gcd_ab]
    ring

/-- **The compatibility criterion for two integer congruences.** Congruences to `x` modulo `m`
and to `y` modulo `n` have a simultaneous solution exactly when `x` and `y` agree modulo
`gcd(m, n)`.

There are no sign or nonzero assumptions: a zero modulus imposes equality. -/
theorem exists_modEq_and_modEq_iff_modEq_gcd {m n x y : ℤ} :
    (∃ z : ℤ, z ≡ x [ZMOD m] ∧ z ≡ y [ZMOD n]) ↔
      x ≡ y [ZMOD ↑(Int.gcd m n)] := by
  constructor
  · rintro ⟨z, hzx, hzy⟩
    exact (hzx.of_dvd (Int.gcd_dvd_left m n)).symm.trans
      (hzy.of_dvd (Int.gcd_dvd_right m n))
  · exact exists_modEq_and_modEq_of_modEq_gcd

end Int

end
