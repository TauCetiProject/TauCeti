/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.GCD
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# The congruence `n ∣ c d' - c' d + j c c'`

For integer pairs `(c, d)` and `(c', d')`, the divisibility `n ∣ c d' - c' d + j c c'` for some
integer `j` is the condition for two cusps of `Γ₀(n)` to be equivalent. This file records how it
interacts with `gcd(c, n)`.

## Main results

* `TauCeti.Int.isCoprime_div_gcd_div_gcd`: dividing `c` and `n` by `gcd(c, n)` leaves coprime
  quotients.
* `TauCeti.Int.gcd_dvd_of_dvd_mul_sub_mul_add_mul`: if `c` is prime to `d`, the congruence
  forces `gcd(c, n) ∣ c'`.
* `TauCeti.Int.gcd_eq_gcd_of_dvd_mul_sub_mul_add_mul`: if both pairs are coprime, the congruence
  forces `gcd(c, n) = gcd(c', n)`.
* `TauCeti.Int.gcd_dvd_mul_sub_mul_of_dvd_mul_sub_mul_add_mul` and
  `TauCeti.Int.exists_dvd_mul_sub_mul_add_mul_of_gcd_dvd`: writing `n = g m`, `c = g c₁` and
  `c' = g c₁'`, the congruence holds for some `j` exactly when `gcd(g, m) ∣ c₁ d' - c₁' d`
  (the converse needing `c₁` and `c₁'` prime to `m`).

Their consumers are the cusp counts of `Γ₀(N)` and `Γ₁(N)` in
`TauCeti/NumberTheory/ModularForms/CongruenceSubgroups/Cusp/`.
-/

public section

namespace TauCeti.Int

/-- Dividing an integer `c` and a nonzero natural number `n` by `gcd(c, n)` leaves coprime
quotients. This is `isCoprime_div_gcd_div_gcd` with the gcd taken in `ℕ`, the form in which it
describes `c / gcd(c, n)` as a residue modulo `n / gcd(c, n)`. -/
theorem isCoprime_div_gcd_div_gcd {n : ℕ} (hn : n ≠ 0) (c : ℤ) :
    IsCoprime (c / Int.gcd c n) ((n / Int.gcd c n : ℕ) : ℤ) := by
  rw [Int.natCast_div, Int.isCoprime_iff_gcd_eq_one]
  exact Int.gcd_ediv_gcd_ediv_gcd_of_ne_zero_right (by exact_mod_cast hn)

/-- If `n ∣ c d' - c' d + j c c'` and `c` is prime to `d`, then `gcd(c, n)` divides `c'`. -/
theorem gcd_dvd_of_dvd_mul_sub_mul_add_mul {n c d c' d' j : ℤ} (hcd : IsCoprime c d)
    (h : n ∣ c * d' - c' * d + j * c * c') : (Int.gcd c n : ℤ) ∣ c' := by
  have hc : (Int.gcd c n : ℤ) ∣ c := Int.gcd_dvd_left ..
  have h' : (Int.gcd c n : ℤ) ∣ c' * d := by
    have := dvd_sub (dvd_add (hc.mul_right d') ((hc.mul_left j).mul_right c'))
      ((Int.gcd_dvd_right ..).trans h)
    convert this using 1
    ring
  exact (hcd.of_isCoprime_of_dvd_left hc).dvd_of_dvd_mul_right h'

/-- The congruence `n ∣ c d' - c' d + j c c'` between coprime pairs forces
`gcd(c, n) = gcd(c', n)`. -/
theorem gcd_eq_gcd_of_dvd_mul_sub_mul_add_mul {n c d c' d' j : ℤ} (hcd : IsCoprime c d)
    (hcd' : IsCoprime c' d') (h : n ∣ c * d' - c' * d + j * c * c') :
    Int.gcd c n = Int.gcd c' n := by
  have h' : n ∣ c' * d - c * d' + -j * c' * c := by
    convert dvd_neg.mpr h using 1
    ring
  exact Nat.dvd_antisymm
    (Int.dvd_gcd (gcd_dvd_of_dvd_mul_sub_mul_add_mul hcd h) (Int.gcd_dvd_right ..))
    (Int.dvd_gcd (gcd_dvd_of_dvd_mul_sub_mul_add_mul hcd' h') (Int.gcd_dvd_right ..))

/-- Write `n = g m`, `c = g c₁` and `c' = g c₁'`. Then `n ∣ c d' - c' d + j c c'` implies
`gcd(g, m) ∣ c₁ d' - c₁' d`. -/
theorem gcd_dvd_mul_sub_mul_of_dvd_mul_sub_mul_add_mul {n : ℤ} {g m : ℕ}
    {c c₁ d c' c₁' d' j : ℤ} (hg : g ≠ 0) (hn : n = g * m) (hc : c = g * c₁)
    (hc' : c' = g * c₁') (h : n ∣ c * d' - c' * d + j * c * c') :
    (Nat.gcd g m : ℤ) ∣ c₁ * d' - c₁' * d := by
  subst hc hc'
  have he : (g : ℤ) * c₁ * d' - g * c₁' * d + j * (g * c₁) * (g * c₁') =
      g * (c₁ * d' - c₁' * d + j * g * c₁ * c₁') := by ring
  rw [hn, he] at h
  have hm := (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right g m)).trans
    (Int.dvd_of_mul_dvd_mul_left (by exact_mod_cast hg) h)
  have hg' : (Nat.gcd g m : ℤ) ∣ j * g * c₁ * c₁' :=
    ((Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left g m)).mul_left j).mul_right _ |>.mul_right _
  simpa using dvd_sub hm hg'

/-- Conversely, write `n = g m`, `c = g c₁` and `c' = g c₁'`. If `c₁` and `c₁'` are prime to `m`
and `gcd(g, m) ∣ c₁ d' - c₁' d`, then some `j` satisfies `n ∣ c d' - c' d + j c c'`. -/
theorem exists_dvd_mul_sub_mul_add_mul_of_gcd_dvd {n : ℤ} {g m : ℕ} {c c₁ d c' c₁' d' : ℤ}
    (hn : n = g * m) (hc : c = g * c₁) (hc' : c' = g * c₁')
    (hc₁ : IsCoprime c₁ m) (hc₁' : IsCoprime c₁' m)
    (h : (Nat.gcd g m : ℤ) ∣ c₁ * d' - c₁' * d) :
    ∃ j : ℤ, n ∣ c * d' - c' * d + j * c * c' := by
  subst hc hc'
  obtain ⟨w, hw⟩ := h
  obtain ⟨u, v, huv⟩ := hc₁.mul_left hc₁'
  have he := Nat.gcd_eq_gcd_ab g m
  refine ⟨-(Nat.gcdA g m * u * w),
    Nat.gcdB g m * w + g * Nat.gcdA g m * v * w, ?_⟩
  rw [hn]
  linear_combination (g : ℤ) * hw + g * w * he - g ^ 2 * Nat.gcdA g m * w * huv

end TauCeti.Int
