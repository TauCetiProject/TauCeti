/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Totient
public import TauCeti.NumberTheory.Modular.Invariants.Geometry
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Elliptic.Gamma.Zero
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Projective
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Cusp.Count

/-!
# Congruence specializations of modular-triple invariants (`Γ₀(N)`)

Using the geometric comparison theorems from `TauCeti.NumberTheory.Modular.Invariants.Geometry`,
this file evaluates the combinatorial invariants of `TauCeti.CongruenceSubgroup.Gamma0Projective N`:

* **Cusp counts and widths**: `cuspCount_Gamma0Projective`, `cuspCount_Gamma0Projective_of_prime`,
  and `cuspWidths_Gamma0Projective_of_prime`.
* **Elliptic point counts**: closed forms `ellipticTwo_Gamma0Projective_eq_prod` and
  `ellipticThree_Gamma0Projective_eq_prod`.
* **Worked invariant vectors**: `invariants_Gamma0Projective_two` (`(3, 0, 1, 0, {1, 2})`) and
  `invariants_Gamma0Projective_eleven` (`(12, 1, 0, 0, {1, 11})`).

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer, 2005, §3.8.
-/

public section

open Matrix Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups

namespace TauCeti.ModularGroup

variable {n : ℕ}

/-- **Cusp count of `Γ₀(N)`.** For every positive `N`, `cuspCount (Gamma0Projective N) e` equals
`∑_{g ∣ N} φ(gcd(g, N / g))`. -/
theorem cuspCount_Gamma0Projective (N : ℕ) [NeZero N]
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective N ≃ Fin n) :
    cuspCount (TauCeti.CongruenceSubgroup.Gamma0Projective N) e =
      ∑ g ∈ N.divisors, Nat.totient (Nat.gcd g (N / g)) := by
  rw [cuspCount_eq_card_fuchsianCuspOrbit, ← Subgroup.map_liftSL_sl2zToPSL2R,
    TauCeti.CongruenceSubgroup.liftSL_Gamma0Projective, TauCeti.card_cuspOrbit_Gamma0]

/-- For prime `p`, `Γ₀(p)` has `2` cusps. -/
theorem cuspCount_Gamma0Projective_of_prime {p : ℕ} [Fact p.Prime]
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective p ≃ Fin n) :
    cuspCount (TauCeti.CongruenceSubgroup.Gamma0Projective p) e = 2 := by
  rw [cuspCount_eq_card_fuchsianCuspOrbit, ← Subgroup.map_liftSL_sl2zToPSL2R,
    TauCeti.CongruenceSubgroup.liftSL_Gamma0Projective, TauCeti.card_cuspOrbit_Gamma0_of_prime]

/-- For prime `p`, the cusp widths of `Γ₀(p)` are `{1, p}` (at the cusps `∞` of width `1` and
`0` of width `p`). -/
theorem cuspWidths_Gamma0Projective_of_prime {p : ℕ} [Fact p.Prime]
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective p ≃ Fin n) :
    cuspWidths (TauCeti.CongruenceSubgroup.Gamma0Projective p) e = {1, p} := by
  have hp : p.Prime := Fact.out
  have hT : (_root_.ModularGroup.T : PSL(2, ℤ)) ∈
      TauCeti.CongruenceSubgroup.Gamma0Projective p := by
    rw [TauCeti.CongruenceSubgroup.mem_Gamma0Projective_mk, CongruenceSubgroup.Gamma0_mem]
    simp [_root_.ModularGroup.T]
  have h1 : 1 ∈ cuspWidths (TauCeti.CongruenceSubgroup.Gamma0Projective p) e :=
    (Nat.dvd_one.mp <| (minimalPeriod_permT_dvd_iff _ e 1 1).mpr (by simp [hT])) ▸
      minimalPeriod_permT_mem_cuspWidths _ e (e ((1 : PSL(2, ℤ)) : _))
  have hcard : (cuspWidths (TauCeti.CongruenceSubgroup.Gamma0Projective p) e).card = 2 := by
    rw [card_cuspWidths, cuspCount_Gamma0Projective_of_prime]
  have hsum : (cuspWidths (TauCeti.CongruenceSubgroup.Gamma0Projective p) e).sum = p + 1 := by
    rw [sum_cuspWidths, ← (TauCeti.CongruenceSubgroup.Gamma0Projective p).index_eq_of_equiv e,
      TauCeti.CongruenceSubgroup.Gamma0Projective_index,
      CongruenceSubgroup.Gamma0_prime_index p hp]
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem h1
  have hct : t.card = 1 := by rw [ht, Multiset.card_cons] at hcard; omega
  obtain ⟨w, rfl⟩ := Multiset.card_eq_one.mp hct
  have hw : w = p := by rw [ht, Multiset.sum_cons, Multiset.sum_singleton] at hsum; omega
  rw [ht, hw]; rfl

/-- **Closed form of `ε₂(Γ₀(N))`.** The combinatorial count
`ellipticTwo (Gamma0Projective N) e` equals `0` when `4 ∣ N`, and `∏_{p ∣ N} (1 + χ₄(p))`
otherwise. -/
theorem ellipticTwo_Gamma0Projective_eq_prod (N : ℕ)
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective N ≃ Fin n) :
    (ellipticTwo (TauCeti.CongruenceSubgroup.Gamma0Projective N) e : ℤ) =
      if 4 ∣ N then 0 else ∏ p ∈ N.primeFactors, (1 + ZMod.χ₄ p) := by
  rw [ellipticTwo_eq_card_orderTwoEllipticOrbits, ← Subgroup.map_liftSL_sl2zToPSL2R,
    TauCeti.CongruenceSubgroup.liftSL_Gamma0Projective,
    TauCeti.card_orderTwoElliptic_Gamma0_eq_prod]

/-- **Closed form of `ε₃(Γ₀(N))`.** The combinatorial count
`ellipticThree (Gamma0Projective N) e` equals `0` when `9 ∣ N`, and
`∏_{p ∣ N} (1 + (p | 3))` otherwise. -/
theorem ellipticThree_Gamma0Projective_eq_prod (N : ℕ)
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective N ≃ Fin n) :
    (ellipticThree (TauCeti.CongruenceSubgroup.Gamma0Projective N) e : ℤ) =
      if 9 ∣ N then 0 else ∏ p ∈ N.primeFactors, (1 + legendreSym 3 p) := by
  rw [ellipticThree_eq_card_orderThreeEllipticOrbits, ← Subgroup.map_liftSL_sl2zToPSL2R,
    TauCeti.CongruenceSubgroup.liftSL_Gamma0Projective,
    TauCeti.card_orderThreeElliptic_Gamma0_eq_prod]

private theorem invariants_Gamma0Projective_of_prime {p g e₂ e₃ : ℕ} (hp : p.Prime)
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective p ≃ Fin n)
    (h2 : (if 4 ∣ p then (0 : ℤ) else 1 + ZMod.χ₄ p) = e₂)
    (h3 : (if 9 ∣ p then (0 : ℤ) else 1 + legendreSym 3 p) = e₃)
    (hg : 12 * g + 3 * e₂ + 4 * e₃ = p + 1) :
    invariants (TauCeti.CongruenceSubgroup.Gamma0Projective p) e =
      ⟨p + 1, g, e₂, e₃, {1, p}⟩ := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : n = p + 1 := by
    rw [← (TauCeti.CongruenceSubgroup.Gamma0Projective p).index_eq_of_equiv e,
      TauCeti.CongruenceSubgroup.Gamma0Projective_index,
      CongruenceSubgroup.Gamma0_prime_index p hp]
  have he₂ : ellipticTwo (TauCeti.CongruenceSubgroup.Gamma0Projective p) e = e₂ := by
    have h := ellipticTwo_Gamma0Projective_eq_prod p e
    rw [hp.primeFactors, Finset.prod_singleton, h2] at h; exact_mod_cast h
  have he₃ : ellipticThree (TauCeti.CongruenceSubgroup.Gamma0Projective p) e = e₃ := by
    have h := ellipticThree_Gamma0Projective_eq_prod p e
    rw [hp.primeFactors, Finset.prod_singleton, h3] at h; exact_mod_cast h
  have hc : cuspCount (TauCeti.CongruenceSubgroup.Gamma0Projective p) e = 2 :=
    cuspCount_Gamma0Projective_of_prime e
  have hgf : genus (TauCeti.CongruenceSubgroup.Gamma0Projective p) e = g := by
    have := genus_formula (TauCeti.CongruenceSubgroup.Gamma0Projective p) e; omega
  ext <;> simp [hn, hgf, he₂, he₃, cuspWidths_Gamma0Projective_of_prime]

/-- **Worked check on `Γ₀(2)`**: invariant vector `(3, 0, 1, 0, {1, 2})`. -/
theorem invariants_Gamma0Projective_two
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective 2 ≃ Fin n) :
    invariants (TauCeti.CongruenceSubgroup.Gamma0Projective 2) e = ⟨3, 0, 1, 0, {1, 2}⟩ :=
  invariants_Gamma0Projective_of_prime Nat.prime_two e (by norm_num [ZMod.χ₄])
    (by split_ifs <;> decide) rfl

/-- **Worked check on `Γ₀(11)`**: invariant vector `(12, 1, 0, 0, {1, 11})`, the first prime
level of positive genus. -/
theorem invariants_Gamma0Projective_eleven
    (e : PSL(2, ℤ) ⧸ TauCeti.CongruenceSubgroup.Gamma0Projective 11 ≃ Fin n) :
    invariants (TauCeti.CongruenceSubgroup.Gamma0Projective 11) e = ⟨12, 1, 0, 0, {1, 11}⟩ :=
  invariants_Gamma0Projective_of_prime (by decide) e (by norm_num [ZMod.χ₄])
    (by split_ifs <;> decide) rfl

end TauCeti.ModularGroup
