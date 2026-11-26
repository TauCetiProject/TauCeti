/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Ore.Basic
public import TauCeti.NumberTheory.LocalField.Padic

/-!
# Ore admissibility over `ℚ_[p]`

This module specializes Ore's admissibility predicate (`TauCeti.IsOreAdmissible 𝒪[ℚ_[p]] n j`)
to the `p`-adic numbers `ℚ_[p]` for a prime `p`. It defines the computable predicate
`TauCeti.IsOreAdmissiblePadic p n j` and proves `TauCeti.isOreAdmissible_padic_iff`: a wild
exponent `j` arises from a totally ramified degree-`n` subextension inside `SeparableClosure ℚ_[p]`
(when `p` is prime) if and only if `0 < n` and
`min(v_p(j % n) * n, v_p(n) * n) ≤ j ≤ v_p(n) * n`, reading `v_p(0) = ∞`.

## Main definitions

* `TauCeti.IsOreAdmissiblePadic p n j`: computable predicate on `(p, n, j)` characterizing Ore
  admissibility over `ℚ_[p]` for prime `p`.

## Main results

* `TauCeti.isOreAdmissible_padic_iff`: Ore's inequality characterizing admissible wild exponents for
  degree-`n` totally ramified subextensions of `SeparableClosure ℚ_[p]` (Pauli–Roblot,
  Proposition 3.1).

## References

* Ø. Ore, *Newtonsche Polygone in der Theorie der algebraischen Körper*, Math. Ann. **99** (1928),
  84–117.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a p-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Proposition 3.1.
-/

public section

open ValuativeRel IsDiscreteValuationRing

namespace TauCeti

/-- **Ore's `p`-adic admissibility predicate** (Pauli–Roblot, Proposition 3.1): computable condition
on `(p, n, j)`. When `p` is prime, it is equivalent to `IsOreAdmissible 𝒪[ℚ_[p]] n j`
(`TauCeti.isOreAdmissible_padic_iff`), i.e., to the existence of a totally ramified degree-`n`
subextension of `SeparableClosure ℚ_[p]` with wild exponent `j`. -/
@[expose] def IsOreAdmissiblePadic (p n j : ℕ) : Prop :=
  0 < n ∧
    (if j % n = 0 then padicValNat p n * n
      else min (padicValNat p (j % n) * n) (padicValNat p n * n)) ≤ j ∧
      j ≤ padicValNat p n * n

instance (p n j : ℕ) : Decidable (IsOreAdmissiblePadic p n j) := by
  delta IsOreAdmissiblePadic
  infer_instance

noncomputable section

/-- **Ore's inequality over `ℚ_[p]`** (Pauli–Roblot, Proposition 3.1): for prime `p`, a wild
exponent `j` is Ore-admissible for degree `n` over `𝒪[ℚ_[p]]` (equivalently, occurs for a totally
ramified degree-`n` subextension inside `SeparableClosure ℚ_[p]`) if and only if
`IsOreAdmissiblePadic p n j` holds, i.e., `0 < n` and
`min(v_p(j % n) * n, v_p(n) * n) ≤ j ≤ v_p(n) * n`, with `v_p(0)` read as `∞` so that `n ∣ j`
requires `j = v_p(n) * n`. -/
theorem isOreAdmissible_padic_iff (p : ℕ) [Fact p.Prime] {n j : ℕ} :
    IsOreAdmissible 𝒪[ℚ_[p]] n j ↔ IsOreAdmissiblePadic p n j := by
  rw [IsOreAdmissiblePadic]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hn0 : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hvn : addVal 𝒪[ℚ_[p]] (n : 𝒪[ℚ_[p]]) = (padicValNat p n : ℕ∞) := by
    rw [TauCeti.IsDiscreteValuationRing.addVal_natCast ℚ_[p] n hn0,
      _root_.Padic.natCastValuation_eq_padicValNat]
  have hdiv := Nat.div_add_mod j n
  have hlt := Nat.mod_lt j hn
  rcases Nat.eq_zero_or_pos (j % n) with hmod | hmod
  · rw [isOreAdmissible_iff_of_mod_eq_zero hmod, ite_eq_left hmod, hvn]
    simp only [hn, true_and, ENat.natCast_inj]
    rw [hmod, add_zero, Nat.mul_comm n (j / n)] at hdiv
    rw [← hdiv, ← le_antisymm_iff, Nat.mul_div_cancel _ hn, Nat.mul_left_inj hn.ne', eq_comm]
  · have hb0 : ((j % n : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hmod.ne'
    have hvb : addVal 𝒪[ℚ_[p]] ((j % n : ℕ) : 𝒪[ℚ_[p]]) = (padicValNat p (j % n) : ℕ∞) := by
      rw [TauCeti.IsDiscreteValuationRing.addVal_natCast ℚ_[p] (j % n) hb0,
        _root_.Padic.natCastValuation_eq_padicValNat]
    rw [isOreAdmissible_iff_of_mod_pos hmod, ite_eq_right hmod.ne', hvn, hvb]
    simp only [hn, true_and]
    norm_cast
    rw [Nat.mul_comm n (j / n)] at hdiv
    refine ⟨fun ⟨h1, h2⟩ ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
    · have hm1 := Nat.mul_le_mul_right n h1
      have hm2 := Nat.mul_le_mul_right n h2
      rw [Nat.add_one_mul] at hm2
      exact ⟨(min_le_left _ _).trans (by omega), by omega⟩
    · have hj_ne : j ≠ padicValNat p n * n := fun heq ↦ hmod.ne' (by rw [heq, Nat.mul_mod_left])
      have hdiv_lt : j / n + 1 ≤ padicValNat p n :=
        Nat.lt_of_mul_lt_mul_right (by omega : (j / n) * n < padicValNat p n * n)
      rcases min_le_iff.mp h1 with hmin | hmin
      · have hm_lt : padicValNat p (j % n) * n < (j / n + 1) * n := by rw [Nat.add_one_mul]; omega
        exact ⟨Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right hm_lt), hdiv_lt⟩
      · exact absurd (le_antisymm h2 hmin) hj_ne

end

end TauCeti
