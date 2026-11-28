/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Ring

/-!
# Graded string-power coordinates and string-map compatibility

In a graded hermitian space `X ⊕ J_s` with generic constant `c ≠ 0` and middle Gram entry
`-N` (`N ≠ 0`) over a field `E`, the string vectors are rescaled to basis vectors `𝔢 ^ i`
(`0 ≤ i < s`) whose scalar coefficients `TauCeti.stringPowerCoeff` are powers of `c` in
nonnegative grade (`2 * i < s`) and `-N` times powers of `c` in negative grade (`s ≤ 2 * i`).

## Main results

* `TauCeti.stringPowerCoeff`: the scalar coefficient of the `i`-th string power `𝔢 ^ i` for a
  string of length `s`.
* `TauCeti.stringPowerCoeff_ne_zero`: `stringPowerCoeff N c s i ≠ 0` whenever `N ≠ 0` and `c ≠ 0`.
* `TauCeti.stringMapFactor_mul_stringPowerCoeff`: multiplying `stringPowerCoeff N c s i` by the
  string-map factor from length `s` to `s - 1` produces `stringPowerCoeff N c (s - 1) i`.
* `TauCeti.exists_stringSum_eq`: over any `E`-algebra `R`, every vector on `ι ≃ X ⊕ Fin s`
  vanishing on `X` is a unique `R`-linear combination of the `s` string-power basis vectors.

## Provenance

Adapted from `New.Grading.powerCoeff`, `New.Grading.powerCoeff_ne_zero`,
`New.Grading.stringMap_factor_mul_powerCoeff`, and `New.Grading.exists_stringSum_eq` in
`src/Lib/Weil/Periods/StringPowers.lean` of `grh-lean`
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC), generalized from CM fields and finite adeles `𝔸f E`
to an arbitrary field `E` and commutative `E`-algebra `R`.
-/

public section

namespace TauCeti

variable {E : Type*} [Field E]

/-- The scalar coefficient of the `i`-th string power `𝔢 ^ i` in a graded string of length `s`
with middle Gram parameter `N` and generic constant `c`. -/
def stringPowerCoeff (N c : E) (s i : ℕ) : E :=
  if 2 * i < s then c ^ ((i : ℤ) - (s / 2 : ℕ))
  else -N * c ^ ((i : ℤ) - ((s - 1) / 2 : ℕ))

/-- `stringPowerCoeff N c s i` is nonzero whenever `N ≠ 0` and `c ≠ 0`. -/
theorem stringPowerCoeff_ne_zero {N c : E} (hN : N ≠ 0) (hc : c ≠ 0) (s i : ℕ) :
    stringPowerCoeff N c s i ≠ 0 := by
  unfold stringPowerCoeff
  split_ifs
  · exact zpow_ne_zero _ hc
  · exact mul_ne_zero (neg_ne_zero.mpr hN) (zpow_ne_zero _ hc)

/-- Multiplying `stringPowerCoeff N c s i` by the transition factor of the string map from
length `s ≥ 2` to `s - 1` yields `stringPowerCoeff N c (s - 1) i`. -/
theorem stringMapFactor_mul_stringPowerCoeff {N c : E} (hc : c ≠ 0) {s : ℕ} (hs : 2 ≤ s) (i : ℕ) :
    (if Odd s ↔ 2 * i + 1 < s then 1 else c) * (if 2 * i + 1 = s then -N else 1) *
      stringPowerCoeff N c s i = stringPowerCoeff N c (s - 1) i := by
  set e : ℤ := if s % 2 = 1 ↔ 2 * i + 1 < s then 0 else 1
  have h_fac : (if Odd s ↔ 2 * i + 1 < s then 1 else c) = c ^ e := by
    simp only [e, Nat.odd_iff]
    split_ifs <;> simp
  rw [h_fac]
  by_cases h_lt : 2 * i + 1 < s
  · have h_e : e + ((i : ℤ) - (s / 2 : ℕ)) = (i : ℤ) - ((s - 1) / 2 : ℕ) := by
      simp only [e]; split_ifs <;> omega
    have h_ne : 2 * i + 1 ≠ s := by omega
    rw [ite_eq_right h_ne, mul_one, stringPowerCoeff, ite_eq_left (by omega),
      stringPowerCoeff, ite_eq_left (by omega), ← zpow_add₀ hc, h_e]
  · by_cases h_eq : 2 * i + 1 = s
    · have h_e : e + ((i : ℤ) - (s / 2 : ℕ)) = (i : ℤ) - ((s - 1 - 1) / 2 : ℕ) := by
        simp only [e]; split_ifs <;> omega
      rw [ite_eq_left h_eq, stringPowerCoeff, ite_eq_left (by omega),
        stringPowerCoeff, ite_eq_right (by omega), mul_comm (c ^ e) (-N), mul_assoc,
        ← zpow_add₀ hc, h_e]
    · have h_e : e + ((i : ℤ) - ((s - 1) / 2 : ℕ)) = (i : ℤ) - ((s - 1 - 1) / 2 : ℕ) := by
        simp only [e]; split_ifs <;> omega
      rw [ite_eq_right h_eq, mul_one, stringPowerCoeff, ite_eq_right (by omega),
        stringPowerCoeff, ite_eq_right (by omega), mul_left_comm, ← zpow_add₀ hc, h_e]

/-- Over any commutative `E`-algebra `R`, the string-power basis vectors span the complement
of `X` in `ι → R` for any equivalence `idx : X ⊕ Fin s ≃ ι`: every vector `y : ι → R`
vanishing on `X` is a linear combination `∑ i ∈ Finset.range s, t i • v i` of the rescaled
string basis vectors. -/
theorem exists_stringSum_eq {R X ι : Type*} [CommRing R] [Algebra E R]
    {N c : E} (hN : N ≠ 0) (hc : c ≠ 0) {s : ℕ} (idx : X ⊕ Fin s ≃ ι)
    {y : ι → R} (hy : ∀ a : X, y (idx (.inl a)) = 0) :
    ∃ t : ℕ → R,
      ∑ i ∈ Finset.range s,
          t i • (fun k ↦ (idx.symm k).elim (fun _ ↦ (0 : R)) fun b : Fin s ↦
            if b.val = i then algebraMap E R (stringPowerCoeff N c s i) else 0) = y := by
  let t (i : ℕ) : R := if hi : i < s then
    algebraMap E R (stringPowerCoeff N c s i)⁻¹ * y (idx (.inr ⟨i, hi⟩)) else 0
  refine ⟨t, funext fun k ↦ ?_⟩
  obtain ⟨a | b, rfl⟩ := idx.surjective k
  · simp [hy a]
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply,
      Sum.elim_inr, mul_ite, mul_zero]
    rw [Finset.sum_eq_single b.val]
    · simp only [↓reduceIte, t, b.isLt, ↓reduceDIte]
      rw [mul_comm _ (algebraMap E R _), ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ (stringPowerCoeff_ne_zero hN hc s b.val), map_one, one_mul]
    · intro i _ hbi
      simp [Ne.symm hbi]
    · intro hb
      exact absurd (Finset.mem_range.mpr b.isLt) hb

end TauCeti
