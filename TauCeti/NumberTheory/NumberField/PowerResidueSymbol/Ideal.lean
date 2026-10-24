/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Basic
import TauCeti.RingTheory.DedekindDomain.Ideal.Basic
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# The `n`-th power residue symbol at an ideal of a number field

Let `K` be a number field whose ring of integers contains a primitive `n`-th root of unity. For an
ideal `𝔞 = P₁ ⋯ Pᵣ` of `𝓞 K`, factored into maximal ideals with repetition, the `n`-th power
residue symbol at `𝔞` is the product of the symbols at the prime factors,
`(α / 𝔞)_n = ∏ᵢ (α / Pᵢ)_n`. It is the analogue for `𝓞 K` of the Jacobi symbol, and is the form
of the symbol in which the general power reciprocity laws relate `(α / β)_n` and `(β / α)_n`
for elements `α, β`, read at the principal ideals they generate.

We define it as a multiplicative character `Ideal.powerResidueSymbolIdeal 𝔞 n` of `𝓞 K ⧸ 𝔞` with
values in `𝓞 K`. On a unit `α mod 𝔞` it is the product above, and it vanishes on nonunits. Since
it is a function of the residue class, `(α / 𝔞)_n` depends only on `α` modulo `𝔞`, and
multiplicativity `(α β / 𝔞)_n = (α / 𝔞)_n (β / 𝔞)_n` is `map_mul`. The prime factors whose norm is
not prime to `n` contribute the trivial character, following the convention of
`Ideal.powerResidueSymbol`; when `N 𝔞` is prime to `n` there are no such factors. The value at the
zero ideal, which has no prime factors, is the trivial character.

## Main definitions and results

* `Ideal.powerResidueSymbolIdeal 𝔞 n`: the `n`-th power residue symbol at the ideal `𝔞`.
* `Ideal.powerResidueSymbolIdeal_of_isMaximal`: at a maximal ideal it is the prime symbol
  `Ideal.powerResidueSymbol`.
* `Ideal.powerResidueSymbolIdeal_mul_right`: `(α / 𝔞 𝔟)_n = (α / 𝔞)_n (α / 𝔟)_n` for nonzero
  `𝔞` and `𝔟`.
* `Ideal.powerResidueSymbolIdeal_pow_right`: `(α / 𝔞 ^ k)_n = ((α / 𝔞)_n) ^ k`.
* `Ideal.powerResidueSymbolIdeal_top`: `(α / 𝓞 K)_n = 1`.
* `Ideal.powerResidueSymbolIdeal_bot`: the symbol at the zero ideal is the trivial character.
* `Ideal.powerResidueSymbolIdeal_mk_eq_zero_iff`: `(α / 𝔞)_n = 0` exactly when `α` and `𝔞` are
  not coprime.
* `Ideal.powerResidueSymbolIdeal_pow_eq_one`: on units the symbol is an `n`-th root of unity.

## References

* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §4.
* P. Shastri, *Reciprocity laws: Artin–Hilbert*, §9.
-/

public section

open NumberField UniqueFactorizationMonoid

namespace Ideal

variable {K : Type*} [Field K] [NumberField K] {𝔞 𝔟 : Ideal (𝓞 K)} {n : ℕ} [NeZero n]
  [HasEnoughRootsOfUnity (𝓞 K) n]

open scoped Classical in
variable (𝔞 n) in
/-- The `n`-th power residue symbol at `P`, read on the units of `𝓞 K ⧸ 𝔞` through the reduction
`𝓞 K ⧸ 𝔞 → 𝓞 K ⧸ P`, when `P` is a maximal ideal containing `𝔞`; the trivial homomorphism
otherwise. -/
private noncomputable def unitsSymbolAt (P : Ideal (𝓞 K)) : (𝓞 K ⧸ 𝔞)ˣ →* (𝓞 K)ˣ :=
  if h : P.IsMaximal ∧ 𝔞 ≤ P then
    letI := h.1
    (powerResidueSymbol P n).toUnitHom.comp
      (Units.map (Quotient.factor h.2 : 𝓞 K ⧸ 𝔞 →* 𝓞 K ⧸ P))
  else 1

open scoped Classical in
variable (n) in
/-- The `n`-th power residue symbol at `P` of an element of `𝓞 K`, when `P` is maximal; `1`
otherwise. -/
private noncomputable def symbolAt (P : Ideal (𝓞 K)) (α : 𝓞 K) : 𝓞 K :=
  if h : P.IsMaximal then
    letI := h
    powerResidueSymbol P n (Quotient.mk P α)
  else 1

variable (𝔞 n) in
/-- **The `n`-th power residue symbol at an ideal** `𝔞` of `𝓞 K`, as a multiplicative character of
`𝓞 K ⧸ 𝔞` with values in `𝓞 K`. If `𝔞 = P₁ ⋯ Pᵣ` is the factorisation of `𝔞` into maximal
ideals, it sends the class of `α` coprime to `𝔞` to `∏ᵢ (α / Pᵢ)_n`, and it vanishes on the
classes not coprime to `𝔞`. -/
noncomputable def powerResidueSymbolIdeal : MulChar (𝓞 K ⧸ 𝔞) (𝓞 K) :=
  MulChar.ofUnitHom ((normalizedFactors 𝔞).map (unitsSymbolAt 𝔞 n)).prod

/-- **The product formula.** On the class of `α` coprime to `𝔞`, the symbol at `𝔞` is the product
of the symbols at the prime factors of `𝔞`. -/
private theorem powerResidueSymbolIdeal_mk_eq_prod {α : 𝓞 K} (hα : IsUnit (Quotient.mk 𝔞 α)) :
    powerResidueSymbolIdeal 𝔞 n (Quotient.mk 𝔞 α) =
      ((normalizedFactors 𝔞).map (symbolAt n · α)).prod := by
  -- A product of homomorphisms is evaluated factorwise.
  have hprod (m : Multiset ((𝓞 K ⧸ 𝔞)ˣ →* (𝓞 K)ˣ)) (u : (𝓞 K ⧸ 𝔞)ˣ) :
      ((m.prod u : (𝓞 K)ˣ) : 𝓞 K) = (m.map fun f ↦ (f u : 𝓞 K)).prod := by
    induction m using Multiset.induction_on <;> simp [*]
  rw [← hα.unit_spec, powerResidueSymbolIdeal, MulChar.ofUnitHom_coe, hprod, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun P hP ↦ ?_)
  have hPm := isMaximal_of_mem_normalizedFactors hP
  have hle := le_of_dvd (dvd_of_mem_normalizedFactors hP)
  simp [unitsSymbolAt, symbolAt, hPm, hle, Quotient.factor_mk]

/-- At a maximal ideal `P`, the symbol at the ideal `P` is the prime symbol at `P`. -/
@[simp]
theorem powerResidueSymbolIdeal_of_isMaximal (P : Ideal (𝓞 K)) [P.IsMaximal] :
    powerResidueSymbolIdeal P n = powerResidueSymbol P n := by
  have hP : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (RingOfIntegers.not_isField K)
  refine MulChar.ext fun u ↦ ?_
  obtain ⟨α, hα⟩ := Quotient.mk_surjective (u : 𝓞 K ⧸ P)
  rw [← hα, powerResidueSymbolIdeal_mk_eq_prod (hα ▸ u.isUnit),
    normalizedFactors_irreducible (prime_of_isPrime hP inferInstance).irreducible, normalize_eq,
    Multiset.map_singleton, Multiset.prod_singleton, symbolAt, dite_eq_left ‹_›]

/-- The symbol at the unit ideal is identically `1`. -/
@[simp]
theorem powerResidueSymbolIdeal_top (x : 𝓞 K ⧸ (⊤ : Ideal (𝓞 K))) :
    powerResidueSymbolIdeal ⊤ n x = 1 := by
  have : Subsingleton (𝓞 K ⧸ (⊤ : Ideal (𝓞 K))) := Quotient.subsingleton_iff.mpr rfl
  rw [Subsingleton.elim x 1, MulChar.map_one]

/-- The zero ideal has no prime factors, so the symbol at it is the trivial character. -/
@[simp]
theorem powerResidueSymbolIdeal_bot : powerResidueSymbolIdeal (⊥ : Ideal (𝓞 K)) n = 1 := by
  have h : normalizedFactors (⊥ : Ideal (𝓞 K)) = 0 := by
    rw [← zero_eq_bot, normalizedFactors_zero]
  refine MulChar.ext fun u ↦ ?_
  simp [powerResidueSymbolIdeal, h]

/-- The symbol at `𝔞` vanishes exactly at the classes of the elements not coprime to `𝔞`. -/
theorem powerResidueSymbolIdeal_mk_eq_zero_iff {α : 𝓞 K} :
    powerResidueSymbolIdeal 𝔞 n (Quotient.mk 𝔞 α) = 0 ↔ ¬IsCoprime (span {α}) 𝔞 := by
  rw [MulChar.apply_eq_zero_iff, Quotient.isUnit_mk_iff, isCoprime_iff_sup_eq]

/-- **Multiplicativity in the ideal.** `(α / 𝔞 𝔟)_n = (α / 𝔞)_n (α / 𝔟)_n` for nonzero ideals
`𝔞` and `𝔟`. -/
theorem powerResidueSymbolIdeal_mul_right (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) (α : 𝓞 K) :
    powerResidueSymbolIdeal (𝔞 * 𝔟) n (Quotient.mk (𝔞 * 𝔟) α) =
      powerResidueSymbolIdeal 𝔞 n (Quotient.mk 𝔞 α) *
        powerResidueSymbolIdeal 𝔟 n (Quotient.mk 𝔟 α) := by
  by_cases hα : IsCoprime (span {α}) (𝔞 * 𝔟)
  · have hu : ∀ {𝔠 : Ideal (𝓞 K)}, IsCoprime (span {α}) 𝔠 → IsUnit (Quotient.mk 𝔠 α) :=
      fun h ↦ Quotient.isUnit_mk_iff.mpr (isCoprime_iff_sup_eq.mp h)
    obtain ⟨h𝔞α, h𝔟α⟩ := IsCoprime.mul_right_iff.mp hα
    rw [powerResidueSymbolIdeal_mk_eq_prod (hu hα), powerResidueSymbolIdeal_mk_eq_prod (hu h𝔞α),
      powerResidueSymbolIdeal_mk_eq_prod (hu h𝔟α), normalizedFactors_mul h𝔞 h𝔟, Multiset.map_add,
      Multiset.prod_add]
  · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr hα]
    rcases not_and_or.mp (IsCoprime.mul_right_iff.not.mp hα) with h | h
    · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr h, zero_mul]
    · rw [powerResidueSymbolIdeal_mk_eq_zero_iff.mpr h, mul_zero]

/-- `(α / 𝔞 ^ k)_n = ((α / 𝔞)_n) ^ k`. -/
theorem powerResidueSymbolIdeal_pow_right (𝔞 : Ideal (𝓞 K)) (α : 𝓞 K) (k : ℕ) :
    powerResidueSymbolIdeal (𝔞 ^ k) n (Quotient.mk (𝔞 ^ k) α) =
      powerResidueSymbolIdeal 𝔞 n (Quotient.mk 𝔞 α) ^ k := by
  induction k with
  | zero => rw [pow_zero, one_eq_top, powerResidueSymbolIdeal_top, pow_zero]
  | succ k ih =>
    obtain rfl | h𝔞 := eq_or_ne 𝔞 ⊥
    · -- At the zero ideal the trivial character takes only the values `0` and `1`.
      rw [show (⊥ : Ideal (𝓞 K)) ^ (k + 1) = ⊥ by rw [← zero_eq_bot, zero_pow k.succ_ne_zero],
        powerResidueSymbolIdeal_bot]
      by_cases hα : IsUnit (Quotient.mk (⊥ : Ideal (𝓞 K)) α)
      · rw [MulChar.one_apply hα, one_pow]
      · rw [MulChar.map_nonunit _ hα, zero_pow k.succ_ne_zero]
    rw [pow_succ, powerResidueSymbolIdeal_mul_right (pow_ne_zero k h𝔞) h𝔞, ih, pow_succ]

/-- On the units of `𝓞 K ⧸ 𝔞`, the symbol at `𝔞` is an `n`-th root of unity. -/
theorem powerResidueSymbolIdeal_pow_eq_one {x : 𝓞 K ⧸ 𝔞} (hx : IsUnit x) :
    powerResidueSymbolIdeal 𝔞 n x ^ n = 1 := by
  obtain ⟨α, rfl⟩ := Quotient.mk_surjective x
  rw [powerResidueSymbolIdeal_mk_eq_prod hx, ← Multiset.prod_map_pow]
  refine Multiset.prod_eq_one fun ξ hξ ↦ ?_
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hξ
  have hPm := isMaximal_of_mem_normalizedFactors hP
  have hαP : IsUnit (Quotient.mk P α) := by
    simpa [Quotient.factor_mk] using
      hx.map (Quotient.factor (le_of_dvd (dvd_of_mem_normalizedFactors hP)))
  rw [symbolAt, dite_eq_left hPm]
  by_cases hn : (absNorm P).Coprime n
  · exact powerResidueSymbol_pow_eq_one hn hαP.ne_zero
  · rw [powerResidueSymbol_of_not_coprime hn, MulChar.one_apply hαP, one_pow]

/-- For `n = 2`, a quadratic nonresidue modulo `P` has symbol `1` at `P ^ 2`, although it is not
a square modulo `P ^ 2`: the value `1` does not detect residues at composite ideals. -/
example (P : Ideal (𝓞 K)) [P.IsMaximal] [HasEnoughRootsOfUnity (𝓞 K) 2] {α : 𝓞 K}
    (hα : powerResidueSymbol P 2 (Quotient.mk P α) = -1) :
    powerResidueSymbolIdeal (P ^ 2) 2 (Quotient.mk (P ^ 2) α) = 1 := by
  rw [powerResidueSymbolIdeal_pow_right, powerResidueSymbolIdeal_of_isMaximal, hα, neg_one_sq]

end Ideal
