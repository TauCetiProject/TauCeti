/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Character

/-!
# The `q`-expansion of the weight-two Eisenstein series with character

For Dirichlet characters `ψ` modulo `u` and `φ` modulo `v`, not both trivial, with
`ψ(-1) φ(-1) = 1` and `u v ∣ N`, we compute the `q`-expansion of the weight-two Eisenstein series
with character `G₂^{ψ,φ}` (`TauCeti.EisensteinSeries.charG2MF`). As in weight `k ≥ 3`
(`TauCeti.EisensteinSeries.qExpansion_charEisensteinSeriesMF_coeff`), its constant coefficient is
`ψ(0) ∑_{d ∈ ℤ} φ⁻¹(d) d⁻²`, and for `n ≥ 1` its `n`-th coefficient is
`-8 π² / v² ∑_{c m = n} ψ(c) φ̂(m) m`, where `φ̂(m) = ∑_{r mod v} φ⁻¹(r) e^(2πi r m / v)`.
For primitive `φ` this is `-8 π² g(φ⁻¹) / v²` times the twisted divisor sum
`σ₁^{ψ,φ}(n) = ∑_{d ∣ n} ψ(n/d) φ(d) d`.

The double series `∑_{(c, d)} ψ(c) φ⁻¹(d) (c v z + d)⁻²` does not converge absolutely, and the
order of summation matters. The series `G₂^{ψ,φ}` is the sum over the translates of a box of
residues modulo `N` (`TauCeti.EisensteinSeries.hasSum_charG2MF`); we show that it is also the sum
over `c` of the absolutely convergent rows `ψ(c) ∑_d φ⁻¹(d) (c v z + d)⁻²`
(`TauCeti.EisensteinSeries.hasSum_charRow_charG2MF`). These are the rows of the weighted series
of `charWeight`, which has total mass zero, so this is the row expansion of weighted weight-two
series (`TauCeti.EisensteinSeries.hasSum_weightedG2Row`). The coefficients
then follow from the row-by-row computation shared with weight `k ≥ 3`
(`TauCeti.EisensteinSeries.qExpansion_coeff_of_apply_eq_tsum_charRow`).

## Main results

* `TauCeti.EisensteinSeries.hasSum_charRow_charG2MF`: `G₂^{ψ,φ}` summed along rows.
* `TauCeti.EisensteinSeries.qExpansion_charG2MF_coeff`: the coefficients of `G₂^{ψ,φ}`.
* `TauCeti.EisensteinSeries.qExpansion_charG2MF_coeff_of_isPrimitive`: for primitive `φ`, the
  nonconstant coefficients are `-8 π² g(φ⁻¹) / v²` times the twisted divisor sums.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.6.
* [T. Miyake, *Modular forms*][miyake1989], §7.1, §7.2.
-/

public section

noncomputable section

open Complex ZMod EisensteinSeries ModularForm
open UpperHalfPlane hiding I
open scoped Real

namespace TauCeti.EisensteinSeries

variable {u v N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- **The weight-two Eisenstein series with character summed along rows**: unless `ψ` and `φ` are
both trivial, `G₂^{ψ,φ}(z)` is the sum over `c ∈ ℤ` of the absolutely convergent rows
`ψ(c) ∑_{d ∈ ℤ} φ⁻¹(d) (c v z + d)⁻²`. The double series itself does not converge absolutely. -/
theorem hasSum_charRow_charG2MF (huv : u * v ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1) (z : ℍ) :
    HasSum (charRow ψ φ 2 z) (charG2MF ψ φ huv z) := by
  have : NeZero v := NeZero.of_dvd (dvd_of_mul_left_dvd huv)
  rw [hasSum_charRow_iff, coe_charG2MF]
  refine (hasSum_weightedG2Row (sum_charWeight_eq_zero ψ φ huv h) z).congr_fun fun c ↦ ?_
  simp [weightedG2Row_def, charWeight_intCast ψ φ huv]

/-- **The `q`-expansion of the weight-two Eisenstein series with character.** For characters `ψ`
modulo `u` and `φ` modulo `v`, not both trivial, with `ψ(-1) φ(-1) = 1`, the constant coefficient
of `G₂^{ψ,φ}` is `ψ(0) ∑_{d ∈ ℤ} φ⁻¹(d) d⁻²`, and for `n ≥ 1` its `n`-th coefficient is
`-8 π² / v² ∑_{c m = n} ψ(c) φ̂(m) m`, where `φ̂(m) = ∑_{r mod v} φ⁻¹(r) e^(2πi r m / v)` is the
discrete Fourier transform of `φ⁻¹` at `-m`. (If `ψ(-1) φ(-1) ≠ 1`, the series is zero:
`charG2MF_eq_zero`.) -/
theorem qExpansion_charG2MF_coeff [NeZero v] (huv : u * v ∣ N) (h : ψ ≠ 1 ∨ φ ≠ 1)
    (hpar : ψ (-1) * φ (-1) = 1) (n : ℕ) :
    (qExpansion 1 (charG2MF ψ φ huv)).coeff n =
      if n = 0 then ψ 0 * ∑' d : ℤ, φ⁻¹ d * (d : ℂ) ^ (-2 : ℤ)
      else -8 * π ^ 2 / v ^ 2 *
        ∑ x ∈ n.divisorsAntidiagonal, ψ x.1 * 𝓕 ⇑(φ⁻¹) (-(x.2 : ZMod v)) * x.2 := by
  rw [qExpansion_coeff_of_apply_eq_tsum_charRow ψ φ (k := 2) le_rfl (by simpa using hpar)
    fun z ↦ (hasSum_charRow_charG2MF ψ φ huv h z).tsum_eq.symm]
  split_ifs
  · simp only [Nat.cast_ofNat]
  · simp only [Nat.add_one_sub_one, pow_one, Nat.factorial_one, Nat.cast_one, one_mul]
    congr 1
    rw [mul_pow, mul_pow, neg_sq, I_sq]
    ring

/-- **The `q`-expansion of the weight-two Eisenstein series with character, for primitive `φ`.**
Then the Fourier transform of `φ⁻¹` is a multiple of `φ` by the Gauss sum `g(φ⁻¹)`, and for
`n ≥ 1` the `n`-th coefficient of `G₂^{ψ,φ}` is `-8 π² g(φ⁻¹) / v² · σ₁^{ψ,φ}(n)`, where
`σ₁^{ψ,φ}(n) = ∑_{d ∣ n} ψ(n/d) φ(d) d` is the twisted divisor sum. -/
theorem qExpansion_charG2MF_coeff_of_isPrimitive [NeZero v] (huv : u * v ∣ N)
    (h : ψ ≠ 1 ∨ φ ≠ 1) (hpar : ψ (-1) * φ (-1) = 1) (hφ : φ.IsPrimitive) {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 (charG2MF ψ φ huv)).coeff n =
      -8 * π ^ 2 / v ^ 2 * gaussSum φ⁻¹ stdAddChar *
        DirichletCharacter.twistedDivisorSum 1 ψ φ n := by
  rw [qExpansion_coeff_of_apply_eq_tsum_charRow_of_isPrimitive ψ φ (k := 2) le_rfl
    (by simpa using hpar) hφ (fun z ↦ (hasSum_charRow_charG2MF ψ φ huv h z).tsum_eq.symm) hn]
  simp only [Nat.add_one_sub_one, Nat.factorial_one, Nat.cast_one, one_mul]
  congr 2
  rw [mul_pow, mul_pow, neg_sq, I_sq]
  ring

end TauCeti.EisensteinSeries
