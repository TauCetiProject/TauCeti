/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Character
import TauCeti.NumberTheory.LSeries.ZMod
import TauCeti.Analysis.Fourier.ZMod

/-!
# Fourier expansions of weighted weight-two Eisenstein series

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

For an arbitrary residue weight `W`, the expansion of `weightedG2MF W` is obtained by
subtracting its average weight and applying the same folded-row formula. Every coefficient,
after division by `(2πi)²`, lies in any subfield containing the weights and the `N`-th roots of
unity. This includes the constant term, evaluated by the finite Fourier transform and the
Bernoulli polynomial `B₂` using `ZMod.hasSum_mul_zpow_neg_bernoulli`. In particular it applies to
the single-residue division values used to construct Fricke functions.

## Main results

* `TauCeti.EisensteinSeries.qExpansion_weightedG2MF_coeff`: all coefficients of the weighted
  weight-two series.
* `TauCeti.EisensteinSeries.qExpansion_weightedG2MF_coeff_div_mem`: their coefficient field
  after normalization by `(2πi)²`.

* `TauCeti.EisensteinSeries.hasSum_charRow_charG2MF`: `G₂^{ψ,φ}` summed along rows.
* `TauCeti.EisensteinSeries.qExpansion_charG2MF_coeff`: the coefficients of `G₂^{ψ,φ}`.
* `TauCeti.EisensteinSeries.qExpansion_charG2MF_coeff_of_isPrimitive`: for primitive `φ`, the
  nonconstant coefficients are `-8 π² g(φ⁻¹) / v²` times the twisted divisor sums.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.6.
* [T. Miyake, *Modular forms*][miyake1989], §7.1, §7.2.
* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §6.1, for
  the arithmetic normalization of division values.
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

open Matrix CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N]

/-- The Fourier coefficients of a weighted weight-two series of total mass zero. The rows
are folded together before regrouping by the product of their two positive indices. -/
theorem qExpansion_weightedG2MF_coeff_of_sum_eq_zero
    {W : (Fin 2 → ZMod N) → ℂ} (hW : ∑ a, W a = 0) (n : ℕ) :
    (qExpansion N (weightedG2MF W)).coeff n =
      if n = 0 then ∑' d : ℤ, W ![0, (d : ZMod N)] * (d : ℂ) ^ (-2 : ℤ)
      else (2 * π * I) ^ 2 / N ^ 2 *
        ∑ x ∈ n.divisorsAntidiagonal,
          𝓕 (fun d ↦ W ![(x.1 : ZMod N), d] + W ![-(x.1 : ZMod N), -d])
            (-(x.2 : ZMod N)) * (x.2 : ℂ) := by
  have hcomp (c d : ℤ) : ((↑) : ℤ → ZMod N) ∘ ![c, d] = ![(c : ZMod N), (d : ZMod N)] := by
    ext i; fin_cases i <;> rfl
  have hrows (z : ℍ) : Summable fun c : ℤ ↦ ∑' d : ℤ,
      W ![(c : ZMod N), (d : ZMod N)] * eisSummand 2 ![c, d] z := by
    refine (summable_weightedG2Row W z).congr fun c ↦ ?_
    simp only [weightedG2Row_def, hcomp]
  have hterms (z : ℍ) (c : ℤ) : Summable fun d : ℤ ↦
      W ![(c : ZMod N), (d : ZMod N)] * eisSummand 2 ![c, d] z := by
    simpa only [hcomp] using summable_weightedG2Row_terms W z c
  have hf (z : ℍ) : weightedG2MF W z = ∑' c : ℤ, ∑' d : ℤ,
      W ![(c : ZMod N), (d : ZMod N)] * eisSummand 2 ![c, d] z := by
    simpa only [weightedG2Row_def, hcomp, coe_weightedG2MF] using
      (hasSum_weightedG2Row hW z).tsum_eq.symm
  simpa using qExpansion_coeff_of_apply_eq_tsum_weightedRow W
    (by simp [strictPeriods_Gamma]) le_rfl hrows hterms hf n

/-- The Fourier coefficients of an arbitrary weighted weight-two series. Subtracting the
average weight removes the regularization term without changing the modular form. -/
theorem qExpansion_weightedG2MF_coeff (W : (Fin 2 → ZMod N) → ℂ) (n : ℕ) :
    (qExpansion N (weightedG2MF W)).coeff n =
      let V := fun a ↦ W a - ((N : ℂ) ^ 2)⁻¹ * ∑ b, W b
      if n = 0 then ∑' d : ℤ, V ![0, (d : ZMod N)] * (d : ℂ) ^ (-2 : ℤ)
      else (2 * π * I) ^ 2 / N ^ 2 *
        ∑ x ∈ n.divisorsAntidiagonal,
          𝓕 (fun d ↦ V ![(x.1 : ZMod N), d] + V ![-(x.1 : ZMod N), -d])
            (-(x.2 : ZMod N)) * (x.2 : ℂ) := by
  classical
  let m : ℂ := ((N : ℂ) ^ 2)⁻¹ * ∑ b, W b
  let V := fun a ↦ W a - m
  have hV : ∑ a, V a = 0 := by
    simp only [V, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, ZMod.card, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    simp [m, NeZero.ne N]
  have hconst : weightedG2 (fun _ : Fin 2 → ZMod N ↦ m) = 0 :=
    weightedG2_eq_zero_of_forall_vecMul_eq fun _ _ ↦ rfl
  have hform : weightedG2MF V = weightedG2MF W := by
    apply DFunLike.ext
    intro z
    have h := congrFun (weightedG2_add V (fun _ ↦ m)) z
    rw [hconst] at h
    simpa [V, Pi.add_def] using h.symm
  rw [← hform]
  exact qExpansion_weightedG2MF_coeff_of_sum_eq_zero hV n

/-- After division by `(2πi)²`, every Fourier coefficient of a weighted division-value
series belongs to any subfield containing its weights and the `N`-th roots of unity. -/
theorem qExpansion_weightedG2MF_coeff_div_mem {K : Subfield ℂ}
    (hK : ∀ ζ : ℂ, ζ ^ N = 1 → ζ ∈ K) {W : (Fin 2 → ZMod N) → ℂ}
    (hW : ∀ a, W a ∈ K) (n : ℕ) :
    (qExpansion N (weightedG2MF W)).coeff n / (2 * π * I) ^ 2 ∈ K := by
  let V := fun a ↦ W a - ((N : ℂ) ^ 2)⁻¹ * ∑ b, W b
  have hV (a) : V a ∈ K :=
    K.sub_mem (hW a) (K.mul_mem (K.inv_mem (K.pow_mem (natCast_mem K N) 2))
      (K.sum_mem fun b _ ↦ hW b))
  have hπ : (2 * π * I : ℂ) ^ 2 ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rw [qExpansion_weightedG2MF_coeff]
  dsimp only
  split_ifs with hn
  · have hsum := (hasSum_mul_zpow_neg_bernoulli (fun d ↦ V ![0, d]) (k := 2) le_rfl).tsum_eq
    norm_num only [Nat.cast_ofNat] at hsum
    rw [hsum]
    have heq (S : ℂ) : (-(2 * π * I) ^ 2 / (2 * N) * S) / (2 * π * I) ^ 2 =
        -S / (2 * N) := by field_simp [hπ]
    rw [heq]
    exact K.div_mem (K.neg_mem (K.sum_mem fun j _ ↦ K.mul_mem
      (dft_apply_mem (R := K.toSubring) hK (fun d ↦ hV _) j) (SubfieldClass.ratCast_mem K _)))
      (K.mul_mem (natCast_mem K 2) (natCast_mem K N))
  · have heq (S : ℂ) : ((2 * π * I) ^ 2 / N ^ 2 * S) / (2 * π * I) ^ 2 =
        S / N ^ 2 := by field_simp [hπ]
    rw [heq]
    exact K.div_mem (K.sum_mem fun x _ ↦ K.mul_mem
      (dft_apply_mem (R := K.toSubring) hK (fun d ↦ K.add_mem (hV _) (hV _)) _)
      (natCast_mem K _)) (K.pow_mem (natCast_mem K N) 2)

end TauCeti.EisensteinSeries
