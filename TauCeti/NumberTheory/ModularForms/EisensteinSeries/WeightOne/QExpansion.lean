/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Character
import TauCeti.Analysis.Fourier.ZMod
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The `q`-expansion of the weight-one Eisenstein series with character

For Dirichlet characters `ψ` modulo `u` and `φ` modulo `v` with `u v ∣ N` and the weight-one
parity `ψ(-1) φ(-1) = -1`, we compute the `q`-expansion of the weight-one Eisenstein series with
character `E₁^{ψ,φ}` (`TauCeti.EisensteinSeries.charE1MF`). Its constant coefficient is its value
at `i∞`, an explicit finite sum, and for `n ≥ 1` its `n`-th coefficient is
`2 (-2π i) / v ∑_{c m = n} ψ(c) φ̂(m)`, where `φ̂(m) = ∑_{r mod v} φ⁻¹(r) e^(2π i r m / v)`: the
formula of weight `k ≥ 3` (`TauCeti.EisensteinSeries.qExpansion_charEisensteinSeriesMF_coeff`)
at `k = 1`. For primitive `φ` this is `2 (-2π i) g(φ⁻¹) / v` times the twisted divisor sum
`σ₀^{ψ,φ}(n) = ∑_{d ∣ n} ψ(n / d) φ(d)`. Together with
`TauCeti.EisensteinSeries.qExpansion_charE1MFRaise_coeff` this gives the `q`-expansions of the
raised series `E₁^{ψ,φ,t}`.

The computation starts from the expansion of the weighted weight-one series in powers of
`e(z / N) = e^(2π i z / N)` (`TauCeti.EisensteinSeries.hasSum_weightedE1_sub_valueAtInfty`),
whose coefficient of `e(z / N)^(c k)` is `∑_j (W(c, j) - W(-c, -j)) e(k j / N)`. For the
character weight the parity makes the odd part `W(c, j) - W(-c, -j)` equal to `2 ψ(c / v) φ⁻¹(j)`
when `v ∣ c`, and the sum over `j` modulo `N` is the discrete Fourier transform of `φ⁻¹` pulled
back from `ZMod v` (`ZMod.dft_comp_natCast_val`): with `L = N / v`, it vanishes unless `L ∣ k`,
and is `L φ̂(k / L)` otherwise. So only the pairs `(c, k) = (v c', L m)` contribute, with
`e(z / N)^(c k) = q^(c' m)`, and regrouping by `n = c' m` gives the coefficients, as in weight
`k ≥ 3`.

## Main results

* `TauCeti.EisensteinSeries.qExpansion_charE1MF_coeff`: the coefficients of `E₁^{ψ,φ}`.
* `TauCeti.EisensteinSeries.qExpansion_charE1MF_coeff_of_isPrimitive`: for primitive `φ`, the
  nonconstant coefficients are `2 (-2π i) g(φ⁻¹) / v` times the twisted divisor sums.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.8.
* [T. Miyake, *Modular forms*][miyake1989], §7.1, §7.2.
-/

public section

noncomputable section

open Complex ZMod EisensteinSeries ModularForm
open UpperHalfPlane hiding I
open scoped Real

namespace TauCeti.EisensteinSeries

variable {u v N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- Under the weight-one parity `ψ(-1) φ(-1) = -1`, the odd part of the character weight at
`(c, j)` is `2 ψ(c / v) φ⁻¹(j)` if `v ∣ c`, and `0` otherwise. -/
private lemma charWeight_sub_charWeight_neg (huv : u * v ∣ N) (hpar : ψ (-1) * φ (-1) = -1)
    (c : ℕ) (j : ZMod N) :
    charWeight N ψ φ ![(c : ZMod N), j] - charWeight N ψ φ ![-(c : ZMod N), -j] =
      if (v : ℤ) ∣ c then 2 * ψ ((c / v : ℤ) : ZMod u) * φ⁻¹ (j.val : ZMod v) else 0 := by
  have hφ : φ⁻¹ (-1) = φ (-1) := by
    rw [MulChar.inv_apply_eq_inv']
    exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, neg_one_mul, neg_neg, map_one])
  have h₁ : ![(c : ZMod N), j] = (↑) ∘ ![(c : ℤ), (j.val : ℤ)] := by
    ext i
    fin_cases i <;> simp
  have h₂ : ![-(c : ZMod N), -j] = (↑) ∘ ![-(c : ℤ), -(j.val : ℤ)] := by
    ext i
    fin_cases i <;> simp
  rw [h₁, h₂, charWeight_intCast ψ φ huv, charWeight_intCast ψ φ huv]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.dvd_neg]
  by_cases hc : (v : ℤ) ∣ c
  · simp only [hc, ↓reduceIte]
    rw [Int.neg_ediv_of_dvd hc, Int.cast_neg, ← neg_one_mul ((c / v : ℤ) : ZMod u), map_mul,
      Int.cast_neg, ← neg_one_mul (((j.val : ℤ)) : ZMod v), map_mul, hφ]
    push_cast
    linear_combination (-(ψ ((c / v : ℤ) : ZMod u) * φ⁻¹ (j.val : ZMod v))) * hpar
  · simp [hc]

/-- The coefficient of `e(z / N)^(c k)` in the `q`-expansion of the weight-one series of the
character weight: it vanishes unless `v ∣ c` and `L = N / v` divides `k`, and then it is
`2 ψ(c / v) L φ̂(k / L)`, with `φ̂(m) = ∑_{r mod v} φ⁻¹(r) e(r m / v)`. -/
private lemma sum_charWeight_mul_stdAddChar [NeZero v] (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (c k : ℕ) :
    ∑ j : ZMod N, (charWeight N ψ φ ![(c : ZMod N), j] - charWeight N ψ φ ![-(c : ZMod N), -j]) *
        stdAddChar ((k : ZMod N) * j) =
      if (v : ℤ) ∣ c ∧ ((N / v : ℕ) : ℤ) ∣ k then
        2 * ψ ((c / v : ℤ) : ZMod u) *
          ((N / v : ℕ) * 𝓕 ⇑(φ⁻¹) (-((k / (N / v : ℕ) : ℤ) : ZMod v)))
      else 0 := by
  have hsum : ∑ j : ZMod N, φ⁻¹ (j.val : ZMod v) * stdAddChar ((k : ZMod N) * j) =
      𝓕 (fun j : ZMod N ↦ φ⁻¹ (j.val : ZMod v)) ((-(k : ℤ) : ℤ) : ZMod N) := by
    rw [dft_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    push_cast
    ring
  simp_rw [charWeight_sub_charWeight_neg ψ φ huv hpar]
  by_cases hc : (v : ℤ) ∣ c
  · simp only [hc, ↓reduceIte, true_and, mul_assoc, ← Finset.mul_sum, hsum,
      dft_comp_natCast_val (dvd_of_mul_left_dvd huv), Int.dvd_neg]
    split_ifs with hk
    · rw [Int.neg_ediv_of_dvd hk, nsmul_eq_mul, Int.cast_neg]
    · rw [mul_zero, mul_zero]
  · simp [hc]

/-- **The weight-one Eisenstein series with character as a double series.** Under the parity
`ψ(-1) φ(-1) = -1`, `E₁^{ψ,φ}(z)` minus its value at `i∞` is
`2 (-2π i) / v ∑_{c, m ≥ 1} ψ(c) φ̂(m) q^(c m)`, with `q = e^(2π i z)`. -/
private lemma hasSum_charE1MF [NeZero v] (huv : u * v ∣ N) (hpar : ψ (-1) * φ (-1) = -1)
    (z : ℍ) :
    HasSum (fun p : ℕ+ × ℕ+ ↦ 2 * (-2 * π * I) / v *
        (ψ (p.1 : ℕ) * 𝓕 ⇑(φ⁻¹) (-((p.2 : ℕ) : ZMod v))) * cexp (2 * π * I * z) ^ ((p.1 : ℕ) * p.2))
      (charE1MF ψ φ huv z - valueAtInfty (weightedE1 (charWeight N ψ φ))) := by
  obtain ⟨L, hN⟩ := dvd_of_mul_left_dvd huv
  have hNL : N / v = L := by rw [hN, Nat.mul_div_cancel_left _ (NeZero.pos v)]
  have hL : 0 < L := Nat.pos_of_ne_zero fun h ↦ NeZero.ne N (by rw [hN, h, mul_zero])
  let vP : ℕ+ := ⟨v, NeZero.pos v⟩
  let LP : ℕ+ := ⟨L, hL⟩
  have hvP : (vP : ℕ) = v := rfl
  have hLP : (LP : ℕ) = L := rfl
  have h := hasSum_weightedE1_sub_valueAtInfty (charWeight N ψ φ) z
  simp_rw [sum_charWeight_mul_stdAddChar ψ φ huv hpar, hNL] at h
  rw [coe_charE1MF]
  -- only the pairs `(v c, L m)` contribute
  have hg : Function.Injective fun p : ℕ+ × ℕ+ ↦ (vP * p.1, LP * p.2) :=
    (mul_right_injective vP).prodMap (mul_right_injective LP)
  refine (((hg.hasSum_iff fun x hx ↦ ?_).mpr h)).congr_fun fun p ↦ ?_
  · have hne : ¬((v : ℤ) ∣ ((x.1 : ℕ) : ℤ) ∧ (L : ℤ) ∣ ((x.2 : ℕ) : ℤ)) := by
      rintro ⟨h₁, h₂⟩
      obtain ⟨c, hc⟩ := Int.natCast_dvd_natCast.mp h₁
      obtain ⟨m, hm⟩ := Int.natCast_dvd_natCast.mp h₂
      have hc0 : 0 < c := Nat.pos_of_ne_zero fun h ↦ x.1.ne_zero (by rw [hc, h, mul_zero])
      have hm0 : 0 < m := Nat.pos_of_ne_zero fun h ↦ x.2.ne_zero (by rw [hm, h, mul_zero])
      exact hx ⟨(⟨c, hc0⟩, ⟨m, hm0⟩), Prod.ext (PNat.eq hc.symm) (PNat.eq hm.symm)⟩
    simp only [hne, ↓reduceIte, mul_zero, zero_mul]
  · have hv0 : (v : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne v)
    have hL0 : (L : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hL.ne'
    have hN' : (N : ℂ) = v * L := by exact_mod_cast hN
    have hpow : cexp (2 * π * I * z / N) ^ ((v * p.1 : ℕ) * (L * p.2 : ℕ)) =
        cexp (2 * π * I * z) ^ ((p.1 : ℕ) * p.2) := by
      rw [show (v * p.1 : ℕ) * (L * p.2 : ℕ) = N * (p.1 * p.2) by rw [hN]; ring, pow_mul,
        ← Complex.exp_nat_mul]
      congr 2
      field_simp [Nat.cast_ne_zero.mpr (NeZero.ne N)]
    simp only [Function.comp_apply, PNat.mul_coe, hvP, hLP, Nat.cast_mul, dvd_mul_right,
      and_self, ↓reduceIte, Int.mul_ediv_cancel_left _ hv0, Int.mul_ediv_cancel_left _ hL0, hpow]
    push_cast
    rw [hN']
    field_simp [Nat.cast_ne_zero.mpr hL.ne']

/-- **The `q`-expansion of the weight-one Eisenstein series with character.** For characters `ψ`
modulo `u` and `φ` modulo `v` with `u v ∣ N` and `ψ(-1) φ(-1) = -1`, the constant coefficient
of `E₁^{ψ,φ}` is its value at `i∞`, `N⁻¹ ∑_a W(a) c_a` with `W = charWeight N ψ φ`,
`c_a = π cot (π a₁ / N)` if `a₀ = 0` and `c_a = π i (2 a₀ / N - 1)` otherwise. For `n ≥ 1` its
`n`-th coefficient is `2 (-2π i) / v ∑_{c m = n} ψ(c) φ̂(m)`, where
`φ̂(m) = ∑_{r mod v} φ⁻¹(r) e^(2π i r m / v)` is the discrete Fourier transform of `φ⁻¹` at `-m`:
the formula of weight `k ≥ 3` (`qExpansion_charEisensteinSeriesMF_coeff`) at `k = 1`. (If the
parity condition fails, the series is zero: `charE1MF_eq_zero`.) -/
theorem qExpansion_charE1MF_coeff [NeZero v] (huv : u * v ∣ N) (hpar : ψ (-1) * φ (-1) = -1)
    (n : ℕ) :
    (qExpansion 1 (charE1MF ψ φ huv)).coeff n =
      if n = 0 then
        (N : ℂ)⁻¹ * ∑ a, charWeight N ψ φ a *
          if (a 0).val = 0 then π * cot (π * ((a 1).val / N))
          else π * I * (2 * (a 0).val / N - 1)
      else 2 * (-2 * π * I) / v *
        ∑ x ∈ n.divisorsAntidiagonal, ψ x.1 * 𝓕 ⇑(φ⁻¹) (-(x.2 : ZMod v)) := by
  set K : ℂ := 2 * (-2 * π * I) / v
  set V := valueAtInfty (weightedE1 (charWeight N ψ φ))
  set a : ℕ → ℂ := fun n ↦ ∑ x ∈ n.divisorsAntidiagonal, ψ x.1 * 𝓕 ⇑(φ⁻¹) (-(x.2 : ZMod v))
    with ha
  set b : ℕ → ℂ := fun n ↦ if n = 0 then V else K * a n
  suffices h : ∀ τ : ℍ, HasSum (fun m ↦ b m • Function.Periodic.qParam 1 τ ^ m)
      (charE1MF ψ φ huv τ) by
    rw [← ModularFormClass.qExpansion_coeff_unique one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map N) h n]
    simp only [b, V, valueAtInfty_weightedE1, a, K]
  intro τ
  set q := cexp (2 * π * I * τ)
  have hq : Function.Periodic.qParam 1 τ = q := by
    simp [Function.Periodic.qParam, q]
  -- regroup the double series by `n = c m`; each group carries `q ^ n`
  have hgroup (n : ℕ+) : ∑ x ∈ (n : ℕ).divisorsAntidiagonal,
      K * (ψ x.1 * 𝓕 ⇑(φ⁻¹) (-(x.2 : ZMod v))) * q ^ (x.1 * x.2) = K * a n * q ^ (n : ℕ) := by
    rw [ha, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  have H := (hasSum_charE1MF ψ φ huv hpar τ).sum_divisorsAntidiagonal
    (f := fun c m ↦ K * (ψ c * 𝓕 ⇑(φ⁻¹) (-(m : ZMod v))) * q ^ (c * m))
  simp_rw [hgroup] at H
  have H' := (hasSum_pnat_iff (f := fun n : ℕ ↦ K * a n * q ^ n)).mp H
  convert! H'.add (hasSum_ite_eq 0 V) using 1
  · ext m
    rcases eq_or_ne m 0 with rfl | hm
    · simp [b, a, hq]
    · simp [b, hm, hq]
  · simp [a, V]

/-- **The `q`-expansion of the weight-one Eisenstein series with character, for primitive `φ`.**
Under the hypotheses of `qExpansion_charE1MF_coeff`, the Fourier transform of `φ⁻¹` is a multiple
of `φ` by the Gauss sum `g(φ⁻¹)`, and for `n ≥ 1` the `n`-th coefficient of `E₁^{ψ,φ}` is
`2 (-2π i) g(φ⁻¹) / v` times the twisted divisor sum `σ₀^{ψ,φ}(n) = ∑_{d ∣ n} ψ(n / d) φ(d)`. -/
theorem qExpansion_charE1MF_coeff_of_isPrimitive [NeZero v] (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 (charE1MF ψ φ huv)).coeff n =
      2 * (-2 * π * I) / v * gaussSum φ⁻¹ stdAddChar *
        DirichletCharacter.twistedDivisorSum 0 ψ φ n := by
  have hφ' : (φ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hφ
  rw [qExpansion_charE1MF_coeff ψ φ huv hpar]
  simp only [hn, ↓reduceIte]
  rw [DirichletCharacter.twistedDivisorSum_apply,
    ← Nat.sum_divisorsAntidiagonal' (f := fun a b : ℕ ↦ ψ a * φ b * (b : ℂ) ^ 0),
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [hφ'.fourierTransform_eq_inv_mul_gaussSum, inv_inv, neg_neg]
  ring

end TauCeti.EisensteinSeries
