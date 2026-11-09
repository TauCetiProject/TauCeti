/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.GeneralizedBernoulli
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.QExpansion
import TauCeti.Data.ZMod.Count
import TauCeti.NumberTheory.DirichletCharacter.LValues

/-!
# Bernoulli constant coefficients of the weight-one Eisenstein series with character

For Dirichlet characters `ψ` modulo `u` and `φ` modulo `v` with `u v ∣ N`, the weight-one parity
`ψ(-1) φ(-1) = -1` and `φ` primitive, the constant coefficient of the weight-one Eisenstein series
with character `E₁^{ψ,φ}` (`TauCeti.EisensteinSeries.charE1MF`) is

`2π i g(φ⁻¹) / v · (δ(φ) B₁,ψ + δ(ψ) B₁,φ)`,

where `g(φ⁻¹)` is the Gauss sum, `B₁,χ` the first generalized Bernoulli number and `δ(χ)` is `1`
if `χ` has modulus one and `0` otherwise. Its nonconstant coefficients are
`2 (-2π i) g(φ⁻¹) / v` times the twisted divisor sums
(`TauCeti.EisensteinSeries.qExpansion_charE1MF_coeff_of_isPrimitive`), so the series is
`-2π i g(φ⁻¹) / v` times `δ(φ) L(0, ψ) + δ(ψ) L(0, φ) + 2 ∑_{n ≥ 1} σ₀^{ψ,φ}(n) qⁿ`, as
`L(0, χ) = -B₁,χ` for a nontrivial character `χ`. In weight one, unlike weight `k ≥ 3`
(`TauCeti.EisensteinSeries.qExpansion_normalizedCharEisensteinSeriesMF_coeff_zero`), both
characters can contribute to the constant term. The first character `ψ` need not be primitive.

The constant coefficient is the value at `i∞`, `N⁻¹ ∑_a W(a) c_a`
(`TauCeti.EisensteinSeries.valueAtInfty_weightedE1`), for the character weight `W`. The residues
`a = (0, j)` carry the cotangent values `c_a = π cot (π j / N)`, and contribute only when `u = 1`.
Their sum against `φ⁻¹(j)` (`DirichletCharacter.IsPrimitive.sum_inv_mul_pi_mul_cot`) is computed
by the finite Fourier expansion of the cotangent: the Fourier transform of `φ⁻¹` pulled back to
`ZMod N` is supported on the multiples of `N / v`, where primitivity makes it a multiple of `φ` by
the Gauss sum, leaving `∑_m m φ(m) = v B₁,φ`. The residues with `a₀ ≠ 0` carry
`c_a = π i (2 a₀ / N - 1)`, independent of `a₁`, and the sum of `φ⁻¹(a₁)` over `a₁` vanishes unless
`v = 1`; then the `N` columns `a₁` contribute `π i N ∑_{a₀} ψ(a₀) (2 a₀ / N - 1) = 2π i N B₁,ψ`
to the sum, that is `2π i B₁,ψ` after the division by `N`.

## Main results

* `TauCeti.EisensteinSeries.qExpansion_charE1MF_coeff_zero`: the constant coefficient of
  `E₁^{ψ,φ}`.
* `TauCeti.EisensteinSeries.qExpansion_charE1MFRaise_coeff_zero`: the raised series `E₁^{ψ,φ,t}`
  has the same constant coefficient.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.8.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 4, Theorem 4.2.
-/

public section

noncomputable section

open Complex ZMod EisensteinSeries ModularForm
open UpperHalfPlane hiding I
open scoped Real

namespace TauCeti.EisensteinSeries

variable {u v N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- The character weight at the residue pair `(a₀, a₁)`, read off the least nonnegative
representatives. -/
private lemma charWeight_cons (huv : u * v ∣ N) (a₀ a₁ : ZMod N) :
    charWeight N ψ φ ![a₀, a₁] =
      if v ∣ a₀.val then ψ ((a₀.val / v : ℕ) : ZMod u) * φ⁻¹ (a₁.val : ZMod v) else 0 := by
  have h : ![a₀, a₁] = (↑) ∘ ![(a₀.val : ℤ), (a₁.val : ℤ)] := by
    ext i
    fin_cases i <;> simp
  rw [h, charWeight_intCast ψ φ huv]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.natCast_dvd_natCast, Int.cast_natCast]
  split_ifs
  · rw [← Int.natCast_div, Int.cast_natCast]
  · rfl

/-- A nontrivial second character makes the character weight sum to zero along each row
`a₀ = const`. -/
private lemma sum_charWeight_cons_eq_zero [NeZero v] (huv : u * v ∣ N) (hφ : φ ≠ 1)
    (a₀ : ZMod N) : ∑ a₁ : ZMod N, charWeight N ψ φ ![a₀, a₁] = 0 := by
  simp only [charWeight_cons ψ φ huv]
  split_ifs
  · rw [← Finset.mul_sum, sum_comp_natCast_val (dvd_of_mul_left_dvd huv) fun r ↦ φ⁻¹ r,
      MulChar.sum_eq_zero_of_ne_one (inv_ne_one.mpr hφ), smul_zero, mul_zero]
  · exact Finset.sum_const_zero

/-- **The row `a₀ = 0` of the constant term**: the cotangent values weighted by `ψ(0) φ⁻¹(a₁)`.
It vanishes unless `u = 1`, and then `v ≠ 1` by the parity condition. -/
private lemma sum_charWeight_zero_mul_pi_mul_cot [NeZero v] (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) :
    ∑ a₁ : ZMod N, charWeight N ψ φ ![0, a₁] * (π * cot (π * (a₁.val / N))) =
      if u = 1 then N * (2 * π * I / v * gaussSum φ⁻¹ stdAddChar * φ.generalizedBernoulli 1)
      else 0 := by
  simp only [charWeight_cons ψ φ huv, val_zero, dvd_zero, ↓reduceIte, Nat.zero_div]
  split_ifs with hu
  · subst hu
    have hv : v ≠ 1 := by
      rintro rfl
      rw [DirichletCharacter.modOne_eq_one', DirichletCharacter.modOne_eq_one'] at hpar
      norm_num at hpar
    simp only [DirichletCharacter.modOne_eq_one', one_mul]
    exact hφ.sum_inv_mul_pi_mul_cot (dvd_of_mul_left_dvd huv) (mt hφ.eq_one_iff.mp hv)
  · simp [ψ.map_zero' hu]

/-- **The rows `a₀ ≠ 0` of the constant term**, where `c_a = π i (2 a₀ / N - 1)` does not depend
on `a₁`. They vanish unless `v = 1`, and then contribute `π i N ∑_{a₀} ψ(a₀) (2 a₀ / N - 1)`,
which is `2π i N B₁,ψ`; the Gauss sum modulo one is `1`. -/
private lemma sum_erase_zero_sum_charWeight_mul [NeZero u] [NeZero v] (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) :
    ∑ a₀ ∈ Finset.univ.erase (0 : ZMod N),
        (∑ a₁ : ZMod N, charWeight N ψ φ ![a₀, a₁]) * (π * I * (2 * a₀.val / N - 1)) =
      if v = 1 then N * (2 * π * I / v * gaussSum φ⁻¹ stdAddChar * ψ.generalizedBernoulli 1)
      else 0 := by
  split_ifs with hv
  · subst hv
    have hψ1 : ψ ≠ 1 := by
      rintro rfl
      rw [MulChar.one_apply (isUnit_one.neg), DirichletCharacter.modOne_eq_one'] at hpar
      norm_num at hpar
    have hu : u ≠ 1 := fun h ↦ hψ1 (ψ.level_one' h)
    have hgauss : gaussSum φ⁻¹ stdAddChar = 1 := by
      rw [gaussSum, Fintype.sum_unique, DirichletCharacter.modOne_eq_one', one_mul]
      convert AddChar.map_zero_eq_one (stdAddChar (N := 1)) using 2
    simp only [charWeight_cons ψ φ huv, isUnit_one.dvd, ↓reduceIte, Nat.div_one,
      DirichletCharacter.modOne_eq_one', mul_one, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul]
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    -- the row `a₀ = 0` would contribute `ψ(0) = 0`
    rw [Finset.sum_erase _ (by simp [ψ.map_zero' hu])]
    have hsum : ∑ a₀ : ZMod N, (N : ℂ) * ψ (a₀.val : ZMod u) * (π * I * (2 * a₀.val / N - 1)) =
        2 * π * I * ∑ a₀ : ZMod N, ψ (a₀.val : ZMod u) * (a₀.val : ℂ) -
          N * (π * I) * ∑ a₀ : ZMod N, ψ (a₀.val : ZMod u) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a₀ _ ↦ ?_
      field_simp
    rw [hsum, ← DirichletCharacter.natCast_mul_generalizedBernoulli_one_of_dvd
      (dvd_of_mul_right_dvd huv) hψ1, sum_comp_natCast_val (dvd_of_mul_right_dvd huv) fun r ↦ ψ r,
      MulChar.sum_eq_zero_of_ne_one hψ1, smul_zero, mul_zero, sub_zero, hgauss]
    push_cast
    ring
  · exact Finset.sum_eq_zero fun a₀ _ ↦ by
      rw [sum_charWeight_cons_eq_zero ψ φ huv (mt hφ.eq_one_iff.mp hv), zero_mul]

/-- **The constant coefficient of the weight-one Eisenstein series with character.** For
characters `ψ` modulo `u` and `φ` modulo `v` with `u v ∣ N`, `ψ(-1) φ(-1) = -1` and `φ` primitive,
the constant coefficient of `E₁^{ψ,φ}` is `2π i g(φ⁻¹) / v · (δ(φ) B₁,ψ + δ(ψ) B₁,φ)`, where
`δ(χ)` is `1` if `χ` has modulus one and `0` otherwise. With `L(0, χ) = -B₁,χ` this is
`-2π i g(φ⁻¹) / v · (δ(φ) L(0, ψ) + δ(ψ) L(0, φ))`. At most one of the two terms is nonzero, by
the parity condition. -/
theorem qExpansion_charE1MF_coeff_zero [NeZero u] [NeZero v] (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) :
    (qExpansion 1 (charE1MF ψ φ huv)).coeff 0 =
      2 * π * I / v * gaussSum φ⁻¹ stdAddChar *
        ((if v = 1 then ψ.generalizedBernoulli 1 else 0) +
          if u = 1 then φ.generalizedBernoulli 1 else 0) := by
  have hpair (a₀ a₁ : ZMod N) : (Fin.cons a₀ (Fin.cons a₁ finZeroElim) : Fin 2 → ZMod N) =
      ![a₀, a₁] := by
    ext i
    fin_cases i <;> rfl
  rw [qExpansion_charE1MF_coeff ψ φ huv hpar]
  simp only [↓reduceIte]
  -- split the sum over residue pairs into the row `a₀ = 0` and the rows `a₀ ≠ 0`
  rw [← (piFinTwoEquiv fun _ ↦ ZMod N).symm.sum_comp, Fintype.sum_prod_type,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  simp only [piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one, hpair, val_zero, ↓reduceIte]
  have hrows : ∑ a₀ ∈ Finset.univ.erase (0 : ZMod N), ∑ a₁ : ZMod N, charWeight N ψ φ ![a₀, a₁] *
      (if a₀.val = 0 then π * cot (π * (a₁.val / N)) else π * I * (2 * a₀.val / N - 1)) =
      ∑ a₀ ∈ Finset.univ.erase (0 : ZMod N),
        (∑ a₁ : ZMod N, charWeight N ψ φ ![a₀, a₁]) * (π * I * (2 * a₀.val / N - 1)) :=
    Finset.sum_congr rfl fun a₀ ha₀ ↦ by
      simp only [(val_ne_zero a₀).mpr (Finset.ne_of_mem_erase ha₀), ↓reduceIte, Finset.sum_mul]
  rw [hrows, sum_charWeight_zero_mul_pi_mul_cot ψ φ huv hpar hφ,
    sum_erase_zero_sum_charWeight_mul ψ φ huv hpar hφ]
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  split_ifs <;> field_simp <;> ring

/-- **The constant coefficient of the raised weight-one series.** Raising by `t` substitutes
`q ↦ q^t`, so `E₁^{ψ,φ,t}` has the constant coefficient of `E₁^{ψ,φ}`
(`qExpansion_charE1MF_coeff_zero`). -/
theorem qExpansion_charE1MFRaise_coeff_zero [NeZero u] [NeZero v] {t : ℕ}
    (htuv : t * (u * v) ∣ N) (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) :
    (qExpansion 1 (charE1MFRaise ψ φ t htuv)).coeff 0 =
      2 * π * I / v * gaussSum φ⁻¹ stdAddChar *
        ((if v = 1 then ψ.generalizedBernoulli 1 else 0) +
          if u = 1 then φ.generalizedBernoulli 1 else 0) := by
  rw [qExpansion_charE1MFRaise_coeff ψ φ htuv 0]
  simpa using qExpansion_charE1MF_coeff_zero ψ φ dvd_rfl hpar hφ

end TauCeti.EisensteinSeries
