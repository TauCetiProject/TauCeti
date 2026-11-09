/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LValues
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Bernoulli
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Normalized
public import TauCeti.NumberTheory.ModularForms.Cusps.LevelRaise
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Cotangent
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Constant terms of weight-one Eisenstein series

The normalized series has constant coefficient
`-(δ(φ) B₁,ψ + δ(ψ) B₁,φ) / 2`, where `δ` detects modulus one.
For primitive characters of opposite parity this coefficient is nonzero exactly when
one character has modulus one.

At the other cusps, slashing the weighted series `E₁^W` by `γ = !![a, b; c, d] ∈ SL(2, ℤ)`
replaces `W` by `x ↦ W(x γ⁻¹)` (`TauCeti.EisensteinSeries.valueAtInfty_weightedE1_slash`). Unlike
in weight `k ≥ 3`, the constant term at `i∞` involves every residue `x`, not only the row
`x₀ = 0`: the residues with `x₀ ≠ 0` contribute `π i (2 x₀ / N - 1)`. This sawtooth is the finite
Fourier transform of the cotangents `π cot (π j / N)`
(`TauCeti.sum_pi_mul_cot_pi_mul_val_div_mul_stdAddChar`), so the constant term of `E₁^W` at the
cusp `a / c` is a cotangent sum along the row `j (-c, a)`, of `W` and of its finite Fourier
transform at `j (a, c)` (`TauCeti.EisensteinSeries.constantTermAt_weightedE1MF`).

For the character weight of primitive `ψ` modulo `u` and `φ` modulo `v` at the natural level
`u v`, the Fourier transform is the character weight with the two characters exchanged, scaled by
Gauss sums. Hence the constant term of `E₁^{ψ,φ}` at the cusp `a / c` is a difference of two
terms: the term `ψ(-c / v) φ⁻¹(a) Λ(ψ, φ⁻¹)` when `v ∣ c`, as in weight `k ≥ 3`, minus the term
`φ(c / u) ψ⁻¹(a) g(ψ) g(φ⁻¹) Λ(ψ⁻¹, φ) / v` when `u ∣ c`, where `Λ(ψ, φ⁻¹)` is a cotangent sum
equal to `2 L(1, ψ φ⁻¹)` when `ψ φ⁻¹` is odd. These constant-term vectors are the input for
proving directness in the decomposition `M₁(N, χ) = S₁(N, χ) ⊕ E₁(N, χ)`, which is not proved
here. For characters of opposite parity, `ψ(-1) φ(-1) = -1`, the cotangent sums are nonzero
(`DirichletCharacter.sum_mul_inv_mul_pi_mul_cot_ne_zero`).

## Main results

* `TauCeti.EisensteinSeries.qExpansion_normalizedCharE1MF_coeff_zero`: the constant coefficient
  of the normalized series at `i∞`.
* `TauCeti.EisensteinSeries.constantTermAt_weightedE1MF`: the constant term of `E₁^W` at every
  cusp.
* `TauCeti.EisensteinSeries.constantTermAt_charE1MF`: the constant term of `E₁^{ψ,φ}` at every
  cusp.
* `TauCeti.EisensteinSeries.constantTermAt_charE1MFRaise`: the constant term of `E₁^{ψ,φ,t}` at
  every cusp, at every level divisible by `t u v`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §4.8.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 4.
-/

public noncomputable section

open Complex ZMod ModularForm
open UpperHalfPlane hiding I
open scoped Real

namespace TauCeti.EisensteinSeries

variable {u v N : ℕ} [NeZero u] [NeZero v] [NeZero N]
    (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- The constant coefficient in the normalization whose first coefficient is one. Both
characters can contribute, unlike in weights greater than one. -/
theorem qExpansion_normalizedCharE1MF_coeff_zero (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) :
    (qExpansion 1 (normalizedCharE1MF ψ φ huv)).coeff 0 =
      -((if v = 1 then ψ.generalizedBernoulli 1 else 0) +
        if u = 1 then φ.generalizedBernoulli 1 else 0) / 2 := by
  have hv : (v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
  have hg := DirichletCharacter.gaussSum_ne_zero_of_isPrimitive hv hφ.inv
    (isPrimitive_stdAddChar v)
  rw [normalizedCharE1MF_def, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul, qExpansion_charE1MF_coeff_zero ψ φ huv hpar hφ, smul_eq_mul]
  field_simp [hv, hg, Real.pi_ne_zero, I_ne_zero]

/-- For primitive characters of opposite parity, the constant term at infinity is nonzero
exactly when one of the characters has modulus one. -/
theorem qExpansion_normalizedCharE1MF_coeff_zero_ne_zero_iff (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hψ : ψ.IsPrimitive) (hφ : φ.IsPrimitive) :
    (qExpansion 1 (normalizedCharE1MF ψ φ huv)).coeff 0 ≠ 0 ↔ u = 1 ∨ v = 1 := by
  rw [qExpansion_normalizedCharE1MF_coeff_zero ψ φ huv hpar hφ]
  by_cases hu : u = 1
  · subst u
    have hodd : φ.Odd := by
      rw [DirichletCharacter.Odd]
      simpa only [DirichletCharacter.modOne_eq_one', one_mul] using hpar
    have hv : v ≠ 1 := by
      intro hv
      subst v
      norm_num [DirichletCharacter.modOne_eq_one'] at hpar
    simp [hv, φ.generalizedBernoulli_one_ne_zero hφ hodd]
  · by_cases hv : v = 1
    · subst v
      have hodd : ψ.Odd := by
        rw [DirichletCharacter.Odd]
        simpa only [DirichletCharacter.modOne_eq_one', mul_one] using hpar
      simp [hu, ψ.generalizedBernoulli_one_ne_zero hψ hodd]
    · simp [hu, hv]

/-- Level raising leaves the Bernoulli constant term unchanged. -/
theorem qExpansion_normalizedCharE1MFRaise_coeff_zero {t : ℕ} (htuv : t * (u * v) ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) :
    (qExpansion 1 (normalizedCharE1MFRaise ψ φ t htuv)).coeff 0 =
      -((if v = 1 then ψ.generalizedBernoulli 1 else 0) +
        if u = 1 then φ.generalizedBernoulli 1 else 0) / 2 := by
  let : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  rw [qExpansion_normalizedCharE1MFRaise, PowerSeries.coeff_expand]
  simp only [dvd_zero, ↓reduceIte, Nat.zero_div]
  exact qExpansion_normalizedCharE1MF_coeff_zero ψ φ dvd_rfl hpar hφ

/-! ### Constant terms at every cusp -/

section Cusps

open _root_.Matrix _root_.Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The constant terms `c_a` of the corrected division values, split into the row `a₀ = 0` and a
cotangent sum. -/
private lemma ite_pi_mul_cot_eq_sub_sum (a : Fin 2 → ZMod N) :
    (if (a 0).val = 0 then π * cot (π * ((a 1).val / N))
        else π * I * (2 * (a 0).val / N - 1)) =
      (if a 0 = 0 then π * cot (π * ((a 1).val / N)) else 0) -
        (N : ℂ)⁻¹ * ∑ j : ZMod N, π * cot (π * (j.val / N)) * stdAddChar (a 0 * j) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [TauCeti.sum_pi_mul_cot_pi_mul_val_div_mul_stdAddChar]
  simp only [ZMod.val_eq_zero]
  split_ifs
  · simp
  · field_simp
    ring

/-- **The constant term of a weighted weight-one series at every cusp.** At the cusp represented
by `γ = !![a, b; c, d] ∈ SL(2, ℤ)`, the constant term of `E₁^W` is
`N⁻¹ ∑_{j mod N} π cot (π j / N) (W(-j c, j a) - N⁻¹ 𝓕W(j a, j c))`, where
`𝓕W(p, q) = ∑_y W(y) e((p y₀ + q y₁) / N)` is the finite Fourier transform of `W`. The first part
is the row `(-j c, j a)` of `γ⁻¹` that also gives the constant term in weight `k ≥ 3`; the second
comes from the residues off that row, whose constant terms `π i (2 a₀ / N - 1)` are the finite
Fourier transform of the cotangents. -/
theorem constantTermAt_weightedE1MF (W : (Fin 2 → ZMod N) → ℂ) (γ : SL(2, ℤ)) :
    constantTermAt γ (weightedE1MF W) = (N : ℂ)⁻¹ * ∑ j : ZMod N, π * cot (π * (j.val / N)) *
      (W ![-(j * (γ 1 0 : ZMod N)), j * (γ 0 0 : ZMod N)] - (N : ℂ)⁻¹ *
        ∑ y, W y * stdAddChar (j * (y 0 * (γ 0 0 : ZMod N) + y 1 * (γ 1 0 : ZMod N)))) := by
  have h : weightedE1 W ∣[(1 : ℤ)] mapGL ℝ γ = weightedE1 W ∣[(1 : ℤ)] γ := (SL_slash _ γ).symm
  rw [constantTermAt_eq_valueAtInfty, coe_translate, coe_weightedE1MF, h,
    valueAtInfty_weightedE1_slash]
  set G := (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))
  -- the row `a₀ = 0` is the multiples `j (-c, a)` of the bottom row of `γ⁻¹`
  have hrow (j : ZMod N) : ![0, j] ᵥ* G = ![-(j * (γ 1 0 : ZMod N)), j * (γ 0 0 : ZMod N)] := by
    ext i
    fin_cases i <;> simp [G, vecMul, dotProduct, adjugate_fin_two]
  have h₁ : ∑ a : Fin 2 → ZMod N,
      W (a ᵥ* G) * (if a 0 = 0 then π * cot (π * ((a 1).val / N)) else 0) =
      ∑ j : ZMod N, π * cot (π * (j.val / N)) *
        W ![-(j * (γ 1 0 : ZMod N)), j * (γ 0 0 : ZMod N)] := by
    rw [← (piFinTwoEquiv fun _ ↦ ZMod N).symm.sum_comp, Fintype.sum_prod_type]
    simp [hrow, mul_comm]
  -- reindex the other residues by `a = y γ`
  have hG : ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) * G = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, mul_inv_cancel, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  have hfourier (j : ZMod N) : ∑ a : Fin 2 → ZMod N, W (a ᵥ* G) * stdAddChar (a 0 * j) =
      ∑ y, W y * stdAddChar (j * (y 0 * (γ 0 0 : ZMod N) + y 1 * (γ 1 0 : ZMod N))) := by
    rw [← Matrix.SpecialLinearGroup.sum_comp_vecMul _ (γ : SL(2, ZMod N))]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [Matrix.vecMul_vecMul, hG, Matrix.vecMul_one, mul_comm j]
    simp [vecMul, dotProduct, Fin.sum_univ_two]
  have h₂ : ∑ a : Fin 2 → ZMod N, W (a ᵥ* G) * ((N : ℂ)⁻¹ *
      ∑ j : ZMod N, π * cot (π * (j.val / N)) * stdAddChar (a 0 * j)) =
      ∑ j : ZMod N, π * cot (π * (j.val / N)) * ((N : ℂ)⁻¹ *
        ∑ y, W y * stdAddChar (j * (y 0 * (γ 0 0 : ZMod N) + y 1 * (γ 1 0 : ZMod N)))) := by
    simp_rw [← hfourier, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring
  simp_rw [ite_pi_mul_cot_eq_sub_sum, mul_sub, Finset.sum_sub_distrib, h₁, h₂]

/-! ### The series with character -/

/-- The character weight along the row `j (-c, a)`. -/
private lemma charWeight_row (j : ZMod (u * v)) (a c : ℤ) :
    charWeight (u * v) ψ φ ![-(j * (c : ZMod (u * v))), j * (a : ZMod (u * v))] =
      (if (v : ℤ) ∣ c then ψ ((-(c / v) : ℤ) : ZMod u) * φ⁻¹ (a : ZMod v) else 0) *
        (ψ (j.val : ZMod u) * φ⁻¹ (j.val : ZMod v)) := by
  have hx : ![-(j * (c : ZMod (u * v))), j * (a : ZMod (u * v))] =
      (↑) ∘ ((j.val : ℤ) • ![-c, a]) := by
    ext i
    fin_cases i <;> simp
  rw [hx, charWeight_intCast_smul ψ φ dvd_rfl, charWeight_intCast ψ φ dvd_rfl]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, dvd_neg,
    Int.cast_natCast]
  split_ifs with hc
  · rw [Int.neg_ediv_of_dvd hc]
    ring
  · simp

/-- **The Fourier transform of the character weight** at `j (a, c)`: the pairs `y` are weighted
by `e(j (y₀ a + y₁ c) / u v)`. It is a product of Gauss sums of `ψ` and of `φ⁻¹`, and vanishes
unless `u ∣ c`. -/
private lemma sum_charWeight_mul_stdAddChar (hψ : ψ.IsPrimitive) (hφ : φ.IsPrimitive)
    (j : ZMod (u * v)) (a c : ℤ) :
    ∑ y, charWeight (u * v) ψ φ y *
        stdAddChar (j * (y 0 * (a : ZMod (u * v)) + y 1 * (c : ZMod (u * v)))) =
      u * (gaussSum ψ stdAddChar * gaussSum φ⁻¹ stdAddChar) *
        (if (u : ℤ) ∣ c then φ ((c / u : ℤ) : ZMod v) * ψ⁻¹ (a : ZMod u) else 0) *
          (ψ⁻¹ (j.val : ZMod u) * φ (j.val : ZMod v)) := by
  -- the sum factors into a sum over `y₀` and a sum over `y₁`
  have hsplit (y₀ y₁ : ZMod (u * v)) :
      let y := (piFinTwoEquiv fun _ ↦ ZMod (u * v)).symm (y₀, y₁)
      charWeight (u * v) ψ φ y *
        stdAddChar (j * (y 0 * (a : ZMod (u * v)) + y 1 * (c : ZMod (u * v)))) =
      ((if v ∣ y₀.val then ψ ((y₀.val / v : ℕ) : ZMod u) else 0) *
        stdAddChar (y₀ * (j * (a : ZMod (u * v))))) *
          (φ⁻¹ (y₁.val : ZMod v) * stdAddChar (j * (c : ZMod (u * v)) * y₁)) := by
    simp only [charWeight_def, piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one]
    rw [show j * (y₀ * (a : ZMod (u * v)) + y₁ * (c : ZMod (u * v))) =
      y₀ * (j * (a : ZMod (u * v))) + j * (c : ZMod (u * v)) * y₁ by ring,
      AddChar.map_add_eq_mul]
    split_ifs <;> ring
  rw [← (piFinTwoEquiv fun _ ↦ ZMod (u * v)).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_congr rfl fun y₀ _ ↦ Finset.sum_congr rfl fun y₁ _ ↦ hsplit y₀ y₁]
  rw [← Finset.sum_mul_sum, hψ.sum_ite_dvd_val_mul_stdAddChar,
    hφ.sum_inv_mul_stdAddChar (dvd_mul_left v u), Nat.mul_div_cancel u (NeZero.pos v)]
  -- the remaining factor is the weight with the characters exchanged at `j (c, a)`
  have hW : (if u ∣ (j * (c : ZMod (u * v))).val then
        φ (((j * (c : ZMod (u * v))).val / u : ℕ) : ZMod v) else 0) *
          ψ⁻¹ ((j * (a : ZMod (u * v))).val : ZMod u) =
      charWeight (u * v) φ ψ ((↑) ∘ ((j.val : ℤ) • ![c, a])) := by
    simp [charWeight_def, ite_mul]
  rw [charWeight_intCast_smul φ ψ (mul_comm v u).dvd, charWeight_intCast φ ψ (mul_comm v u).dvd]
    at hW
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Int.cast_natCast] at hW
  trans u * (gaussSum ψ stdAddChar * gaussSum φ⁻¹ stdAddChar) *
    ((if u ∣ (j * (c : ZMod (u * v))).val then
      φ (((j * (c : ZMod (u * v))).val / u : ℕ) : ZMod v) else 0) *
        ψ⁻¹ ((j * (a : ZMod (u * v))).val : ZMod u))
  · split_ifs <;> ring
  rw [hW]
  ring

/-- **The constant term of the weight-one Eisenstein series with character at every cusp.** For
primitive `ψ` modulo `u` and `φ` modulo `v`, at the natural level `u v`, and
`γ = !![a, b; c, d] ∈ SL(2, ℤ)`, the constant term of `E₁^{ψ,φ}` at the cusp `a / c` is

`[v ∣ c] ψ(-c / v) φ⁻¹(a) Λ(ψ, φ⁻¹) - [u ∣ c] φ(c / u) ψ⁻¹(a) g(ψ) g(φ⁻¹) / v · Λ(ψ⁻¹, φ)`,

where `Λ(ψ, φ⁻¹) = (u v)⁻¹ ∑_{j mod u v} ψ(j) φ⁻¹(j) π cot (π j / u v)` and `g` is the Gauss sum.
The first term is the one of weight `k ≥ 3` (`constantTermAt_charEisensteinSeriesMF`); the second,
with the roles of the characters exchanged, is particular to weight one. For
`ψ(-1) φ(-1) = -1` both cotangent sums are `2 L(1, ·)` of an odd character, hence nonzero
(`DirichletCharacter.sum_mul_inv_mul_pi_mul_cot_ne_zero`). No parity hypothesis is needed. -/
theorem constantTermAt_charE1MF (hψ : ψ.IsPrimitive) (hφ : φ.IsPrimitive) (γ : SL(2, ℤ)) :
    constantTermAt γ (charE1MF ψ φ (dvd_refl (u * v))) =
      (if (v : ℤ) ∣ γ 1 0 then ψ ((-(γ 1 0 / v) : ℤ) : ZMod u) * φ⁻¹ (γ 0 0 : ZMod v) else 0) *
          (((u : ℂ) * v)⁻¹ * ∑ j : ZMod (u * v), ψ (j.val : ZMod u) * φ⁻¹ (j.val : ZMod v) *
            (π * cot (π * (j.val / (u * v))))) -
        (if (u : ℤ) ∣ γ 1 0 then φ ((γ 1 0 / u : ℤ) : ZMod v) * ψ⁻¹ (γ 0 0 : ZMod u) else 0) *
          (gaussSum ψ stdAddChar * gaussSum φ⁻¹ stdAddChar / v) *
          (((u : ℂ) * v)⁻¹ * ∑ j : ZMod (u * v), ψ⁻¹ (j.val : ZMod u) * φ (j.val : ZMod v) *
            (π * cot (π * (j.val / (u * v))))) := by
  have h := constantTermAt_weightedE1MF (charWeight (u * v) ψ φ) γ
  rw [constantTermAt_eq_valueAtInfty, coe_translate, coe_weightedE1MF] at h
  rw [constantTermAt_eq_valueAtInfty, coe_translate, coe_charE1MF, h]
  simp_rw [charWeight_row, sum_charWeight_mul_stdAddChar ψ φ hψ hφ]
  have hu : (u : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne u)
  have hv : (v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  field_simp

/-- **The constant term of a raised weight-one Eisenstein series with character at every cusp.**
At the cusp `a / c` put `g = gcd(c, t)`. The constant term of `E₁^{ψ,φ,t}(z) = E₁^{ψ,φ}(t z)` is
`g / t` times the constant term of `E₁^{ψ,φ}` at a cusp `(t a / g) / (c / g)`
(`constantTermAt_charE1MF`). The integer divisions are exact. -/
theorem constantTermAt_charE1MFRaise (hψ : ψ.IsPrimitive) (hφ : φ.IsPrimitive) {t : ℕ}
    (htuv : t * (u * v) ∣ N) (γ : SL(2, ℤ)) :
    constantTermAt γ (charE1MFRaise ψ φ t htuv) = (Int.gcd (γ 1 0) t : ℂ) / t *
      ((if (v : ℤ) ∣ γ 1 0 / Int.gcd (γ 1 0) t then
          ψ ((-(γ 1 0 / Int.gcd (γ 1 0) t / v) : ℤ) : ZMod u) *
            φ⁻¹ (((t : ℤ) * γ 0 0 / Int.gcd (γ 1 0) t : ℤ) : ZMod v) else 0) *
          (((u : ℂ) * v)⁻¹ * ∑ j : ZMod (u * v), ψ (j.val : ZMod u) * φ⁻¹ (j.val : ZMod v) *
            (π * cot (π * (j.val / (u * v))))) -
        (if (u : ℤ) ∣ γ 1 0 / Int.gcd (γ 1 0) t then
          φ ((γ 1 0 / Int.gcd (γ 1 0) t / u : ℤ) : ZMod v) *
            ψ⁻¹ (((t : ℤ) * γ 0 0 / Int.gcd (γ 1 0) t : ℤ) : ZMod u) else 0) *
          (gaussSum ψ stdAddChar * gaussSum φ⁻¹ stdAddChar / v) *
          (((u : ℂ) * v)⁻¹ * ∑ j : ZMod (u * v), ψ⁻¹ (j.val : ZMod u) * φ (j.val : ZMod v) *
            (π * cot (π * (j.val / (u * v)))))) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  obtain ⟨δ, hδa, hδc, hδ⟩ := _root_.ModularForm.exists_constantTermAt_levelRaise
    (charE1MF ψ φ dvd_rfl) (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv) γ
  rw [charE1MFRaise_eq_levelRaise, hδ, constantTermAt_charE1MF ψ φ hψ hφ, hδa, hδc, zpow_one]

end Cusps

end TauCeti.EisensteinSeries
