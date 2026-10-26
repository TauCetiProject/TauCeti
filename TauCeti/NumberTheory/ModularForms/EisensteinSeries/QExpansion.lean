/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import TauCeti.NumberTheory.ArithmeticFunction.TwistedDivisorSum
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Character
public import TauCeti.NumberTheory.TsumDivisorsAntidiagonal
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The `q`-expansion of Eisenstein series with character

For Dirichlet characters `ψ` modulo `u` and `φ` modulo `v` and a weight `k ≥ 3` with
`ψ(-1) φ(-1) = (-1)^k`, we compute the `q`-expansion of the Eisenstein series with character
`G_k^{ψ,φ}(z) = ∑_{(c, d) ∈ ℤ²} ψ(c) φ⁻¹(d) (c v z + d)^(-k)`
(`TauCeti.EisensteinSeries.charEisensteinSeriesMF`). Its constant coefficient is
`ψ(0) ∑_{d ∈ ℤ} φ⁻¹(d) d^(-k)`, and for `n ≥ 1` its `n`-th coefficient is
`2 (-2πi)^k / ((k-1)! v^k) ∑_{c m = n} ψ(c) φ̂(m) m^(k-1)`, where
`φ̂(m) = ∑_{r mod v} φ⁻¹(r) e^(2πi r m / v)`. When `φ` is primitive, `φ̂(m) = g(φ⁻¹) φ(m)` with
`g(φ⁻¹)` the Gauss sum, so the `n`-th coefficient is a constant multiple of the twisted divisor
sum `σ_{k-1}^{ψ,φ}(n) = ∑_{d ∣ n} ψ(n/d) φ(d) d^(k-1)`.

The analytic input is a Lipschitz formula along residue classes: for any `f : ZMod v → ℂ`,
`∑_{n ∈ ℤ} f(n) (z + n)^(-k) = (-2πi)^k / ((k-1)! v^k) ∑_{m ≥ 1} 𝓕f(-m) m^(k-1) e^(2πi m z / v)`,
obtained by applying Mathlib's `EisensteinSeries.qExpansion_identity_pnat` to each residue class
of `n` modulo `v`. The rows `c` and `-c` of `G_k^{ψ,φ}` contribute equally by the parity
condition, the row `c = 0` gives the constant term, and the remaining double series is regrouped
by `n = c m` (`HasSum.sum_divisorsAntidiagonal`).

This computation only uses that the series is the sum over `c ∈ ℤ` of its rows
`ψ(c) ∑_d φ⁻¹(d) (c v z + d)^(-k)`, and the rows form a summable family for every `k ≥ 2`. We
therefore state it for any modular form whose values are these sums of rows
(`TauCeti.EisensteinSeries.qExpansion_coeff_of_apply_eq_tsum_charRow`), so that it also applies
in weight two, where the double series does not converge absolutely.

The coefficient-identification argument follows Mathlib's
`EisensteinSeries.E_qExpansion_coeff`.

## Main definitions

* `TauCeti.EisensteinSeries.charRow`: the row `ψ(c) ∑_d φ⁻¹(d) (c v z + d)^(-k)` of `G_k^{ψ,φ}`.

## Main results

* `TauCeti.EisensteinSeries.qExpansion_identity_zmod`: the Lipschitz formula for a function of
  residues modulo `v`.
* `TauCeti.EisensteinSeries.summable_charRow`: for `k ≥ 2` the rows are summable.
* `TauCeti.EisensteinSeries.qExpansion_coeff_of_apply_eq_tsum_charRow`,
  `TauCeti.EisensteinSeries.qExpansion_coeff_of_apply_eq_tsum_charRow_of_isPrimitive`: the
  coefficients of a modular form of weight `k ≥ 2` which is the sum of these rows.
* `TauCeti.EisensteinSeries.hasSum_charRow_charEisensteinSeriesMF`: for `k ≥ 3`, `G_k^{ψ,φ}` is
  the sum of its rows.
* `TauCeti.EisensteinSeries.qExpansion_charEisensteinSeriesMF_coeff`: the coefficients of
  `G_k^{ψ,φ}`.
* `TauCeti.EisensteinSeries.qExpansion_charEisensteinSeriesMF_coeff_of_isPrimitive`: for
  primitive `φ`, the nonconstant coefficients are `2 (-2πi)^k g(φ⁻¹) / ((k-1)! v^k)` times the
  twisted divisor sums.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.5,
  Theorem 4.5.1.
* [T. Miyake, *Modular forms*][miyake1989], §7.1.
-/

public section

noncomputable section

open Complex ZMod EisensteinSeries ModularForm CongruenceSubgroup
open Matrix.SpecialLinearGroup (mapGL)
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

namespace TauCeti.EisensteinSeries

/-! ### The Lipschitz formula along residue classes -/

variable {v : ℕ} [NeZero v]

/-- The point `(z + r) / v` of the upper half-plane. -/
private def residuePoint (v : ℕ) [NeZero v] (z : ℍ) (r : ℕ) : ℍ :=
  ⟨((z : ℂ) + r) / v, by
    simpa [Complex.div_natCast_im] using div_pos z.2 (Nat.cast_pos.mpr (NeZero.pos v))⟩

private lemma coe_residuePoint (z : ℍ) (r : ℕ) :
    (residuePoint v z r : ℂ) = ((z : ℂ) + r) / v :=
  rfl

/-- The Lipschitz formula along one residue class modulo `v`. -/
private lemma tsum_residue (z : ℍ) {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    ∑' q : ℤ, ((z : ℂ) + (q * v + r : ℤ)) ^ (-(k : ℤ)) =
      (-2 * π * I) ^ k / ((k - 1).factorial * v ^ k) * ∑' m : ℕ+,
        (m : ℂ) ^ (k - 1) * cexp (2 * π * I * residuePoint v z r) ^ (m : ℕ) := by
  have hv : (v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
  have H := qExpansion_identity_pnat (k := k - 1) (by omega) (residuePoint v z r)
  have hk' : k - 1 + 1 = k := by omega
  rw [hk'] at H
  have hterm (q : ℤ) : ((z : ℂ) + (q * v + r : ℤ)) ^ (-(k : ℤ)) =
      ((v : ℂ) ^ k)⁻¹ * (1 / ((residuePoint v z r : ℂ) + q) ^ k) := by
    have : (z : ℂ) + (q * v + r : ℤ) = v * ((residuePoint v z r : ℂ) + q) := by
      rw [coe_residuePoint]
      push_cast
      field_simp
      ring
    rw [this, zpow_neg, zpow_natCast, mul_pow, mul_inv, one_div]
  simp_rw [hterm, tsum_mul_left, H]
  field_simp

/-- **The Lipschitz formula along residue classes.** For a function `f` of residues modulo `v`,
a weight `k ≥ 2` and `z` in the upper half-plane,
`∑_{n ∈ ℤ} f(n) (z + n)^(-k) = (-2πi)^k / ((k-1)! v^k) ∑_{m ≥ 1} 𝓕f(-m) m^(k-1) e^(2πi m z / v)`,
where `𝓕f(-m) = ∑_{r mod v} f(r) e^(2πi r m / v)` is the discrete Fourier transform of `f`.
For `v = 1` this is `f 0` times Mathlib's `EisensteinSeries.qExpansion_identity_pnat`. -/
theorem qExpansion_identity_zmod (f : ZMod v → ℂ) {k : ℕ} (hk : 2 ≤ k) (z : ℍ) :
    ∑' n : ℤ, f n * ((z : ℂ) + n) ^ (-(k : ℤ)) =
      (-2 * π * I) ^ k / ((k - 1).factorial * v ^ k) * ∑' m : ℕ+,
        𝓕 f (-(m : ZMod v)) * (m : ℂ) ^ (k - 1) * cexp (2 * π * I * z / v) ^ (m : ℕ) := by
  -- the series converges absolutely, as `f` is bounded
  have hS : Summable fun n : ℤ ↦ f n * ((z : ℂ) + n) ^ (-(k : ℤ)) := by
    have h0 : Summable fun n : ℤ ↦ ‖((z : ℂ) + n) ^ (-(k : ℤ))‖ :=
      summable_norm_iff.mpr <| (linear_right_summable (z : ℂ) 1 (k := k) (by omega)).congr
        fun n ↦ by simp [zpow_neg]
    refine (h0.mul_left (∑ x, ‖f x‖)).of_norm_bounded fun n ↦ ?_
    rw [norm_mul]
    gcongr
    exact Finset.single_le_sum (f := fun x ↦ ‖f x‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_univ _)
  -- split `n = q v + r` according to the residue `r` of `n` modulo `v`
  let e : Fin v × ℤ ≃ ℤ := (Equiv.prodComm _ _).trans (Int.divModEquiv v).symm
  have he (p : Fin v × ℤ) : e p = p.2 * v + (p.1 : ℕ) := by
    simp [e]
  have hprod := (e.summable_iff.mpr hS).tsum_prod
  simp only [Function.comp_def] at hprod
  rw [← e.tsum_eq, hprod, tsum_fintype]
  simp_rw [he]
  have hf (r : Fin v) (q : ℤ) : f ((q * v + (r : ℕ) : ℤ) : ZMod v) = f ((r : ℕ) : ZMod v) := by
    push_cast
    simp
  simp_rw [hf, tsum_mul_left, tsum_residue z hk]
  have hsum (r : Fin v) : Summable fun m : ℕ+ ↦
      (m : ℂ) ^ (k - 1) * cexp (2 * π * I * residuePoint v z (r : ℕ)) ^ (m : ℕ) := by
    have := (summable_pow_mul_cexp (k - 1) 1 (residuePoint v z r)).comp_injective
      PNat.coe_injective
    simpa [Function.comp_def] using this
  simp_rw [mul_left_comm (f _), ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun r _ ↦ ((hsum r).mul_left (f r)).mul_left _]
  refine tsum_congr fun m ↦ ?_
  rw [← Finset.mul_sum]
  congr 1
  -- the residue `r` contributes the additive character `r m / v` to the exponential
  have hexp (r : Fin v) : cexp (2 * π * I * residuePoint v z (r : ℕ)) ^ (m : ℕ) =
      stdAddChar (-(((r : ℕ) : ZMod v) * -(m : ZMod v))) * cexp (2 * π * I * z / v) ^ (m : ℕ) := by
    have hrm : -(((r : ℕ) : ZMod v) * -(m : ZMod v)) = (((r : ℕ) * m : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hrm, stdAddChar_coe, coe_residuePoint, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hbij : Function.Bijective fun r : Fin v ↦ ((r : ℕ) : ZMod v) :=
    (Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨fun j ↦ ⟨⟨j.val, j.val_lt⟩, by simp⟩, by simp [ZMod.card]⟩
  rw [dft_apply, Finset.sum_mul, Finset.sum_mul,
    ← Fintype.sum_bijective _ hbij (fun r : Fin v ↦ _) _ fun _ ↦ rfl]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [hexp, smul_eq_mul]
  ring

/-! ### The Eisenstein series with character -/

section Character

variable {u v N : ℕ} [NeZero v] [NeZero N] (ψ : DirichletCharacter ℂ u)
  (φ : DirichletCharacter ℂ v) {k : ℕ}

omit [NeZero v] in
/-- The row `c` of the Eisenstein series with character `G_k^{ψ,φ}`, weighted by `ψ(c)`:
`ψ(c) ∑_{d ∈ ℤ} φ⁻¹(d) (c v z + d)^(-k)`. For `k ≥ 2` the rows are summable
(`summable_charRow`), and `G_k^{ψ,φ}(z)` is their sum: for `k ≥ 3` when `u v ∣ N`
(`hasSum_charRow_charEisensteinSeriesMF`), and for `k = 2`, where the double series does not
converge absolutely, when `ψ` and `φ` are not both trivial (`hasSum_charRow_charG2MF`). -/
def charRow (k : ℕ) (z : ℍ) (c : ℤ) : ℂ :=
  ψ c * ∑' d : ℤ, φ⁻¹ d * (((v * c : ℤ) : ℂ) * z + d) ^ (-(k : ℤ))

omit [NeZero v] in
lemma charRow_def (k : ℕ) (z : ℍ) (c : ℤ) :
    charRow ψ φ k z c = ψ c * ∑' d : ℤ, φ⁻¹ d * (((v * c : ℤ) : ℂ) * z + d) ^ (-(k : ℤ)) :=
  (rfl)

omit [NeZero v] in
/-- Negating the row index `c` multiplies the row sum by `φ⁻¹(-1) (-1)^k`. -/
private lemma tsum_row_neg (z : ℍ) (c : ℤ) :
    ∑' d : ℤ, φ⁻¹ d * (((v * -c : ℤ) : ℂ) * z + d) ^ (-(k : ℤ)) =
      φ⁻¹ (-1) * (-1) ^ k * ∑' d : ℤ, φ⁻¹ d * (((v * c : ℤ) : ℂ) * z + d) ^ (-(k : ℤ)) := by
  rw [← (Equiv.neg ℤ).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun d ↦ ?_
  have h : ((v * -c : ℤ) : ℂ) * z + ((-d : ℤ) : ℂ) = -(((v * c : ℤ) : ℂ) * z + d) := by
    push_cast
    ring
  rw [Equiv.neg_apply, h, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, neg_pow, mul_inv,
    Int.cast_neg, ← neg_one_mul (d : ZMod v), map_mul]
  have h1 : ((-1 : ℂ) ^ k)⁻¹ = (-1) ^ k := by
    rw [← inv_pow]
    norm_num
  rw [h1]
  ring

omit [NeZero v] in
/-- The row `c = 0` is `ψ(0) ∑_{d ∈ ℤ} φ⁻¹(d) d^(-k)`. -/
@[simp]
lemma charRow_zero (k : ℕ) (z : ℍ) :
    charRow ψ φ k z 0 = ψ 0 * ∑' d : ℤ, φ⁻¹ d * (d : ℂ) ^ (-(k : ℤ)) := by
  simp [charRow_def]

omit [NeZero v] in
/-- Negating the row index `c` multiplies the row by `ψ(-1) φ⁻¹(-1) (-1)^k`. -/
lemma charRow_neg (z : ℍ) (c : ℤ) :
    charRow ψ φ k z (-c) = ψ (-1) * φ⁻¹ (-1) * (-1) ^ k * charRow ψ φ k z c := by
  rw [charRow_def, charRow_def, tsum_row_neg φ z, Int.cast_neg, ← neg_one_mul (c : ZMod u),
    map_mul]
  ring

/-- The row sum at `c ≥ 1`, by the Lipschitz formula along residue classes modulo `v`. -/
private lemma tsum_row_pnat (hk : 2 ≤ k) (z : ℍ) (c : ℕ+) :
    ∑' d : ℤ, φ⁻¹ d * (((v * c : ℤ) : ℂ) * z + d) ^ (-(k : ℤ)) =
      (-2 * π * I) ^ k / ((k - 1).factorial * v ^ k) * ∑' m : ℕ+,
        𝓕 ⇑(φ⁻¹) (-(m : ZMod v)) * (m : ℂ) ^ (k - 1) * cexp (2 * π * I * z) ^ (c * m : ℕ) := by
  let w : ℍ := ⟨((v * c : ℕ) : ℂ) * z, by
    simpa using mul_pos (Nat.cast_pos.mpr (mul_pos (NeZero.pos v) c.pos)) z.2⟩
  have hw : (((v * c : ℤ) : ℂ) * z) = (w : ℂ) := by
    simp [w]
  simp_rw [hw]
  rw [qExpansion_identity_zmod (⇑φ⁻¹) hk w]
  congr 1
  refine tsum_congr fun m ↦ ?_
  have hv : (v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
  rw [pow_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 2
  simp only [w]
  push_cast
  field_simp

/-- The row `c ≥ 1`, by the Lipschitz formula along residue classes. -/
private lemma charRow_pnat (hk : 2 ≤ k) (z : ℍ) (c : ℕ+) :
    charRow ψ φ k z c =
      (-2 * π * I) ^ k / ((k - 1).factorial * v ^ k) * ∑' m : ℕ+,
        ψ c * 𝓕 ⇑(φ⁻¹) (-(m : ZMod v)) * (m : ℂ) ^ (k - 1) *
          cexp (2 * π * I * z) ^ (c * m : ℕ) := by
  rw [charRow_def, tsum_row_pnat φ hk z c, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  exact tsum_congr fun m ↦ by push_cast; ring

/-- The double series over `(c, m)` with `c, m ≥ 1` of the nonconstant terms converges
absolutely. -/
private lemma summable_norm_charTerm (z : ℍ) :
    Summable fun p : ℕ+ × ℕ+ ↦ ‖ψ (p.1 : ℕ) * 𝓕 ⇑(φ⁻¹) (-((p.2 : ℕ) : ZMod v)) *
      ((p.2 : ℕ) : ℂ) ^ (k - 1) * cexp (2 * π * I * z) ^ ((p.1 : ℕ) * p.2)‖ := by
  set q := cexp (2 * π * I * z)
  have hr : ‖‖q‖‖ < 1 := by simpa using norm_exp_two_pi_I_lt_one z
  refine ((summable_prod_mul_pow (k - 1) hr).mul_left
    (∑ j, ‖𝓕 ⇑(φ⁻¹) j‖)).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun p ↦ ?_
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  have h1 := DirichletCharacter.norm_le_one ψ (p.1 : ℕ)
  have h2 : ‖𝓕 ⇑(φ⁻¹) (-(p.2 : ℕ))‖ ≤ ∑ j, ‖𝓕 ⇑(φ⁻¹) j‖ :=
    Finset.single_le_sum (f := fun j ↦ ‖𝓕 ⇑(φ⁻¹) j‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_univ _)
  calc ‖ψ (p.1 : ℕ)‖ * ‖𝓕 ⇑(φ⁻¹) (-(p.2 : ℕ))‖ * ((p.2 : ℕ) : ℝ) ^ (k - 1) *
        ‖q‖ ^ ((p.1 : ℕ) * p.2)
      ≤ 1 * (∑ j, ‖𝓕 ⇑(φ⁻¹) j‖) * ((p.2 : ℕ) : ℝ) ^ (k - 1) * ‖q‖ ^ ((p.1 : ℕ) * p.2) := by
        gcongr
    _ = _ := by ring

/-- **The rows are summable.** For `k ≥ 2`, the rows `ψ(c) ∑_d φ⁻¹(d) (c v z + d)^(-k)` of the
Eisenstein series with character form a summable family in `c ∈ ℤ`; they decay exponentially in
`|c|`. In weight two this holds although the double series does not converge absolutely. -/
theorem summable_charRow (hk : 2 ≤ k) (z : ℍ) : Summable (charRow ψ φ k z) := by
  have hS := summable_norm_charTerm ψ φ (k := k) z
  -- the rows `c ≥ 1`, by the Lipschitz formula
  have hpnat : Summable fun c : ℕ+ ↦ charRow ψ φ k z c := by
    refine (hS.prod.mul_left ‖(-2 * π * I) ^ k / ((k - 1).factorial * v ^ k)‖).of_norm_bounded
      fun c ↦ ?_
    rw [charRow_pnat ψ φ hk z c, norm_mul]
    gcongr
    exact norm_tsum_le_tsum_norm (hS.prod_factor c)
  have hnat : Summable fun n : ℕ ↦ charRow ψ φ k z n := summable_pnat_iff_summable_nat.mp hpnat
  -- the row `-n` is a multiple of the row `n` by a scalar of norm at most one
  refine .of_nat_of_neg hnat ((summable_norm_iff.mpr hnat).of_norm_bounded fun n ↦ ?_)
  rw [charRow_neg, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) ((mul_le_mul (DirichletCharacter.norm_le_one _ _)
    (DirichletCharacter.norm_le_one _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

/-- **Parity folding.** Under `ψ(-1) φ(-1) = (-1)^k`, the rows `c` and `-c` of the Eisenstein
series with character contribute equally. -/
private lemma tsum_charRow_eq_add_tsum_pnat (hk : 2 ≤ k) (hpar : ψ (-1) * φ (-1) = (-1) ^ k)
    (z : ℍ) :
    ∑' c : ℤ, charRow ψ φ k z c =
      ψ 0 * ∑' d : ℤ, φ⁻¹ d * (d : ℂ) ^ (-(k : ℤ)) +
        2 * (-2 * π * I) ^ k / ((k - 1).factorial * v ^ k) * ∑' c : ℕ+, ∑' m : ℕ+,
          ψ c * 𝓕 ⇑(φ⁻¹) (-(m : ZMod v)) * (m : ℂ) ^ (k - 1) *
            cexp (2 * π * I * z) ^ (c * m : ℕ) := by
  -- `φ⁻¹(-1) = φ(-1)`, as `φ(-1)² = 1`
  have hφ : φ⁻¹ (-1) = φ (-1) := by
    rw [MulChar.inv_apply_eq_inv']
    exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, neg_one_mul, neg_neg, map_one])
  have heven : Function.Even (charRow ψ φ k z) := by
    intro c
    have hsq : ((-1 : ℂ) ^ k) ^ 2 = 1 := by
      rw [sq, ← mul_pow, neg_one_mul, neg_neg, one_pow]
    rw [charRow_neg, hφ]
    linear_combination (charRow ψ φ k z c * (-1) ^ k) * hpar + charRow ψ φ k z c * hsq
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven (summable_charRow ψ φ hk z),
    tsum_congr (charRow_pnat ψ φ hk z), tsum_mul_left]
  simp only [charRow_zero, nsmul_eq_mul, Nat.cast_ofNat, add_right_inj]
  ring

/-! ### The `q`-expansion -/

omit [NeZero N] in
/-- **The `q`-expansion of a sum of rows.** Let `k ≥ 2` and `ψ(-1) φ(-1) = (-1)^k`. A modular form
for `Γ₁(N)` whose value at every `z` is the sum over `c ∈ ℤ` of the rows
`ψ(c) ∑_{d ∈ ℤ} φ⁻¹(d) (c v z + d)^(-k)` has constant coefficient
`ψ(0) ∑_{d ∈ ℤ} φ⁻¹(d) d^(-k)`, and for `n ≥ 1` its `n`-th coefficient is
`2 (-2πi)^k / ((k-1)! v^k) ∑_{c m = n} ψ(c) φ̂(m) m^(k-1)`, where
`φ̂(m) = ∑_{r mod v} φ⁻¹(r) e^(2πi r m / v)`. This applies to the Eisenstein series with character
in weight `k ≥ 3`, where the double series converges absolutely, and in weight two, where the
double series is not absolutely convergent and this theorem uses its iterated sum along rows. -/
theorem qExpansion_coeff_of_apply_eq_tsum_charRow (hk : 2 ≤ k)
    (hpar : ψ (-1) * φ (-1) = (-1) ^ k) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : ∀ z : ℍ, f z = ∑' c : ℤ, charRow ψ φ k z c)
    (n : ℕ) :
    (qExpansion 1 f).coeff n =
      if n = 0 then ψ 0 * ∑' d : ℤ, φ⁻¹ d * (d : ℂ) ^ (-(k : ℤ))
      else 2 * (-2 * π * I) ^ k / ((k - 1).factorial * v ^ k) *
        ∑ x ∈ n.divisorsAntidiagonal,
          ψ x.1 * 𝓕 ⇑(φ⁻¹) (-(x.2 : ZMod v)) * (x.2 : ℂ) ^ (k - 1) := by
  set K : ℂ := 2 * (-2 * π * I) ^ k / ((k - 1).factorial * v ^ k)
  set a : ℕ → ℂ := fun n ↦ ∑ x ∈ n.divisorsAntidiagonal,
    ψ x.1 * 𝓕 ⇑(φ⁻¹) (-(x.2 : ZMod v)) * (x.2 : ℂ) ^ (k - 1) with ha
  set b : ℕ → ℂ := fun n ↦ if n = 0 then ψ 0 * ∑' d : ℤ, φ⁻¹ d * (d : ℂ) ^ (-(k : ℤ))
    else K * a n
  suffices h : ∀ τ : ℍ, HasSum (fun m ↦ b m • Function.Periodic.qParam 1 τ ^ m) (f τ) from
    (ModularFormClass.qExpansion_coeff_unique one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map N) h n).symm
  intro τ
  set q := cexp (2 * π * I * τ)
  have hq : Function.Periodic.qParam 1 τ = q := by
    simp [Function.Periodic.qParam, q]
  -- the double series over `(c, m)` converges absolutely
  set T : ℕ → ℕ → ℂ := fun c m ↦
    ψ c * 𝓕 ⇑(φ⁻¹) (-(m : ZMod v)) * (m : ℂ) ^ (k - 1) * q ^ (c * m) with hT
  have hTs : Summable fun p : ℕ+ × ℕ+ ↦ T p.1 p.2 := (summable_norm_charTerm ψ φ τ).of_norm
  -- regroup by `n = c m`; each group carries `q ^ n`
  have hgroup (n : ℕ+) : ∑ x ∈ (n : ℕ).divisorsAntidiagonal, T x.1 x.2 = a n * q ^ (n : ℕ) := by
    rw [ha, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp only [hT]
    rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  have H := (hTs.hasSum.sum_divisorsAntidiagonal).mul_left K
  simp_rw [hgroup] at H
  have H' := (hasSum_pnat_iff (f := fun n : ℕ ↦ K * (a n * q ^ n))).mp H
  have hconst := hasSum_ite_eq 0 (ψ 0 * ∑' d : ℤ, φ⁻¹ d * (d : ℂ) ^ (-(k : ℤ)))
  convert! H'.add hconst using 1
  · ext m
    rcases eq_or_ne m 0 with rfl | hm
    · simp [b, a, hq]
    · simp [b, hm, hq, mul_assoc]
  · rw [hf τ, tsum_charRow_eq_add_tsum_pnat ψ φ hk hpar τ, ← hTs.tsum_prod]
    simp only [Nat.divisorsAntidiagonal_zero, Finset.sum_empty, pow_zero, mul_one, mul_zero,
      add_zero, T, q, a]
    ring

omit [NeZero N] in
/-- **The `q`-expansion of a sum of rows, for primitive `φ`.** Under the hypotheses of
`qExpansion_coeff_of_apply_eq_tsum_charRow`, the Fourier transform of `φ⁻¹` is a multiple of `φ`
by the Gauss sum `g(φ⁻¹)`, and for `n ≥ 1` the `n`-th coefficient is
`2 (-2πi)^k / ((k-1)! v^k) g(φ⁻¹) σ_{k-1}^{ψ,φ}(n)`, where
`σ_{k-1}^{ψ,φ}(n) = ∑_{d ∣ n} ψ(n/d) φ(d) d^(k-1)` is the twisted divisor sum. -/
theorem qExpansion_coeff_of_apply_eq_tsum_charRow_of_isPrimitive (hk : 2 ≤ k)
    (hpar : ψ (-1) * φ (-1) = (-1) ^ k) (hφ : φ.IsPrimitive)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : ∀ z : ℍ, f z = ∑' c : ℤ, charRow ψ φ k z c)
    {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 f).coeff n =
      2 * (-2 * π * I) ^ k / ((k - 1).factorial * v ^ k) * gaussSum φ⁻¹ stdAddChar *
        DirichletCharacter.twistedDivisorSum (k - 1) ψ φ n := by
  have hφ' : (φ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hφ
  rw [qExpansion_coeff_of_apply_eq_tsum_charRow ψ φ hk hpar hf]
  simp only [hn, ↓reduceIte]
  rw [DirichletCharacter.twistedDivisorSum_apply,
    ← Nat.sum_divisorsAntidiagonal' (f := fun a b : ℕ ↦ ψ a * φ b * (b : ℂ) ^ (k - 1)),
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [hφ'.fourierTransform_eq_inv_mul_gaussSum, inv_inv, neg_neg]
  ring

/-! ### The Eisenstein series with character in weight `k ≥ 3` -/

/-- **The Eisenstein series with character summed along rows.** For `k ≥ 3`, `G_k^{ψ,φ}(z)` is the
sum over `c ∈ ℤ` of the rows `ψ(c) ∑_{d ∈ ℤ} φ⁻¹(d) (c v z + d)^(-k)`: only the pairs `(v c, d)`
contribute to the absolutely convergent double series. -/
theorem hasSum_charRow_charEisensteinSeriesMF (hk : 3 ≤ (k : ℤ)) (huv : u * v ∣ N) (z : ℍ) :
    HasSum (charRow ψ φ k z) (charEisensteinSeriesMF ψ φ hk huv z) := by
  convert (summable_charRow ψ φ (k := k) (by omega) z).hasSum using 1
  set F : ℤ × ℤ → ℂ := fun p ↦
    (if (v : ℤ) ∣ p.1 then ψ ((p.1 / v : ℤ) : ZMod u) * φ⁻¹ (p.2 : ZMod v) else 0) *
      eisSummand k ![p.1, p.2] z with hF
  -- the weights are bounded by `1`, so the double series converges absolutely
  have hW : Summable fun x : Fin 2 → ℤ ↦
      (if (v : ℤ) ∣ x 0 then ψ ((x 0 / v : ℤ) : ZMod u) * φ⁻¹ (x 1 : ZMod v) else 0) *
        eisSummand k x z := by
    refine (summable_norm_eisSummand hk z).of_norm_bounded fun x ↦ ?_
    rw [norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    split_ifs
    · rw [norm_mul]
      exact (mul_le_mul (DirichletCharacter.norm_le_one _ _) (DirichletCharacter.norm_le_one _ _)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    · simp
  have hsum : Summable F := by
    simpa [Function.comp_def, hF] using (finTwoArrowEquiv ℤ).symm.summable_iff.mpr hW
  -- only the pairs `(v c, d)` contribute
  have hinj : Function.Injective fun c : ℤ ↦ (v : ℤ) * c :=
    mul_right_injective₀ (Int.natCast_ne_zero.mpr (NeZero.ne v))
  have hsupp : Function.support (fun a ↦ ∑' d, F (a, d)) ⊆ Set.range fun c : ℤ ↦ (v : ℤ) * c := by
    intro a ha
    by_contra h
    have hdvd : ¬ (v : ℤ) ∣ a := fun ⟨c, hc⟩ ↦ h ⟨c, hc.symm⟩
    exact ha (by simp [hF, hdvd])
  have hT (c : ℤ) : ∑' d, F ((v : ℤ) * c, d) =
      ψ c * ∑' d : ℤ, φ⁻¹ d * (((v * c : ℤ) : ℂ) * z + d) ^ (-(k : ℤ)) := by
    simp [hF, eisSummand, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (NeZero.ne v)),
      ← tsum_mul_left, mul_assoc]
  rw [charEisensteinSeriesMF_apply]
  have hW' := (finTwoArrowEquiv ℤ).symm.tsum_eq fun x : Fin 2 → ℤ ↦
      (if (v : ℤ) ∣ x 0 then ψ ((x 0 / v : ℤ) : ZMod u) * φ⁻¹ (x 1 : ZMod v) else 0) *
        eisSummand k x z
  simp only [finTwoArrowEquiv_symm_apply] at hW'
  have hFsum : (∑' p : ℤ × ℤ,
      (if (v : ℤ) ∣ ![p.1, p.2] 0 then
        ψ ((![p.1, p.2] 0 / v : ℤ) : ZMod u) * φ⁻¹ (![p.1, p.2] 1 : ZMod v) else 0) *
          eisSummand k ![p.1, p.2] z) = ∑' p, F p :=
    tsum_congr fun p ↦ by simp [hF]
  rw [← hW', hFsum, hsum.tsum_prod, ← hinj.tsum_eq hsupp]
  exact tsum_congr fun c ↦ (hT c).trans (charRow_def ψ φ k z c).symm

/-- **The `q`-expansion of the Eisenstein series with character.** For characters `ψ` modulo
`u` and `φ` modulo `v` with `ψ(-1) φ(-1) = (-1)^k`, the constant coefficient of `G_k^{ψ,φ}` is
`ψ(0) ∑_{d ∈ ℤ} φ⁻¹(d) d^(-k)`, and for `n ≥ 1` its `n`-th coefficient is
`2 (-2πi)^k / ((k-1)! v^k) ∑_{c m = n} ψ(c) φ̂(m) m^(k-1)`,
where `φ̂(m) = ∑_{r mod v} φ⁻¹(r) e^(2πi r m / v)` is the discrete Fourier transform of `φ⁻¹`
at `-m`. (If the parity condition fails, the series is zero:
`charEisensteinSeriesMF_eq_zero`.) -/
theorem qExpansion_charEisensteinSeriesMF_coeff (hk : 3 ≤ (k : ℤ)) (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = (-1) ^ k) (n : ℕ) :
    (qExpansion 1 (charEisensteinSeriesMF ψ φ hk huv)).coeff n =
      if n = 0 then ψ 0 * ∑' d : ℤ, φ⁻¹ d * (d : ℂ) ^ (-(k : ℤ))
      else 2 * (-2 * π * I) ^ k / ((k - 1).factorial * v ^ k) *
        ∑ x ∈ n.divisorsAntidiagonal,
          ψ x.1 * 𝓕 ⇑(φ⁻¹) (-(x.2 : ZMod v)) * (x.2 : ℂ) ^ (k - 1) :=
  qExpansion_coeff_of_apply_eq_tsum_charRow ψ φ (by omega) hpar
    (fun z ↦ (hasSum_charRow_charEisensteinSeriesMF ψ φ hk huv z).tsum_eq.symm) n

/-- **The `q`-expansion of the Eisenstein series with character, for primitive `φ`.** Then the
Fourier transform of `φ⁻¹` is a multiple of `φ` by the Gauss sum `g(φ⁻¹)`, and for `n ≥ 1` the
`n`-th coefficient of `G_k^{ψ,φ}` is
`2 (-2πi)^k / ((k-1)! v^k) g(φ⁻¹) σ_{k-1}^{ψ,φ}(n)`, where
`σ_{k-1}^{ψ,φ}(n) = ∑_{d ∣ n} ψ(n/d) φ(d) d^(k-1)` is the twisted divisor sum. -/
theorem qExpansion_charEisensteinSeriesMF_coeff_of_isPrimitive (hk : 3 ≤ (k : ℤ))
    (huv : u * v ∣ N) (hpar : ψ (-1) * φ (-1) = (-1) ^ k) (hφ : φ.IsPrimitive) {n : ℕ}
    (hn : n ≠ 0) :
    (qExpansion 1 (charEisensteinSeriesMF ψ φ hk huv)).coeff n =
      2 * (-2 * π * I) ^ k / ((k - 1).factorial * v ^ k) * gaussSum φ⁻¹ stdAddChar *
        DirichletCharacter.twistedDivisorSum (k - 1) ψ φ n :=
  qExpansion_coeff_of_apply_eq_tsum_charRow_of_isPrimitive ψ φ (by omega) hpar hφ
    (fun z ↦ (hasSum_charRow_charEisensteinSeriesMF ψ φ hk huv z).tsum_eq.symm) hn

end Character

end TauCeti.EisensteinSeries
