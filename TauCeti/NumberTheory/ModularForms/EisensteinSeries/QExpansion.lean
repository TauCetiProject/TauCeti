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

The same Lipschitz formula gives the expansion of every weighted Eisenstein series
`G_W(z) = ∑_{x ∈ ℤ²} W(x mod N) (x₀ z + x₁)^(-k)` of level `Γ(N)` in `e^{2πi z / N}`
(`TauCeti.EisensteinSeries.qExpansion_coeff_of_coe_eq_weightedEisensteinSeries`). Here no parity
condition relates the rows `c` and `-c`; they are folded together into the residue function
`d ↦ W(c, d) + (-1)^k W(-c, -d)`. Since slashing by `SL₂(ℤ)` only changes the weight `W`, this
gives the expansions of `G_W` at every cusp.

The coefficient-identification argument follows Mathlib's
`EisensteinSeries.E_qExpansion_coeff`.

## Main definitions

* `TauCeti.EisensteinSeries.charRow`: the row `ψ(c) ∑_d φ⁻¹(d) (c v z + d)^(-k)` of `G_k^{ψ,φ}`.

## Main results

* `TauCeti.EisensteinSeries.qExpansion_identity_zmod`: the Lipschitz formula for a function of
  residues modulo `v`.
* `TauCeti.EisensteinSeries.summable_charRow`: the rows are summable (for `k ≥ 2` they decay
  exponentially, for `k < 2` they vanish).
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
* `TauCeti.EisensteinSeries.qExpansion_coeff_of_coe_eq_weightedEisensteinSeries`: the
  coefficients at the period `N` of a modular form whose values are those of a weighted Eisenstein
  series of weight `k ≥ 3`.

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
/-- The weights `ψ(a) φ⁻¹(b)` of the Eisenstein series with character have norm at most `1`. -/
lemma norm_apply_mul_inv_apply_le_one (a : ZMod u) (b : ZMod v) : ‖ψ a * φ⁻¹ b‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_mul (DirichletCharacter.norm_le_one _ _) (DirichletCharacter.norm_le_one _ _)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- **Only the rows `v c` contribute.** Weight the term `(c, d)` of the Eisenstein series by
`ψ(c / v) φ⁻¹(d)` if `v ∣ c` and by `0` otherwise. The row `a` of the weighted double series
vanishes unless `v ∣ a`, and its row `v c` is `charRow ψ φ k z c`, so its rows sum to `s` exactly
when the `charRow ψ φ k z c` do. -/
lemma hasSum_charRow_iff (k : ℕ) (z : ℍ) {s : ℂ} :
    HasSum (charRow ψ φ k z) s ↔ HasSum (fun c : ℤ ↦ ∑' d : ℤ,
      (if (v : ℤ) ∣ c then ψ ((c / v : ℤ) : ZMod u) * φ⁻¹ (d : ZMod v) else 0) *
        eisSummand k ![c, d] z) s := by
  have hv : (v : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne v)
  set R : ℤ → ℂ := fun c ↦ ∑' d : ℤ,
    (if (v : ℤ) ∣ c then ψ ((c / v : ℤ) : ZMod u) * φ⁻¹ (d : ZMod v) else 0) *
      eisSummand k ![c, d] z with hR
  have hRv : R ∘ (fun c : ℤ ↦ (v : ℤ) * c) = charRow ψ φ k z := by
    ext c
    simp [charRow_def, hR, eisSummand, Int.mul_ediv_cancel_left _ hv, ← tsum_mul_left, mul_assoc]
  rw [← hRv]
  refine (mul_right_injective₀ hv).hasSum_iff fun a ha ↦ ?_
  have hdvd : ¬ (v : ℤ) ∣ a := fun ⟨c, hc⟩ ↦ ha ⟨c, hc.symm⟩
  simp [hR, hdvd]

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

/-- In weight `k < 2` the inner series of a row is not summable, along the residue class `d ≡ 1`
modulo `v` its terms decay no faster than `1 / n`; so the row is zero. -/
private lemma charRow_eq_zero_of_lt_two (hk : k < 2) (z : ℍ) (c : ℤ) :
    charRow ψ φ k z c = 0 := by
  rw [charRow_def, tsum_eq_zero_of_not_summable, mul_zero]
  intro h
  set w : ℂ := ((v * c : ℤ) : ℂ) * z + 1 with hw
  have hv : (0 : ℝ) < v := Nat.cast_pos.mpr (NeZero.pos v)
  have h1 : Summable fun n : ℕ ↦ ‖(w + (v : ℂ) * n) ^ (-(k : ℤ))‖ := by
    have := (h.comp_injective (i := fun n : ℕ ↦ (1 + v * n : ℤ)) fun m n hmn ↦
      (by simpa using hmn : m = n ∨ v = 0).resolve_right (NeZero.ne v)).norm
    simpa [Function.comp_def, hw, add_assoc] using this
  have hne (n : ℕ) : w + (v : ℂ) * n ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    have hre := congrArg Complex.re h0
    simp only [hw, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.one_im, Complex.natCast_im, Complex.natCast_re, Complex.mul_re, Complex.add_re,
      Complex.one_re, Complex.zero_im, Complex.zero_re] at him hre
    push_cast at him hre
    have hz := z.2
    have hc : c = 0 := by
      by_contra hc
      have : (v : ℝ) * c * (z : ℂ).im = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact (mul_ne_zero hv.ne' (by exact_mod_cast hc)) h
      · exact hz.ne' h
    subst hc
    have : (0 : ℝ) ≤ (v : ℝ) * n := by positivity
    simp at hre
    linarith
  set C : ℝ := ‖w‖ + v with hC
  have hC1 : 1 ≤ C := by
    have : (1 : ℝ) ≤ v := Nat.one_le_cast.mpr (NeZero.pos v)
    linarith [norm_nonneg w]
  have hbound (n : ℕ) : 1 / (C * (n + 1)) ≤ ‖(w + (v : ℂ) * n) ^ (-(k : ℤ))‖ := by
    have hpos : 0 < ‖w + (v : ℂ) * n‖ := norm_pos_iff.mpr (hne n)
    have hle : ‖w + (v : ℂ) * n‖ ≤ C * (n + 1) := by
      calc ‖w + (v : ℂ) * n‖ ≤ ‖w‖ + v * n := by
            refine (norm_add_le _ _).trans ?_
            simp
        _ ≤ C * (n + 1) := by
            rw [hC]
            have : (0 : ℝ) ≤ n := n.cast_nonneg
            nlinarith [norm_nonneg w]
    interval_cases k
    · simp only [Nat.cast_zero, neg_zero, zpow_zero, norm_one]
      rw [div_le_one (by positivity)]
      nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    · simp only [Nat.cast_one, zpow_neg, zpow_one, norm_inv]
      rw [← one_div]
      exact one_div_le_one_div_of_le hpos hle
  have h2 : Summable fun n : ℕ ↦ 1 / (C * (n + 1)) :=
    h1.of_nonneg_of_le (fun n ↦ by positivity) hbound
  have h3 : Summable fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ) := by
    refine (h2.mul_left C).congr fun n ↦ ?_
    push_cast
    field_simp
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp h3)

/-- **The rows are summable.** The rows `ψ(c) ∑_d φ⁻¹(d) (c v z + d)^(-k)` of the Eisenstein
series with character form a summable family in `c ∈ ℤ`. For `k ≥ 2` they decay exponentially in
`|c|`; in weight two this holds although the double series does not converge absolutely. For
`k < 2` the inner series are not summable, so every row is zero (`charRow_eq_zero_of_lt_two`). -/
theorem summable_charRow (z : ℍ) : Summable (charRow ψ φ k z) := by
  rcases lt_or_ge k 2 with hk | hk
  · rw [funext (charRow_eq_zero_of_lt_two ψ φ hk z)]
    exact summable_zero
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
  rw [charRow_neg, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_apply_mul_inv_apply_le_one ψ φ _ _)

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
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven (summable_charRow ψ φ z),
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

omit [NeZero v] in
/-- **The Eisenstein series with character summed along rows.** For `k ≥ 3`, `G_k^{ψ,φ}(z)` is the
sum over `c ∈ ℤ` of the rows `ψ(c) ∑_{d ∈ ℤ} φ⁻¹(d) (c v z + d)^(-k)`: only the pairs `(v c, d)`
contribute to the absolutely convergent double series. -/
theorem hasSum_charRow_charEisensteinSeriesMF (hk : 3 ≤ (k : ℤ)) (huv : u * v ∣ N) (z : ℍ) :
    HasSum (charRow ψ φ k z) (charEisensteinSeriesMF ψ φ hk huv z) := by
  have : NeZero v := ⟨fun h ↦ NeZero.ne N (by simpa [h] using huv)⟩
  convert (summable_charRow ψ φ z).hasSum using 1
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
    · exact norm_apply_mul_inv_apply_le_one ψ φ _ _
    · simp
  have hsum : Summable F := by
    simpa [Function.comp_def, hF] using (finTwoArrowEquiv ℤ).symm.summable_iff.mpr hW
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
  rw [← hW', hFsum, hsum.tsum_prod]
  -- only the pairs `(v c, d)` contribute
  exact ((hasSum_charRow_iff ψ φ k z).mp (summable_charRow ψ φ z).hasSum).tsum_eq

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

/-! ### Weighted Eisenstein series at the period `N` -/

section Weighted

variable {N : ℕ} [NeZero N] (W : (Fin 2 → ZMod N) → ℂ) {k : ℕ}

/-- **The rows `c` and `-c` together.** For `c ≥ 1`, the sum of the rows `c` and `-c` of the
weighted Eisenstein series is, by the Lipschitz formula along residue classes modulo `N`, a power
series in `e^{2πi z / N}` supported on the multiples of `c`. Its coefficients are the Fourier
coefficients of the folded weight `d ↦ W(c, d) + (-1)^k W(-c, -d)`. -/
private lemma tsum_row_add_tsum_row_neg (hk : 2 ≤ k) (z : ℍ) (c : ℕ+)
    (h₁ : Summable fun d : ℤ ↦
      W ![((c : ℕ) : ZMod N), (d : ZMod N)] * eisSummand k ![((c : ℕ) : ℤ), d] z)
    (h₂ : Summable fun d : ℤ ↦
      W ![-((c : ℕ) : ZMod N), (d : ZMod N)] * eisSummand k ![-((c : ℕ) : ℤ), d] z) :
    ∑' d : ℤ, W ![((c : ℕ) : ZMod N), (d : ZMod N)] * eisSummand k ![((c : ℕ) : ℤ), d] z +
      ∑' d : ℤ, W ![-((c : ℕ) : ZMod N), (d : ZMod N)] * eisSummand k ![-((c : ℕ) : ℤ), d] z =
    (-2 * π * I) ^ k / ((k - 1).factorial * N ^ k) * ∑' m : ℕ+,
      𝓕 (fun d ↦ W ![((c : ℕ) : ZMod N), d] + (-1) ^ k * W ![-((c : ℕ) : ZMod N), -d])
        (-(m : ZMod N)) * (m : ℂ) ^ (k - 1) * cexp (2 * π * I * z / N) ^ ((c : ℕ) * m) := by
  let w : ℍ := ⟨((c : ℕ) : ℂ) * z, by simpa using mul_pos (Nat.cast_pos.mpr c.pos) z.2⟩
  have hw : (w : ℂ) = ((c : ℕ) : ℂ) * z := rfl
  have hsign : ((-1 : ℂ) ^ k)⁻¹ = (-1) ^ k := by
    rw [← inv_pow, inv_neg, inv_one]
  -- the row `c` is a row against `(c z + d)^(-k)`
  have hpos (d : ℤ) : W ![((c : ℕ) : ZMod N), (d : ZMod N)] * eisSummand k ![((c : ℕ) : ℤ), d] z =
      W ![((c : ℕ) : ZMod N), (d : ZMod N)] * ((w : ℂ) + d) ^ (-(k : ℤ)) := by
    simp [eisSummand, hw]
  -- the row `-c`, reindexed by `d ↦ -d`, is `(-1)^k` times a row against `(c z + d)^(-k)`
  have hneg (d : ℤ) : W ![-((c : ℕ) : ZMod N), ((-d : ℤ) : ZMod N)] *
        eisSummand k ![-((c : ℕ) : ℤ), -d] z =
      (-1) ^ k * W ![-((c : ℕ) : ZMod N), -(d : ZMod N)] * ((w : ℂ) + d) ^ (-(k : ℤ)) := by
    have h : ((-((c : ℕ) : ℤ) : ℤ) : ℂ) * z + ((-d : ℤ) : ℂ) = -((w : ℂ) + d) := by
      rw [hw]
      push_cast
      ring
    simp only [eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [h, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, neg_pow, mul_inv, hsign, Int.cast_neg]
    ring
  have hrow : ∑' d : ℤ, W ![-((c : ℕ) : ZMod N), (d : ZMod N)] *
        eisSummand k ![-((c : ℕ) : ℤ), d] z =
      ∑' d : ℤ,
        (-1) ^ k * W ![-((c : ℕ) : ZMod N), -(d : ZMod N)] * ((w : ℂ) + d) ^ (-(k : ℤ)) := by
    rw [← (Equiv.neg ℤ).tsum_eq]
    exact tsum_congr hneg
  have h₂' := (h₂.comp_injective neg_injective).congr fun d ↦ hneg d
  rw [tsum_congr hpos, hrow, ← Summable.tsum_add (h₁.congr hpos) h₂']
  have H := qExpansion_identity_zmod
    (fun d ↦ W ![((c : ℕ) : ZMod N), d] + (-1) ^ k * W ![-((c : ℕ) : ZMod N), -d]) hk w
  trans ∑' n : ℤ, (W ![((c : ℕ) : ZMod N), (n : ZMod N)] +
      (-1) ^ k * W ![-((c : ℕ) : ZMod N), -(n : ZMod N)]) * ((w : ℂ) + n) ^ (-(k : ℤ))
  · exact tsum_congr fun d ↦ by ring
  rw [H]
  congr 1
  refine tsum_congr fun m ↦ ?_
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, hw]
  congr 2
  push_cast
  ring

/-- The double series over `(c, m)` with `c, m ≥ 1` of the nonconstant terms of a weighted
Eisenstein series converges absolutely: its Fourier coefficients take finitely many values. -/
private lemma summable_norm_weightedTerm (z : ℍ) :
    Summable fun p : ℕ+ × ℕ+ ↦
      ‖𝓕 (fun d ↦ W ![((p.1 : ℕ) : ZMod N), d] + (-1) ^ k * W ![-((p.1 : ℕ) : ZMod N), -d])
          (-((p.2 : ℕ) : ZMod N)) * ((p.2 : ℕ) : ℂ) ^ (k - 1) *
        cexp (2 * π * I * z / N) ^ ((p.1 : ℕ) * p.2)‖ := by
  set q := cexp (2 * π * I * z / N)
  set g : ZMod N × ZMod N → ℝ := fun x ↦ ‖𝓕 (fun d ↦ W ![x.1, d] + (-1) ^ k * W ![-x.1, -d]) x.2‖
  have hr : ‖‖q‖‖ < 1 := by
    simpa [q, Function.Periodic.qParam] using UpperHalfPlane.norm_qParam_lt_one N z
  refine ((summable_prod_mul_pow (k - 1) hr).mul_left (∑ x, g x)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun p ↦ ?_
  have hg : g (((p.1 : ℕ) : ZMod N), -((p.2 : ℕ) : ZMod N)) ≤ ∑ x, g x :=
    Finset.single_le_sum (f := g) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ _)
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, mul_assoc]
  exact mul_le_mul hg le_rfl (by positivity) ((norm_nonneg _).trans hg)

/-- **Folding the rows of a weighted Eisenstein series.** The double series over `ℤ × ℤ` is the
sum of the row `c = 0` and the folded rows `c` and `-c` for `c ≥ 1`, each of which is given by
`tsum_row_add_tsum_row_neg`. -/
private lemma tsum_weightedEisensteinSummand_fold (hk : 2 ≤ k) (z : ℍ)
    (hF : Summable fun p : ℤ × ℤ ↦
      W ![(p.1 : ZMod N), (p.2 : ZMod N)] * eisSummand k ![p.1, p.2] z) :
    ∑' p : ℤ × ℤ, W ![(p.1 : ZMod N), (p.2 : ZMod N)] * eisSummand k ![p.1, p.2] z =
      ∑' d : ℤ, W ![0, (d : ZMod N)] * eisSummand k ![0, d] z +
        (-2 * π * I) ^ k / ((k - 1).factorial * N ^ k) * ∑' p : ℕ+ × ℕ+,
          𝓕 (fun d ↦ W ![((p.1 : ℕ) : ZMod N), d] +
              (-1) ^ k * W ![-((p.1 : ℕ) : ZMod N), -d]) (-((p.2 : ℕ) : ZMod N)) *
            ((p.2 : ℕ) : ℂ) ^ (k - 1) * cexp (2 * π * I * z / N) ^ ((p.1 : ℕ) * p.2) := by
  set F : ℤ × ℤ → ℂ := fun p ↦
    W ![(p.1 : ZMod N), (p.2 : ZMod N)] * eisSummand k ![p.1, p.2] z with hFdef
  have hT := (summable_norm_weightedTerm (k := k) W z).of_norm
  have hrows : Summable fun c : ℤ ↦ ∑' d, F (c, d) := hF.prod
  have hpos : Summable fun c : ℕ+ ↦ ∑' d, F (((c : ℕ) : ℤ), d) :=
    hrows.comp_injective (Nat.cast_injective.comp PNat.coe_injective)
  have hneg : Summable fun c : ℕ+ ↦ ∑' d, F (-((c : ℕ) : ℤ), d) :=
    hrows.comp_injective (neg_injective.comp (Nat.cast_injective.comp PNat.coe_injective))
  rw [hF.tsum_prod, tsum_int_eq_zero_add_tsum_pnat hrows, add_assoc, ← hpos.tsum_add hneg,
    hT.tsum_prod, ← tsum_mul_left]
  congr 1
  · exact tsum_congr fun d ↦ by simp [hFdef]
  refine tsum_congr fun c ↦ ?_
  simp only [hFdef, Int.cast_natCast, Int.cast_neg]
  rw [tsum_row_add_tsum_row_neg W hk z c
    (by simpa only [hFdef, Int.cast_natCast] using hF.prod_factor ((c : ℕ) : ℤ))
    (by simpa only [hFdef, Int.cast_natCast, Int.cast_neg] using
      hF.prod_factor (-((c : ℕ) : ℤ)))]

/-- **The `q`-expansion of a weighted Eisenstein series at the period `N`.** Let `k ≥ 3` and let
`f` be a modular form, on any group having `N` as a strict period, whose values are those of the
weighted Eisenstein series `∑_{x ∈ ℤ²} W(x mod N) (x₀ z + x₁)^(-k)`. Its expansion in
`e^{2πi z / N}` has constant coefficient `∑_{d ∈ ℤ} W(0, d) d^(-k)`, and for `n ≥ 1` its `n`-th
coefficient is `(-2πi)^k / ((k-1)! N^k) ∑_{c m = n} 𝓕h_c(-m) m^(k-1)`, where `𝓕` is the discrete
Fourier transform modulo `N` and `h_c(d) = W(c, d) + (-1)^k W(-c, -d)` folds the rows `c` and `-c`
of the series together. -/
theorem qExpansion_coeff_of_coe_eq_weightedEisensteinSeries {𝒢 : Subgroup (GL (Fin 2) ℝ)}
    (hN : (N : ℝ) ∈ 𝒢.strictPeriods) (hk : 3 ≤ k) {f : ModularForm 𝒢 k}
    (hf : ⇑f = weightedEisensteinSeries W k) (n : ℕ) :
    (qExpansion N f).coeff n =
      if n = 0 then ∑' d : ℤ, W ![0, (d : ZMod N)] * (d : ℂ) ^ (-(k : ℤ))
      else (-2 * π * I) ^ k / ((k - 1).factorial * N ^ k) *
        ∑ x ∈ n.divisorsAntidiagonal,
          𝓕 (fun d ↦ W ![(x.1 : ZMod N), d] + (-1) ^ k * W ![-(x.1 : ZMod N), -d])
            (-(x.2 : ZMod N)) * (x.2 : ℂ) ^ (k - 1) := by
  set K : ℂ := (-2 * π * I) ^ k / ((k - 1).factorial * N ^ k)
  set a : ℕ → ℂ := fun n ↦ ∑ x ∈ n.divisorsAntidiagonal,
    𝓕 (fun d ↦ W ![(x.1 : ZMod N), d] + (-1) ^ k * W ![-(x.1 : ZMod N), -d])
      (-(x.2 : ZMod N)) * (x.2 : ℂ) ^ (k - 1) with ha
  set b : ℕ → ℂ := fun n ↦
    if n = 0 then ∑' d : ℤ, W ![0, (d : ZMod N)] * (d : ℂ) ^ (-(k : ℤ)) else K * a n
  suffices h : ∀ τ : ℍ, HasSum (fun m ↦ b m • Function.Periodic.qParam N τ ^ m) (f τ) from
    (ModularFormClass.qExpansion_coeff_unique (Nat.cast_pos.mpr (NeZero.pos N)) hN h n).symm
  intro τ
  set q := cexp (2 * π * I * τ / N)
  have hq : Function.Periodic.qParam N τ = q := by simp [Function.Periodic.qParam, q]
  -- the double series over `ℤ × ℤ` converges absolutely
  set F : ℤ × ℤ → ℂ := fun p ↦
    W ![(p.1 : ZMod N), (p.2 : ZMod N)] * eisSummand k ![p.1, p.2] τ with hF
  have hcomp (x y : ℤ) : ((↑) : ℤ → ZMod N) ∘ ![x, y] = ![(x : ZMod N), (y : ZMod N)] := by
    ext i; fin_cases i <;> rfl
  have hFs : Summable F := ((finTwoArrowEquiv ℤ).symm.summable_iff.mpr
    (summable_norm_weightedEisensteinSummand W (by exact_mod_cast hk : (3 : ℤ) ≤ k) τ).of_norm
    ).congr fun p ↦ by simp only [Function.comp_apply, finTwoArrowEquiv_symm_apply, hcomp, hF]
  -- the double series over `(c, m)` of the nonconstant terms converges absolutely
  set T : ℕ → ℕ → ℂ := fun c m ↦
    𝓕 (fun d ↦ W ![(c : ZMod N), d] + (-1) ^ k * W ![-(c : ZMod N), -d]) (-(m : ZMod N)) *
      (m : ℂ) ^ (k - 1) * q ^ (c * m) with hT
  have hTs : Summable fun p : ℕ+ × ℕ+ ↦ T p.1 p.2 := (summable_norm_weightedTerm W τ).of_norm
  have hfτ : f τ = ∑' p, F p := by
    rw [hf, weightedEisensteinSeries_def, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
    simp [hF, hcomp]
  have hfold : ∑' p, F p = ∑' d : ℤ, F (0, d) + K * ∑' p : ℕ+ × ℕ+, T p.1 p.2 :=
    by simpa only [hF, hT, K, Int.cast_zero] using
      tsum_weightedEisensteinSummand_fold W (by omega) τ hFs
  -- regroup by `n = c m`; each group carries `q ^ n`
  have hgroup (n : ℕ+) : ∑ x ∈ (n : ℕ).divisorsAntidiagonal, T x.1 x.2 = a n * q ^ (n : ℕ) := by
    rw [ha, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x hx ↦ by simp only [hT, (Nat.mem_divisorsAntidiagonal.mp hx).1]
  have H := (hTs.hasSum.sum_divisorsAntidiagonal).mul_left K
  simp_rw [hgroup] at H
  convert! ((hasSum_pnat_iff (f := fun n : ℕ ↦ K * (a n * q ^ n))).mp H).add
    (hasSum_ite_eq 0 (∑' d : ℤ, W ![0, (d : ZMod N)] * (d : ℂ) ^ (-(k : ℤ)))) using 1
  · ext m
    rcases eq_or_ne m 0 with rfl | hm
    · simp [b, a, hq]
    · simp [b, hm, hq, mul_assoc]
  · rw [hfτ, hfold]
    simp only [a, Nat.divisorsAntidiagonal_zero, Finset.sum_empty, zero_mul, mul_zero, add_zero]
    rw [add_comm]
    congr 1
    refine tsum_congr fun d ↦ ?_
    simp [hF, eisSummand]

end Weighted

end TauCeti.EisensteinSeries
