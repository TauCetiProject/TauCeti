/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DedekindSum
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup

/-!
# Dedekind's functional equation and the explicit eta multiplier

`TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation` establishes nonconstructively (by
modularity of `Δ = η²⁴` and connectedness of `ℍ`) that `η(γ • τ) = ε(γ) √(c τ + d) η(τ)` on the
upper half-plane for a 24th root of unity `ε(γ) = TauCeti.ModularForm.etaMultiplier γ`, where
`√(c τ + d)` is the principal square root `Complex.sqrt ((c : ℂ) * τ + d)` (cut along `(-∞, 0]`,
with nonnegative real part). Computing explicit transformation factors, Nebentypus characters via
Kronecker/Jacobi symbols, and cusp expansions of eta quotients on congruence subgroups requires
closed arithmetic formulas for `ε(γ)` in terms of the matrix entries.

This file evaluates `etaMultiplier γ` for every `γ = (a b; c d) ∈ SL(2, ℤ)` with `c ≠ 0` in terms
of Dedekind sums `s(d, c) = TauCeti.dedekindSum d c` (complementing the `c = 0` formulas in
`DedekindEta.Transformation`):

* When `c > 0`,
  $$\varepsilon(\gamma) =
    \exp\!\left(\pi i \left(\frac{a + d}{12 c} - s(d, c) - \frac{1}{4}\right)\right),$$
  so `η(γ • τ) = exp(π i ((a + d) / (12 c) - s(d, c) - 1/4)) √(c τ + d) η(τ)` on `ℍ` with the
  principal square root `Complex.sqrt` (`etaMultiplier_of_c_pos`,
  `etaMultiplier_eq_exp_sum_fract_of_c_pos`, `eta_smul_of_c_pos`). On `ℍ`, `c τ + d` lies in the
  upper half-plane when `c > 0`, so `√(-i (c τ + d)) = e^{-π i / 4} √(c τ + d)`
  (`Complex.sqrt_neg_I_mul`); using the principal root `√(c τ + d)` rather than Apostol's
  `√(-i (c τ + d))` normalization accounts for the `-1/4` shift in the exponent.
* For arbitrary `c ≠ 0`, combining `etaMultiplier_of_c_pos` with `etaMultiplier_neg_of_c_pos`
  yields the `c < 0` formula (`etaMultiplier_of_c_neg`) and Rademacher's sign-unified formula
  $$\varepsilon(\gamma) =
    \exp\!\left(\pi i \left(\frac{a + d}{12 c}
      - \operatorname{sgn}(c)\left(s(d, |c|) + \frac{1}{4}\right)\right)\right)$$
  (`etaMultiplier_of_c_ne_zero`), where `-sgn(c) / 4` converts from Rademacher–Grosswald's
  `√((c τ + d) / (i sgn c))` normalization to the principal root `Complex.sqrt ((c : ℂ) * τ + d)`.
  Since `a d - b c = 1` implies `a d ≡ 1 [ZMOD |c|]`, `TauCeti.dedekindSum_eq_of_mul_modEq_one`
  identifies `s(d, |c|)` with `s(a, |c|)`.

## Implementation notes

The proof of `etaMultiplier_of_c_pos` inducts on `c` along the Euclidean algorithm using the
generator laws `etaMultiplier_mul_T_zpow`, `etaMultiplier_mul_S`, and `etaMultiplier_of_c_eq_one`
from `TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation`, matched at the inversion step
by Dedekind's reciprocity law `TauCeti.dedekindSum_add_dedekindSum`.

## Main results

* `TauCeti.ModularForm.etaMultiplier_of_c_pos`,
  `TauCeti.ModularForm.etaMultiplier_eq_exp_sum_fract_of_c_pos`,
  `TauCeti.ModularForm.eta_smul_of_c_pos`: **Dedekind's functional equation** for `c > 0`.
* `TauCeti.ModularForm.etaMultiplier_of_c_neg`,
  `TauCeti.ModularForm.etaMultiplier_of_c_ne_zero`: explicit Dedekind-sum formulas for `c < 0` and
  all `c ≠ 0`.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed., Theorem 3.4.
* H. Rademacher and E. Grosswald, *Dedekind Sums*, Carus Mathematical Monographs 16, 1972, Ch. 4.
-/

public section

open Complex ModularGroup
open scoped UpperHalfPlane
open scoped Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### Dedekind's functional equation (`c > 0`) -/

private theorem euclidean_step_exp {a b₁ c d q r : ℤ} (hc : 0 < c) (hr : 0 < r)
    (hdiv : c * q + r = d) (hdet : a * r - b₁ * c = 1) :
    (q : ℚ) / 12 + 1 / 4 +
        (((b₁ : ℚ) + (-c : ℤ)) / (12 * r) - dedekindSum (-c) r - 1 / 4) =
      ((a : ℚ) + d) / (12 * c) - dedekindSum d c - 1 / 4 := by
  have hcop : IsCoprime r c := ⟨a, -b₁, by linarith⟩
  have hrec := dedekindSum_add_dedekindSum hr hc hcop
  have hmod : dedekindSum d c = dedekindSum r c := by
    rw [← hdiv, add_comm, mul_comm, dedekindSum_add_mul_self]
  have hcQ : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne'
  have hrQ : (r : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hr.ne'
  have hdetQ : (a : ℚ) * r - (b₁ : ℚ) * c = 1 := by exact_mod_cast hdet
  have hdivQ : (c : ℚ) * q + r = d := by exact_mod_cast hdiv
  have hsr : dedekindSum c r =
      ((r : ℚ) ^ 2 + (c : ℚ) ^ 2 + 1) / (12 * r * c) - 1 / 4 - dedekindSum r c := by
    linarith
  rw [dedekindSum_neg, hmod, hsr]
  push_cast
  field_simp
  linear_combination 4 * (r : ℚ) * hdivQ - 4 * hdetQ

/-- Euclidean reduction step for `etaMultiplier_of_c_pos`: when `1 < γ 1 0`, right-multiplying `γ`
by `T ^ (-(γ 1 1 / γ 1 0)) * S` produces `γ₂` with `0 < γ₂ 1 0 < γ 1 0`, and Dedekind's
reciprocity law transports the Dedekind-sum formula from `γ₂` back to `γ`. -/
private theorem etaMultiplier_euclidean_step (γ : SL(2, ℤ)) (hc : 1 < γ 1 0) :
    let q : ℤ := γ 1 1 / γ 1 0
    let γ₂ : SL(2, ℤ) := γ * T ^ (-q) * S
    0 < γ₂ 1 0 ∧ γ₂ 1 0 < γ 1 0 ∧
      (etaMultiplier γ₂ =
          cexp (π * I *
            (((γ₂ 0 0 : ℂ) + γ₂ 1 1) / (12 * γ₂ 1 0) -
              dedekindSum (γ₂ 1 1) (γ₂ 1 0) - 1 / 4)) →
        etaMultiplier γ =
          cexp (π * I *
            (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
              dedekindSum (γ 1 1) (γ 1 0) - 1 / 4))) := by
  let c : ℤ := γ 1 0
  let d : ℤ := γ 1 1
  let q : ℤ := d / c
  let r : ℤ := d % c
  have hc_pos : 0 < c := by omega
  -- Euclidean division `d = c * q + r`; coprimality of `(c, d)` with `1 < c` forces `0 < r < c`.
  have hdiv : c * q + r = d := Int.mul_ediv_add_emod d c
  have hr_lt : r < c := Int.emod_lt_of_pos d hc_pos
  have hr_pos : 0 < r := by
    refine lt_of_le_of_ne (Int.emod_nonneg d hc_pos.ne') fun hr0 ↦ ?_
    have hcr : c ∣ 1 := (γ.isCoprime_row 1).isUnit_of_dvd' dvd_rfl ⟨q, by linarith⟩ |>.dvd
    exact absurd (Int.le_of_dvd zero_lt_one hcr) (by omega)
  -- Read off the entries of `γ₁ = γ * T ^ (-q)` and `γ₂ = γ₁ * S`.
  let γ₁ : SL(2, ℤ) := γ * T ^ (-q)
  let γ₂ : SL(2, ℤ) := γ₁ * S
  have hγ₁_00 : γ₁ 0 0 = γ 0 0 := by dsimp only [γ₁]; rw [γ.coe_mul_T_zpow]; simp
  have hγ₁_10 : γ₁ 1 0 = c := by dsimp only [γ₁, c]; rw [γ.coe_mul_T_zpow]; simp
  have hγ₁_11 : γ₁ 1 1 = r := by
    have h11 : γ₁ 1 1 = c * (-q) + d := by dsimp only [γ₁, c, d]; rw [γ.coe_mul_T_zpow]; simp
    linarith [h11, mul_neg c q, hdiv]
  have hγ₂_00 : γ₂ 0 0 = γ₁ 0 1 := by dsimp only [γ₂]; rw [γ₁.coe_mul_S]; simp
  have hγ₂_10 : γ₂ 1 0 = r := by dsimp only [γ₂]; rw [γ₁.coe_mul_S]; simp [hγ₁_11]
  have hγ₂_11 : γ₂ 1 1 = -c := by dsimp only [γ₂]; rw [γ₁.coe_mul_S]; simp [hγ₁_10]
  refine ⟨hγ₂_10 ▸ hr_pos, hγ₂_10 ▸ hr_lt, fun hIH ↦ ?_⟩
  -- Combine `γ = γ₁ * T ^ q` and `γ₂ = γ₁ * S` with `euclidean_step_exp`.
  have hdet₁ : γ 0 0 * r - γ₁ 0 1 * c = 1 := by
    simpa only [hγ₁_00, hγ₁_10, hγ₁_11] using γ₁.fin_two_mul_sub_mul_eq_one
  have hT : etaMultiplier γ = cexp (π * I * q / 12) * etaMultiplier γ₁ := by
    simpa [γ₁, mul_assoc] using etaMultiplier_mul_T_zpow γ₁ q
  have hγ₁_eq : etaMultiplier γ₁ = cexp (π * I / 4) * etaMultiplier γ₂ := by
    dsimp only [γ₂]
    rw [etaMultiplier_mul_S γ₁ (hγ₁_11 ▸ hr_pos), ← mul_assoc, ← Complex.exp_add]
    simp
  rw [hT, hγ₁_eq, hIH, hγ₂_00, hγ₂_10, hγ₂_11, ← Complex.exp_add, ← Complex.exp_add]
  have hexpC :=
    congrArg (fun x : ℚ ↦ π * I * (x : ℂ)) (euclidean_step_exp hc_pos hr_pos hdiv hdet₁)
  push_cast at hexpC
  congr 1
  push_cast
  linear_combination hexpC

/-- **Dedekind's functional equation for the eta multiplier** (Apostol, Theorem 3.4):
for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0`,
$$\varepsilon(\gamma) =
  \exp\!\left(\pi i \left(\frac{a + d}{12 c} - s(d, c) - \frac{1}{4}\right)\right),$$
where `ε(γ) = etaMultiplier γ` is normalized with respect to the principal square root
`Complex.sqrt ((c : ℂ) * τ + d)` in `eta_smul` (accounting for the `-1/4` shift relative to
Apostol's `√(-i (c τ + d))` convention). -/
theorem etaMultiplier_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) := by
  -- Strong induction on `n = (γ 1 0).toNat`: base case `c = 1`, step `1 < c` via
  -- `etaMultiplier_euclidean_step`.
  suffices hmain : ∀ n : ℕ, 0 < n → ∀ γ : SL(2, ℤ), γ 1 0 = n →
      etaMultiplier γ =
        cexp (π * I *
          (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) by
    exact hmain (γ 1 0).toNat (by omega) γ (Int.toNat_of_nonneg hc.le).symm
  intro n
  refine Nat.strongRecOn n fun n ih hn γ hc ↦ ?_
  by_cases hn1 : n = 1
  · subst hn1
    rw [etaMultiplier_of_c_eq_one γ (by simpa using hc)]
    simp [hc]
  · obtain ⟨hr_pos, hr_lt, hstep⟩ := etaMultiplier_euclidean_step γ (by omega)
    exact hstep (ih _ (by omega) (by omega) _ (Int.toNat_of_nonneg hr_pos.le).symm)

/-- Explicit fractional-part form of `etaMultiplier_of_c_pos`: for `γ = (a b; c d) ∈ SL(2, ℤ)`
with `c > 0`, `s(d, c)` expands to the unguarded fractional-part sum over `Finset.Ioo 0 c`. -/
theorem etaMultiplier_eq_exp_sum_fract_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    etaMultiplier γ =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
          (∑ r ∈ Finset.Ioo 0 (γ 1 0),
            ((r : ℂ) / γ 1 0) * (((Int.fract ((γ 1 1 * r : ℝ) / γ 1 0) : ℝ) : ℂ) - 1 / 2)) -
          1 / 4)) := by
  have hsum : ((dedekindSum (γ 1 1) (γ 1 0) : ℚ) : ℂ) =
      ∑ r ∈ Finset.Ioo 0 (γ 1 0),
        ((r : ℂ) / γ 1 0) * (((Int.fract ((γ 1 1 * r : ℝ) / γ 1 0) : ℝ) : ℂ) - 1 / 2) := by
    rw [(γ.isCoprime_row 1).symm.dedekindSum_eq]
    push_cast
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hfract : ((Int.fract ((γ 1 1 * r : ℚ) / γ 1 0) : ℚ) : ℝ) =
        Int.fract ((γ 1 1 * r : ℝ) / γ 1 0) := by
      simp
    rw [← Complex.ofReal_ratCast (Int.fract _), hfract]
  rw [etaMultiplier_of_c_pos γ hc, hsum]

/-- **Dedekind's functional equation for `η`** (Apostol, Theorem 3.4):
for `γ = (a b; c d) ∈ SL(2, ℤ)` with `c > 0` and `τ ∈ ℍ`,
$$\eta(\gamma \cdot \tau) =
  \exp\!\left(\pi i \left(\frac{a + d}{12 c} - s(d, c) - \frac{1}{4}\right)\right)
  \sqrt{c \tau + d}\,\eta(\tau),$$
where `√(c τ + d)` is the principal square root `Complex.sqrt ((c : ℂ) * τ + d)` (so `-1/4`
converts from Apostol's `√(-i (c τ + d))` normalization via `Complex.sqrt_neg_I_mul`). -/
theorem eta_smul_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (τ : ℍ) :
    η (γ • τ : ℍ) =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) - dedekindSum (γ 1 1) (γ 1 0) - 1 / 4)) *
      Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η τ := by
  rw [eta_smul, etaMultiplier_of_c_pos γ hc]

/-! ### Formulas for `c < 0` and arbitrary `c ≠ 0` -/

/-- Explicit eta multiplier when `c < 0` (normalized with respect to the principal square root
`Complex.sqrt ((c : ℂ) * τ + d)`):
`ε(γ) = exp(π i ((a + d) / (12 c) + s(d, -c) + 1/4))`. -/
theorem etaMultiplier_of_c_neg (γ : SL(2, ℤ)) (hc : γ 1 0 < 0) :
    etaMultiplier γ =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) + dedekindSum (γ 1 1) (-γ 1 0) + 1 / 4)) := by
  have hc' : 0 < (-γ) 1 0 := by
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Left.neg_pos_iff]
    exact hc
  have hneg := etaMultiplier_neg_of_c_pos (-γ) hc'
  rw [neg_neg, ← exp_pi_div_two_mul_I] at hneg
  rw [hneg, etaMultiplier_of_c_pos (-γ) hc', ← Complex.exp_add]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, dedekindSum_neg]
  have hcC : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc.ne
  congr 1
  push_cast
  field_simp
  ring

/-- **Rademacher's sign-unified formula** for the eta multiplier when `c ≠ 0` (Rademacher–Grosswald,
Ch. 4):
$$\varepsilon(\gamma) =
  \exp\!\left(\pi i \left(\frac{a + d}{12 c}
    - \operatorname{sgn}(c)\left(s(d, |c|) + \frac{1}{4}\right)\right)\right),$$
normalized with respect to the principal square root `Complex.sqrt ((c : ℂ) * τ + d)` in
`eta_smul` (so `-sgn(c) / 4` converts from Rademacher–Grosswald's `√((c τ + d) / (i sgn c))`
branch convention). -/
theorem etaMultiplier_of_c_ne_zero (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) :
    etaMultiplier γ =
      cexp (π * I *
        (((γ 0 0 : ℂ) + γ 1 1) / (12 * γ 1 0) -
          (γ 1 0).sign * (dedekindSum (γ 1 1) (γ 1 0).natAbs + 1 / 4))) := by
  rcases lt_or_gt_of_ne hc with hlt | hgt
  · rw [etaMultiplier_of_c_neg γ hlt, Int.sign_eq_neg_one_of_neg hlt,
      Int.natCast_natAbs, abs_of_neg hlt]
    congr 1
    push_cast
    ring
  · rw [etaMultiplier_of_c_pos γ hgt, Int.sign_eq_one_of_pos hgt,
      Int.natCast_natAbs, abs_of_pos hgt]
    congr 1
    push_cast
    ring

end TauCeti.ModularForm
