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

The value for `c > 0`, `etaMultiplier_of_c_pos`, is proved in
`TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation` by induction on `c` along the
Euclidean algorithm, matched at the inversion step by Dedekind's reciprocity law
`TauCeti.dedekindSum_add_dedekindSum`; this file derives the other forms from it.

## Main results

* `TauCeti.ModularForm.etaMultiplier_eq_exp_sum_fract_of_c_pos`,
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
