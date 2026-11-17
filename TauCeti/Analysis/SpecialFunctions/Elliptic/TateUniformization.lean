/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Coordinates
import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
import TauCeti.Analysis.SpecialFunctions.Elliptic.Uniformization
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion

/-!
# The complex Tate curve

For `z` in the upper half-plane let `q = e^(2π i z)`, and for `x ∈ ℂ` let `t = e^(2π i x)`.
The map `x ↦ t` carries the lattice `ℤ z + ℤ` onto `q^ℤ`, and this file shows that in the
parameter `t` the Weierstrass coordinates of the lattice `ℤ z + ℤ` become the Tate coordinates
`X(t) = ∑_{n ∈ ℤ} qⁿt / (1 - qⁿt)² - 2 s₁(q)` and `Y(t) = ∑_{n ∈ ℤ} (qⁿt)² / (1 - qⁿt)³ + s₁(q)`
(`TauCeti.tateUniformizationX`, `TauCeti.tateUniformizationY`): for `x ∉ ℤ z + ℤ`,

`X(t) = (2π i)⁻² ℘(x; ℤ z + ℤ) - 1 / 12`  and  `2 Y(t) + X(t) = (2π i)⁻³ ℘'(x; ℤ z + ℤ)`.

The second identity says that the invariant differential `dX / (2Y + X)` of the Tate curve is
`dt / t = 2π i dx`. This is the bridge between the analytic theory of modular forms, whose
`q`-expansions are taken in `q = e^(2π i z)` against `dx`, and the Tate curve
`y² + x y = x³ + a₄(q) x + a₆(q)` over `ℤ⟦q⟧`, whose expansions are taken against `dt / t`.

Both identities are proved by summing the lattice series of `℘` and `℘'` along the rows
`m z + ℤ`. A row is `∑_n (w + n)⁻²` or `∑_n (w + n)⁻³` at `w = x - m z`, whose exponential form
in `e^(2π i w) = q⁻ᵐ t` (`TauCeti.UpperHalfPlane.rowSum_eq_cexp`,
`TauCeti.UpperHalfPlane.tsum_one_div_add_intCast_pow_three_eq_cexp`) is one term of the Tate
series. The rows of `℘` through the multiples `m z` are those of the series of `G₂`, which sum
to `2 ζ(2) - 8 π² s₁(q)` (Mathlib's `EisensteinSeries.hasSum_e2Summand_symmetricIcc`), and
`2 ζ(2) = π² / 3 = -(2π i)² / 12` produces the constant `-1 / 12`.

With `g₂ = (2π i)⁴ E₄ / 12`, `g₃ = -(2π i)⁶ E₆ / 216`, `E₄ = 1 + 240 s₃(q)` and
`E₆ = 1 - 504 s₅(q)`, the Weierstrass equation `℘'² = 4 ℘³ - g₂ ℘ - g₃` becomes the Tate equation
`Y² + X Y = X³ - 5 s₃(q) X - (5 s₃(q) + 7 s₅(q)) / 12`. Every unit `q` of `ℂ` with `‖q‖ < 1` is
`e^(2π i z)` for some `z ∈ ℍ` (`TauCeti.UpperHalfPlane.exists_cexp_two_pi_I_mul_eq`), and every
unit `t ∉ q^ℤ` is `e^(2π i x)` for some `x ∉ ℤ z + ℤ`
(`UpperHalfPlane.mem_zpowers_iff_mem_lattice_periodPair`),
so the Tate coordinates satisfy the Tate equation over `ℂ` at every `t ∉ q^ℤ`: the archimedean
counterpart of the non-archimedean equation
`TauCeti.equation_tateUniformizationX_tateUniformizationY_of_notMem_zpowers`.

## Main results

* `UpperHalfPlane.tateUniformizationX_eq_weierstrassP`:
  `X(t) = (2π i)⁻² ℘(x; ℤ z + ℤ) - 1 / 12`.
* `UpperHalfPlane.two_mul_tateUniformizationY_add_tateUniformizationX_eq_derivWeierstrassP`:
  `2 Y(t) + X(t) = (2π i)⁻³ ℘'(x; ℤ z + ℤ)`.
* `UpperHalfPlane.tateUniformizationY_eq_derivWeierstrassP_sub_weierstrassP`: the same identity
  solved for `Y(t)`.
* `TauCeti.tateUniformizationY_sq_add_mul_eq_of_notMem_zpowers`: over `ℂ`, the Tate coordinates
  satisfy the Tate equation at every `t ∉ q^ℤ`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Graduate Texts in
  Mathematics 151, Springer, 1994, Theorem V.1.1.
-/

public section

noncomputable section

open Complex PeriodPair
open scoped Real ArithmeticFunction.sigma

namespace UpperHalfPlane

open TauCeti TauCeti.UpperHalfPlane

/-- `(2π i)² = -4π²`. -/
private lemma two_pi_I_sq : (2 * π * Complex.I) ^ 2 = -(4 * π ^ 2) := by
  rw [mul_pow, Complex.I_sq]
  ring

/-- With `q = e^(2π i z)` and `t = e^(2π i x)`, the parameter of `x - m z` is `q⁻ᵐ t`. -/
private lemma cexp_sub_intCast_mul (z : ℍ) {x : ℂ} {q t : ℂˣ}
    (hq : (q : ℂ) = cexp (2 * π * Complex.I * z)) (ht : (t : ℂ) = cexp (2 * π * Complex.I * x))
    (m : ℤ) : cexp (2 * π * Complex.I * (x - m * z)) = (q : ℂ) ^ (-m) * t := by
  rw [show 2 * π * Complex.I * (x - m * z) =
      2 * π * Complex.I * x - m * (2 * π * Complex.I * z) by ring,
    Complex.exp_sub, Complex.exp_int_mul, ← hq, ← ht, zpow_neg, div_eq_inv_mul]

/-- **The complex Tate uniformisation, first coordinate.** For `z ∈ ℍ`, `q = e^(2π i z)`, a point
`x ∉ ℤ z + ℤ` and its multiplicative parameter `t = e^(2π i x)`, the first Tate coordinate is
`X(t) = (2π i)⁻² ℘(x; ℤ z + ℤ) - 1 / 12`. -/
theorem tateUniformizationX_eq_weierstrassP (z : ℍ) {x : ℂ}
    (hx : x ∉ z.periodPair.lattice) {q t : ℂˣ} (hq : (q : ℂ) = cexp (2 * π * Complex.I * z))
    (ht : (t : ℂ) = cexp (2 * π * Complex.I * x)) :
    tateUniformizationX q t = ℘[z.periodPair] x / (2 * π * Complex.I) ^ 2 - 1 / 12 := by
  have hq₁ : ‖(q : ℂ)‖ < 1 := hq ▸ norm_exp_two_pi_I_lt_one z
  set S := ∑' n : ℤ, (q : ℂ) ^ n * t / (1 - (q : ℂ) ^ n * t) ^ 2
  -- the rows through `x` sum to `(2π i)² S`
  have hS : HasSum (fun m : ℤ ↦ rowSum (x - m * z)) ((2 * π * Complex.I) ^ 2 * S) := by
    have h := (summable_tateUniformizationX q hq₁ t).hasSum.mul_left ((2 * π * Complex.I) ^ 2)
    rw [← (Equiv.neg ℤ).hasSum_iff] at h
    refine h.congr_fun fun m ↦ ?_
    simp only [Function.comp_apply, Equiv.neg_apply]
    rw [rowSum_eq_cexp (sub_intCast_mul_mem_integerComplement z hx m),
      cexp_sub_intCast_mul z hq ht]
  -- the rows through the multiples of `z` are those of the series of `G₂`, which Mathlib sums
  -- symmetrically to `2 ζ(2) - 8 π² s₁(q)`
  have hG : HasSum (fun m : ℤ ↦ rowSum (m * z)) ((2 * π * Complex.I) ^ 2 * S - ℘[z.periodPair] x)
      (SummationFilter.symmetricIcc ℤ) :=
    ((hS.sub (hasSum_weierstrassP_periodPair_rows z x)).congr_fun fun m ↦
      (sub_sub_cancel _ _).symm).mono_left SummationFilter.le_atTop
  have h℘ := hG.unique ((EisensteinSeries.hasSum_e2Summand_symmetricIcc z).congr_fun fun m ↦ by
    simp [rowSum_def, EisensteinSeries.e2Summand, EisensteinSeries.eisSummand])
  rw [← hq, ← divisorSumAt_eq_tsum_pnat] at h℘
  -- `2 ζ(2) = π² / 3 = -(2π i)² / 12`
  rw [riemannZeta_two, two_pi_I_sq] at h℘
  have hπ : (4 * π ^ 2 : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero))
  rw [tateUniformizationX_def, two_pi_I_sq, show ℘[z.periodPair] x =
    -(4 * π ^ 2) * (S - 2 * divisorSumAt 1 (q : ℂ) + 1 / 12) by linear_combination -h℘,
    mul_div_cancel_left₀ _ (neg_ne_zero.mpr hπ)]
  ring

/-- **The complex Tate uniformisation, second coordinate.** For `z ∈ ℍ`, `q = e^(2π i z)`, a point
`x ∉ ℤ z + ℤ` and its multiplicative parameter `t = e^(2π i x)`, the Tate coordinates satisfy
`2 Y(t) + X(t) = (2π i)⁻³ ℘'(x; ℤ z + ℤ)`. Together with
`UpperHalfPlane.tateUniformizationX_eq_weierstrassP` this says that the invariant
differential `dX / (2Y + X)` of the Tate curve corresponds to `dt / t = 2π i dx`. -/
theorem two_mul_tateUniformizationY_add_tateUniformizationX_eq_derivWeierstrassP (z : ℍ) {x : ℂ}
    (hx : x ∉ z.periodPair.lattice) {q t : ℂˣ}
    (hq : (q : ℂ) = cexp (2 * π * Complex.I * z)) (ht : (t : ℂ) = cexp (2 * π * Complex.I * x)) :
    2 * tateUniformizationY q t + tateUniformizationX q t =
      ℘'[z.periodPair] x / (2 * π * Complex.I) ^ 3 := by
  have hq₁ : ‖(q : ℂ)‖ < 1 := hq ▸ norm_exp_two_pi_I_lt_one z
  set Sx := ∑' n : ℤ, (q : ℂ) ^ n * t / (1 - (q : ℂ) ^ n * t) ^ 2
  set Sy := ∑' n : ℤ, ((q : ℂ) ^ n * t) ^ 2 / (1 - (q : ℂ) ^ n * t) ^ 3
  -- the rows of `℘'` sum to `(2π i)³ (2 Sy + Sx)`
  have hrows : HasSum (fun m : ℤ ↦ -2 * ∑' n : ℤ, 1 / (x - m * z + n) ^ 3)
      ((2 * π * Complex.I) ^ 3 * (2 * Sy + Sx)) := by
    have h := (((summable_tateUniformizationY q hq₁ t).hasSum.mul_left 2).add
      (summable_tateUniformizationX q hq₁ t).hasSum).mul_left ((2 * π * Complex.I) ^ 3)
    rw [← (Equiv.neg ℤ).hasSum_iff] at h
    refine h.congr_fun fun m ↦ ?_
    simp only [Function.comp_apply, Equiv.neg_apply]
    rw [tsum_one_div_add_intCast_pow_three_eq_cexp
      (sub_intCast_mul_mem_integerComplement z hx m), cexp_sub_intCast_mul z hq ht]
    -- `e (1 + e) / (1 - e)³ = 2 e² / (1 - e)³ + e / (1 - e)²`
    set e := (q : ℂ) ^ (-m) * t
    rcases eq_or_ne e 1 with he | he
    · simp [he]
    · have h₁ : 1 - e ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
      field_simp
      ring
  have h℘ := hrows.unique (hasSum_derivWeierstrassP_periodPair_rows z x)
  rw [tateUniformizationY_def, tateUniformizationX_def, ← h℘,
    mul_div_cancel_left₀ _ (pow_ne_zero 3 two_pi_I_ne_zero)]
  ring

/-- **The complex Tate uniformisation, second coordinate solved for `Y`.** For `z ∈ ℍ`,
`q = e^(2π i z)`, a point `x ∉ ℤ z + ℤ` and its multiplicative parameter `t = e^(2π i x)`,
`Y(t) = ((2π i)⁻³ ℘'(x; ℤ z + ℤ) - (2π i)⁻² ℘(x; ℤ z + ℤ) + 1 / 12) / 2`. -/
theorem tateUniformizationY_eq_derivWeierstrassP_sub_weierstrassP (z : ℍ) {x : ℂ}
    (hx : x ∉ z.periodPair.lattice) {q t : ℂˣ}
    (hq : (q : ℂ) = cexp (2 * π * Complex.I * z)) (ht : (t : ℂ) = cexp (2 * π * Complex.I * x)) :
    tateUniformizationY q t = (℘'[z.periodPair] x / (2 * π * Complex.I) ^ 3 -
      ℘[z.periodPair] x / (2 * π * Complex.I) ^ 2 + 1 / 12) / 2 := by
  rw [← two_mul_tateUniformizationY_add_tateUniformizationX_eq_derivWeierstrassP z hx hq ht,
    tateUniformizationX_eq_weierstrassP z hx hq ht]
  ring

end UpperHalfPlane

namespace TauCeti

open _root_.UpperHalfPlane

/-- **The Tate equation over `ℂ`.** For units `q` and `t` of `ℂ` with `‖q‖ < 1` and `t ∉ q^ℤ`,
the Tate coordinates satisfy `Y² + X Y = X³ - 5 s₃(q) X - (5 s₃(q) + 7 s₅(q)) / 12`. Its
coefficients are those of the Tate curve over `ℤ⟦q⟧`, `a₄ = -5 s₃` and `12 a₆ = -(5 s₃ + 7 s₅)`
(`TauCeti.tateCurve_a₄`, `TauCeti.twelve_mul_tateCurve_a₆`), summed at `q`. -/
theorem tateUniformizationY_sq_add_mul_eq_of_notMem_zpowers (q t : ℂˣ) (hq : ‖(q : ℂ)‖ < 1)
    (ht : t ∉ Subgroup.zpowers q) :
    tateUniformizationY q t ^ 2 + tateUniformizationX q t * tateUniformizationY q t =
      tateUniformizationX q t ^ 3 - 5 * divisorSumAt 3 (q : ℂ) * tateUniformizationX q t -
        (5 * divisorSumAt 3 (q : ℂ) + 7 * divisorSumAt 5 (q : ℂ)) / 12 := by
  obtain ⟨z, hqz⟩ := TauCeti.UpperHalfPlane.exists_cexp_two_pi_I_mul_eq q.ne_zero hq
  rw [eq_comm] at hqz
  set x := Function.Periodic.invQParam 1 t
  have htx : (t : ℂ) = cexp (2 * π * Complex.I * x) := by
    simpa [Function.Periodic.qParam] using
      (Function.Periodic.qParam_right_inv one_ne_zero t.ne_zero).symm
  have hx : x ∉ z.periodPair.lattice :=
    (mem_zpowers_iff_mem_lattice_periodPair z hqz htx).not.mp ht
  have hX := tateUniformizationX_eq_weierstrassP z hx hqz htx
  have hY := two_mul_tateUniformizationY_add_tateUniformizationX_eq_derivWeierstrassP z hx hqz htx
  have hE₄ := ModularForm.E₄_apply_eq_divisorSumAt z
  have hE₆ := ModularForm.E₆_apply_eq_divisorSumAt z
  rw [← hqz] at hE₄ hE₆
  have h := z.periodPair.derivWeierstrassP_sq x hx
  rw [g₂_periodPair, g₃_periodPair, hE₄, hE₆] at h
  set X := tateUniformizationX q t
  set Y := tateUniformizationY q t
  -- substitute `℘ = (2π i)² (X + 1 / 12)` and `℘' = (2π i)³ (2Y + X)`, with `(2π i)² = -4π²`
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h℘ : ℘[z.periodPair] x = -(4 * π ^ 2) * (X + 1 / 12) := by
    rw [hX, ← two_pi_I_sq]
    field_simp
    ring
  have h℘' : ℘'[z.periodPair] x ^ 2 = -(64 * π ^ 6) * (2 * Y + X) ^ 2 := by
    have h6 : (2 * π * Complex.I) ^ (3 * 2) = -(64 * π ^ 6) := by
      rw [mul_comm 3 2, pow_mul, two_pi_I_sq]
      ring
    rw [hY, div_pow, ← pow_mul, h6]
    field_simp
  rw [h℘, h℘'] at h
  have key : (256 * π ^ 6 : ℂ) * (Y ^ 2 + X * Y - (X ^ 3 - 5 * divisorSumAt 3 (q : ℂ) * X -
      (5 * divisorSumAt 3 (q : ℂ) + 7 * divisorSumAt 5 (q : ℂ)) / 12)) = 0 := by
    linear_combination (-1 : ℂ) * h
  rw [← sub_eq_zero]
  exact (mul_eq_zero.mp key).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero _ hπ))

end TauCeti
