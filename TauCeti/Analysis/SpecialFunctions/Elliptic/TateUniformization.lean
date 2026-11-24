/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Coordinates
public import TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Gamma1.Moduli
import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
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

The same identities, read as a change of variables, identify the curves themselves. The complex
Tate curve `E_q : y² + x y = x³ - 5 s₃(q) x - (5 s₃(q) + 7 s₅(q)) / 12`
(`TauCeti.complexTateCurve`), whose coefficients for `‖q‖ < 1` are the sums at `q` of those of the
Tate curve over `ℤ⟦q⟧`, is obtained from the Weierstrass model `y² = x³ - (g₂ / 4) x - g₃ / 4` of
`ℂ / (ℤ z + ℤ)` by the change of variables `(u, r, s, t) = (2π i, (2π i)² / 12, π i, 0)`
(`TauCeti.complexTateVariableChange`); its discriminant is the modular discriminant `Δ(z)`.
Composing the exponential isomorphism `ℂ / (ℤ z + ℤ) ≃ ℂˣ / q^ℤ`
(`UpperHalfPlane.latticeQuotientEquivZPowers`), the `℘`-uniformisation
`ℂ / (ℤ z + ℤ) ≃ E_z(ℂ)` (`PeriodPair.weierstrassPointEquiv`) and this change of variables gives
the complex Tate uniformisation `ℂˣ / q^ℤ ≃ E_q(ℂ)`, a group isomorphism which sends the class of
every `t ∉ q^ℤ` to the point `(X(t), Y(t))`. Under it the root of unity `e^(2π i / N)` corresponds
to the point `1 / N` of `E_z`, so the canonical `μ_N ⊂ ℂˣ` of the Tate curve corresponds to the
level structure of `UpperHalfPlane.pointedWeierstrassCurve`.

## Main definitions

* `TauCeti.complexTateCurve`: the Tate curve `y² + x y = x³ + a₄(q) x + a₆(q)` at `q ∈ ℂ`.
* `TauCeti.complexTateVariableChange`: the change of variables from `E_z` to the Tate curve.
* `UpperHalfPlane.complexTateUniformization`: the complex Tate uniformisation
  `ℂˣ / q^ℤ ≃ E_q(ℂ)`.

## Main results

* `UpperHalfPlane.tateUniformizationX_eq_weierstrassP`:
  `X(t) = (2π i)⁻² ℘(x; ℤ z + ℤ) - 1 / 12`.
* `UpperHalfPlane.two_mul_tateUniformizationY_add_tateUniformizationX_eq_derivWeierstrassP`:
  `2 Y(t) + X(t) = (2π i)⁻³ ℘'(x; ℤ z + ℤ)`.
* `UpperHalfPlane.tateUniformizationY_eq_derivWeierstrassP_sub_weierstrassP`: the same identity
  solved for `Y(t)`.
* `TauCeti.tateUniformizationY_sq_add_mul_eq_of_notMem_zpowers`: over `ℂ`, the Tate coordinates
  satisfy the Tate equation at every `t ∉ q^ℤ`.
* `TauCeti.hasSum_coeff_tateCurve_a₄`, `TauCeti.hasSum_coeff_tateCurve_a₆`: the coefficients of
  the complex Tate curve are the sums at `q` of those of the Tate curve over `ℤ⟦q⟧`.
* `UpperHalfPlane.complexTateVariableChange_smul_weierstrassCurve`: the complex Tate curve at
  `q = e^(2π i z)` is a change of variables of the Weierstrass curve of `ℤ z + ℤ`.
* `UpperHalfPlane.complexTateCurve_Δ`: its discriminant is `Δ(z)`.
* `UpperHalfPlane.complexTateUniformization_mk_of_notMem_zpowers`: the complex Tate uniformisation
  sends the class of `t ∉ q^ℤ` to `(X(t), Y(t))`.
* `UpperHalfPlane.complexTateVariableChange_smul_pointedWeierstrassCurve`: the change of variables
  carries `E_z` with the point `1 / N` to the Tate curve with the image of `e^(2π i / N)`.

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
    Complex.exp_sub, Complex.exp_intCast_mul, ← hq, ← ht, zpow_neg, div_eq_inv_mul]

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

/-! ### The complex Tate curve as a Weierstrass curve -/

namespace TauCeti

/-- The **complex Tate curve** `y² + x y = x³ - 5 s₃(q) x - (5 s₃(q) + 7 s₅(q)) / 12` at a parameter
`q ∈ ℂ`, where `s_k(q) = ∑_{n ≥ 1} σ_k(n) qⁿ` (`TauCeti.divisorSumAt`). For `‖q‖ < 1` its
coefficients are the sums at `q` of those of the Tate curve over `ℤ⟦q⟧`
(`TauCeti.hasSum_coeff_tateCurve_a₄`, `TauCeti.hasSum_coeff_tateCurve_a₆`). -/
def complexTateCurve (q : ℂ) : WeierstrassCurve ℂ where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := -5 * divisorSumAt 3 q
  a₆ := -(5 * divisorSumAt 3 q + 7 * divisorSumAt 5 q) / 12

@[simp] lemma complexTateCurve_a₁ (q : ℂ) : (complexTateCurve q).a₁ = 1 := (rfl)
@[simp] lemma complexTateCurve_a₂ (q : ℂ) : (complexTateCurve q).a₂ = 0 := (rfl)
@[simp] lemma complexTateCurve_a₃ (q : ℂ) : (complexTateCurve q).a₃ = 0 := (rfl)

@[simp] lemma complexTateCurve_a₄ (q : ℂ) :
    (complexTateCurve q).a₄ = -5 * divisorSumAt 3 q := (rfl)

@[simp] lemma complexTateCurve_a₆ (q : ℂ) :
    (complexTateCurve q).a₆ = -(5 * divisorSumAt 3 q + 7 * divisorSumAt 5 q) / 12 := (rfl)

/-- For `‖q‖ < 1`, the coefficient `a₄` of the complex Tate curve is the sum at `q` of the
coefficient `a₄ ∈ ℤ⟦q⟧` of the Tate curve. -/
theorem hasSum_coeff_tateCurve_a₄ {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ ((PowerSeries.coeff n tateCurve.a₄ : ℤ) : ℂ) * q ^ n)
      (complexTateCurve q).a₄ := by
  rw [complexTateCurve_a₄, divisorSumAt_def]
  refine ((summable_divisorSumSeries 3 hq).hasSum.mul_left (-5)).congr_fun fun n ↦ ?_
  simp only [coeff_tateCurve_a₄, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast]
  ring

/-- For `‖q‖ < 1`, the coefficient `a₆` of the complex Tate curve is the sum at `q` of the
coefficient `a₆ ∈ ℤ⟦q⟧` of the Tate curve, whose coefficients are the integers
`-(5 σ₃(n) + 7 σ₅(n)) / 12`. -/
theorem hasSum_coeff_tateCurve_a₆ {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ ((PowerSeries.coeff n tateCurve.a₆ : ℤ) : ℂ) * q ^ n)
      (complexTateCurve q).a₆ := by
  rw [complexTateCurve_a₆, divisorSumAt_def, divisorSumAt_def]
  refine ((((summable_divisorSumSeries 3 hq).hasSum.mul_left 5).add
    ((summable_divisorSumSeries 5 hq).hasSum.mul_left 7)).neg.div_const 12).congr_fun fun n ↦ ?_
  have h : (12 : ℂ) * ((PowerSeries.coeff n tateCurve.a₆ : ℤ) : ℂ) = -(5 * σ 3 n + 7 * σ 5 n) := by
    exact_mod_cast twelve_mul_coeff_tateCurve_a₆ n
  simp only [Int.cast_natCast]
  linear_combination (q ^ n / 12) * h

/-- The change of variables `(u, r, s, t) = (2π i, (2π i)² / 12, π i, 0)`, which carries the
Weierstrass model `y² = x³ - (g₂ / 4) x - g₃ / 4` of `ℂ / (ℤ z + ℤ)` to the complex Tate curve at
`q = e^(2π i z)` (`UpperHalfPlane.complexTateVariableChange_smul_weierstrassCurve`): in Tate
coordinates `(X, Y)`, the Weierstrass coordinates are `x = (2π i)² (X + 1 / 12)` and
`y = (2π i)³ (2 Y + X) / 2`. -/
def complexTateVariableChange : WeierstrassCurve.VariableChange ℂ where
  u := Units.mk0 (2 * π * Complex.I) two_pi_I_ne_zero
  r := (2 * π * Complex.I) ^ 2 / 12
  s := π * Complex.I
  t := 0

@[simp] lemma coe_complexTateVariableChange_u :
    (complexTateVariableChange.u : ℂ) = 2 * π * Complex.I := (rfl)

@[simp] lemma complexTateVariableChange_r :
    complexTateVariableChange.r = (2 * π * Complex.I) ^ 2 / 12 := (rfl)

@[simp] lemma complexTateVariableChange_s : complexTateVariableChange.s = π * Complex.I := (rfl)

@[simp] lemma complexTateVariableChange_t : complexTateVariableChange.t = 0 := (rfl)

end TauCeti

namespace UpperHalfPlane

open TauCeti WeierstrassCurve

/-- **The complex Tate curve is the Weierstrass curve of `ℤ z + ℤ`.** For `z ∈ ℍ` and
`q = e^(2π i z)`, the change of variables `TauCeti.complexTateVariableChange` carries the curve
`y² = x³ - (g₂ / 4) x - g₃ / 4` of the lattice `ℤ z + ℤ` to the Tate curve
`y² + x y = x³ - 5 s₃(q) x - (5 s₃(q) + 7 s₅(q)) / 12`. -/
theorem complexTateVariableChange_smul_weierstrassCurve (z : ℍ) {q : ℂ}
    (hq : q = cexp (2 * π * Complex.I * z)) :
    complexTateVariableChange • z.periodPair.weierstrassCurve = complexTateCurve q := by
  have hE₄ := ModularForm.E₄_apply_eq_divisorSumAt z
  have hE₆ := ModularForm.E₆_apply_eq_divisorSumAt z
  rw [← hq] at hE₄ hE₆
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI₆ : Complex.I ^ 6 = -1 := by norm_num [pow_succ]
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, Units.val_inv_eq_inv_val, coe_complexTateVariableChange_u,
    complexTateVariableChange_r, complexTateVariableChange_s, complexTateVariableChange_t,
    PeriodPair.weierstrassCurve_a₁,
    PeriodPair.weierstrassCurve_a₂, PeriodPair.weierstrassCurve_a₃,
    PeriodPair.weierstrassCurve_a₄, PeriodPair.weierstrassCurve_a₆, g₂_periodPair, g₃_periodPair,
    complexTateCurve_a₁, complexTateCurve_a₂, complexTateCurve_a₃, complexTateCurve_a₄,
    complexTateCurve_a₆, hE₄, hE₆]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp only [I_sq, I_pow_four, hI₆]
  all_goals ring

/-- The discriminant of the complex Tate curve at `q = e^(2π i z)` is the modular discriminant
`Δ(z) = q ∏ (1 - qⁿ)²⁴`. -/
theorem complexTateCurve_Δ (z : ℍ) {q : ℂ} (hq : q = cexp (2 * π * Complex.I * z)) :
    (complexTateCurve q).Δ = ModularForm.discriminant z := by
  rw [← complexTateVariableChange_smul_weierstrassCurve z hq, variableChange_Δ,
    weierstrassCurve_Δ_periodPair]
  rw [Units.val_inv_eq_inv_val, coe_complexTateVariableChange_u]
  have hI : Complex.I ^ 12 = 1 := by norm_num [pow_succ]
  have hπ : (2 * π : ℂ) ^ 12 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero
    (by exact_mod_cast Real.pi_ne_zero))
  rw [inv_pow, mul_pow (2 * (π : ℂ)), hI, mul_one, inv_mul_cancel_left₀ hπ]

/-- **The complex Tate uniformisation** `ℂˣ / q^ℤ ≃ E_q(ℂ)` onto the points of the complex Tate
curve at `q = e^(2π i z)`, written additively on the source. It is the exponential uniformisation
`ℂ / (ℤ z + ℤ) ≃ ℂˣ / q^ℤ` followed by `℘`-uniformisation `ℂ / (ℤ z + ℤ) ≃ E_z(ℂ)` and the change
of variables `TauCeti.complexTateVariableChange`. Away from `q^ℤ` it is given by the Tate
coordinates (`UpperHalfPlane.complexTateUniformization_mk_of_notMem_zpowers`). -/
def complexTateUniformization (z : ℍ) {q : ℂˣ}
    (hq : (q : ℂ) = cexp (2 * π * Complex.I * z)) :
    Additive (ℂˣ ⧸ Subgroup.zpowers q) ≃+ (complexTateCurve q).toAffine.Point :=
  (latticeQuotientEquivZPowers z hq).symm.trans <| z.periodPair.weierstrassPointEquiv.trans <|
    (Affine.Point.addEquivVariableChange _ complexTateVariableChange).symm.trans <|
      AddEquiv.cast (M := fun V : WeierstrassCurve ℂ ↦ V.toAffine.Point)
        (complexTateVariableChange_smul_weierstrassCurve z hq)

/-- **The complex Tate uniformisation on pointed curves.** The change of variables
`TauCeti.complexTateVariableChange` carries `E_z` with the point of `x` to the complex Tate curve
with the image of `e^(2π i x)` under `UpperHalfPlane.complexTateUniformization`. -/
theorem complexTateVariableChange_smul_mk_weierstrassPoint (z : ℍ) {q : ℂˣ}
    (hq : (q : ℂ) = cexp (2 * π * Complex.I * z)) (x : ℂ) :
    complexTateVariableChange •
        (⟨z.periodPair.weierstrassCurve, z.periodPair.weierstrassPoint x⟩ :
          PointedWeierstrassCurve ℂ) =
      ⟨complexTateCurve q, complexTateUniformization z hq
        (.ofMul ↑(Units.mk0 (cexp (2 * π * Complex.I * x)) (Complex.exp_ne_zero _)))⟩ := by
  refine PointedWeierstrassCurve.ext_cast
    (complexTateVariableChange_smul_weierstrassCurve z hq) ?_
  rw [PointedWeierstrassCurve.smul_point, complexTateUniformization]
  simp only [AddEquiv.trans_apply, latticeQuotientEquivZPowers_symm_ofMul,
    PeriodPair.weierstrassPointEquiv_mk,
    Affine.Point.coe_addEquivVariableChange_symm, AddEquiv.cast_apply]

/-- **The canonical `μ_N` of the Tate curve is the level structure `1 / N` of `E_z`.** The change
of variables `TauCeti.complexTateVariableChange` carries `E_z` with the point of `1 / N` to the
complex Tate curve with the image of the root of unity `e^(2π i / N)`. -/
theorem complexTateVariableChange_smul_pointedWeierstrassCurve (N : ℕ) (z : ℍ) {q : ℂˣ}
    (hq : (q : ℂ) = cexp (2 * π * Complex.I * z)) :
    complexTateVariableChange • z.pointedWeierstrassCurve N =
      ⟨complexTateCurve q, complexTateUniformization z hq
        (.ofMul ↑(Units.mk0 (cexp (2 * π * Complex.I / N)) (Complex.exp_ne_zero _)))⟩ := by
  rw [pointedWeierstrassCurve_def, complexTateVariableChange_smul_mk_weierstrassPoint z hq]
  simp only [mul_one_div]

end UpperHalfPlane

namespace TauCeti

open WeierstrassCurve

/-- For `0 < ‖q‖ < 1` the complex Tate curve is an elliptic curve: it is a change of variables of
the Weierstrass curve of a lattice. -/
theorem isElliptic_complexTateCurve {q : ℂ} (hq₀ : q ≠ 0) (hq : ‖q‖ < 1) :
    (complexTateCurve q).IsElliptic := by
  obtain ⟨z, hz⟩ := UpperHalfPlane.exists_cexp_two_pi_I_mul_eq hq₀ hq
  rw [← _root_.UpperHalfPlane.complexTateVariableChange_smul_weierstrassCurve z hz.symm]
  infer_instance

/-- For units `q` and `t` of `ℂ` with `‖q‖ < 1` and `t ∉ q^ℤ`, the Tate coordinates
`(X(t), Y(t))` are a nonsingular point of the complex Tate curve. -/
theorem nonsingular_complexTateCurve (q t : ℂˣ) (hq : ‖(q : ℂ)‖ < 1)
    (ht : t ∉ Subgroup.zpowers q) :
    (complexTateCurve q).toAffine.Nonsingular (tateUniformizationX q t)
      (tateUniformizationY q t) := by
  have := isElliptic_complexTateCurve q.ne_zero hq
  rw [← Affine.equation_iff_nonsingular, Affine.equation_iff]
  simp only [complexTateCurve_a₁, complexTateCurve_a₂, complexTateCurve_a₃, complexTateCurve_a₄,
    complexTateCurve_a₆]
  linear_combination tateUniformizationY_sq_add_mul_eq_of_notMem_zpowers q t hq ht

end TauCeti

namespace UpperHalfPlane

open TauCeti WeierstrassCurve

/-- **The complex Tate uniformisation in Tate coordinates.** For `z ∈ ℍ`, `q = e^(2π i z)` and a
unit `t ∉ q^ℤ`, `UpperHalfPlane.complexTateUniformization` sends the class of `t` to the point
`(X(t), Y(t))` of the complex Tate curve given by the Tate coordinate series. -/
theorem complexTateUniformization_mk_of_notMem_zpowers (z : ℍ) {q : ℂˣ}
    (hq : (q : ℂ) = cexp (2 * π * Complex.I * z)) {t : ℂˣ} (ht : t ∉ Subgroup.zpowers q)
    (h : (complexTateCurve q).toAffine.Nonsingular (tateUniformizationX q t)
      (tateUniformizationY q t)) :
    complexTateUniformization z hq (.ofMul ↑t) = .some _ _ h := by
  set x := Function.Periodic.invQParam 1 (t : ℂ)
  have htx : (t : ℂ) = cexp (2 * π * Complex.I * x) := by
    simpa [Function.Periodic.qParam] using
      (Function.Periodic.qParam_right_inv one_ne_zero t.ne_zero).symm
  have hx : x ∉ z.periodPair.lattice :=
    (mem_zpowers_iff_mem_lattice_periodPair z hq htx).not.mp ht
  have hpt := complexTateVariableChange_smul_mk_weierstrassPoint z hq x
  have hxt : Units.mk0 (cexp (2 * π * Complex.I * x)) (Complex.exp_ne_zero _) = t :=
    Units.ext htx.symm
  rw [hxt, z.periodPair.weierstrassPoint_of_notMem hx] at hpt
  -- in Tate coordinates, `℘ = (2π i)² (X + 1 / 12)` and `℘' / 2 = (2π i)³ (2 Y + X) / 2`
  have hcoord := (PointedWeierstrassCurve.smul_mk_some_eq_mk_some_iff
    complexTateVariableChange (z.periodPair.nonsingular_weierstrassP hx) h).mpr
    ⟨complexTateVariableChange_smul_weierstrassCurve z hq, ?_, ?_⟩
  · exact PointedWeierstrassCurve.mk_inj.mp (hpt.symm.trans hcoord)
  · rw [coe_complexTateVariableChange_u, complexTateVariableChange_r,
      tateUniformizationX_eq_weierstrassP z hx hq htx]
    field_simp
    ring
  · rw [coe_complexTateVariableChange_u, complexTateVariableChange_s, complexTateVariableChange_t]
    have hY := two_mul_tateUniformizationY_add_tateUniformizationX_eq_derivWeierstrassP z hx hq htx
    rw [eq_div_iff (pow_ne_zero 3 two_pi_I_ne_zero)] at hY
    linear_combination hY / 2

end UpperHalfPlane
