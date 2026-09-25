/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Congruence
public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Series

/-!
# The Tate curve over `ℤ⟦q⟧`

The Tate curve is the Weierstrass equation

`E_q : y² + xy = x³ + a₄(q) x + a₆(q)`,  `a₄(q) = -5 s₃(q)`,  `a₆(q) = -(5 s₃(q) + 7 s₅(q)) / 12`,

where `s_k(q) = ∑_{n ≥ 1} nᵏ qⁿ / (1 - qⁿ) = ∑_{n ≥ 1} σ_k(n) qⁿ`. This file defines it as a
Weierstrass curve over the formal power series ring `ℤ⟦q⟧`. The division by `12` in `a₆` is
carried out on coefficients, using `12 ∣ 5 σ₃(n) + 7 σ₅(n)`, so no denominator is ever
introduced: the curve is defined over `ℤ⟦q⟧`, and by `WeierstrassCurve.map` over `R⟦q⟧` for
every commutative ring `R`, residue characteristics `2` and `3` included. Over a complete
non-archimedean field `K` and `q ∈ Kˣ` with `|q| < 1` the series converge, and specialising gives
the curve whose points are `Kˣ / qᶻ`; this file contains the formal half of that story.

The formal invariants are those of the Tate curve as an elliptic curve over the Laurent series
`ℤ⸨q⸩`: `c₄ = 1 + 240 s₃` and `c₆ = -1 + 504 s₅`, the discriminant is `q` times a unit of
`ℤ⟦q⟧`, so that the curve is elliptic over `ℤ⸨q⸩`, and its `j`-invariant is
`1 / q + 744 + ⋯` with integral coefficients.

## Main definitions

* `TauCeti.divisorSumSeries k`: the series `s_k(q) = ∑_{n ≥ 1} σ_k(n) qⁿ` in `ℤ⟦q⟧`.
* `TauCeti.tateCurve`: the Tate curve, a Weierstrass curve over `ℤ⟦q⟧`.

## Main results

* `TauCeti.tateCurve_a₄` and `TauCeti.twelve_mul_tateCurve_a₆`: `a₄ = -5 s₃` and
  `12 a₆ = -(5 s₃ + 7 s₅)`, which determine the coefficients since `ℤ⟦q⟧` is torsion-free.
* `TauCeti.constantCoeff_tateCurve_a₄` and `TauCeti.constantCoeff_tateCurve_a₆`: at `q = 0` the
  Tate curve is the nodal cubic `y² + xy = x³`.
* `TauCeti.tateCurve_c₄` and `TauCeti.tateCurve_c₆`: `c₄ = 1 + 240 s₃` and `c₆ = -1 + 504 s₅`.
* `TauCeti.order_tateCurve_Δ` and `TauCeti.exists_tateCurve_Δ_eq_X_mul`: `Δ = q · u` with `u` a
  power series of constant coefficient `1`, and `Δ = q - 24 q² + ⋯`.
* `TauCeti.exists_tateCurve_j_eq`: over `ℤ⸨q⸩` the Tate curve is elliptic and
  `j = q⁻¹ · J(q)` with `J ∈ ℤ⟦q⟧` and `J = 1 + 744 q + ⋯`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, §V.3.
* J. Tate, *A review of non-Archimedean elliptic functions*, in *Elliptic curves, modular forms,
  & Fermat's last theorem* (Hong Kong, 1993), International Press (1995), 162–184.
-/

public section

open PowerSeries ArithmeticFunction
open scoped ArithmeticFunction.sigma LaurentSeries

namespace TauCeti

/-- **The Tate curve** `y² + xy = x³ + a₄ x + a₆` over `ℤ⟦q⟧`, with `a₄ = -5 s₃` and
`a₆ = -(5 s₃ + 7 s₅) / 12`. The `n`-th coefficient of `a₆` is `-(5 σ₃(n) + 7 σ₅(n)) / 12`, an
integer by `twelve_dvd_five_mul_sigma_three_add_seven_mul_sigma_five`; use
`coeff_tateCurve_a₆` and `twelve_mul_tateCurve_a₆` rather than the definition. -/
noncomputable def tateCurve : WeierstrassCurve ℤ⟦X⟧ where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := PowerSeries.mk fun n ↦ -5 * σ 3 n
  a₆ := PowerSeries.mk fun n ↦ -(((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : ℤ)

@[simp] theorem tateCurve_a₁ : tateCurve.a₁ = 1 := (rfl)
@[simp] theorem tateCurve_a₂ : tateCurve.a₂ = 0 := (rfl)
@[simp] theorem tateCurve_a₃ : tateCurve.a₃ = 0 := (rfl)

@[simp]
theorem coeff_tateCurve_a₄ (n : ℕ) : coeff n tateCurve.a₄ = -5 * σ 3 n := by
  simp [tateCurve]

/-- The `n`-th coefficient of `a₆` is `-(5 σ₃(n) + 7 σ₅(n)) / 12`. -/
@[simp]
theorem coeff_tateCurve_a₆ (n : ℕ) :
    coeff n tateCurve.a₆ = -(((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : ℤ) := by
  simp [tateCurve]

/-- The coefficients of `a₆`: `12 · [qⁿ] a₆ = -(5 σ₃(n) + 7 σ₅(n))`. -/
theorem twelve_mul_coeff_tateCurve_a₆ (n : ℕ) :
    12 * coeff n tateCurve.a₆ = -(5 * σ 3 n + 7 * σ 5 n) := by
  have h : (12 : ℤ) * (((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : ℤ) = 5 * σ 3 n + 7 * σ 5 n := by
    exact_mod_cast Nat.mul_div_cancel' (twelve_dvd_five_mul_sigma_three_add_seven_mul_sigma_five n)
  simp only [tateCurve, coeff_mk]
  linear_combination -h

/-- `a₄ = -5 s₃`. -/
@[simp]
theorem tateCurve_a₄ : tateCurve.a₄ = -5 * divisorSumSeries 3 := by
  ext n
  rw [coeff_tateCurve_a₄, ← map_ofNat C 5, ← map_neg, coeff_C_mul, coeff_divisorSumSeries]

/-- `12 a₆ = -(5 s₃ + 7 s₅)`. -/
@[simp]
theorem twelve_mul_tateCurve_a₆ :
    12 * tateCurve.a₆ = -(5 * divisorSumSeries 3 + 7 * divisorSumSeries 5) := by
  ext n
  rw [← map_ofNat C 12, ← map_ofNat C 5, ← map_ofNat C 7]
  simp only [coeff_C_mul, map_neg, map_add, coeff_divisorSumSeries]
  exact twelve_mul_coeff_tateCurve_a₆ n

/-- `c₄ = 1 + 240 s₃`, the normalised Eisenstein series of weight `4`. -/
@[simp]
theorem tateCurve_c₄ : tateCurve.c₄ = 1 + 240 * divisorSumSeries 3 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, tateCurve_a₁,
    tateCurve_a₂, tateCurve_a₃, tateCurve_a₄]
  ring

/-- `c₆ = -1 + 504 s₅`, minus the normalised Eisenstein series of weight `6`. -/
@[simp]
theorem tateCurve_c₆ : tateCurve.c₆ = -1 + 504 * divisorSumSeries 5 := by
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    tateCurve_a₁, tateCurve_a₂, tateCurve_a₃, tateCurve_a₄]
  linear_combination (-72 : ℤ⟦X⟧) * twelve_mul_tateCurve_a₆

private theorem tateCurve_Δ_eq :
    tateCurve.Δ = tateCurve.a₄ ^ 2 - tateCurve.a₆ - 64 * tateCurve.a₄ ^ 3
      - 432 * tateCurve.a₆ ^ 2 + 72 * (tateCurve.a₄ * tateCurve.a₆) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, tateCurve_a₁, tateCurve_a₂, tateCurve_a₃]
  ring

private theorem coeff_tateCurve_a₆_one : coeff 1 tateCurve.a₆ = -1 := by
  rw [coeff_tateCurve_a₆]
  norm_num [sigma_apply, Nat.divisors_one]

private theorem coeff_tateCurve_a₆_two : coeff 2 tateCurve.a₆ = -23 := by
  rw [coeff_tateCurve_a₆]
  norm_num [sigma_apply, Nat.Prime.divisors Nat.prime_two]

/-- `a₄` vanishes at `q = 0`. -/
theorem constantCoeff_tateCurve_a₄ : constantCoeff tateCurve.a₄ = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_tateCurve_a₄]
  simp

/-- `a₆` vanishes at `q = 0`. -/
@[simp]
theorem constantCoeff_tateCurve_a₆ : constantCoeff tateCurve.a₆ = 0 := by
  have h := twelve_mul_coeff_tateCurve_a₆ 0
  simp only [ArithmeticFunction.map_zero, coeff_zero_eq_constantCoeff_apply] at h
  omega

private theorem coeff_tateCurve_Δ :
    constantCoeff tateCurve.Δ = 0 ∧ coeff 1 tateCurve.Δ = 1 ∧ coeff 2 tateCurve.Δ = -24 := by
  simp [map_ofNat constantCoeff, tateCurve_Δ_eq, coeff_mul, pow_succ,
    Finset.Nat.antidiagonal_succ, constantCoeff_tateCurve_a₆, sigma_apply,
    Nat.Prime.divisors Nat.prime_two]

/-- `Δ` vanishes at `q = 0`. -/
@[simp]
theorem constantCoeff_tateCurve_Δ : constantCoeff tateCurve.Δ = 0 :=
  coeff_tateCurve_Δ.1

/-- The `q`-coefficient of `Δ` is `1`. -/
@[simp]
theorem coeff_one_tateCurve_Δ : coeff 1 tateCurve.Δ = 1 :=
  coeff_tateCurve_Δ.2.1

/-- The `q²`-coefficient of `Δ` is `-24`. -/
@[simp]
theorem coeff_two_tateCurve_Δ : coeff 2 tateCurve.Δ = -24 :=
  coeff_tateCurve_Δ.2.2

/-- **`v(Δ) = v(q)`**: the discriminant of the Tate curve has order `1` in `q`. -/
@[simp]
theorem order_tateCurve_Δ : tateCurve.Δ.order = 1 := by
  rw [← Nat.cast_one, order_eq_nat]
  refine ⟨by simp, fun i hi ↦ ?_⟩
  obtain rfl : i = 0 := by omega
  simp

/-- **The discriminant of the Tate curve is `q` times a unit**: `Δ = q · u` with `u ∈ ℤ⟦q⟧` of
constant coefficient `1`, hence invertible in `ℤ⟦q⟧`. -/
theorem exists_tateCurve_Δ_eq_X_mul :
    ∃ u : ℤ⟦X⟧, constantCoeff u = 1 ∧ tateCurve.Δ = X * u := by
  obtain ⟨u, hu⟩ := X_dvd_iff.mpr constantCoeff_tateCurve_Δ
  refine ⟨u, ?_, hu⟩
  have h := coeff_one_tateCurve_Δ
  rwa [hu, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] at h

/-- Over the Laurent series `ℤ⸨q⸩`, where `q` is invertible, the Tate curve is elliptic. -/
instance isElliptic_baseChange_tateCurve : (tateCurve.baseChange ℤ⸨X⸩).IsElliptic := by
  obtain ⟨u, hu, hΔ⟩ := exists_tateCurve_Δ_eq_X_mul
  refine ⟨?_⟩
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, hΔ, map_mul]
  exact (IsLocalization.map_units ℤ⸨X⸩ (⟨X, 1, pow_one X⟩ : Submonoid.powers (X : ℤ⟦X⟧))).mul
    (((isUnit_iff_constantCoeff (φ := u)).mpr (by simp [hu])).map _)

private theorem coeff_tateCurve_c₄_pow_three :
    constantCoeff (tateCurve.c₄ ^ 3) = 1 ∧ coeff 1 (tateCurve.c₄ ^ 3) = 720 := by
  simp [map_ofNat constantCoeff, tateCurve_c₄, coeff_mul, pow_succ, Finset.Nat.antidiagonal_succ,
    constantCoeff_divisorSumSeries, sigma_apply]

/-- **`j(q) = 1 / q + 744 + ⋯`**: over `ℤ⸨q⸩` the `j`-invariant of the Tate curve is `q⁻¹ · J(q)`
for a power series `J ∈ ℤ⟦q⟧` with `J = 1 + 744 q + ⋯`. In particular `j` has a simple pole at
`q = 0` and integral coefficients. -/
theorem exists_tateCurve_j_eq :
    ∃ J : ℤ⟦X⟧, constantCoeff J = 1 ∧ coeff 1 J = 744 ∧
      (tateCurve.baseChange ℤ⸨X⸩).j = HahnSeries.single (-1) 1 * (J : ℤ⸨X⸩) := by
  obtain ⟨u, hu₀, hΔ⟩ := exists_tateCurve_Δ_eq_X_mul
  have hu₁ : coeff 1 u = -24 := by
    have h := coeff_two_tateCurve_Δ
    rwa [hΔ, coeff_succ_X_mul] at h
  set v := invOfUnit u 1
  have huv : u * v = 1 := mul_invOfUnit u 1 (by simp [hu₀])
  have hv₀ : constantCoeff v = 1 := by
    simpa [hu₀] using congrArg constantCoeff huv
  have hv₁ : coeff 1 v = 24 := by
    have h := congrArg (coeff 1) huv
    simp [coeff_mul, Finset.Nat.antidiagonal_succ, hu₀, hu₁, hv₀] at h
    linarith
  refine ⟨v * tateCurve.c₄ ^ 3, ?_, ?_, ?_⟩
  · rw [map_mul, coeff_tateCurve_c₄_pow_three.1]
    simp [hv₀]
  · rw [coeff_one_mul, coeff_tateCurve_c₄_pow_three.1, coeff_tateCurve_c₄_pow_three.2]
    simp [hv₀, hv₁]
  · have hinv : (((tateCurve.baseChange ℤ⸨X⸩).Δ'⁻¹ : ℤ⸨X⸩ˣ) : ℤ⸨X⸩) =
        HahnSeries.single (-1) 1 * (v : ℤ⸨X⸩) := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [WeierstrassCurve.coe_Δ', WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, hΔ,
        LaurentSeries.coe_algebraMap, map_mul, HahnSeries.ofPowerSeries_X,
        mul_mul_mul_comm, HahnSeries.single_mul_single, ← map_mul, huv]
      simp
    rw [WeierstrassCurve.j, hinv, WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄,
      LaurentSeries.coe_algebraMap]
    simp only [map_mul, map_pow]
    ring

end TauCeti

end
