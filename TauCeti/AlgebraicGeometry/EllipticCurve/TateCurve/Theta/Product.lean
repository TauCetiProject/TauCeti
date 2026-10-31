/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Theta.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Theta.Coefficients
import TauCeti.Analysis.Normed.Module.InfiniteSum
import TauCeti.Data.Int.MulPred

/-!
# Products of two translated theta functions

For a unit `q` with `‖q‖ < 1` in a complete normed field and a unit `a`, the product
`θ(a u) θ(a⁻¹ u)` of two translates of the theta function of the Tate curve is a Laurent series
in `u` converging at every unit. Its coefficients are the Cauchy product of the coefficients of
`θ(a u)` and `θ(a⁻¹ u)`, and they satisfy the degree-two quasi-periodicity recurrence
`t(n + 2) = qⁿ t(n)`, so they lie in the two-dimensional coefficient space
`TauCeti.tateThetaCoefficients q 1 2`. This holds over every complete normed field, archimedean
or not.

## Main definitions

* `TauCeti.tateThetaCoeff q n`: the Laurent coefficient `(-1)ⁿ q^(n (n - 1) / 2)` of `θ`.
* `TauCeti.tateThetaProductCoeff q a n`: the Laurent coefficient of `θ(a u) θ(a⁻¹ u)`.

## Main results

* `TauCeti.tateThetaCoeff_add_one`: the recurrence `c(n + 1) = -qⁿ c(n)` of the theta
  coefficients.
* `TauCeti.tateThetaProductCoeff_mem`: the coefficients are quasi-periodic of degree two.
* `TauCeti.hasSum_tateThetaProductCoeff`: the Laurent series converges to
  `θ(a u) θ(a⁻¹ u)` at every unit `u`.
* `TauCeti.exists_hasSum_tateTheta_mul_tateTheta`: the Laurent coefficients of
  `θ(a u) θ(a⁻¹ u)` are quasi-periodic of degree two.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*, in *Elliptic curves, modular forms,
  & Fermat's last theorem* (Hong Kong, 1993), International Press (1995), 162–184.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, §V.3.
-/

public section

namespace TauCeti

variable {K : Type*} [NormedField K]

/-- The Laurent coefficient `(-1)ⁿ q^(n (n - 1) / 2)` of the theta function of the Tate curve. -/
noncomputable def tateThetaCoeff (q : Kˣ) (n : ℤ) : K :=
  (-1) ^ n * (q : K) ^ (n * (n - 1) / 2)

/-- The formula for the Laurent coefficients of the theta function. -/
theorem tateThetaCoeff_def (q : Kˣ) (n : ℤ) :
    tateThetaCoeff q n = (-1) ^ n * (q : K) ^ (n * (n - 1) / 2) := (rfl)

/-- The Laurent coefficients of the theta function satisfy `c(n + 1) = -qⁿ c(n)`. -/
theorem tateThetaCoeff_add_one (q : Kˣ) (n : ℤ) :
    tateThetaCoeff q (n + 1) = -(q : K) ^ n * tateThetaCoeff q n := by
  rw [tateThetaCoeff_def, tateThetaCoeff_def, Int.add_mul_add_sub_one_ediv_two n 1]
  simp only [mul_one, sub_self, mul_zero, Int.zero_ediv, add_zero]
  rw [zpow_add₀ (neg_ne_zero.mpr one_ne_zero), zpow_add₀ q.ne_zero, zpow_one]
  ring

/-- The term of index `n` of the theta series at `b u`, written with the coefficient
`tateThetaCoeff q n * bⁿ`. -/
private theorem tateThetaCoeff_mul_zpow_mul_zpow (q b u : Kˣ) (n : ℤ) :
    tateThetaCoeff q n * (b : K) ^ n * (u : K) ^ n =
      (-1) ^ n * (q : K) ^ (n * (n - 1) / 2) * ((b * u : Kˣ) : K) ^ n := by
  rw [Units.val_mul, mul_zpow, mul_assoc, tateThetaCoeff_def]

/-- The Laurent coefficients of `θ(a u) θ(a⁻¹ u)`: the Cauchy product of the coefficients
`tateThetaCoeff q n * aⁿ` of `θ(a u)` and `tateThetaCoeff q n * a⁻ⁿ` of `θ(a⁻¹ u)`. -/
noncomputable def tateThetaProductCoeff (q a : Kˣ) (n : ℤ) : K :=
  ∑' m, tateThetaCoeff q m * (a : K) ^ m *
    (tateThetaCoeff q (n - m) * ((a⁻¹ : Kˣ) : K) ^ (n - m))

/-- The Cauchy-product formula for the Laurent coefficients of `θ(a u) θ(a⁻¹ u)`. -/
theorem tateThetaProductCoeff_def (q a : Kˣ) (n : ℤ) :
    tateThetaProductCoeff q a n = ∑' m, tateThetaCoeff q m * (a : K) ^ m *
      (tateThetaCoeff q (n - m) * ((a⁻¹ : Kˣ) : K) ^ (n - m)) := (rfl)

/-- The Laurent coefficients of `θ(a u) θ(a⁻¹ u)` satisfy `t(n + 2) = qⁿ t(n)`. -/
theorem tateThetaProductCoeff_add_two (q a : Kˣ) (n : ℤ) :
    tateThetaProductCoeff q a (n + 2) = (q : K) ^ n * tateThetaProductCoeff q a n := by
  rw [tateThetaProductCoeff_def, tateThetaProductCoeff_def,
    ← (Equiv.addRight (1 : ℤ)).tsum_eq, ← tsum_mul_left]
  congr 1 with m
  have h₁ : n + 2 - (m + 1) = n - m + 1 := by ring
  simp only [Equiv.coe_addRight, h₁, tateThetaCoeff_add_one, Units.val_inv_eq_inv_val,
    inv_zpow', zpow_add₀ a.ne_zero, zpow_one, zpow_sub₀ q.ne_zero, neg_add, zpow_neg]
  field_simp

/-- The Laurent coefficients of `θ(a u) θ(a⁻¹ u)` are quasi-periodic of degree two. -/
theorem tateThetaProductCoeff_mem (q a : Kˣ) :
    tateThetaProductCoeff q a ∈ tateThetaCoefficients q 1 2 := by
  rw [mem_tateThetaCoefficients_iff]
  intro n
  simp [tateThetaProductCoeff_add_two]

variable [CompleteSpace K]

/-- **The Laurent expansion of `θ(a u) θ(a⁻¹ u)`** converges at every unit `u`, over every
complete normed field. -/
theorem hasSum_tateThetaProductCoeff (q a u : Kˣ) (hq : ‖(q : K)‖ < 1) :
    HasSum (fun n ↦ tateThetaProductCoeff q a n * (u : K) ^ n)
      (tateTheta q (a * u) * tateTheta q (a⁻¹ * u)) := by
  -- Both theta series converge absolutely, so their Cauchy product converges to the product.
  have h := hasSum_laurent_mul_of_summable_norm
    (f := fun n ↦ tateThetaCoeff q n * (a : K) ^ n)
    (g := fun n ↦ tateThetaCoeff q n * ((a⁻¹ : Kˣ) : K) ^ n) u.ne_zero
    (by simpa only [tateThetaCoeff_mul_zpow_mul_zpow] using summable_norm_tateTheta q (a * u) hq)
    (by simpa only [tateThetaCoeff_mul_zpow_mul_zpow] using
      summable_norm_tateTheta q (a⁻¹ * u) hq)
  simp only [tateThetaCoeff_mul_zpow_mul_zpow, (hasSum_tateTheta q _ hq).tsum_eq] at h
  exact h

/-- **The Laurent expansion of `θ(a u) θ(a⁻¹ u)`.** Its coefficients are quasi-periodic of
degree two, and the Laurent series converges at every unit. This holds over every complete
normed field, archimedean or not. -/
theorem exists_hasSum_tateTheta_mul_tateTheta (q : Kˣ) (hq : ‖(q : K)‖ < 1) (a : Kˣ) :
    ∃ b ∈ tateThetaCoefficients q 1 2, ∀ u : Kˣ,
      HasSum (fun n ↦ b n * (u : K) ^ n) (tateTheta q (a * u) * tateTheta q (a⁻¹ * u)) :=
  ⟨_, tateThetaProductCoeff_mem q a, fun u ↦ hasSum_tateThetaProductCoeff q a u hq⟩

end TauCeti

end
