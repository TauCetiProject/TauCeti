/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.NormCoeff
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Moebius.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The row estimate for Möbius slash operators

Let `R` be a complete ultrametric normed commutative ring with `‖1‖ = 1`, and let
`g = !![a, b; c, d]` lie in `TauCeti.MvPowerSeries.moebiusSubmonoid R`. In the variable `Xᵢ` of
the unit Tate algebra `R⟨X₁, …, X_k⟩` the Möbius series of `g` expands as

```text
(a Xᵢ + b) / (c Xᵢ + d) = b / d + (det g / d) Xᵢ (c Xᵢ + d)⁻¹,
(c Xᵢ + d)⁻¹ = d⁻¹ ∑ₙ (-c Xᵢ / d) ^ n,
```

so if `‖c‖ ≤ sᵢ` and `‖det g‖ ≤ sᵢ`, its coefficient of `Xᵢ ^ n` has norm at most `sᵢ ^ n`
(`TauCeti.MvPowerSeries.norm_coeff_moebius_le`). Geometric coefficient bounds are multiplicative
(`MvPowerSeries.norm_coeff_mul_le_mul_prod_pow`) and survive analytic substitution
(`TauCeti.MvPowerSeries.norm_coeff_restrictedAnalyticSubst_le`). Hence, for a restricted
automorphy factor whose substitution at `γ` is the Möbius series of matrices `gᵢ` with
`‖cᵢ‖, ‖det gᵢ‖ ≤ sᵢ` and whose factor `j γ` has coefficients of norm at most `∏ᵢ sᵢ ^ mᵢ`, the
slash operator satisfies the **row estimate**

```text
‖coeff_m (f | γ)‖ ≤ ‖f‖ ∏ᵢ sᵢ ^ mᵢ
```

(`TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.norm_coeff_slash_le`). Taking `f = Xʳ`, the
coefficient `a_{m,r}(γ)` of `Xᵐ` in `Xʳ | γ` has norm at most `∏ᵢ sᵢ ^ mᵢ` for every `r`. When every
`sᵢ < 1`, these bounds on the rows of the matrix of the slash operator decay geometrically; bounds
of this kind are what make the operator `U_p` compact on overconvergent automorphic forms. The
algebraic weight-`n` factor `∏ᵢ (cᵢ Xᵢ + dᵢ) ^ nᵢ` meets the hypothesis on `j γ` as soon as
`‖cᵢ‖ ≤ sᵢ` (`TauCeti.MvPowerSeries.norm_coeff_moebiusAutomorphyFactor_slash_le`).

For example, in weight zero `diag(p, 1)` acts on `Xᵢ ^ r` by `p ^ r Xᵢ ^ r` and meets the estimate
with `sᵢ = ‖p‖`. The matrix `!![1, 0; p, 1]` has determinant `1`, so it is not covered: its Möbius
series `Xᵢ / (p Xᵢ + 1)` has coefficient `(-p) ^ (n - 1)` at `Xᵢ ^ n`, which exceeds `‖p‖ ^ n`
when `0 < ‖p‖ < 1`.

## Main results

* `TauCeti.MvPowerSeries.norm_coeff_moebiusDenom_le`: the coefficient bound of `c Xᵢ + d`.
* `TauCeti.MvPowerSeries.norm_coeff_ringInverse_moebiusDenom_le`: the coefficient bound of
  `(c Xᵢ + d)⁻¹`.
* `TauCeti.MvPowerSeries.norm_coeff_moebius_le`: the coefficient bound of the Möbius series.
* `TauCeti.MvPowerSeries.RestrictedAutomorphyFactor.norm_coeff_slash_le`: the row estimate for the
  slash operators of an automorphy factor with Möbius substitutions.
* `TauCeti.MvPowerSeries.norm_coeff_moebiusAutomorphyFactor_slash_le`: the row estimate for the
  weight-`n` slash operators.

## References

* D. Jacobs, *Slopes of compact Hecke operators*, PhD thesis, Imperial College London (2003),
  §1.5.
* K. Buzzard, *Eigenvarieties*, in *L-functions and Galois representations*, LMS Lecture Note
  Ser. 320 (2007), 59–120, §§9–10.
-/

public section

open MvPowerSeries MulOpposite

namespace TauCeti.MvPowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {k : ℕ} {s : Fin k → ℝ} {i : Fin k}
  {g : Matrix (Fin 2) (Fin 2) R}

/-- If `‖c‖ ≤ sᵢ` and `‖d‖ ≤ 1`, the denominator `c Xᵢ + d` of `g = !![a, b; c, d]` has
coefficients bounded by `∏ⱼ sⱼ ^ tⱼ`. -/
theorem norm_coeff_moebiusDenom_le (hs : ∀ j, 0 ≤ s j) (hc : ‖g 1 0‖ ≤ s i) (hd : ‖g 1 1‖ ≤ 1)
    (t : Fin k →₀ ℕ) :
    ‖coeff t (moebiusDenom i g : _root_.MvPowerSeries (Fin k) R)‖ ≤ t.prod (s · ^ ·) := by
  rw [coe_moebiusDenom, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans <| max_le
    (norm_coeff_monomial_le_prod_pow hs (by rwa [prod_pow_single, pow_one]) t)
    (norm_coeff_monomial_le_prod_pow hs (by simpa using hd) t)

variable [CompleteSpace R] [NormOneClass R]

/-- The lower right entry `d` of a matrix in `moebiusSubmonoid R` has an inverse of norm one. -/
private theorem norm_inv_lowerRight_unit (hg : g ∈ moebiusSubmonoid R) :
    ‖(↑(isNormMulUnit_lowerRight_of_mem_moebiusSubmonoid hg).isUnit.unit⁻¹ : R)‖ = 1 := by
  rw [NormedRing.norm_units_inv_of_norm_mul
    (isNormMulUnit_lowerRight_of_mem_moebiusSubmonoid hg).norm_mul, IsUnit.unit_spec,
    norm_lowerRight_eq_one_of_mem_moebiusSubmonoid hg, inv_one]

/-- **The coefficients of `(c Xᵢ + d)⁻¹`.** For `g = !![a, b; c, d] ∈ moebiusSubmonoid R` with
`‖c‖ ≤ sᵢ`, the inverse `d⁻¹ ∑ₙ (-c Xᵢ / d) ^ n` of the denominator has coefficients bounded by
`∏ⱼ sⱼ ^ tⱼ`. -/
theorem norm_coeff_ringInverse_moebiusDenom_le (hs : ∀ j, 0 ≤ s j) (hg : g ∈ moebiusSubmonoid R)
    (hc : ‖g 1 0‖ ≤ s i) (t : Fin k →₀ ℕ) :
    ‖coeff t (↑(Ring.inverse (moebiusDenom i g)) : _root_.MvPowerSeries (Fin k) R)‖ ≤
      t.prod (s · ^ ·) := by
  classical
  set u := (isNormMulUnit_lowerRight_of_mem_moebiusSubmonoid hg).isUnit.unit
  -- The inverse in the Tate algebra is Mathlib's formal inverse `invOfUnit _ u`.
  have hinv : (↑(Ring.inverse (moebiusDenom i g)) : _root_.MvPowerSeries (Fin k) R) =
      invOfUnit (moebiusDenom i g : _root_.MvPowerSeries (Fin k) R) u := by
    refine left_inv_eq_right_inv ?_ (mul_invOfUnit _ _ ?_)
    · rw [← Subring.coe_mul, Ring.inverse_mul_cancel _ (isUnit_moebiusDenom hg), Subring.coe_one]
    · rw [constantCoeff_moebiusDenom, IsUnit.unit_spec]
  rw [hinv]
  refine norm_coeff_invOfUnit_le_prod_pow hs (norm_inv_lowerRight_unit hg).le (fun t ht ↦ ?_) t
  rw [coe_moebiusDenom, map_add]
  simp only [coeff_monomial t (0 : Fin k →₀ ℕ), ht, ↓reduceIte, add_zero]
  exact norm_coeff_monomial_le_prod_pow hs (by rwa [prod_pow_single, pow_one]) t

/-- **The coefficients of a Möbius series.** For `g = !![a, b; c, d] ∈ moebiusSubmonoid R` with
`‖c‖ ≤ sᵢ` and `‖det g‖ ≤ sᵢ`, the Möbius series `(a Xᵢ + b) / (c Xᵢ + d)` has coefficients bounded
by `∏ⱼ sⱼ ^ tⱼ`: its constant term `b / d` has norm at most one, and its coefficient of `Xᵢ ^ n`
for `n ≥ 1` is `(det g / d²) (-c / d) ^ (n - 1)`. -/
theorem norm_coeff_moebius_le (hs : ∀ j, 0 ≤ s j) (hg : g ∈ moebiusSubmonoid R)
    (hc : ‖g 1 0‖ ≤ s i) (hdet : ‖g.det‖ ≤ s i) (t : Fin k →₀ ℕ) :
    ‖coeff t (moebius i g : _root_.MvPowerSeries (Fin k) R)‖ ≤ t.prod (s · ^ ·) := by
  classical
  set u := (isNormMulUnit_lowerRight_of_mem_moebiusSubmonoid hg).isUnit.unit
  have hu : ‖(↑u⁻¹ : R)‖ = 1 := norm_inv_lowerRight_unit hg
  have hdu : g 1 1 * ↑u⁻¹ = 1 := by
    rw [← IsUnit.unit_spec (isNormMulUnit_lowerRight_of_mem_moebiusSubmonoid hg).isUnit]
    exact u.mul_inv
  -- `a Xᵢ + b = (b / d) (c Xᵢ + d) + (det g / d) Xᵢ`
  have hnum : (moebiusNum i g : _root_.MvPowerSeries (Fin k) R) =
      C (g 0 1 * ↑u⁻¹) * (moebiusDenom i g : _root_.MvPowerSeries (Fin k) R) +
        monomial (Finsupp.single i 1) (g.det * ↑u⁻¹) := by
    ext t
    rw [map_add, coeff_C_mul, coe_moebiusNum, coe_moebiusDenom, Matrix.det_fin_two]
    simp only [map_add, coeff_monomial]
    split_ifs with h₁ h₂
    · exact absurd (h₂ ▸ h₁).symm (Finsupp.single_ne_zero.mpr one_ne_zero)
    · linear_combination (-(g 0 0)) * hdu
    · linear_combination (-(g 0 1)) * hdu
    · ring
  -- hence `(a Xᵢ + b) / (c Xᵢ + d) = b / d + (det g / d) Xᵢ (c Xᵢ + d)⁻¹`
  have hW : (moebius i g : _root_.MvPowerSeries (Fin k) R) =
      monomial 0 (g 0 1 * ↑u⁻¹) +
        monomial (Finsupp.single i 1) (g.det * ↑u⁻¹) *
          (↑(Ring.inverse (moebiusDenom i g)) : _root_.MvPowerSeries (Fin k) R) := by
    rw [moebius_def, Subring.coe_mul, hnum, add_mul, mul_assoc, ← Subring.coe_mul,
      Ring.mul_inverse_cancel _ (isUnit_moebiusDenom hg), Subring.coe_one, mul_one,
      monomial_zero_eq_C_apply]
  rw [hW, map_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine norm_coeff_monomial_le_prod_pow hs ?_ t
    simpa [hu] using norm_mul_le_of_le (norm_upperRight_le_one_of_mem_moebiusSubmonoid hg) hu.le
  · have hm := norm_coeff_monomial_le_prod_pow (x := g.det * ↑u⁻¹) hs (by
      rw [prod_pow_single, pow_one]
      simpa [hu] using norm_mul_le_of_le hdet hu.le)
    exact norm_coeff_mul_le_prod_pow hm (norm_coeff_ringInverse_moebiusDenom_le hs hg hc) t

/-- **The row estimate.** Let `A` be a restricted automorphy factor whose substitution at `γ` is
the Möbius series of matrices `gᵢ = !![aᵢ, bᵢ; cᵢ, dᵢ] ∈ moebiusSubmonoid R` with
`‖cᵢ‖ ≤ sᵢ` and `‖det gᵢ‖ ≤ sᵢ`, and whose factor `j γ` has coefficients bounded by
`∏ᵢ sᵢ ^ tᵢ`. Then every coefficient of `f | γ = j γ · f(w_γ)` satisfies
`‖coeff_t (f | γ)‖ ≤ ‖f‖ ∏ᵢ sᵢ ^ tᵢ`. For `f = Xʳ` this bounds the coefficient of `Xᵗ` in `Xʳ | γ`
by `∏ᵢ sᵢ ^ tᵢ`, uniformly in `r`. -/
theorem RestrictedAutomorphyFactor.norm_coeff_slash_le {M : Type*} [Monoid M]
    (A : RestrictedAutomorphyFactor M R k) {γ : M} {g : Fin k → Matrix (Fin 2) (Fin 2) R}
    (hsubst : ∀ i, A.subst γ i = moebius i (g i)) (hg : ∀ i, g i ∈ moebiusSubmonoid R)
    (hc : ∀ i, ‖g i 1 0‖ ≤ s i) (hdet : ∀ i, ‖(g i).det‖ ≤ s i)
    (hj : ∀ t, ‖coeff t (A.factor γ : _root_.MvPowerSeries (Fin k) R)‖ ≤ t.prod (s · ^ ·))
    (f : IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) (t : Fin k →₀ ℕ) :
    ‖coeff t (A.slash (op γ) f : _root_.MvPowerSeries (Fin k) R)‖ ≤ ‖f‖ * t.prod (s · ^ ·) := by
  have hs (i : Fin k) : 0 ≤ s i := (norm_nonneg _).trans (hc i)
  rw [RestrictedAutomorphyFactor.slash_apply, Subring.coe_mul, ← one_mul ‖f‖]
  refine norm_coeff_mul_le_mul_prod_pow (fun t ↦ (one_mul _).trans_ge (hj t))
    (norm_coeff_restrictedAnalyticSubst_le _ _ hs (fun i e ↦ ?_) f) t
  rw [hsubst, one_mul]
  exact norm_coeff_moebius_le hs (hg i) (hc i) (hdet i) e

/-- **The row estimate in weight `n`.** For `k`-tuples `γ` of matrices
`!![aᵢ, bᵢ; cᵢ, dᵢ] ∈ moebiusSubmonoid R` with `‖cᵢ‖ ≤ sᵢ` and `‖det γᵢ‖ ≤ sᵢ`, the weight-`n` slash
operator `f ↦ ∏ᵢ (cᵢ Xᵢ + dᵢ) ^ nᵢ · f(w_γ)` satisfies
`‖coeff_t (f | γ)‖ ≤ ‖f‖ ∏ᵢ sᵢ ^ tᵢ`. -/
theorem norm_coeff_moebiusAutomorphyFactor_slash_le (n : Fin k → ℕ)
    (γ : Fin k → moebiusSubmonoid R) (hc : ∀ i, ‖(γ i : Matrix (Fin 2) (Fin 2) R) 1 0‖ ≤ s i)
    (hdet : ∀ i, ‖(γ i : Matrix (Fin 2) (Fin 2) R).det‖ ≤ s i)
    (f : IsRestricted.subring (R := R) fun _ : Fin k ↦ (1 : ℝ)) (t : Fin k →₀ ℕ) :
    ‖coeff t ((moebiusAutomorphyFactor R n).slash (op γ) f : _root_.MvPowerSeries (Fin k) R)‖ ≤
      ‖f‖ * t.prod (s · ^ ·) := by
  have hs (i : Fin k) : 0 ≤ s i := (norm_nonneg _).trans (hc i)
  refine (moebiusAutomorphyFactor R n).norm_coeff_slash_le (moebiusAutomorphyFactor_subst n γ)
    (fun i ↦ (γ i).property) hc hdet (fun t ↦ ?_) f t
  rw [moebiusAutomorphyFactor_factor]
  push_cast
  exact norm_coeff_prod_le_prod_pow hs Finset.univ (fun i _ ↦ norm_coeff_pow_le_prod_pow hs
    (norm_coeff_moebiusDenom_le hs (hc i)
      (norm_lowerRight_eq_one_of_mem_moebiusSubmonoid (γ i).property).le) (n i)) t

end TauCeti.MvPowerSeries
