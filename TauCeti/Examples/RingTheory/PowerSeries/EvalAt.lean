/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.WithAbs
public import TauCeti.NumberTheory.Padics.FermatLittle
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AnalyticSubst
public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.HasseDeriv.Basic
public import TauCeti.RingTheory.PowerSeries.TateAlgebra
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Values, translations and derivatives of restricted power series

These examples test how restricted power series behave as functions on a closed disc: their
values at points, their translations, and the Hasse derivatives that give the coefficients of
their expansions at points.

* **Hasse derivatives in characteristic two.** In every commutative semiring the second Hasse
  derivative of `X²` is `1`, while in characteristic two the second ordinary derivative of `X²`
  is `2 = 0`. The coefficients of the expansion of a series at a point are the values of its
  Hasse derivatives, not of its ordinary derivatives divided by factorials.
* **Translation by a unit.** The series `X + 1` cannot be substituted formally into a power
  series over a nontrivial ring, since its constant coefficient `1` is not nilpotent. Analytic
  translation `X ↦ X + 1` is nevertheless an isometric automorphism of the series restricted at
  the unit radius.
* **Maximum modulus over `ℚ_p`.** The polynomial `X ^ p - X` has Gauss norm one at the unit radius,
  but by Fermat's little theorem all its values at points of `ℤ_p` have norm at most `p⁻¹`. So the
  Gauss norm of a series over `K` need not be attained at a point of the closed unit disc of `K`
  itself. The maximum modulus principle `TauCeti.MvPowerSeries.exists_pointNorm_eq_norm` attains
  it at a maximal ideal, whose residue field is a finite extension of `K`.
* **No coefficient recovery over `𝔽_p`.** Over `𝔽_p` with its trivial norm, every element lies in
  the closed unit disc and is a root of `X ^ p - X`. So this nonzero restricted series vanishes at
  every point of the closed unit disc, and a restricted series over an arbitrary complete field is
  not determined by its values there. The identity principle
  `PowerSeries.IsRestricted.eq_zero_of_infinite_of_evalAt_eq_zero` needs infinitely many zeros,
  and the closed unit disc of `𝔽_p` is finite.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§5.1.3–5.1.4.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open PowerSeries TauCeti.PowerSeries
open scoped Polynomial

namespace TauCeti.Examples.PowerSeriesEvalAt

section HasseDeriv

variable {R : Type*} [CommSemiring R]

-- The second Hasse derivative of `X²` is `1` over every commutative semiring.
example : hasseDeriv 2 (X ^ 2 : R⟦X⟧) = 1 := by
  ext n
  rcases n with _ | n
  · simp [coeff_hasseDeriv, coeff_X_pow]
  · simp [coeff_hasseDeriv, coeff_X_pow, coeff_one]

-- In characteristic two the second ordinary derivative of `X²` vanishes, since it is
-- `2! • Δ²(X²) = 2`.
example [CharP R 2] : (derivative (R := R))^[2] (X ^ 2 : R⟦X⟧) = 0 := by
  rw [← factorial_smul_hasseDeriv]
  ext n
  rcases n with _ | n
  · simp [coeff_hasseDeriv, coeff_X_pow, Nat.factorial, CharTwo.two_eq_zero]
  · simp [coeff_hasseDeriv, coeff_X_pow]

end HasseDeriv

section Translate

open TauCeti.MvPowerSeries

-- `X + 1` cannot be substituted formally: its constant coefficient `1` is not nilpotent.
example {R : Type*} [CommRing R] [Nontrivial R] :
    ¬_root_.MvPowerSeries.HasSubst
      (fun _ : Fin 1 ↦ (_root_.MvPowerSeries.X 0 + 1 : _root_.MvPowerSeries (Fin 1) R)) :=
  fun h ↦ not_isNilpotent_one (by simpa using h.const_coeff 0)

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]

-- Analytic translation by `1` is an isometric automorphism of the series restricted at the unit
-- radius, sending `X` to `X + 1`, although the constant coefficient of `X + 1` is nonzero.
example : ∃ e : _root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin 1 ↦ 1) ≃ₐ[R]
      _root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin 1 ↦ 1),
    e ⟨_root_.MvPowerSeries.X 0, _root_.MvPowerSeries.isRestricted_monomial _ _ 1⟩ =
        ⟨_root_.MvPowerSeries.X 0, _root_.MvPowerSeries.isRestricted_monomial _ _ 1⟩ + 1 ∧
      ∀ f, ‖e f‖ = ‖f‖ :=
  ⟨restrictedTranslateEquiv (fun _ ↦ 1) fun _ ↦ by simp, by simp, by simp⟩

end Translate

section Padic

variable (p : ℕ) [hp : Fact p.Prime]

/-- The polynomial `X ^ p - X` over `ℚ_p` has Gauss norm one at the unit radius: its coefficients
have norm at most one, and its linear coefficient is `-1`. -/
theorem norm_polynomialToRestricted_X_pow_sub_X :
    ‖polynomialToRestricted 1 (Polynomial.X ^ p - Polynomial.X : ℚ_[p][X])‖ = 1 := by
  refine le_antisymm (norm_le_iff.mpr fun n ↦ ?_) ?_
  · rw [coe_polynomialToRestricted, Polynomial.coeff_coe, one_pow, mul_one,
      Polynomial.coeff_sub, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [Polynomial.coeff_X_pow]
      split_ifs <;> simp
    · rw [norm_neg, Polynomial.coeff_X]
      split_ifs <;> simp
  · refine (le_of_eq ?_).trans (norm_coeff_mul_pow_le _ 1)
    simp [hp.out.one_lt.ne]

/-- At every point `x` of `ℤ_p`, the value of `X ^ p - X` has norm at most `p⁻¹`: by Fermat's
little theorem, `x ^ p - x` reduces to zero in `𝔽_p`. -/
theorem norm_evalAt_X_pow_sub_X_le {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) :
    ‖(polynomialToRestricted 1 (Polynomial.X ^ p - Polynomial.X : ℚ_[p][X]) :
      ℚ_[p]⟦X⟧).evalAt x‖ ≤ (p : ℝ)⁻¹ := by
  rw [coe_polynomialToRestricted, evalAt_coe, map_sub, map_pow, Polynomial.aeval_X]
  exact Padic.norm_pow_sub_self_le hx

/-- **The Gauss norm is not attained at a point of the closed unit disc of `ℚ_p`.** The value of
`X ^ p - X` at every point of `ℤ_p` has norm smaller than its Gauss norm one at the unit radius. -/
theorem not_exists_norm_evalAt_X_pow_sub_X_eq :
    ¬∃ x : ℚ_[p], ‖x‖ ≤ 1 ∧
      ‖(polynomialToRestricted 1 (Polynomial.X ^ p - Polynomial.X : ℚ_[p][X]) :
        ℚ_[p]⟦X⟧).evalAt x‖ =
          ‖polynomialToRestricted 1 (Polynomial.X ^ p - Polynomial.X : ℚ_[p][X])‖ := by
  rintro ⟨x, hx, heq⟩
  have h := norm_evalAt_X_pow_sub_X_le p hx
  rw [heq, norm_polynomialToRestricted_X_pow_sub_X] at h
  exact (inv_lt_one_of_one_lt₀ (mod_cast hp.out.one_lt : (1 : ℝ) < p)).not_ge h

end Padic

section FiniteField

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Coefficient recovery fails over `𝔽_p`.** With its trivial norm, `𝔽_p` is a complete
ultrametric field all of whose elements lie in the closed unit disc. The nonzero series `X ^ p - X`,
restricted at the unit radius, vanishes at each of them. -/
theorem exists_ne_zero_forall_evalAt_eq_zero :
    ∃ f : IsRestricted.subring (R := WithAbs (AbsoluteValue.trivial : AbsoluteValue (ZMod p) ℝ)) 1,
      f ≠ 0 ∧ ∀ x : WithAbs (AbsoluteValue.trivial : AbsoluteValue (ZMod p) ℝ), ‖x‖ ≤ 1 →
        f.val.evalAt x = 0 := by
  refine ⟨polynomialToRestricted 1 (Polynomial.X ^ p - Polynomial.X), ?_, fun x _ ↦ ?_⟩
  · rw [Ne, ← map_zero (polynomialToRestricted 1), (polynomialToRestricted_injective 1).eq_iff]
    exact Polynomial.X_pow_sub_X_ne_zero hp.out.one_lt
  · rw [coe_polynomialToRestricted, evalAt_coe, map_sub, map_pow, Polynomial.aeval_X, sub_eq_zero]
    -- every element of `𝔽_p` is a root of `X ^ p - X`, by Fermat's little theorem
    exact (WithAbs.equiv _).injective (by rw [map_pow, ZMod.pow_card])

end FiniteField

end TauCeti.Examples.PowerSeriesEvalAt
