/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Log
public import TauCeti.RingTheory.MvPowerSeries.Derivative
public import TauCeti.RingTheory.FormalGroup.Hom

import Mathlib.RingTheory.PowerSeries.WellKnown
import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.PowerSeries.SubstInv

/-!
# The invariant differential and the logarithm of a formal group law

Let `F(X, Y)` be a one-dimensional formal group law over a commutative ring `R`. Its normalised
**invariant differential** is `ω = P(T) dT` with `P(T) = F_X(0, T)⁻¹`, where `F_X` is the partial
derivative of `F` in its first variable; the constant coefficient of `F_X(0, T)` is `1`, so the
inverse exists over any `R`. Differentiating the associativity law `F(F(U, T), S) = F(U, F(T, S))`
in `U` and setting `U = 0` shows that `ω` is invariant under translation:
`P(F(T, S)) · F_X(T, S) = P(T)`.

When `R` is an algebra over `ℚ`, the **formal logarithm** `log_F(T) = ∫ P(T) dT` is the power series
with zero constant coefficient and derivative `P`. Invariance of `ω` makes `log_F` a homomorphism
from `F` to the additive formal group law:

  `log_F(F(X, Y)) = log_F(X) + log_F(Y)`.

The logarithm has linear coefficient `1`, so it has a compositional inverse, the **formal
exponential** `exp_F`, and `F(X, Y) = exp_F(log_F(X) + log_F(Y))`: over a `ℚ`-algebra every
formal group law is strictly isomorphic to the additive one. Up to a scalar, `log_F` is the only
power series that is additive along `F`.

For the additive formal group law `X + Y` the invariant differential is `dT` and both `log` and
`exp` are `T`. For the multiplicative formal group law `X + Y + XY` the invariant differential is
`dT / (1 + T)`, and `log` and `exp` are Mathlib's `PowerSeries.log`, the series of `log(1 + T)`,
and `e^T - 1`.

## Main definitions

* `FormalGroup.invariantDifferential`: the coefficient `P(T)` of the normalised invariant
  differential `ω = P(T) dT` of `F`.
* `FormalGroup.invariantDerivation`: the dual derivation `F_X(0, T) d/dT`.
* `FormalGroup.log`: the formal logarithm of `F`, over a `ℚ`-algebra.
* `FormalGroup.exp`: the formal exponential of `F`, the compositional inverse of `FormalGroup.log`.

## Main results

* `TauCeti.FormalGroupHom.derivative_eq_zero_iff`: a homomorphism has zero derivative exactly
  when its linear coefficient vanishes, over any commutative coefficient ring.

* `FormalGroup.subst_invariantDifferential_mul_pderiv`: **the invariant differential is
  invariant**, `P(F(X, Y)) · F_X(X, Y) = P(X)`.
* `FormalGroup.subst_invariantDifferential_mul_pderiv_one`: for commutative `F`, the same in the
  second variable, `P(F(X, Y)) · F_Y(X, Y) = P(Y)`.
* `FormalGroup.invariantDifferential_mul_invariantDerivation`: multiplying the invariant
  derivative by `P(T)` recovers the ordinary derivative.
* `FormalGroup.invariantDerivation_log`: the invariant derivative of `log_F` is `1`.
* `FormalGroup.map_invariantDerivation`: the invariant derivation commutes with coefficient maps.
* `FormalGroup.map_invariantDifferential`: the invariant differential commutes with
  coefficient maps.
* `FormalGroup.natCast_mul_coeff_log_mem_range`: each logarithm coefficient becomes integral
  after multiplication by its degree.
* `FormalGroup.subst_toPowerSeries_log`: `log_F(F(X, Y)) = log_F(X) + log_F(Y)`.
* `FormalGroup.subst_subst_toPowerSeries_log`: the same at any pair of power series that can be
  substituted.
* `FormalGroup.subst_toPowerSeries_eq_add_iff`: a power series `g` satisfies
  `g(F(X, Y)) = g(X) + g(Y)` exactly when it is a scalar multiple of `log_F`.
* `FormalGroup.subst_exp_log` and `FormalGroup.subst_log_exp`: `log_F` and `exp_F` are inverse.
* `FormalGroup.eq_exp_of_subst_log_eq_X`: `exp_F` is the only right inverse of `log_F`.
* `FormalGroup.map_log` and `FormalGroup.map_exp`: the logarithm and exponential commute with
  base change along homomorphisms of `ℚ`-algebras.
* `FormalGroup.derivative_exp`: `exp_F'(T) = F_X(0, exp_F(T))`.
* `FormalGroup.toPowerSeries_eq_subst_exp`: `F(X, Y) = exp_F(log_F(X) + log_F(Y))`.
* `FormalGroup.logIso`: the strict isomorphism from `F` to the additive formal group, with
  forward homomorphism `FormalGroup.logHom` and inverse `FormalGroup.expHom`.
* `FormalGroup.eq_logIso`: this is the unique strict isomorphism to the additive formal group.
* `FormalGroup.invariantDifferential_𝔾ₐ`, `FormalGroup.log_𝔾ₐ`, `FormalGroup.exp_𝔾ₐ`: the additive
  formal group law has invariant differential `dT`, and logarithm and exponential `T`.
* `FormalGroup.invariantDifferential_𝔾ₘ`, `FormalGroup.log_𝔾ₘ`, `FormalGroup.exp_𝔾ₘ`: the
  multiplicative formal group law has invariant differential `dT / (1 + T)`, logarithm
  `log(1 + T)` and exponential `e^T - 1`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4 and IV.5.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

/-! ### The invariant differential -/

/-- `F_X(0, T)`, the partial derivative of `F` in its first variable, restricted to `X = 0`. -/
private noncomputable abbrev derivZeroX : PowerSeries R :=
  subst ![0, PowerSeries.X] (pderiv 0 F.toPowerSeries)

private theorem constantCoeff_derivZeroX : PowerSeries.constantCoeff F.derivZeroX = 1 := by
  have hD : constantCoeff (pderiv 0 F.toPowerSeries) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, _root_.zero_add, F.lin_coeff_X]
    simp
  have ha : HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) := HasSubst.zero_X
  -- `F_X - 1` has zero constant coefficient, and so does its substitution
  have := constantCoeff_subst_eq_zero ha (fun s ↦ by fin_cases s <;> simp [PowerSeries.X])
    (f := pderiv 0 F.toPowerSeries - 1) (by simp [hD])
  rwa [← coe_substAlgHom ha, map_sub, map_one, map_sub, map_one, sub_eq_zero,
    coe_substAlgHom] at this

/-- Substituting `g` into `F_X(0, T)` is substituting `(0, g)` into `F_X`. -/
private theorem subst_derivZeroX {σ : Type*} {g : MvPowerSeries σ R}
    (hg : PowerSeries.HasSubst g) :
    PowerSeries.subst g F.derivZeroX = subst ![0, g] (pderiv 0 F.toPowerSeries) := by
  have ha : HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) := HasSubst.zero_X
  rw [derivZeroX, PowerSeries.subst_def, subst_comp_subst_apply ha hg.const]
  congr 1
  funext s
  fin_cases s
  · simpa using map_zero (substAlgHom (R := R) hg.const)
  · simp [← PowerSeries.subst_def, PowerSeries.subst_X hg]

/-- Differentiating associativity `F(F(U, T), S) = F(U, F(T, S))` in `U` at `U = 0`:
`F_X(T, S) · F_X(0, T) = F_X(0, F(T, S))`. -/
private theorem pderiv_mul_subst_derivZeroX :
    pderiv 0 F.toPowerSeries * PowerSeries.subst (X 0) F.derivZeroX =
      PowerSeries.subst F.toPowerSeries F.derivZeroX := by
  have h₁ := HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 F.zero_constantCoeff
  have h₂ := HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 F.zero_constantCoeff
  -- the derivative in `U` of associativity, in the three variables `U, T, S`
  have hd : subst ![subst ![X 0, X 1] F.toPowerSeries, X 2] (pderiv 0 F.toPowerSeries) *
      subst (![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) R) (pderiv 0 F.toPowerSeries) =
        subst ![X 0, subst ![X 1, X 2] F.toPowerSeries] (pderiv 0 F.toPowerSeries) := by
    have := congrArg (pderiv (R := R) 0) F.assoc
    rw [pderiv_subst h₁, pderiv_subst h₂] at this
    simpa [Fin.sum_univ_two, pderiv_subst HasSubst.X_X] using this
  -- now set `U = 0`, renaming `T, S` to the two variables `X 0, X 1`
  set b : Fin 3 → MvPowerSeries (Fin 2) R := ![0, X 0, X 1]
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero fun s ↦ by fin_cases s <;> simp [b]
  have e₀ : (fun s ↦ subst b ((![X 0, X 1] : Fin 2 → MvPowerSeries (Fin 3) R) s)) = ![0, X 0] := by
    funext s; fin_cases s <;> simp [subst_X hb, b]
  have e₁ : (fun s ↦ subst b ((![subst ![X 0, X 1] F.toPowerSeries, X 2] :
      Fin 2 → MvPowerSeries (Fin 3) R) s)) = X := by
    funext s; fin_cases s
    · simp [subst_comp_subst_apply HasSubst.X_X hb, e₀, F.zero_add (PowerSeries.HasSubst.X _)]
    · simp [subst_X hb, b]
  have e₂ : (fun s ↦ subst b ((![X 0, subst ![X 1, X 2] F.toPowerSeries] :
      Fin 2 → MvPowerSeries (Fin 3) R) s)) = ![0, F.toPowerSeries] := by
    funext s; fin_cases s
    · simp [subst_X hb, b]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        subst_comp_subst_apply HasSubst.X_X hb]
      have : (fun s ↦ subst b ((![X 1, X 2] : Fin 2 → MvPowerSeries (Fin 3) R) s)) = X := by
        funext s; fin_cases s <;> simp [subst_X hb, b]
      rw [this, subst_self, id]
  have := congrArg (subst b) hd
  rw [subst_mul hb, subst_comp_subst_apply h₁ hb, subst_comp_subst_apply HasSubst.X_X hb,
    subst_comp_subst_apply h₂ hb, e₀, e₁, e₂, subst_self] at this
  rw [subst_derivZeroX _ (PowerSeries.HasSubst.X _), subst_derivZeroX _
    (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff)]
  exact this

/-- **The invariant differential** of a formal group law `F`, recorded by its coefficient: the
power series `P(T) = F_X(0, T)⁻¹`, so that `ω = P(T) dT` is the normalised invariant differential of
`F` (Silverman IV.4.2). Here `F_X` is the partial derivative of `F` in its first variable. -/
noncomputable def invariantDifferential : PowerSeries R :=
  PowerSeries.invOfUnit F.derivZeroX 1

/-- The invariant differential is normalised: `P(0) = 1`. -/
@[simp]
theorem constantCoeff_invariantDifferential :
    PowerSeries.constantCoeff F.invariantDifferential = 1 := by
  simp [invariantDifferential, PowerSeries.constantCoeff_invOfUnit]

/-- `P(T) · F_X(0, T) = 1`: the defining property of the invariant differential. -/
theorem invariantDifferential_mul_subst_pderiv :
    F.invariantDifferential * subst ![0, PowerSeries.X] (pderiv 0 F.toPowerSeries) = 1 :=
  PowerSeries.invOfUnit_mul _ _ (by simp [constantCoeff_derivZeroX])

/-- The invariant derivation `F_X(0, T) d/dT` of a formal group law. Its dual invariant
differential is `dT / F_X(0, T)`. -/
noncomputable def invariantDerivation :
    Derivation R (PowerSeries R) (PowerSeries R) :=
  (subst ![(0 : PowerSeries R), PowerSeries.X] (pderiv 0 F.toPowerSeries)) •
    PowerSeries.derivative

theorem invariantDerivation_apply (g : PowerSeries R) :
    F.invariantDerivation g =
      subst ![(0 : PowerSeries R), PowerSeries.X] (pderiv 0 F.toPowerSeries) *
        PowerSeries.derivative g := (rfl)

/-- The invariant derivation commutes with change of coefficients. -/
@[simp]
theorem map_invariantDerivation {S : Type*} [CommRing S] (f : R →+* S) (g : PowerSeries R) :
    PowerSeries.map f (F.invariantDerivation g) =
      (F.map f).invariantDerivation (PowerSeries.map f g) := by
  have hA : PowerSeries.map f (subst ![(0 : PowerSeries R), PowerSeries.X]
      (pderiv 0 F.toPowerSeries)) =
      subst ![(0 : PowerSeries S), PowerSeries.X] (pderiv 0 (F.map f).toPowerSeries) := by
    ext n
    simp [PowerSeries.coeff_map, coeff_subst_zero_X, coeff_pderiv]
  simp only [invariantDerivation_apply, map_mul, PowerSeries.derivative_map, hA]

/-- The invariant differential commutes with change of coefficients. -/
@[simp]
theorem map_invariantDifferential {S : Type*} [CommRing S] (f : R →+* S) :
    PowerSeries.map f F.invariantDifferential = (F.map f).invariantDifferential := by
  have hD := F.map_invariantDerivation f PowerSeries.X
  simp only [invariantDerivation_apply, PowerSeries.derivative_X, mul_one,
    PowerSeries.map_X] at hD
  have hleft := congrArg (PowerSeries.map f) F.invariantDifferential_mul_subst_pderiv
  rw [map_mul, map_one, hD] at hleft
  exact left_inv_eq_right_inv hleft
    (by simpa [mul_comm] using (F.map f).invariantDifferential_mul_subst_pderiv)

/-- Multiplying the invariant derivative by the invariant differential's coefficient
recovers the ordinary derivative. -/
theorem invariantDifferential_mul_invariantDerivation (g : PowerSeries R) :
    F.invariantDifferential * F.invariantDerivation g = PowerSeries.derivative g := by
  rw [invariantDerivation_apply, ← mul_assoc, invariantDifferential_mul_subst_pderiv, one_mul]

/-- **The invariant differential is invariant** (Silverman IV.4.2): `ω(F(X, Y)) = ω(X)`, that is
`P(F(X, Y)) · F_X(X, Y) = P(X)`. -/
theorem subst_invariantDifferential_mul_pderiv :
    PowerSeries.subst F.toPowerSeries F.invariantDifferential * pderiv 0 F.toPowerSeries =
      PowerSeries.subst (X 0) F.invariantDifferential := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX := PowerSeries.HasSubst.X (S := R) (0 : Fin 2)
  -- `P(g) · F_X(0, g) = 1` for every `g`
  have h₁ (g : MvPowerSeries (Fin 2) R) (hg : PowerSeries.HasSubst g) :
      PowerSeries.subst g F.invariantDifferential * PowerSeries.subst g F.derivZeroX = 1 := by
    rw [← PowerSeries.subst_mul hg, invariantDifferential_mul_subst_pderiv,
      ← PowerSeries.coe_substAlgHom hg, map_one]
  calc _ = PowerSeries.subst F.toPowerSeries F.invariantDifferential *
        (pderiv 0 F.toPowerSeries * PowerSeries.subst (X 0) F.derivZeroX) *
          PowerSeries.subst (X 0) F.invariantDifferential := by
        rw [mul_assoc, mul_assoc, mul_comm (PowerSeries.subst (X 0) F.derivZeroX), h₁ _ hX,
          mul_one]
    _ = _ := by rw [pderiv_mul_subst_derivZeroX, h₁ _ hF, one_mul]

/-- **The invariant differential is invariant in the second variable** for a commutative formal
group law: `P(F(X, Y)) · F_Y(X, Y) = P(Y)`, where `F_Y` is the partial derivative of `F` in its
second variable. -/
theorem subst_invariantDifferential_mul_pderiv_one [F.IsComm] :
    PowerSeries.subst F.toPowerSeries F.invariantDifferential * pderiv 1 F.toPowerSeries =
      PowerSeries.subst (X 1) F.invariantDifferential := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hsw : HasSubst (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) R) := HasSubst.X_X
  have hc : F.toPowerSeries =
      subst (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) R) F.toPowerSeries := IsComm.comm
  -- `F_Y(X, Y) = F_X(Y, X)`, differentiating `F(X, Y) = F(Y, X)` in `Y`
  have hY : pderiv 1 F.toPowerSeries = subst ![X 1, X 0] (pderiv 0 F.toPowerSeries) := by
    have := congrArg (pderiv (R := R) 1) hc
    rw [pderiv_subst hsw] at this
    simpa [Fin.sum_univ_two, pderiv_X_of_ne] using this
  -- and the invariance `P(F(X, Y)) · F_X(X, Y) = P(X)` read at `(Y, X)`
  have := congrArg (subst (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) R))
    F.subst_invariantDifferential_mul_pderiv
  rwa [subst_mul hsw, subst_powerSeriesSubst hsw hF, ← hc, ← hY,
    subst_powerSeriesSubst hsw (PowerSeries.HasSubst.X 0), subst_X hsw] at this

/-! ### The additive and multiplicative formal group laws -/

/-- The invariant differential of the additive formal group law `X + Y` is `dT`. -/
@[simp]
theorem invariantDifferential_𝔾ₐ : (𝔾ₐ (R := R)).invariantDifferential = 1 := by
  have ha : HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) := HasSubst.zero_X
  have hD : pderiv 0 (𝔾ₐ (R := R)).toPowerSeries = 1 := by simp [pderiv_X_of_ne]
  have h := (𝔾ₐ (R := R)).invariantDifferential_mul_subst_pderiv
  rwa [hD, ← coe_substAlgHom ha, map_one, mul_one] at h

/-- The invariant differential of the multiplicative formal group law `X + Y + XY` is
`dT / (1 + T) = (1 - T + T² - ⋯) dT`. -/
@[simp]
theorem invariantDifferential_𝔾ₘ :
    (𝔾ₘ (R := R)).invariantDifferential = PowerSeries.mk fun n ↦ (-1) ^ n := by
  have ha : HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) := HasSubst.zero_X
  have hD : pderiv 0 (𝔾ₘ (R := R)).toPowerSeries = 1 + X 1 := by simp [pderiv_X_of_ne]
  have h := (𝔾ₘ (R := R)).invariantDifferential_mul_subst_pderiv
  rw [hD, ← coe_substAlgHom ha, map_add, map_one, coe_substAlgHom, subst_X ha] at h
  -- `P(T) · (1 + T) = 1`, and `1 - T + T² - ⋯` is the inverse of `1 + T`
  refine left_inv_eq_right_inv (by simpa using h) ?_
  rw [mul_comm, PowerSeries.mk_neg_one_pow_mul_one_add_eq_one]

/-! ### The logarithm -/

variable [Algebra ℚ R]

/-- **The formal logarithm** `log_F(T) = ∫ P(T) dT` of a formal group law `F` over a `ℚ`-algebra:
the power series with zero constant coefficient whose derivative is the invariant differential
(Silverman IV.5). -/
noncomputable def log : PowerSeries R :=
  PowerSeries.mk fun n ↦ (n : ℚ)⁻¹ • PowerSeries.coeff (n - 1) F.invariantDifferential

/-- The coefficients of the logarithm: `log_F(T) = ∑_{n ≥ 1} (pₙ₋₁ / n) Tⁿ` for
`P(T) = ∑ₙ pₙ Tⁿ`. At `n = 0` the formula reads `0`, since `0⁻¹ = 0` in `ℚ`. -/
theorem coeff_log (n : ℕ) :
    PowerSeries.coeff n F.log = (n : ℚ)⁻¹ • PowerSeries.coeff (n - 1) F.invariantDifferential :=
  PowerSeries.coeff_mk _ _

/-- The logarithm has no constant term. -/
@[simp]
theorem constantCoeff_log : PowerSeries.constantCoeff F.log = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_log]
  simp

/-- The logarithm has linear coefficient `1`: `log_F(T) = T + ⋯`. -/
@[simp]
theorem coeff_one_log : PowerSeries.coeff 1 F.log = 1 := by
  simp [coeff_log]

/-- The derivative of the logarithm is the invariant differential. -/
@[simp]
theorem derivative_log : PowerSeries.derivative F.log = F.invariantDifferential := by
  ext n
  -- the factor `n + 1` of `coeff_derivative` is the rational scalar cancelling the `(n + 1)⁻¹` of
  -- `coeff_log`
  have hn (x : R) : x * (n + 1) = ((n + 1 : ℕ) : ℚ) • x := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm, Nat.cast_succ]
  rw [PowerSeries.coeff_derivative, coeff_log, hn, smul_smul]
  simp [mul_inv_cancel₀ (Nat.cast_add_one_ne_zero (R := ℚ) n)]

omit [Algebra ℚ R] in
/-- Every logarithm coefficient becomes integral after multiplication by its degree. -/
theorem natCast_mul_coeff_log_mem_range {S : Type*} [CommRing S] [Algebra ℚ S]
    (f : R →+* S) (n : ℕ) :
    n * PowerSeries.coeff n (F.map f).log ∈ Set.range f := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, by simp⟩
  · refine ⟨PowerSeries.coeff (n - 1) F.invariantDifferential, ?_⟩
    have h := congrArg (PowerSeries.coeff (n - 1)) (F.map f).derivative_log
    rw [PowerSeries.coeff_derivative, ← Nat.cast_add_one, Nat.sub_add_cancel hn,
      mul_comm] at h
    rw [← F.map_invariantDifferential f, PowerSeries.coeff_map] at h
    exact h.symm

/-- The invariant derivative of the formal logarithm is one. -/
@[simp]
theorem invariantDerivation_log : F.invariantDerivation F.log = 1 := by
  rw [invariantDerivation_apply, derivative_log, mul_comm,
    invariantDifferential_mul_subst_pderiv]

/-- **The logarithm is additive along `F`** (Silverman IV.5.2):
`log_F(F(X, Y)) = log_F(X) + log_F(Y)`. -/
theorem subst_toPowerSeries_log :
    PowerSeries.subst F.toPowerSeries F.log =
      PowerSeries.subst (X 0) F.log + PowerSeries.subst (X 1) F.log := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  have hb : HasSubst (![0, X 1] : Fin 2 → MvPowerSeries (Fin 2) R) := HasSubst.zero_X
  have : HasUniqueDiv R := .of_isTorsionFree ℚ R
  rw [← sub_eq_zero]
  apply eq_zero_of_pderiv_eq_zero_of_subst_eq_zero (i := 0)
  -- the derivative in `X` is `P(F(X, Y)) · F_X(X, Y) - P(X) = 0`
  · rw [map_sub, map_add, PowerSeries.pderiv_subst hF, PowerSeries.pderiv_subst (hX 0),
      PowerSeries.pderiv_subst (hX 1), derivative_log, subst_invariantDifferential_mul_pderiv,
      pderiv_X_self, pderiv_X_of_ne (by decide), mul_one, mul_zero, _root_.add_zero, sub_self]
  -- at `X = 0` it is `log_F(Y) - log_F(0) - log_F(Y) = 0`
  · have hX₀ : Function.update X 0 0 = (![0, X 1] : Fin 2 → MvPowerSeries (Fin 2) R) := by
      funext s; fin_cases s <;> simp
    rw [hX₀, subst_sub hb, subst_add hb, subst_powerSeriesSubst hb hF,
      subst_powerSeriesSubst hb (hX 0), subst_powerSeriesSubst hb (hX 1), F.zero_add (hX 1),
      subst_X hb, subst_X hb]
    simp

/-- **The logarithm is additive along `F`** at any pair of power series `f₀, f₁` that can be
substituted: `log_F(F(f₀, f₁)) = log_F(f₀) + log_F(f₁)`. -/
theorem subst_subst_toPowerSeries_log {σ : Type*} {f₀ f₁ : MvPowerSeries σ R}
    (h₀ : PowerSeries.HasSubst f₀) (h₁ : PowerSeries.HasSubst f₁) :
    PowerSeries.subst (subst ![f₀, f₁] F.toPowerSeries) F.log =
      PowerSeries.subst f₀ F.log + PowerSeries.subst f₁ F.log :=
  powerSeriesSubst_subst_finTwo_eq_add
    (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff) F.subst_toPowerSeries_log
    h₀ h₁

/-- **The additive power series along `F` are the multiples of the logarithm**: a power series
`g` satisfies `g(F(X, Y)) = g(X) + g(Y)` exactly when `g = c • log_F` for some `c : R`. -/
theorem subst_toPowerSeries_eq_add_iff {g : PowerSeries R} :
    PowerSeries.subst F.toPowerSeries g =
        PowerSeries.subst (X 0) g + PowerSeries.subst (X 1) g ↔
      ∃ c : R, g = c • F.log := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  refine ⟨fun h ↦ ⟨PowerSeries.coeff 1 g, ?_⟩, ?_⟩
  · have : HasUniqueDiv R := .of_isTorsionFree ℚ R
    -- `g(0) = g(0) + g(0)`
    have hg₀ : PowerSeries.constantCoeff g = 0 := by
      have := congrArg constantCoeff h
      rw [map_add, PowerSeries.constantCoeff_subst_of_constantCoeff_zero F.zero_constantCoeff,
        PowerSeries.constantCoeff_subst_of_constantCoeff_zero (constantCoeff_X _),
        PowerSeries.constantCoeff_subst_of_constantCoeff_zero (constantCoeff_X _)] at this
      simpa using this
    -- differentiate in `X` and set `X = 0`: `g'(T) · F_X(0, T) = g'(0)`
    have hd := congrArg (pderiv 0) h
    rw [map_add, PowerSeries.pderiv_subst hF, PowerSeries.pderiv_subst (hX 0),
      PowerSeries.pderiv_subst (hX 1), pderiv_X_self, pderiv_X_of_ne (by decide), mul_one,
      mul_zero, _root_.add_zero] at hd
    have ha : HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) := HasSubst.zero_X
    have := congrArg (subst (![0, PowerSeries.X] : Fin 2 → PowerSeries R)) hd
    rw [subst_mul ha, subst_powerSeriesSubst ha hF, subst_powerSeriesSubst ha (hX 0),
      F.zero_add PowerSeries.HasSubst.X', subst_X ha, PowerSeries.X_subst] at this
    -- so `g' = g'(0) · P`
    have hg' : PowerSeries.derivative g = PowerSeries.coeff 1 g • F.invariantDifferential := by
      rw [Matrix.cons_val_zero, PowerSeries.subst_zero_eq_C_constantCoeff,
        Algebra.algebraMap_self, map_id, RingHom.id_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative] at this
      have hP := F.invariantDifferential_mul_subst_pderiv
      calc PowerSeries.derivative g
          _ = PowerSeries.derivative g * subst ![0, PowerSeries.X] (pderiv 0 F.toPowerSeries) *
              F.invariantDifferential := by
            rw [mul_assoc, mul_comm _ F.invariantDifferential, hP, mul_one]
          _ = _ := by
            rw [this, MvPowerSeries.smul_eq_C_mul]
            simp
    refine PowerSeries.derivative.ext ?_ (by simp [hg₀])
    rw [hg', Derivation.map_smul, derivative_log]
  · rintro ⟨c, rfl⟩
    rw [PowerSeries.subst_smul hF, PowerSeries.subst_smul (hX 0), PowerSeries.subst_smul (hX 1),
      subst_toPowerSeries_log, smul_add]

/-- **The formal exponential** `exp_F` of a formal group law `F` over a `ℚ`-algebra: the
compositional inverse of the logarithm, which exists since `log_F(T) = T + ⋯`. -/
noncomputable def exp : PowerSeries R :=
  F.log.substInvOfIsUnit (by simp)

/-- The exponential has no constant term. -/
@[simp]
theorem constantCoeff_exp : PowerSeries.constantCoeff F.exp = 0 := by
  simp [exp]

/-- The exponential has linear coefficient `1`: `exp_F(T) = T + ⋯`. -/
@[simp]
theorem coeff_one_exp : PowerSeries.coeff 1 F.exp = 1 := by
  simp [exp]

/-- `log_F(exp_F(T)) = T`. -/
@[simp]
theorem subst_exp_log : PowerSeries.subst F.exp F.log = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_right _ F.constantCoeff_log _

/-- `exp_F(log_F(T)) = T`. -/
@[simp]
theorem subst_log_exp : PowerSeries.subst F.log F.exp = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_left _ F.constantCoeff_log _

/-- The exponential is the only right inverse of the logarithm: if `log_F(Q(T)) = T` then
`Q = exp_F`. -/
theorem eq_exp_of_subst_log_eq_X {Q : PowerSeries R} (hQ : PowerSeries.HasSubst Q)
    (h : PowerSeries.subst Q F.log = PowerSeries.X) : Q = F.exp := by
  simpa only [exp] using F.log.eq_substInvOfIsUnit_of_subst_eq_X F.constantCoeff_log (by simp) hQ h

/-- **The logarithm commutes with base change**: applying a ring homomorphism `f : R →+* S` of
`ℚ`-algebras to the coefficients of `log_F` gives the logarithm of `F.map f`. -/
@[simp]
theorem map_log {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S) :
    F.log.map f = (F.map f).log := by
  ext n
  rw [PowerSeries.coeff_map, coeff_log, coeff_log, map_rat_smul, ← map_invariantDifferential,
    PowerSeries.coeff_map]

/-- **The exponential commutes with base change**: applying a ring homomorphism `f : R →+* S` of
`ℚ`-algebras to the coefficients of `exp_F` gives the exponential of `F.map f`. -/
@[simp]
theorem map_exp {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S) :
    F.exp.map f = (F.map f).exp := by
  rw [exp, PowerSeries.map_substInvOfIsUnit f F.constantCoeff_log, exp]
  congr 1
  exact F.map_log f

/-- The formal exponential solves the invariant differential equation
`exp_F'(T) = F_X(0, exp_F(T))`. -/
theorem derivative_exp :
    PowerSeries.derivative F.exp =
      PowerSeries.subst F.exp
        (subst ![(0 : PowerSeries R), PowerSeries.X] (pderiv 0 F.toPowerSeries)) := by
  have hsub := PowerSeries.HasSubst.of_constantCoeff_zero' F.constantCoeff_exp
  have hd : PowerSeries.subst F.exp F.invariantDifferential *
      PowerSeries.derivative F.exp = 1 := by
    rw [← F.derivative_log, ← PowerSeries.derivative_subst hsub, F.subst_exp_log]
    exact PowerSeries.derivative_X
  have hi := congrArg (PowerSeries.subst F.exp) F.invariantDifferential_mul_subst_pderiv
  rw [PowerSeries.subst_mul hsub, PowerSeries.subst_one hsub] at hi
  calc
    PowerSeries.derivative F.exp =
        (PowerSeries.subst F.exp F.invariantDifferential *
          PowerSeries.subst F.exp
            (subst ![(0 : PowerSeries R), PowerSeries.X] (pderiv 0 F.toPowerSeries))) *
          PowerSeries.derivative F.exp := by rw [hi, one_mul]
    _ = _ := by rw [mul_right_comm, hd, one_mul]

/-- **A formal group law over a `ℚ`-algebra is strictly isomorphic to the additive one**
(Silverman IV.5.2): `F(X, Y) = exp_F(log_F(X) + log_F(Y))`. -/
theorem toPowerSeries_eq_subst_exp :
    F.toPowerSeries =
      PowerSeries.subst (PowerSeries.subst (X 0) F.log + PowerSeries.subst (X 1) F.log) F.exp := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hlog := PowerSeries.HasSubst.of_constantCoeff_zero' F.constantCoeff_log
  rw [← subst_toPowerSeries_log, ← PowerSeries.subst_comp_subst_apply hlog hF, subst_log_exp,
    PowerSeries.subst_X hF]

/-- The logarithm, bundled as a homomorphism to the additive formal group. -/
noncomputable def logHom : TauCeti.FormalGroupHom F (𝔾ₐ (R := R)) where
  toPowerSeries := F.log
  zero_constantCoeff := F.constantCoeff_log
  hom := (TauCeti.FormalGroupHom.hom_additive_iff F.constantCoeff_log).mpr
    F.subst_toPowerSeries_log

@[simp]
theorem logHom_toPowerSeries : F.logHom.toPowerSeries = F.log := (rfl)

/-- The normalized logarithm is a strict isomorphism from `F` to the additive formal group,
with the formal exponential as its inverse. -/
noncomputable def logIso : TauCeti.FormalGroupIso F (𝔾ₐ (R := R)) :=
  F.logHom.toIso (by simp)

/-- The exponential, bundled as a homomorphism from the additive formal group. -/
noncomputable def expHom : TauCeti.FormalGroupHom (𝔾ₐ (R := R)) F :=
  F.logIso.invHom

@[simp]
theorem expHom_toPowerSeries : F.expHom.toPowerSeries = F.exp := by
  simp only [expHom, logIso, TauCeti.FormalGroupHom.toIso_invHom_toPowerSeries,
    logHom, exp]

@[simp]
theorem logIso_toHom : F.logIso.toHom = F.logHom := by
  simp only [logIso, TauCeti.FormalGroupHom.toIso_toHom]

@[simp]
theorem logIso_invHom : F.logIso.invHom = F.expHom := (rfl)

instance : F.logIso.IsStrict where
  coeff_one := by simpa only [logIso_toHom, logHom_toPowerSeries] using F.coeff_one_log

variable {F} in
/-- A homomorphism to the additive group is its linear coefficient times the logarithm:
`f(X) = f'(0) · log_F(X)`. -/
theorem _root_.TauCeti.FormalGroupHom.toPowerSeries_eq_coeff_one_smul_log
    (f : TauCeti.FormalGroupHom F (𝔾ₐ (R := R))) :
    f.toPowerSeries = PowerSeries.coeff 1 f.toPowerSeries • F.log := by
  have h := (TauCeti.FormalGroupHom.hom_additive_iff f.zero_constantCoeff).mp f.hom
  obtain ⟨c, hc⟩ := F.subst_toPowerSeries_eq_add_iff.mp h
  have hc₁ := congrArg (PowerSeries.coeff 1) hc
  simp only [map_smul, coeff_one_log, smul_eq_mul, mul_one] at hc₁
  rwa [hc₁]

/-- A homomorphism to the additive group with linear coefficient one is the logarithm. -/
theorem eq_logHom_of_coeff_one (f : TauCeti.FormalGroupHom F (𝔾ₐ (R := R)))
    (hf : PowerSeries.coeff 1 f.toPowerSeries = 1) : f = F.logHom := by
  apply TauCeti.FormalGroupHom.ext
  rw [f.toPowerSeries_eq_coeff_one_smul_log, hf, one_smul, logHom_toPowerSeries]

/-- The logarithm is the unique strict isomorphism from `F` to the additive formal group. -/
theorem eq_logIso (f : TauCeti.FormalGroupIso F (𝔾ₐ (R := R))) [f.IsStrict] :
    f = F.logIso := by
  apply TauCeti.FormalGroupIso.ext
  simpa only [logIso_toHom] using
    F.eq_logHom_of_coeff_one f.toHom (TauCeti.FormalGroupIso.IsStrict.coeff_one (f := f))

/-! ### The logarithms of the additive and multiplicative formal group laws -/

/-- The logarithm of the additive formal group law is `log_{𝔾ₐ}(T) = T`. -/
@[simp]
theorem log_𝔾ₐ : (𝔾ₐ (R := R)).log = PowerSeries.X := by
  have : HasUniqueDiv R := .of_isTorsionFree ℚ R
  exact PowerSeries.derivative.ext (by simp) (by simp)

/-- The exponential of the additive formal group law is `exp_{𝔾ₐ}(T) = T`. -/
@[simp]
theorem exp_𝔾ₐ : (𝔾ₐ (R := R)).exp = PowerSeries.X := by
  simpa [PowerSeries.X_subst] using (𝔾ₐ (R := R)).subst_log_exp

/-- The logarithm of the multiplicative formal group law is the logarithm series
`log_{𝔾ₘ}(T) = log(1 + T) = T - T² / 2 + T³ / 3 - ⋯`. -/
@[simp]
theorem log_𝔾ₘ : (𝔾ₘ (R := R)).log = PowerSeries.log R := by
  have : HasUniqueDiv R := .of_isTorsionFree ℚ R
  exact PowerSeries.derivative.ext (by simp [PowerSeries.derivative_log]) (by simp)

/-- The exponential of the multiplicative formal group law is `exp_{𝔾ₘ}(T) = e^T - 1`. -/
@[simp]
theorem exp_𝔾ₘ : (𝔾ₘ (R := R)).exp = PowerSeries.exp R - 1 := by
  have hlog {Q : PowerSeries R} := (PowerSeries.log R).eq_substInvOfIsUnit_of_subst_eq_X (Q := Q)
    PowerSeries.constantCoeff_log (by simp)
  rw [hlog (PowerSeries.HasSubst.of_constantCoeff_zero' (𝔾ₘ (R := R)).constantCoeff_exp)
    (by rw [← log_𝔾ₘ, subst_exp_log]), hlog PowerSeries.HasSubst.exp_sub_one
    (PowerSeries.subst_log_exp_sub_one R)]

end FormalGroup

namespace TauCeti.FormalGroupHom

open MvPowerSeries

variable {R : Type*} [CommRing R] {F G : FormalGroup R}

/-- A homomorphism of formal groups has zero derivative exactly when its tangent map is zero.
This holds over arbitrary coefficient rings, without commutativity of the formal groups. -/
theorem derivative_eq_zero_iff (f : FormalGroupHom F G) :
    PowerSeries.derivative f.toPowerSeries = 0 ↔ PowerSeries.coeff 1 f.toPowerSeries = 0 := by
  constructor
  · intro h
    have := congrArg (PowerSeries.coeff 0) h
    simpa [PowerSeries.coeff_derivative] using this
  · intro hf
    have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
    have ha : HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) := HasSubst.zero_X
    have hd := congrArg (pderiv (R := R) 0) f.hom
    rw [PowerSeries.pderiv_subst hF, pderiv_subst (.toMvPowerSeries f.zero_constantCoeff),
      Fin.sum_univ_two] at hd
    have h := congrArg (subst (![0, PowerSeries.X] : Fin 2 → PowerSeries R)) hd
    simp only [PowerSeries.toMvPowerSeries_eq_subst,
      PowerSeries.pderiv_subst (PowerSeries.HasSubst.X _), pderiv_X_self,
      pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0), mul_one, mul_zero, add_zero] at h
    rw [subst_mul ha, subst_powerSeriesSubst ha hF, F.zero_add PowerSeries.HasSubst.X',
      PowerSeries.X_subst, subst_mul ha,
      subst_powerSeriesSubst ha (PowerSeries.HasSubst.X 0), subst_X ha,
      Matrix.cons_val_zero, PowerSeries.subst_zero_eq_C_constantCoeff] at h
    simp only [Algebra.algebraMap_self,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative,
      zero_add, zero_mul, Nat.cast_zero, hf, map_zero, mul_zero] at h
    have hP := F.invariantDifferential_mul_subst_pderiv
    calc PowerSeries.derivative f.toPowerSeries
        = (PowerSeries.derivative f.toPowerSeries *
          subst ![0, PowerSeries.X] (pderiv 0 F.toPowerSeries)) *
            F.invariantDifferential := by
          rw [mul_assoc, mul_comm _ F.invariantDifferential, hP, mul_one]
      _ = 0 := by rw [h, zero_mul]

end TauCeti.FormalGroupHom
