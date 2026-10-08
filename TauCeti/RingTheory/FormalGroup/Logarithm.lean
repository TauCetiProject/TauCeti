/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.RingTheory.MvPowerSeries.Derivative
public import TauCeti.RingTheory.MvPowerSeries.Substitution

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

## Main definitions

* `FormalGroup.invariantDifferential`: the coefficient `P(T)` of the normalised invariant
  differential `ω = P(T) dT` of `F`.
* `FormalGroup.log`: the formal logarithm of `F`, over a `ℚ`-algebra.
* `FormalGroup.exp`: the formal exponential of `F`, the compositional inverse of `FormalGroup.log`.

## Main results

* `FormalGroup.subst_invariantDifferential_mul_pderiv`: **the invariant differential is
  invariant**, `P(F(X, Y)) · F_X(X, Y) = P(X)`.
* `FormalGroup.subst_toPowerSeries_log`: `log_F(F(X, Y)) = log_F(X) + log_F(Y)`.
* `FormalGroup.subst_subst_toPowerSeries_log`: the same at any pair of power series that can be
  substituted.
* `FormalGroup.subst_toPowerSeries_eq_add_iff`: a power series `g` satisfies
  `g(F(X, Y)) = g(X) + g(Y)` exactly when it is a scalar multiple of `log_F`.
* `FormalGroup.subst_exp_log` and `FormalGroup.subst_log_exp`: `log_F` and `exp_F` are inverse.
* `FormalGroup.toPowerSeries_eq_subst_exp`: `F(X, Y) = exp_F(log_F(X) + log_F(Y))`.

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

private theorem hasSubst_zero_X : HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) :=
  hasSubst_of_constantCoeff_zero fun s ↦ by fin_cases s <;> simp [PowerSeries.X]

private theorem constantCoeff_derivZeroX : PowerSeries.constantCoeff F.derivZeroX = 1 := by
  have hD : constantCoeff (pderiv 0 F.toPowerSeries) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, _root_.zero_add, F.lin_coeff_X]
    simp
  have ha := hasSubst_zero_X (R := R)
  -- `F_X - 1` has zero constant coefficient, and so does its substitution
  have := constantCoeff_subst_eq_zero ha (fun s ↦ by fin_cases s <;> simp [PowerSeries.X])
    (f := pderiv 0 F.toPowerSeries - 1) (by simp [hD])
  rwa [← coe_substAlgHom ha, map_sub, map_one, map_sub, map_one, sub_eq_zero,
    coe_substAlgHom] at this

/-- Substituting `g` into `F_X(0, T)` is substituting `(0, g)` into `F_X`. -/
private theorem subst_derivZeroX {σ : Type*} {g : MvPowerSeries σ R}
    (hg : PowerSeries.HasSubst g) :
    PowerSeries.subst g F.derivZeroX = subst ![0, g] (pderiv 0 F.toPowerSeries) := by
  rw [derivZeroX, PowerSeries.subst_def, subst_comp_subst_apply hasSubst_zero_X hg.const]
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

/-- **The logarithm is additive along `F`** (Silverman IV.5.2):
`log_F(F(X, Y)) = log_F(X) + log_F(Y)`. -/
theorem subst_toPowerSeries_log :
    PowerSeries.subst F.toPowerSeries F.log =
      PowerSeries.subst (X 0) F.log + PowerSeries.subst (X 1) F.log := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  have hb : HasSubst (![0, X 1] : Fin 2 → MvPowerSeries (Fin 2) R) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by fin_cases s <;> simp
  have : IsAddTorsionFree R := .of_isTorsionFree ℚ R
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
      PowerSeries.subst f₀ F.log + PowerSeries.subst f₁ F.log := by
  have hf : HasSubst ![f₀, f₁] :=
    hasSubst_of_constantCoeff_nilpotent fun s ↦ by fin_cases s <;> simpa
  have := congrArg (subst ![f₀, f₁]) F.subst_toPowerSeries_log
  rwa [subst_add hf, subst_powerSeriesSubst hf (PowerSeries.HasSubst.X _),
    subst_powerSeriesSubst hf (PowerSeries.HasSubst.X _),
    subst_powerSeriesSubst hf (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    subst_X hf, subst_X hf] at this

/-- **The additive power series along `F` are the multiples of the logarithm**: a power series
`g` satisfies `g(F(X, Y)) = g(X) + g(Y)` exactly when `g = c • log_F` for some `c : R`. -/
theorem subst_toPowerSeries_eq_add_iff {g : PowerSeries R} :
    PowerSeries.subst F.toPowerSeries g =
        PowerSeries.subst (X 0) g + PowerSeries.subst (X 1) g ↔
      ∃ c : R, g = c • F.log := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hX (i : Fin 2) := PowerSeries.HasSubst.X (S := R) i
  refine ⟨fun h ↦ ⟨PowerSeries.coeff 1 g, ?_⟩, ?_⟩
  · have : IsAddTorsionFree R := .of_isTorsionFree ℚ R
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
    have := congrArg (subst (![0, PowerSeries.X] : Fin 2 → PowerSeries R)) hd
    rw [subst_mul hasSubst_zero_X, subst_powerSeriesSubst hasSubst_zero_X hF,
      subst_powerSeriesSubst hasSubst_zero_X (hX 0), F.zero_add PowerSeries.HasSubst.X',
      subst_X hasSubst_zero_X, PowerSeries.X_subst] at this
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

/-- **A formal group law over a `ℚ`-algebra is strictly isomorphic to the additive one**
(Silverman IV.5.2): `F(X, Y) = exp_F(log_F(X) + log_F(Y))`. -/
theorem toPowerSeries_eq_subst_exp :
    F.toPowerSeries =
      PowerSeries.subst (PowerSeries.subst (X 0) F.log + PowerSeries.subst (X 1) F.log) F.exp := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hlog := PowerSeries.HasSubst.of_constantCoeff_zero' F.constantCoeff_log
  rw [← subst_toPowerSeries_log, ← PowerSeries.subst_comp_subst_apply hlog hF, subst_log_exp,
    PowerSeries.subst_X hF]

end FormalGroup
