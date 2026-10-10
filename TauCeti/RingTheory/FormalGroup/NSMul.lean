/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Logarithm
-- Proof-only: splitting a power series into its truncation and its tail.
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Multiplication by `n` on a formal group law

Let `F(X, Y)` be a one-dimensional formal group law over a commutative ring `R`. Multiplication by
`n` on `F` is the power series `[n]_F(T)` with `[0]_F(T) = 0` and `[n + 1]_F(T) = F([n]_F(T), T)`:
it is `n` times the tautological point `T` in Mathlib's monoid `F.Point Unit` of power-series
points of `F`.

When `F` is commutative, `[n]_F` multiplies the invariant differential `ω = P(T) dT` by `n`, by
the chain rule and the invariance of `ω` in both variables
(`FormalGroup.subst_invariantDifferential_mul_pderiv` and
`FormalGroup.subst_invariantDifferential_mul_pderiv_one`):

  `P([n]_F(T)) · [n]_F'(T) = n · P(T)`.

Since `P` has constant coefficient `1`, `P([n]_F(T))` is a unit, so the derivative of `[n]_F` is
divisible by `n`. Reading this coefficientwise, `n` divides the coefficient of `Tᵏ` in `[n]_F`
for every `k` coprime to `n`. For a prime `p` this gives the shape of `[p]_F` that controls
`p`-torsion in formal groups:

  `[p]_F(T) = p T u(T) + Tᵖ h(T)` with `u(0) = 1`

(Silverman IV.4.4 records the stronger `[p]_F(T) = p f(T) + g(Tᵖ)`). At a nonzero point `t` of a
complete local domain, the first term can only cancel the second if `p` is divisible by
`t ^ (p - 1)`; this is how `p`-torsion in the points of a formal group is bounded (Silverman
IV.6.1).

## Main definitions

* `FormalGroup.nsmulSeries`: the multiplication-by-`n` series `[n]_F(T)`.

## Main results

* `FormalGroup.nsmulSeries_succ`: `[n + 1]_F(T) = F([n]_F(T), T)`.
* `FormalGroup.nsmulSeries_add`: `[m + n]_F(T) = F([m]_F(T), [n]_F(T))`.
* `FormalGroup.nsmulSeries_mul`: `[m n]_F(T) = [m]_F([n]_F(T))`.
* `FormalGroup.subst_nsmulSeries_invariantDifferential_mul_derivative`:
  `P([n]_F(T)) · [n]_F'(T) = n · P(T)`.
* `FormalGroup.coeff_one_nsmulSeries`: `[n]_F(T) = n T + ⋯`.
* `FormalGroup.natCast_dvd_derivative_nsmulSeries`: `n` divides the derivative of `[n]_F`.
* `FormalGroup.natCast_dvd_coeff_nsmulSeries`: `n` divides the coefficient of `Tᵏ` in `[n]_F`
  for `k` coprime to `n`.
* `FormalGroup.exists_nsmulSeries_eq_of_prime`: `[p]_F(T) = p T u(T) + Tᵖ h(T)` with `u(0) = 1`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.2, IV.4 and IV.6.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

/-- The tautological point `T` of `F`, with values in the power series ring `R⟦T⟧`. -/
private noncomputable def tautologicalPoint : F.Point Unit :=
  ⟨PowerSeries.X, PowerSeries.HasSubst.X'⟩

private theorem val_tautologicalPoint : F.tautologicalPoint.val = PowerSeries.X := (rfl)

/-- **Multiplication by `n`** on a formal group law `F`: the power series `[n]_F(T)`, which is `n`
times the tautological point `T` in the monoid `F.Point Unit` of power-series points of `F`. -/
noncomputable def nsmulSeries (n : ℕ) : PowerSeries R :=
  (n • F.tautologicalPoint).val

@[simp]
theorem nsmulSeries_zero : F.nsmulSeries 0 = 0 := by
  rw [nsmulSeries, zero_nsmul, zero_apply]

/-- `[n + 1]_F(T) = F([n]_F(T), T)`. -/
theorem nsmulSeries_succ (n : ℕ) :
    F.nsmulSeries (n + 1) = subst ![F.nsmulSeries n, PowerSeries.X] F.toPowerSeries := by
  rw [nsmulSeries, nsmulSeries, succ_nsmul, add_apply, val_tautologicalPoint]

/-- `[m + n]_F(T) = F([m]_F(T), [n]_F(T))`. -/
theorem nsmulSeries_add (m n : ℕ) :
    F.nsmulSeries (m + n) = subst ![F.nsmulSeries m, F.nsmulSeries n] F.toPowerSeries := by
  rw [nsmulSeries, add_nsmul, add_apply]
  rfl

@[simp]
theorem nsmulSeries_one : F.nsmulSeries 1 = PowerSeries.X := by
  rw [nsmulSeries_succ, nsmulSeries_zero, F.zero_add PowerSeries.HasSubst.X']

/-- `[n]_F(T)` has no constant term. -/
@[simp]
theorem constantCoeff_nsmulSeries (n : ℕ) :
    PowerSeries.constantCoeff (F.nsmulSeries n) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha : ∀ s, constantCoeff ((![F.nsmulSeries n, PowerSeries.X] :
        Fin 2 → PowerSeries R) s) = 0 := fun s ↦ by
      fin_cases s
      · exact ih
      · exact PowerSeries.constantCoeff_X
    rw [nsmulSeries_succ]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha F.zero_constantCoeff

/-- `[m n]_F(T) = [m]_F([n]_F(T))`: multiplication by `m n` is the composite of multiplication by
`m` and by `n`. -/
theorem nsmulSeries_mul (m n : ℕ) :
    F.nsmulSeries (m * n) = PowerSeries.subst (F.nsmulSeries n) (F.nsmulSeries m) := by
  have hn : PowerSeries.HasSubst (F.nsmulSeries n) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (F.constantCoeff_nsmulSeries n)
  induction m with
  | zero => rw [zero_mul, nsmulSeries_zero, ← PowerSeries.coe_substAlgHom hn, map_zero]
  | succ m ih =>
    have ha : HasSubst ![F.nsmulSeries m, PowerSeries.X] :=
      hasSubst_of_constantCoeff_zero fun s ↦ by
        fin_cases s
        · exact F.constantCoeff_nsmulSeries m
        · exact PowerSeries.constantCoeff_X
    -- `[m n + n]_F(T) = F([m]_F([n]_F(T)), [n]_F(T))`, and substituting `[n]_F(T)` into
    -- `[m + 1]_F(T) = F([m]_F(T), T)` gives the same
    rw [add_mul, one_mul, nsmulSeries_add, ih, nsmulSeries_succ,
      PowerSeries.subst_def _ (subst _ _), subst_comp_subst_apply ha hn.const]
    congr 1
    funext s
    fin_cases s
    · rfl
    · exact (PowerSeries.subst_X hn).symm

/-- **Multiplication by `n` multiplies the invariant differential by `n`** (Silverman IV.4.3):
`P([n]_F(T)) · [n]_F'(T) = n · P(T)` for a commutative formal group law `F`. -/
theorem subst_nsmulSeries_invariantDifferential_mul_derivative [F.IsComm] (n : ℕ) :
    PowerSeries.subst (F.nsmulSeries n) F.invariantDifferential *
        PowerSeries.derivative (F.nsmulSeries n) =
      (n : PowerSeries R) * F.invariantDifferential := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
    set a : Fin 2 → PowerSeries R := ![F.nsmulSeries n, PowerSeries.X]
    have ha : HasSubst a := hasSubst_of_constantCoeff_zero fun s ↦ by
      fin_cases s
      · exact F.constantCoeff_nsmulSeries n
      · exact PowerSeries.constantCoeff_X
    -- the chain rule for `[n + 1]_F(T) = F([n]_F(T), T)`
    have hd : PowerSeries.derivative (subst a F.toPowerSeries) =
        subst a (pderiv 0 F.toPowerSeries) * PowerSeries.derivative (F.nsmulSeries n) +
          subst a (pderiv 1 F.toPowerSeries) := by
      -- `PowerSeries.derivative` is by definition the partial derivative in the unique variable
      change pderiv () (subst a F.toPowerSeries) = _
      rw [pderiv_subst ha, Fin.sum_univ_two]
      simp [a, PowerSeries.derivative, PowerSeries.X]
    have hP (i : Fin 2) : subst a (PowerSeries.subst (X (R := R) i) F.invariantDifferential) =
        PowerSeries.subst (a i) F.invariantDifferential := by
      rw [subst_powerSeriesSubst ha (PowerSeries.HasSubst.X i), subst_X ha]
    rw [nsmulSeries_succ, ← subst_powerSeriesSubst ha hF, hd, mul_add, ← mul_assoc,
      ← subst_mul ha, ← subst_mul ha, subst_invariantDifferential_mul_pderiv,
      subst_invariantDifferential_mul_pderiv_one, hP, hP]
    simp only [a, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [ih, PowerSeries.X_subst]
    push_cast
    ring

/-- `P([n]_F(T))` is a unit, its constant coefficient being `1`. -/
private theorem isUnit_subst_nsmulSeries_invariantDifferential (n : ℕ) :
    IsUnit (PowerSeries.subst (F.nsmulSeries n) F.invariantDifferential) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_eq,
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero (F.constantCoeff_nsmulSeries n)]
  simp

/-- **`[n]_F(T)` has linear coefficient `n`**: `[n]_F(T) = n T + ⋯`. -/
@[simp]
theorem coeff_one_nsmulSeries [F.IsComm] (n : ℕ) :
    PowerSeries.coeff 1 (F.nsmulSeries n) = n := by
  have h := congrArg PowerSeries.constantCoeff
    (F.subst_nsmulSeries_invariantDifferential_mul_derivative n)
  rw [map_mul, map_mul, PowerSeries.constantCoeff_eq,
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero
    (F.constantCoeff_nsmulSeries n), ← PowerSeries.coeff_zero_eq_constantCoeff_apply
    (PowerSeries.derivative _), PowerSeries.coeff_derivative] at h
  simpa using h

/-- **The derivative of `[n]_F` is divisible by `n`**, for a commutative formal group law `F`. -/
theorem natCast_dvd_derivative_nsmulSeries [F.IsComm] (n : ℕ) :
    (n : PowerSeries R) ∣ PowerSeries.derivative (F.nsmulSeries n) := by
  rw [← (F.isUnit_subst_nsmulSeries_invariantDifferential n).dvd_mul_left,
    F.subst_nsmulSeries_invariantDifferential_mul_derivative]
  exact dvd_mul_right _ _

/-- **`n` divides the coefficients of `[n]_F` in degrees coprime to `n`**, for a commutative
formal group law `F`. -/
theorem natCast_dvd_coeff_nsmulSeries [F.IsComm] {n k : ℕ} (hk : k.Coprime n) :
    (n : R) ∣ PowerSeries.coeff k (F.nsmulSeries n) := by
  rcases k with _ | k
  · simp
  obtain ⟨g, hg⟩ := F.natCast_dvd_derivative_nsmulSeries n
  have h := congrArg (PowerSeries.coeff k) hg
  rw [PowerSeries.coeff_derivative, ← map_natCast PowerSeries.C, PowerSeries.coeff_C_mul] at h
  have hcop : IsCoprime (n : R) ((k + 1 : ℕ) : R) := by
    simpa using (Nat.isCoprime_iff_coprime.mpr hk.symm).intCast (R := R)
  refine hcop.dvd_of_dvd_mul_right ⟨PowerSeries.coeff k g, ?_⟩
  rw [← h]
  push_cast
  ring

/-- **The shape of multiplication by a prime** (compare Silverman IV.4.4): for a commutative formal
group law `F` and a prime `p`, `[p]_F(T) = p T u(T) + Tᵖ h(T)` for power series `u` and `h` with
`u(0) = 1`. -/
theorem exists_nsmulSeries_eq_of_prime [F.IsComm] {p : ℕ} (hp : p.Prime) :
    ∃ u h : PowerSeries R, PowerSeries.constantCoeff u = 1 ∧
      F.nsmulSeries p = (p : PowerSeries R) * PowerSeries.X * u + PowerSeries.X ^ p * h := by
  -- the coefficients of `[p]_F` below degree `p` are multiples of `p`
  have hdvd : ∀ k, 0 < k → k < p → ∃ c : R, PowerSeries.coeff k (F.nsmulSeries p) = p * c :=
    fun k hk₀ hkp ↦ F.natCast_dvd_coeff_nsmulSeries
      ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (Nat.not_dvd_of_pos_of_lt hk₀ hkp))))
  choose! c hc using hdvd
  -- split `[p]_F` into its terms of degree below `p` and its tail
  refine ⟨PowerSeries.mk fun j ↦ if j = 0 then 1 else if j + 1 < p then c (j + 1) else 0,
    PowerSeries.mk fun j ↦ PowerSeries.coeff (j + p) (F.nsmulSeries p), by simp, ?_⟩
  conv_lhs => rw [(F.nsmulSeries p).eq_X_pow_mul_shift_add_trunc p, add_comm]
  congr 1
  ext k
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, mul_assoc, ← map_natCast PowerSeries.C,
    PowerSeries.coeff_C_mul]
  rcases k with _ | j
  · simp [hp.pos]
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hp.one_lt]
  rcases lt_or_ge (j + 1) p with hjp | hjp
  · simp [hj.ne', hjp, hc (j + 1) (by omega) hjp]
  · simp [hj.ne', hjp.not_gt]

end FormalGroup
