/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Logarithm

/-!
# Base change of formal group laws

Mathlib constructs the base change `F.map f` of a formal group law by applying `f` to every
coefficient. This file supplies its basic functorial API: identity and composition laws,
preservation of commutativity, and compatibility with the additive and multiplicative formal
group laws. The normalized invariant differential, logarithm and exponential also commute with
coefficient maps. In particular, integral coefficients of the invariant differential remain
integral after extending the coefficient ring.

## Main results

* `FormalGroup.map_id` and `FormalGroup.map_comp`: base change is functorial.
* `FormalGroup.isComm_map`: base change preserves commutativity.
* `FormalGroup.map_𝔾ₐ` and `FormalGroup.map_𝔾ₘ`: the standard laws are stable under base change.
* `FormalGroup.map_invariantDifferential`, `FormalGroup.map_log` and `FormalGroup.map_exp`:
  the differential and the two series commute with coefficient maps.
* `FormalGroup.natCast_mul_coeff_log_map`: the degree clears a logarithm coefficient's denominator.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4–5.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- Base-changing a formal group law along the identity homomorphism changes nothing. -/
@[simp]
theorem map_id (F : FormalGroup R) : F.map (RingHom.id R) = F := by
  ext
  simp

/-- Successive base changes of a formal group law agree with base change along the composite. -/
@[simp]
theorem map_comp (F : FormalGroup R) (f : R →+* S) (g : S →+* T) :
    (F.map f).map g = F.map (g.comp f) := by
  ext
  simp

/-- A base change of a commutative formal group law is commutative. -/
instance isComm_map (F : FormalGroup R) [F.IsComm] (f : R →+* S) : (F.map f).IsComm where
  comm := by
    have h := congrArg (MvPowerSeries.map f) (IsComm.comm (F := F))
    rw [MvPowerSeries.map_subst HasSubst.X_X] at h
    rw [map_toPowerSeries]
    calc
      _ = subst (fun i ↦ MvPowerSeries.map f (![X 1, X 0] i))
          (MvPowerSeries.map f F.toPowerSeries) := h
      _ = _ := by
        congr 1
        funext i
        fin_cases i <;> simp

/-- The additive formal group law is unchanged by base change. -/
@[simp]
theorem map_𝔾ₐ (f : R →+* S) : (𝔾ₐ (R := R)).map f = 𝔾ₐ := by
  ext
  simp [FormalGroup.𝔾ₐ]

/-- The multiplicative formal group law is unchanged by base change. -/
@[simp]
theorem map_𝔾ₘ (f : R →+* S) : (𝔾ₘ (R := R)).map f = 𝔾ₘ := by
  ext
  simp [FormalGroup.𝔾ₘ]

/-- The normalized invariant differential commutes with arbitrary coefficient maps. -/
@[simp]
theorem map_invariantDifferential (F : FormalGroup R) (f : R →+* S) :
    PowerSeries.map f F.invariantDifferential = (F.map f).invariantDifferential := by
  have hD : PowerSeries.map f
      (subst ![0, PowerSeries.X] (pderiv 0 F.toPowerSeries)) =
      subst ![0, PowerSeries.X] (pderiv 0 (F.map f).toPowerSeries) := by
    -- Multivariate substitution returns a series in Unit variables here; unfold the
    -- univariate wrappers to apply its coefficient-map theorem.
    simp only [PowerSeries.map, PowerSeries.X]
    rw [MvPowerSeries.map_subst (HasSubst.zero_X :
      HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R)), ← pderiv_map,
      map_toPowerSeries]
    congr 1
    funext i
    fin_cases i <;> simp
  apply left_inv_eq_right_inv (a :=
    subst ![0, PowerSeries.X] (pderiv 0 (F.map f).toPowerSeries))
  · rw [← hD, ← map_mul, invariantDifferential_mul_subst_pderiv, map_one]
  · rw [mul_comm]
    exact (F.map f).invariantDifferential_mul_subst_pderiv

/-- The formal logarithm commutes with coefficient maps between rational algebras. -/
@[simp]
theorem map_log [Algebra ℚ R] [Algebra ℚ S] (F : FormalGroup R) (f : R →+* S) :
    PowerSeries.map f F.log = (F.map f).log := by
  ext n
  simp only [PowerSeries.coeff_map, coeff_log, map_rat_smul,
    ← map_invariantDifferential F f, PowerSeries.coeff_map]

/-- For a formal group over `R`, the coefficient of degree `n + 1` of its logarithm after
mapping to a rational algebra has denominator dividing `n + 1`: multiplication by `n + 1`
recovers the image of an invariant-differential coefficient in `R`. -/
theorem natCast_mul_coeff_log_map [Algebra ℚ S] (F : FormalGroup R) (f : R →+* S) (n : ℕ) :
    (n + 1 : S) * PowerSeries.coeff (n + 1) (F.map f).log =
      f (PowerSeries.coeff n F.invariantDifferential) := by
  have h := congrArg (PowerSeries.coeff n) (F.map f).derivative_log
  rw [PowerSeries.coeff_derivative, ← map_invariantDifferential,
    PowerSeries.coeff_map] at h
  simpa only [mul_comm] using h

/-- The formal exponential commutes with coefficient maps between rational algebras. -/
@[simp]
theorem map_exp [Algebra ℚ R] [Algebra ℚ S] (F : FormalGroup R) (f : R →+* S) :
    PowerSeries.map f F.exp = (F.map f).exp := by
  -- Compose with the known inverse; no recursive description of the exponential is needed.
  have he := PowerSeries.HasSubst.of_constantCoeff_zero F.constantCoeff_exp
  have hm : PowerSeries.HasSubst (PowerSeries.map f F.exp) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, F.constantCoeff_exp, map_zero]
  have hl := PowerSeries.HasSubst.of_constantCoeff_zero (F.map f).constantCoeff_log
  have hi : PowerSeries.subst (PowerSeries.map f F.exp) (F.map f).log = PowerSeries.X := by
    rw [← map_log]
    have h := PowerSeries.map_subst (h := f) he F.log
    -- map_subst uses MvPowerSeries.map even for its univariate result; unfold
    -- PowerSeries.map and X to match those Unit-variable wrappers.
    simp only [PowerSeries.map] at h ⊢
    rw [← h, subst_exp_log]
    simp [PowerSeries.X]
  calc
    _ = PowerSeries.subst (PowerSeries.map f F.exp) PowerSeries.X :=
      (PowerSeries.subst_X hm).symm
    _ = PowerSeries.subst (PowerSeries.map f F.exp)
        (PowerSeries.subst (F.map f).log (F.map f).exp) := by rw [subst_log_exp]
    _ = (F.map f).exp := by
      rw [PowerSeries.subst_comp_subst_apply hl hm, hi, PowerSeries.X_subst]

end FormalGroup
