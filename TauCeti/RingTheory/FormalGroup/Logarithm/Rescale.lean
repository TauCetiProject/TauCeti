/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Logarithm.Basic
public import TauCeti.RingTheory.FormalGroup.Rescale.Basic
-- Proof-only: the derivative commutes with change of coefficients.
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Integral logarithms of rescaled formal group laws

Let `F` be a formal group law over a commutative ring `R`, with invariant differential
`P(T) = ∑ pₙ Tⁿ`, and let `s ∈ R`. The rescaling `F^s`, with `s · F^s(X, Y) = F(s X, s Y)`
(`FormalGroup.rescale`), has invariant differential `P(s T)`
(`FormalGroup.invariantDifferential_rescale`), so over a `ℚ`-algebra its logarithm is

`log_{F^s}(T) = ∑_{n ≥ 0} (sⁿ / (n + 1)) pₙ Tⁿ⁺¹`,

that is `s · log_{F^s}(T) = log_F(s T)` (`FormalGroup.smul_log_rescale`). The denominators of
`log_F` are cancelled by the powers of `s` as soon as `n + 1` divides `sⁿ` in `R` for every `n`.
Then the series above has coefficients in `R`, even though `R` need not contain `ℚ`. This series is
`FormalGroup.rescaleLog`. Over a ring without additive torsion it is additive along `F^s`, and its
linear coefficient is `1`. So it is a strict isomorphism from `F^s` to the additive formal group
law, defined over `R` (`FormalGroup.rescaleLogIso`). After base change to any `ℚ`-algebra it
becomes the logarithm of `F^s`, and its inverse becomes the exponential of `F^s`
(`FormalGroup.map_rescaleLog`, `FormalGroup.map_invHom_rescaleLogIso`).

The divisibility hypothesis holds when `p ∣ s ^ (p - 1)` for a prime `p` and every natural number
prime to `p` is a unit of `R` (`TauCeti.natCast_add_one_dvd_pow`). For the ring of integers of a
finite extension of `ℚ_p` with normalised valuation `v`, this asks `v(s) ≥ v(p) / (p - 1)`; for
`ℤ_p` one may take `s = p`, including `p = 2`. Since the points of `F^s` in the maximal ideal `𝔪`
are carried to the points of `F` in `s 𝔪` by `t ↦ s t`, this is the formal input to the comparison
of the formal group `F(s 𝔪)` with the additive group `s 𝔪` through the logarithm (Silverman IV.6.4).

## Main definitions

* `FormalGroup.rescaleLog`: the integral logarithm of `F^s`.
* `FormalGroup.rescaleLogHom` and `FormalGroup.rescaleLogIso`: the integral logarithm as a
  homomorphism and as a strict isomorphism from `F^s` to the additive formal group law.

## Main results

* `FormalGroup.smul_log_rescale`: over a `ℚ`-algebra, `s · log_{F^s}(T) = log_F(s T)`.
* `FormalGroup.derivative_rescaleLog`: the derivative of the integral logarithm of `F^s` is the
  invariant differential of `F^s`; over a ring without additive torsion this characterises it
  (`FormalGroup.eq_rescaleLog_of_derivative_eq`).
* `FormalGroup.map_rescaleLog`: after base change to a `ℚ`-algebra, the integral logarithm of `F^s`
  is the logarithm of `F^s`.
* `FormalGroup.map_invHom_rescaleLogIso`: after base change to a `ℚ`-algebra, the inverse of the
  integral logarithm is the exponential of `F^s`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.5 and IV.6.
-/

public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R) (s : R)

/-- **The logarithm of the rescaling**: over a `ℚ`-algebra, `s · log_{F^s}(T) = log_F(s T)`. So
`log_{F^s}(T) = s⁻¹ log_F(s T)` when `s` is a unit. -/
theorem smul_log_rescale [Algebra ℚ R] :
    s • (F.rescale s).log = PowerSeries.rescale s F.log := by
  ext n
  rcases n with _ | n
  · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simp only [PowerSeries.coeff_smul, PowerSeries.coeff_rescale, coeff_log,
      invariantDifferential_rescale, Nat.add_sub_cancel, smul_eq_mul]
    simp only [Algebra.smul_def]
    ring

variable {s}

/-- **The integral logarithm of the rescaling** `F^s`, when `n + 1` divides `sⁿ` for every `n`: the
power series `∑_{n ≥ 0} (sⁿ / (n + 1)) pₙ Tⁿ⁺¹` with coefficients in `R`, where `P(T) = ∑ pₙ Tⁿ`
is the invariant differential of `F`. Its derivative is the invariant differential of `F^s`
(`FormalGroup.derivative_rescaleLog`), and after base change to a `ℚ`-algebra it is the logarithm
of `F^s` (`FormalGroup.map_rescaleLog`). The quotient `sⁿ / (n + 1)` is a chosen witness of the
divisibility; it is unique when `R` has no additive torsion, which is the case in which the series
is additive along `F^s`. -/
noncomputable def rescaleLog (hs : ∀ n : ℕ, (n + 1 : R) ∣ s ^ n) : PowerSeries R :=
  PowerSeries.mk fun
    | 0 => 0
    | n + 1 => (hs n).choose * PowerSeries.coeff n F.invariantDifferential

variable (hs : ∀ n : ℕ, (n + 1 : R) ∣ s ^ n)

/-- The coefficient of `Tⁿ⁺¹` in the integral logarithm is the chosen quotient `sⁿ / (n + 1)`
times the coefficient `pₙ` of the invariant differential of `F`. -/
theorem coeff_succ_rescaleLog (n : ℕ) :
    PowerSeries.coeff (n + 1) (F.rescaleLog hs) =
      (hs n).choose * PowerSeries.coeff n F.invariantDifferential := by
  rw [rescaleLog, PowerSeries.coeff_mk]

/-- The integral logarithm has no constant term. -/
@[simp]
theorem constantCoeff_rescaleLog : PowerSeries.constantCoeff (F.rescaleLog hs) = 0 := by
  simp [rescaleLog, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- **The derivative of the integral logarithm** of `F^s` is the invariant differential of `F^s`:
the coefficient of `Tⁿ⁺¹` times `n + 1` is `sⁿ pₙ`. -/
@[simp]
theorem derivative_rescaleLog :
    PowerSeries.derivative (F.rescaleLog hs) = (F.rescale s).invariantDifferential := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_succ_rescaleLog, invariantDifferential_rescale,
    PowerSeries.coeff_rescale]
  conv_rhs => rw [(hs n).choose_spec]
  ring

/-- The integral logarithm has linear coefficient `1`. -/
@[simp]
theorem coeff_one_rescaleLog : PowerSeries.coeff 1 (F.rescaleLog hs) = 1 := by
  have h := congrArg PowerSeries.constantCoeff (F.derivative_rescaleLog hs)
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative,
    constantCoeff_invariantDifferential] at h
  simpa using h

/-- Over a ring without additive torsion, the integral logarithm of `F^s` is the only power series
with no constant term whose derivative is the invariant differential of `F^s`. In particular it
does not depend on the chosen quotients `sⁿ / (n + 1)`. -/
theorem eq_rescaleLog_of_derivative_eq [HasUniqueDiv R] {g : PowerSeries R}
    (hg₀ : PowerSeries.constantCoeff g = 0)
    (hg : PowerSeries.derivative g = (F.rescale s).invariantDifferential) :
    g = F.rescaleLog hs :=
  PowerSeries.derivative.ext (by rw [hg, derivative_rescaleLog])
    (by rw [hg₀, constantCoeff_rescaleLog])

/-- **The integral logarithm becomes the logarithm** of `F^s` after base change to a `ℚ`-algebra. -/
@[simp]
theorem map_rescaleLog {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S) :
    (F.rescaleLog hs).map f = ((F.rescale s).map f).log := by
  have : HasUniqueDiv S := .of_isTorsionFree ℚ S
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [PowerSeries.derivative_map, derivative_rescaleLog, derivative_log,
      map_invariantDifferential]
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rescaleLog, map_zero,
      constantCoeff_log]

/-- The integral logarithm of `F^s`, as a homomorphism from `F^s` to the additive formal group law,
over a ring without additive torsion. -/
noncomputable def rescaleLogHom [HasUniqueDiv R] : TauCeti.FormalGroupHom (F.rescale s) 𝔾ₐ where
  toPowerSeries := F.rescaleLog hs
  zero_constantCoeff := F.constantCoeff_rescaleLog hs
  hom := (TauCeti.FormalGroupHom.hom_additive_iff (F.constantCoeff_rescaleLog hs)).mpr
    ((F.rescale s).subst_toPowerSeries_eq_add_of_derivative_eq (F.constantCoeff_rescaleLog hs)
      (F.derivative_rescaleLog hs))

@[simp]
theorem rescaleLogHom_toPowerSeries [HasUniqueDiv R] :
    (F.rescaleLogHom hs).toPowerSeries = F.rescaleLog hs := (rfl)

/-- **The integral logarithm is a strict isomorphism** from `F^s` to the additive formal group law,
defined over `R`, when `R` has no additive torsion and `n + 1` divides `sⁿ` for every `n`. -/
noncomputable def rescaleLogIso [HasUniqueDiv R] : TauCeti.FormalGroupIso (F.rescale s) 𝔾ₐ :=
  (F.rescaleLogHom hs).toIso (by simp)

@[simp]
theorem rescaleLogIso_toHom [HasUniqueDiv R] :
    (F.rescaleLogIso hs).toHom = F.rescaleLogHom hs := by
  simp only [rescaleLogIso, TauCeti.FormalGroupHom.toIso_toHom]

instance [HasUniqueDiv R] : (F.rescaleLogIso hs).IsStrict where
  coeff_one := by simp

/-- **The inverse of the integral logarithm becomes the exponential** of `F^s` after base change to
a `ℚ`-algebra. So the exponential of `F^s` has coefficients in `R`. -/
theorem map_invHom_rescaleLogIso [HasUniqueDiv R] {S : Type*} [CommRing S] [Algebra ℚ S]
    (f : R →+* S) :
    (F.rescaleLogIso hs).invHom.toPowerSeries.map f = ((F.rescale s).map f).exp := by
  have hinv := (F.rescaleLogIso hs).invHom.zero_constantCoeff
  refine ((F.rescale s).map f).eq_exp_of_subst_log_eq_X
    (.of_constantCoeff_zero' (by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hinv, map_zero])) ?_
  simpa using ((F.rescaleLogIso hs).map f).subst_invHom_toHom

end FormalGroup
