/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.PowerSeries
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Geometric series of a positive monomial in Hahn series

Let `Γ` be a partially ordered cancellative additive monoid and `0 < g`. The multiples `n • g`
form an ordered copy of `ℕ` in `Γ`, so substituting the monomial `t ^ g` for `X` is an injective
ring homomorphism `R⟦X⟧ →+* R⟦Γ⟧`. It carries the geometric series identity
`(1 - r X) (1 + r X + r² X² + ⋯) = 1` to Hahn series: `1 - r t ^ g` is a unit with inverse
`∑ₙ rⁿ t ^ (n • g)`.

Mathlib proves the invertibility of such series when `Γ` is linearly ordered
(`HahnSeries.isUnit_of_orderTop_pos`). Exponents ordered by a cone, as for characters of
representations, are only partially ordered, and this file covers that case.

## Main definitions

* `HahnSeries.ofPowerSeriesSingle hg`: the ring homomorphism `R⟦X⟧ →+* R⟦Γ⟧` sending `X` to
  `t ^ g`, for `0 < g`.

## Main results

* `HahnSeries.ofPowerSeriesSingle_X`: it sends `X` to `single g 1`.
* `HahnSeries.coeff_ofPowerSeriesSingle_nsmul` and
  `HahnSeries.coeff_ofPowerSeriesSingle_of_forall_ne`: its coefficients.
* `HahnSeries.one_sub_single_mul_ofPowerSeriesSingle_mk_pow`:
  `(1 - r t ^ g) * ∑ₙ rⁿ t ^ (n • g) = 1`.
* `HahnSeries.isUnit_one_sub_single`: `1 - r t ^ g` is a unit.
-/

public section

namespace HahnSeries

variable {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ] {g : Γ}

section Semiring

variable [Semiring R]

/-- For `0 < g`, taking multiples of `g` is strictly monotone. -/
private theorem strictMono_multiplesHom (hg : 0 < g) : StrictMono (multiplesHom Γ g) :=
  nsmul_left_strictMono hg

variable (R) in
/-- For `0 < g`, the ring homomorphism `R⟦X⟧ →+* R⟦Γ⟧` substituting the monomial `t ^ g` for
`X`: it moves the coefficient of `Xⁿ` to the exponent `n • g`. -/
noncomputable def ofPowerSeriesSingle (hg : 0 < g) : PowerSeries R →+* R⟦Γ⟧ :=
  (embDomainRingHom (multiplesHom Γ g) (strictMono_multiplesHom hg).injective
    fun _ _ ↦ (strictMono_multiplesHom hg).le_iff_le).comp toPowerSeries.symm.toRingHom

/-- The coefficient of `ofPowerSeriesSingle R hg f` at `n • g` is the `n`-th coefficient
of `f`. -/
@[simp]
theorem coeff_ofPowerSeriesSingle_nsmul (hg : 0 < g) (f : PowerSeries R) (n : ℕ) :
    (ofPowerSeriesSingle R hg f).coeff (n • g) = PowerSeries.coeff n f := by
  rw [ofPowerSeriesSingle, RingHom.comp_apply, embDomainRingHom_apply, ← multiplesHom_apply,
    embDomain_mk_coeff]
  simp

/-- `ofPowerSeriesSingle R hg f` vanishes away from the multiples of `g`. -/
theorem coeff_ofPowerSeriesSingle_of_forall_ne (hg : 0 < g) (f : PowerSeries R) {a : Γ}
    (ha : ∀ n : ℕ, n • g ≠ a) : (ofPowerSeriesSingle R hg f).coeff a = 0 := by
  rw [ofPowerSeriesSingle, RingHom.comp_apply, embDomainRingHom_apply]
  exact embDomain_of_notMem_range fun ⟨n, hn⟩ ↦ ha n hn

/-- Substituting `t ^ g` for `X` is injective. -/
theorem ofPowerSeriesSingle_injective (hg : 0 < g) :
    Function.Injective (ofPowerSeriesSingle R hg) := by
  intro f f' h
  ext n
  rw [← coeff_ofPowerSeriesSingle_nsmul hg, h, coeff_ofPowerSeriesSingle_nsmul]

/-- `ofPowerSeriesSingle R hg` sends `X` to the monomial `t ^ g`. -/
@[simp]
theorem ofPowerSeriesSingle_X (hg : 0 < g) :
    ofPowerSeriesSingle R hg PowerSeries.X = single g 1 := by
  have hX : toPowerSeries.symm (PowerSeries.X : PowerSeries R) = single 1 1 := by
    ext n
    simp [PowerSeries.coeff_X, coeff_single]
  simp [ofPowerSeriesSingle, hX, embDomain_single]

/-- `ofPowerSeriesSingle R hg` sends constants to constants. -/
@[simp]
theorem ofPowerSeriesSingle_C (hg : 0 < g) (r : R) :
    ofPowerSeriesSingle R hg (PowerSeries.C r) = C r := by
  have hC : toPowerSeries.symm (PowerSeries.C r) = C r := by
    ext n
    simp [PowerSeries.coeff_C, coeff_single]
  simp [ofPowerSeriesSingle, hC]

end Semiring

section CommRing

variable [CommRing R]

/-- **The geometric series of a positive monomial**: for `0 < g`,
`(1 - r t ^ g) * ∑ₙ rⁿ t ^ (n • g) = 1`. -/
theorem one_sub_single_mul_ofPowerSeriesSingle_mk_pow (hg : 0 < g) (r : R) :
    (1 - single g r) * ofPowerSeriesSingle R hg (PowerSeries.mk fun n ↦ r ^ n) = 1 := by
  have h := congrArg (PowerSeries.rescale r) (PowerSeries.mk_one_mul_one_sub_eq_one R)
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X, PowerSeries.rescale_mk,
    Pi.one_apply, mul_one] at h
  simpa [single_mul_single, mul_comm] using congrArg (ofPowerSeriesSingle R hg) h

/-- For `0 < g`, the series `1 - r t ^ g` is a unit, with inverse `∑ₙ rⁿ t ^ (n • g)`. -/
theorem isUnit_one_sub_single (hg : 0 < g) (r : R) : IsUnit (1 - single g r) :=
  IsUnit.of_mul_eq_one _ (one_sub_single_mul_ofPowerSeriesSingle_mk_pow hg r)

end CommRing

end HahnSeries
