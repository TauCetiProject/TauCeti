/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Substitution of power series: orders, linear coefficients, algebra maps, and the binomial series

Mathlib substitutes a power series `b` with nilpotent constant coefficient into a power series
`f` through `PowerSeries.subst b f`, and records the side condition on `b` as
`PowerSeries.HasSubst b`.

Over a ring without zero divisors, substituting a series `φ` of zero constant coefficient
multiplies orders: `ord (f (φ)) = ord φ * ord f`. Mathlib records only the inequality
`PowerSeries.le_order_subst`. The equality shows that substitution of a nonzero such `φ` is
injective, which is what extends it to Laurent series by passing to fraction fields.

Substitution of series of zero constant coefficient is compatible with congruences modulo
powers of `X`, in both the substituted series and the series substituted into. This makes
truncation modulo `X ^ n` compatible with composition of formal coordinates.

An algebra map on power series whose value at `X` has nilpotent constant coefficient is the
corresponding substitution, without any continuity hypothesis. Over a field, every algebra
endomorphism of the power series ring has this form. In particular, a perturbation `X + h` of `X`
with `h ^ 2 = 0` substitutes by the first-order Taylor formula `f (X + h) = f + h f'`, since the
right-hand side is multiplicative in `f` by the Leibniz rule.

This file also records that the substitution `X ↦ (1 + X) ^ u - 1`, for a binomial series
`(1 + X) ^ u`, is legitimate: it is the change of variable relating the power-series coordinates
of a completed group algebra attached to two topological generators.

## Main results

* `PowerSeries.order_subst`: `ord (f (φ)) = ord φ * ord f` when `φ` has zero constant
  coefficient.
* `PowerSeries.subst_eq_zero_iff`: substitution of a nonzero `φ` of zero constant coefficient
  has trivial kernel.
* `PowerSeries.toNat_order_ne_zero`: such a `φ` has positive integer order.
* `PowerSeries.coeff_one_subst`: linear coefficients multiply under substitution.
* `PowerSeries.X_pow_dvd_subst`: substitution preserves divisibility by `X ^ n`.
* `PowerSeries.X_pow_dvd_subst_sub_subst`: substitution respects congruence modulo `X ^ n` of
  the substituted series.
* `PowerSeries.algHom_eq_substAlgHom`: an algebra map `R⟦X⟧ → S⟦X⟧` sending `X` to a
  substitutable series is a substitution.
* `PowerSeries.subst_X_add_of_sq_eq_zero`: `f (X + h) = f + h f'` when `h ^ 2 = 0`.
* `AlgHom.apply_eq_subst`: over a field, every algebra endomorphism of `K⟦X⟧` is substitution by
  its value at `X`.
* `TauCeti.hasSubst_binomialSeries_sub_one`: `(1 + X) ^ u - 1` can be substituted.
-/

public section

namespace PowerSeries

/-- A nonzero power series of zero constant coefficient has positive integer order, so it
multiplies orders under substitution by a positive integer. -/
theorem toNat_order_ne_zero {R : Type*} [Semiring R] {φ : R⟦X⟧} (hφ : constantCoeff φ = 0)
    (hφ₀ : φ ≠ 0) : φ.order.toNat ≠ 0 := by
  rw [Ne, ENat.toNat_eq_zero, not_or, order_eq_top]
  exact ⟨order_ne_zero_iff_constCoeff_eq_zero.mpr hφ, hφ₀⟩

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {φ : R⟦X⟧}

/-- Substituting a power series `φ` of zero constant coefficient multiplies orders:
`ord (f (φ)) = ord φ * ord f`. -/
theorem order_subst (hφ : constantCoeff φ = 0) (f : R⟦X⟧) :
    PowerSeries.order (f.subst φ) = φ.order * f.order := by
  have ha : HasSubst φ := .of_constantCoeff_zero' hφ
  rcases eq_or_ne f 0 with rfl | hf
  · rw [← coe_substAlgHom ha, map_zero, order_zero, ENat.mul_top]
    exact order_ne_zero_iff_constCoeff_eq_zero.mpr hφ
  have : Nontrivial R := have := nontrivial_of_ne f 0 hf; (C (R := R)).domain_nontrivial
  -- Write `f = X ^ m * g` with `m = ord f`; then `g (φ)` has the nonzero constant coefficient
  -- of `g`, so it has order zero.
  have hg : PowerSeries.order (f.divXPowOrder.subst φ) = 0 := by
    rw [← not_ne_iff, order_ne_zero_iff_constCoeff_eq_zero]
    have h := constantCoeff_subst_of_constantCoeff_zero hφ f.divXPowOrder
    rw [Algebra.algebraMap_self_apply] at h
    -- `h` is stated with the multivariate constant coefficient, which is the univariate one
    rw [show constantCoeff (f.divXPowOrder.subst φ) = f.divXPowOrder.constantCoeff from h]
    exact constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hf
  nth_rw 1 [← X_pow_order_mul_divXPowOrder (f := f)]
  rw [subst_mul ha, subst_pow ha, subst_X ha, order_mul, order_pow, hg, add_zero, nsmul_eq_mul,
    coe_toNat_order hf, mul_comm]

/-- Substituting a nonzero power series `φ` of zero constant coefficient sends only `0` to `0`. -/
theorem subst_eq_zero_iff (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0) {f : R⟦X⟧} :
    (f.subst φ : R⟦X⟧) = 0 ↔ f = 0 := by
  have h₀ := order_ne_zero_iff_constCoeff_eq_zero.mpr hφ
  have h₁ : φ.order ≠ ⊤ := order_eq_top.not.mpr hφ₀
  rw [← order_eq_top, ← order_eq_top (φ := f), order_subst hφ]
  exact WithTop.mul_eq_top_iff.trans (by tauto)

section Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The linear coefficient of `f (a)`, for `a` of zero constant coefficient, is the product of
the linear coefficients of `f` and `a`. -/
theorem coeff_one_subst {a : S⟦X⟧} (ha : constantCoeff a = 0) (f : R⟦X⟧) :
    coeff 1 (f.subst a) = algebraMap R S (coeff 1 f) * coeff 1 a := by
  obtain ⟨b, rfl⟩ := X_dvd_iff.mpr ha
  rw [coeff_subst' (.of_constantCoeff_zero' ha), finsum_eq_single _ 1, pow_one, Algebra.smul_def]
  -- `(X * b) ^ d` has no linear term unless `d = 1`
  rintro (_ | _ | d) hd
  · simp
  · exact absurd rfl hd
  · simp [mul_pow, coeff_X_pow_mul']

/-- An `R`-algebra map `σ : R⟦X⟧ → S⟦X⟧` such that `σ X` can be substituted is the
substitution `f ↦ f (σ X)`. No continuity hypothesis is needed. -/
theorem algHom_eq_substAlgHom {σ : R⟦X⟧ →ₐ[R] S⟦X⟧} (hσ : HasSubst (σ X)) :
    σ = substAlgHom hσ := by
  have hpoly : σ.comp (Polynomial.coeToPowerSeries.algHom R) =
      (substAlgHom hσ).comp (Polynomial.coeToPowerSeries.algHom R) :=
    Polynomial.algHom_ext (by simp [substAlgHom_X])
  refine AlgHom.ext fun f ↦ ext fun n ↦ ?_
  obtain ⟨m, hm⟩ := (hσ.eventually_coeff_pow_eq_zero n).exists_forall_of_atTop
  have key (g : S⟦X⟧) : coeff n (σ X ^ m * g) = 0 := by
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [hm m le_rfl p.1 (by grind [Finset.mem_antidiagonal]), zero_mul]
  -- The maps agree on the polynomial truncation. The remaining multiple of `X ^ m` has
  -- zero coefficients through degree `n` after either map is applied.
  rw [eq_X_pow_mul_shift_add_trunc m f]
  simp only [map_add, map_mul, map_pow, substAlgHom_X, key, zero_add]
  exact congr(coeff n ($hpoly (trunc m f)))

/-- A square-zero perturbation `X + h` of `X` can be substituted. -/
theorem hasSubst_X_add_of_sq_eq_zero {h : S⟦X⟧} (hh : h ^ 2 = 0) : HasSubst (X + h) :=
  HasSubst.X'.add <| IsNilpotent.map (⟨2, hh⟩ : IsNilpotent h) MvPowerSeries.constantCoeff

/-- The first-order Taylor formula: substituting a square-zero perturbation `X + h` of `X` gives
`f (X + h) = f + h f'`. -/
theorem subst_X_add_of_sq_eq_zero {h : S⟦X⟧} (hh : h ^ 2 = 0) (f : S⟦X⟧) :
    f.subst (X + h) = f + h * d⁄dX f := by
  -- `f ↦ f + h f'` is an algebra map, multiplicative by the Leibniz rule and `h ^ 2 = 0`, and it
  -- sends `X` to `X + h`, so it is the substitution of `X + h`.
  let T : S⟦X⟧ →ₐ[S] S⟦X⟧ :=
    { toFun g := g + h * d⁄dX g
      map_one' := by simp
      map_mul' g₁ g₂ := by
        simp only [Derivation.leibniz, smul_eq_mul]
        linear_combination (-(d⁄dX g₁ * d⁄dX g₂)) * hh
      map_zero' := by simp
      map_add' g₁ g₂ := by
        simp only [map_add]
        ring
      commutes' r := by simp }
  have hT (g : S⟦X⟧) : T g = g + h * d⁄dX g := rfl
  have hTX : T X = X + h := by rw [hT, derivative_X, mul_one]
  have hσ := congr($(algHom_eq_substAlgHom (σ := T) (hTX ▸ hasSubst_X_add_of_sq_eq_zero hh)) f)
  rw [coe_substAlgHom, hTX, hT] at hσ
  exact hσ.symm

/-- Substituting a series of zero constant coefficient preserves divisibility by `X ^ n`. -/
theorem X_pow_dvd_subst {a : S⟦X⟧} (ha : constantCoeff a = 0) {n : ℕ} {f : R⟦X⟧}
    (hf : X ^ n ∣ f) : X ^ n ∣ f.subst a := by
  have ha' : HasSubst a := .of_constantCoeff_zero' ha
  obtain ⟨g, rfl⟩ := hf
  rw [subst_mul ha', subst_pow ha', subst_X ha']
  exact (pow_dvd_pow_of_dvd (X_dvd_iff.mpr ha) n).mul_right _

/-- Substitution respects congruence modulo `X ^ n` of the substituted series: if `a ≡ b` modulo
`X ^ n`, then `f (a) ≡ f (b)` modulo `X ^ n`. -/
theorem X_pow_dvd_subst_sub_subst {a b : S⟦X⟧} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) {n : ℕ} (hab : X ^ n ∣ a - b) (f : R⟦X⟧) :
    X ^ n ∣ f.subst a - f.subst b := by
  have ha' : HasSubst a := .of_constantCoeff_zero' ha
  have hb' : HasSubst b := .of_constantCoeff_zero' hb
  -- On the polynomial truncation this is `a - b ∣ p (a) - p (b)`; the remaining multiple of
  -- `X ^ n` stays one after either substitution.
  rw [eq_X_pow_mul_shift_add_trunc n f, subst_add ha', subst_add hb', add_sub_add_comm]
  refine dvd_add (dvd_sub (X_pow_dvd_subst ha (dvd_mul_right _ _))
    (X_pow_dvd_subst hb (dvd_mul_right _ _))) (hab.trans ?_)
  rw [subst_coe ha', subst_coe hb', ← Polynomial.eval_map_algebraMap,
    ← Polynomial.eval_map_algebraMap]
  exact Polynomial.sub_dvd_eval_sub _ _ _

end Algebra

end PowerSeries

section Field

open PowerSeries

/-- Over a field `K`, every `K`-algebra endomorphism of `K⟦X⟧` sends `X` to a series of zero
constant coefficient. -/
theorem AlgHom.constantCoeff_apply_X {K : Type*} [Field K] (σ : K⟦X⟧ →ₐ[K] K⟦X⟧) :
    constantCoeff (σ X) = 0 := by
  by_contra hc
  -- If the constant coefficient were `c ≠ 0`, the unit `X - c` would map to a nonunit.
  have hu : IsUnit (X - C (constantCoeff (σ X)) : K⟦X⟧) := by
    simpa [isUnit_iff_constantCoeff] using hc
  have hσ : σ (X - C (constantCoeff (σ X))) = σ X - C (constantCoeff (σ X)) := by
    rw [map_sub, ← algebraMap_eq, AlgHom.commutes]
  simpa [hσ, isUnit_iff_constantCoeff] using hu.map σ

/-- Over a field `K`, every `K`-algebra endomorphism `σ` of `K⟦X⟧` is the substitution
`f ↦ f (σ X)`. -/
theorem AlgHom.apply_eq_subst {K : Type*} [Field K] (σ : K⟦X⟧ →ₐ[K] K⟦X⟧) (f : K⟦X⟧) :
    σ f = f.subst (σ X) := by
  let hσ : HasSubst (σ X) := .of_constantCoeff_zero' σ.constantCoeff_apply_X
  rw [← coe_substAlgHom hσ, ← algHom_eq_substAlgHom hσ]

end Field

namespace TauCeti

open PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The binomial series `(1 + X) ^ u - 1` has constant coefficient zero, so power series can be
substituted into it. -/
theorem hasSubst_binomialSeries_sub_one [BinomialRing R] (u : R) :
    HasSubst (binomialSeries S u - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)

end TauCeti
