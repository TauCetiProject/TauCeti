/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Partial derivatives of multivariate power series: order and the chain rule

A partial derivative lowers the order of a multivariate power series by at most one. Over a
commutative semiring without additive torsion the order is in turn detected by the partial
derivatives: `f` has order at least `n + 1`, for `n : ℕ∞`, exactly when its constant coefficient
vanishes and each of its partial derivatives has order at least `n`.

Applied to the Taylor expansion of a polynomial at a point, this is the characterization of the
order of vanishing of the polynomial at the point by its partial derivatives
(`MvPolynomial.le_orderAt_iff_eval_foldl_pderiv`).

Partial derivatives also obey the **chain rule** for substitution: if `a : σ → R⟦τ⟧` is a
family of power series that can be substituted (`MvPowerSeries.HasSubst a`), then
`∂ᵢ (f ∘ a) = ∑ⱼ (∂ⱼ f ∘ a) · ∂ᵢ aⱼ` for every `f : R⟦σ⟧` with finitely many variables. For
polynomials `f` this is the Leibniz rule; it extends to power series because both sides are
continuous in `f` for the coefficientwise topology, in which polynomials are dense. The
one-variable case of Mathlib, `PowerSeries.derivative_subst`, substitutes into a one-variable
series only; here the substituted series may have any number of variables.

## Main results

* `MvPowerSeries.le_order_pderiv`: if `n + 1 ≤ f.order` then `n ≤ (pderiv i f).order`.
* `MvPowerSeries.succ_le_order_iff`: `n + 1 ≤ f.order` if and only if the constant coefficient of
  `f` vanishes and `n ≤ (pderiv i f).order` for every `i`.
* `MvPowerSeries.eq_zero_of_pderiv_eq_zero_of_subst_eq_zero`: over a ring without additive
  torsion, a series vanishes if its partial derivative in `X i` and its value at `X i = 0` do.
* `MvPowerSeries.WithPiTopology.continuous_pderiv`: a partial derivative is continuous for the
  coefficientwise topology.
* `MvPowerSeries.pderiv_subst`: the chain rule for substitution into a multivariate power series.
* `PowerSeries.pderiv_subst`: the chain rule for substitution of a multivariate power series into
  a one-variable power series.
-/

public section

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

/-- A partial derivative lowers the order of a power series by at most one. -/
theorem le_order_pderiv [CommSemiring R] {f : MvPowerSeries σ R} {n : ℕ∞}
    (h : n + 1 ≤ f.order) (i : σ) : n ≤ (pderiv i f).order := by
  refine le_order fun d hd ↦ ?_
  rw [coeff_pderiv, coeff_of_lt_order (lt_of_lt_of_le ?_ h), zero_mul]
  simpa only [map_add, degree_single, Nat.cast_add, Nat.cast_one] using
    (ENat.add_lt_add_iff_right ENat.one_ne_top).mpr hd

variable [CommSemiring R] [IsAddTorsionFree R]

/-- Over a commutative semiring without additive torsion, a coefficient of the partial derivative
in `X i` vanishes exactly when the corresponding coefficient of `f`, with the exponent of `X i`
raised by one, does. -/
@[simp]
theorem coeff_pderiv_eq_zero_iff {f : MvPowerSeries σ R} {i : σ} {d : σ →₀ ℕ} :
    coeff d (pderiv i f) = 0 ↔ coeff (d + single i 1) f = 0 := by
  rw [coeff_pderiv, mul_comm, ← Nat.cast_succ, ← nsmul_eq_mul, nsmul_eq_zero_iff,
    or_iff_left (Nat.succ_ne_zero _)]

/-- Over a commutative semiring without additive torsion, `f` has order at least `n + 1` if and
only if its constant coefficient vanishes and each partial derivative has order at least `n`. -/
theorem succ_le_order_iff {f : MvPowerSeries σ R} {n : ℕ∞} :
    n + 1 ≤ f.order ↔
      constantCoeff f = 0 ∧ ∀ i, n ≤ (pderiv i f).order := by
  refine ⟨fun h ↦ ⟨?_, le_order_pderiv h⟩, fun ⟨h0, h⟩ ↦ le_order fun d hd ↦ ?_⟩
  · exact one_le_order_iff_constCoeff_eq_zero.mp (le_trans (by simp) h)
  obtain rfl | hi := eq_or_ne d 0
  · rwa [coeff_zero_eq_constantCoeff_apply]
  obtain ⟨i, hi⟩ := ne_iff.mp hi
  -- Write `d = e + single i 1` and read the coefficient of `X ^ e` in `pderiv i f`.
  obtain ⟨e, rfl⟩ : ∃ e, d = e + single i 1 :=
    ⟨d - single i 1, (sub_add_single_one_cancel hi).symm⟩
  have he : (e.degree : ℕ∞) < n := by
    simpa only [map_add, degree_single, Nat.cast_add, Nat.cast_one,
      ENat.add_lt_add_iff_right ENat.one_ne_top] using hd
  exact coeff_pderiv_eq_zero_iff.mp (coeff_of_lt_order (lt_of_lt_of_le he (h i)))

end MvPowerSeries

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*} [CommRing R] [IsAddTorsionFree R]

/-- Over a ring without additive torsion, a power series vanishes if its partial derivative in
`X i` vanishes and it vanishes at `X i = 0`. -/
theorem eq_zero_of_pderiv_eq_zero_of_subst_eq_zero [DecidableEq σ] {i : σ}
    {f : MvPowerSeries σ R} (h₀ : pderiv i f = 0)
    (h₁ : subst (Function.update (X : σ → MvPowerSeries σ R) i 0) f = 0) : f = 0 := by
  -- the coefficients of `f` without `X i` are those of `f` at `X i = 0`
  have hr : rescale (Function.update (1 : σ → R) i 0) f = 0 := by
    rw [rescale_eq_subst, ← h₁]
    congr 1
    funext s
    by_cases hs : s = i <;> simp [Function.update, hs]
  ext n
  by_cases hn : n i = 0
  · have := congrArg (coeff n) hr
    rw [coeff_rescale, Finsupp.prod, Finset.prod_eq_one fun s hs ↦ ?_, one_mul] at this
    · simpa using this
    · rw [Function.update_of_ne (by rintro rfl; simp_all), Pi.one_apply, one_pow]
  -- the others are read off the vanishing derivative, since `n i` is nonzero
  · have := congrArg (coeff (n - single i 1)) h₀
    rwa [map_zero, coeff_pderiv_eq_zero_iff, sub_add_single_one_cancel hn] at this

end MvPowerSeries

/-! ### The chain rule -/

namespace MvPowerSeries

variable {σ τ R : Type*}

namespace WithPiTopology

/-- **A partial derivative is continuous** for the coefficientwise topology: each coefficient of
`pderiv i f` is a coefficient of `f` times a constant. -/
theorem continuous_pderiv [CommSemiring R] [TopologicalSpace R] [SeparatelyContinuousMul R]
    (i : σ) : Continuous (pderiv (R := R) i : MvPowerSeries σ R → MvPowerSeries σ R) :=
  -- the coefficientwise topology is the product topology, so continuity is coefficientwise
  continuous_pi fun n ↦ by
    simpa only [← coeff_apply, coeff_pderiv] using (continuous_coeff R _).mul_const _

end WithPiTopology

open WithPiTopology in
/-- **The chain rule** for substitution into a multivariate power series:
`∂ᵢ (f ∘ a) = ∑ⱼ (∂ⱼ f ∘ a) · ∂ᵢ aⱼ`. -/
theorem pderiv_subst [CommRing R] [Fintype σ] {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (f : MvPowerSeries σ R) (i : τ) :
    pderiv i (subst a f) = ∑ j, subst a (pderiv j f) * pderiv i (a j) := by
  classical
  let : UniformSpace R := ⊥
  have : DiscreteUniformity R := ⟨rfl⟩
  revert f
  rw [← funext_iff]
  -- Both sides are continuous in `f`, so it suffices to check the identity on polynomials.
  refine Continuous.ext_on denseRange_toMvPowerSeries
    ((continuous_pderiv i).comp (continuous_subst ha))
    (continuous_finsetSum _ fun j _ ↦
      ((continuous_subst ha).comp (continuous_pderiv j)).mul continuous_const) ?_
  have h0 : subst a (0 : MvPowerSeries σ R) = 0 := by rw [← coe_substAlgHom ha, map_zero]
  have h1 : subst a (1 : MvPowerSeries σ R) = 1 := by rw [← coe_substAlgHom ha, map_one]
  rintro _ ⟨p, rfl⟩
  induction p using MvPolynomial.induction_on with
  | C r => simp [h0]
  | add p q hp hq =>
    simp only [MvPolynomial.coe_add, map_add, subst_add ha] at hp hq ⊢
    simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul ha, subst_X ha,
      Derivation.leibniz, smul_eq_mul, subst_add ha] at hp ⊢
    simp [hp, pderiv_X, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
      Pi.single_apply, apply_ite (subst a), h0, h1]

end MvPowerSeries

namespace PowerSeries

/-- **The chain rule** for substitution of a multivariate power series `g` into a one-variable
power series `f`: `∂ᵢ (f ∘ g) = (f' ∘ g) · ∂ᵢ g`. -/
theorem pderiv_subst {τ R : Type*} [CommRing R] {g : MvPowerSeries τ R} (hg : HasSubst g)
    (f : PowerSeries R) (i : τ) :
    MvPowerSeries.pderiv i (subst g f) = subst g (derivative f) * MvPowerSeries.pderiv i g := by
  -- `PowerSeries.derivative` is by definition the partial derivative in the unique variable
  rw [subst_def, MvPowerSeries.pderiv_subst hg.const, Fintype.sum_unique, derivative, subst_def]

end PowerSeries
