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

When a substitutable family `a` is perturbed by a family `h` whose entries pairwise multiply to
zero, such as series with coefficients in an ideal of square zero, substitution obeys the
**first-order Taylor formula** `f ∘ (a + h) = f ∘ a + ∑ᵢ hᵢ · (∂ᵢ f ∘ a)`, extending
`PowerSeries.subst_add_of_sq_eq_zero` to finitely many variables.

## Main results

* `MvPowerSeries.le_order_pderiv`: if `n + 1 ≤ f.order` then `n ≤ (pderiv i f).order`.
* `MvPowerSeries.coeff_pderiv_mem`: partial derivatives keep the coefficients in an additive
  submonoid, such as a subring.
* `MvPowerSeries.succ_le_order_iff`: `n + 1 ≤ f.order` if and only if the constant coefficient of
  `f` vanishes and `n ≤ (pderiv i f).order` for every `i`.
* `MvPowerSeries.eq_zero_of_pderiv_eq_zero_of_subst_eq_zero`: over a ring without additive
  torsion, a series vanishes if its partial derivative in `X i` and its value at `X i = 0` do.
* `MvPowerSeries.WithPiTopology.continuous_pderiv`: a partial derivative is continuous for the
  coefficientwise topology.
* `MvPowerSeries.pderiv_subst`: the chain rule for substitution into a multivariate power series.
* `MvPowerSeries.subst_add_of_mul_eq_zero`, `MvPowerSeries.subst_X_add_of_mul_eq_zero`: the
  first-order Taylor formula for perturbations whose entries pairwise multiply to zero.
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

/-- Partial differentiation keeps the coefficients in an additive submonoid of the coefficient
ring, such as a subring. -/
theorem coeff_pderiv_mem [CommSemiring R] {S : Type*} [SetLike S R] [AddSubmonoidClass S R]
    {s : S} {f : MvPowerSeries σ R} (hf : ∀ m, coeff m f ∈ s) (i : σ) (m : σ →₀ ℕ) :
    coeff m (pderiv i f) ∈ s := by
  rw [coeff_pderiv, ← Nat.cast_succ, mul_comm, ← nsmul_eq_mul]
  exact nsmul_mem (hf _) _

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

/-- A family of power series whose entries satisfy `h i ^ 2 = 0` can be substituted, since each
constant coefficient squares to zero. -/
theorem HasSubst.of_sq_eq_zero {S : Type*} [CommRing S] [Finite σ] {h : σ → MvPowerSeries τ S}
    (hh : ∀ i, h i ^ 2 = 0) : HasSubst h :=
  hasSubst_of_constantCoeff_nilpotent fun i ↦ ⟨2, by rw [← map_pow, hh, map_zero]⟩

open WithPiTopology in
/-- **The first-order Taylor formula** for multivariate power series: if `a` can be substituted
and the perturbations `h i` pairwise multiply to zero, then
`f(a + h) = f(a) + ∑ᵢ hᵢ · (∂ᵢ f)(a)`. -/
theorem subst_add_of_mul_eq_zero {S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype σ]
    {a h : σ → MvPowerSeries τ S} (ha : HasSubst a) (hh : ∀ i j, h i * h j = 0)
    (f : MvPowerSeries σ R) :
    subst (a + h) f = subst a f + ∑ i, h i * subst a (pderiv i f) := by
  classical
  let : UniformSpace R := ⊥
  have : DiscreteUniformity R := ⟨rfl⟩
  let : UniformSpace S := ⊥
  have : DiscreteUniformity S := ⟨rfl⟩
  have hah : HasSubst (a + h) := ha.add (.of_sq_eq_zero fun i ↦ by rw [sq, hh])
  revert f
  rw [← funext_iff]
  -- Both sides are continuous in `f`, so it suffices to check the identity on polynomials.
  refine Continuous.ext_on denseRange_toMvPowerSeries (continuous_subst hah)
    ((continuous_subst ha).add (continuous_finsetSum _ fun i _ ↦
      continuous_const.mul ((continuous_subst ha).comp (continuous_pderiv i)))) ?_
  have h0 : subst a (0 : MvPowerSeries σ R) = 0 := by rw [← coe_substAlgHom ha, map_zero]
  have h1 : subst a (1 : MvPowerSeries σ R) = 1 := by rw [← coe_substAlgHom ha, map_one]
  rintro _ ⟨p, rfl⟩
  induction p using MvPolynomial.induction_on with
  | C r =>
    dsimp only
    rw [subst_coe, subst_coe]
    simp [h0]
  | add p q hp hq =>
    simp only [MvPolynomial.coe_add, map_add, subst_add hah, subst_add ha] at hp hq ⊢
    rw [hp, hq]
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  | mul_X p j hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul hah, subst_X hah,
      Pi.add_apply, subst_mul ha, subst_X ha, Derivation.leibniz, smul_eq_mul, subst_add ha] at hp ⊢
    have hmul : (∑ i, h i * subst a (pderiv i (p : MvPowerSeries σ R))) * h j = 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [mul_right_comm, hh i j, zero_mul]
    have hsum : (∑ i, h i * subst a (pderiv i (p : MvPowerSeries σ R))) * a j =
        ∑ i, h i * (a j * subst a (pderiv i (p : MvPowerSeries σ R))) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hp, add_mul, mul_add, mul_add, hmul, add_zero, hsum]
    simp only [pderiv_X, Pi.single_apply, mul_ite, mul_one, mul_zero, apply_ite (subst a),
      h0, h1, mul_add, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    ring

/-- **The first-order Taylor formula at `X`**: if the perturbations `h i` pairwise multiply to
zero, then `f(X + h) = f + ∑ᵢ hᵢ · ∂ᵢ f`. -/
theorem subst_X_add_of_mul_eq_zero [CommRing R] [Fintype σ] {h : σ → MvPowerSeries σ R}
    (hh : ∀ i j, h i * h j = 0) (f : MvPowerSeries σ R) :
    subst (X + h) f = f + ∑ i, h i * pderiv i f := by
  rw [subst_add_of_mul_eq_zero HasSubst.X hh, subst_self]
  simp

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
