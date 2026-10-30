/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.Taylor
public import TauCeti.RingTheory.PowerSeries.HasseDeriv.Basic

/-!
# Hasse derivatives of multivariate power series

For a multi-index `d : σ →₀ ℕ`, the `d`-th Hasse derivative of a multivariate power series
`f = ∑ₘ aₘ Xᵐ` is

```text
∂^d f = ∑ₘ (∏ⱼ (mⱼ + dⱼ choose dⱼ)) • aₘ₊d Xᵐ.
```

It is defined coefficientwise over any semiring: only natural-number multiples of coefficients
occur, so the coefficients need not commute. Unlike `(∂/∂X)^d / d!`, it needs no division by
factorials, so it keeps its meaning in positive characteristic; in a single variable `Xᵢ`,
`k! • ∂^(k eᵢ)` is the `k`-th iterated partial derivative. The coefficient formula, the values on
monomials, the composition rule and commutation hold over any semiring.

On polynomials, `∂^d` is `MvPolynomial.hasseDeriv`, whose values are the Taylor coefficients of a
polynomial (`MvPolynomial.coeff_taylor_X_map_C`). Since a coefficient of `∂^d f` only sees
finitely many coefficients of `f`, the Leibniz rule is deduced from the polynomial Leibniz rule
`MvPolynomial.hasseDeriv_mul`; like the comparison with polynomials and with partial derivatives,
it is stated over commutative semirings, where `MvPolynomial` and `MvPowerSeries.pderiv` live.
The definitions and lemmas parallel the one-variable `PowerSeries.hasseDeriv` and the polynomial
`MvPolynomial.hasseDeriv`. Hasse derivatives act on restricted power series at every positive
polyradius (`TauCeti.RingTheory.MvPowerSeries.HasseDeriv.GaussNorm`).

## Main definitions

* `MvPowerSeries.hasseDeriv d`: the `d`-th Hasse derivative, an `R`-linear endomorphism of
  `MvPowerSeries σ R`.

## Main results

* `MvPowerSeries.coeff_hasseDeriv`: `[Xᵐ] ∂^d f = (∏ⱼ (mⱼ + dⱼ choose dⱼ)) [X^(m + d)] f`.
* `MvPowerSeries.hasseDeriv_monomial`, `MvPowerSeries.hasseDeriv_C`: values on monomials and
  constants.
* `MvPowerSeries.hasseDeriv_map`: Hasse derivatives commute with coefficient maps.
* `MvPowerSeries.hasseDeriv_comp`: `∂^a ∘ ∂^b = (∏ⱼ (aⱼ + bⱼ choose aⱼ)) • ∂^(a + b)`, and
  `MvPowerSeries.hasseDeriv_comm`: Hasse derivatives commute with each other.
* `MvPowerSeries.hasseDeriv_coe` and `MvPowerSeries.trunc'_hasseDeriv`: comparison with
  `MvPolynomial.hasseDeriv` on polynomials and on truncations.
* `MvPowerSeries.hasseDeriv_mul`: the Leibniz rule `∂^d (f g) = ∑_{a + b = d} ∂^a f · ∂^b g`.
* `MvPowerSeries.factorial_smul_hasseDeriv_single`: `k! • ∂^(k eᵢ) f = (∂/∂Xᵢ)^[k] f`.
* `PowerSeries.hasseDeriv_eq_mvPowerSeries_hasseDeriv`: on `R⟦X⟧ = MvPowerSeries Unit R`,
  `PowerSeries.hasseDeriv k` is `MvPowerSeries.hasseDeriv (single () k)`.

## References

* H. Hasse, *Theorie der höheren Differentiale in einem algebraischen Funktionenkörper mit
  vollkommenem Konstantenkörper bei beliebiger Charakteristik*, J. Reine Angew. Math. 175 (1936).
-/

public section

noncomputable section

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

section Semiring

variable [Semiring R]

/-- The `d`-th Hasse derivative `∂^d` of a multivariate power series, the `R`-linear map with
`[Xᵐ] ∂^d f = (∏ⱼ (mⱼ + dⱼ choose dⱼ)) [X^(m + d)] f`. Over a commutative semiring, in a single
variable `Xᵢ`, `k! • ∂^(k eᵢ)` is the `k`-th iterated partial derivative
(`MvPowerSeries.factorial_smul_hasseDeriv_single`). -/
def hasseDeriv (d : σ →₀ ℕ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R where
  toFun f m := ((d.prod fun j k ↦ (m j + k).choose k : ℕ) : R) * coeff (m + d) f
  map_add' _ _ := funext fun _ ↦ mul_add _ _ _
  map_smul' a _ := funext fun _ ↦ (Nat.cast_commute _ a).left_comm _

/-- The coefficients of a Hasse derivative:
`[Xᵐ] ∂^d f = (∏ⱼ (mⱼ + dⱼ choose dⱼ)) [X^(m + d)] f`. -/
@[simp]
theorem coeff_hasseDeriv (d m : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    coeff m (hasseDeriv d f) =
      ((d.prod fun j k ↦ (m j + k).choose k : ℕ) : R) * coeff (m + d) f :=
  (rfl)

/-- The `0`-th Hasse derivative is the identity. -/
@[simp]
theorem hasseDeriv_zero : hasseDeriv (0 : σ →₀ ℕ) = (LinearMap.id : MvPowerSeries σ R →ₗ[R] _) := by
  ext f m
  simp

/-- The Hasse derivative of a monomial: `∂^d (a Xᵐ) = (∏ⱼ (mⱼ choose dⱼ)) a X^(m - d)`. The
coefficient vanishes unless `d ≤ m`. -/
@[simp]
theorem hasseDeriv_monomial (d m : σ →₀ ℕ) (a : R) :
    hasseDeriv d (monomial m a) =
      monomial (m - d) (((d.prod fun j k ↦ (m j).choose k : ℕ) : R) * a) := by
  classical
  ext n
  rw [coeff_hasseDeriv, coeff_monomial, coeff_monomial]
  by_cases h : n + d = m
  · subst h
    simp only [↓reduceIte, add_tsub_cancel_right]
    rw [Finsupp.prod_congr (g2 := fun j k ↦ ((n + d) j).choose k) fun j _ ↦ by
      rw [Finsupp.add_apply]]
  · rw [ite_eq_right_iff.2 fun h' ↦ absurd h' h, mul_zero, eq_comm, ite_eq_right_iff]
    intro hn
    by_cases hdm : d ≤ m
    · exact absurd ((tsub_eq_iff_eq_add_of_le hdm).1 hn.symm).symm h
    · simp [prod_choose_eq_zero hdm]

/-- Every Hasse derivative of positive order kills constants. -/
@[simp]
theorem hasseDeriv_C {d : σ →₀ ℕ} (hd : d ≠ 0) (a : R) : hasseDeriv d (C a) = 0 := by
  rw [← monomial_zero_eq_C_apply, hasseDeriv_monomial,
    prod_choose_eq_zero (by simpa [nonpos_iff_eq_zero] using hd)]
  simp

/-- Every Hasse derivative of positive order kills the constant series `1`. -/
@[simp]
theorem hasseDeriv_one {d : σ →₀ ℕ} (hd : d ≠ 0) :
    hasseDeriv d (1 : MvPowerSeries σ R) = 0 := by
  simpa only [map_one] using hasseDeriv_C (R := R) hd 1

/-- Hasse derivatives commute with coefficient maps. -/
@[simp]
theorem hasseDeriv_map {S : Type*} [Semiring S] (φ : R →+* S) (d : σ →₀ ℕ)
    (f : MvPowerSeries σ R) : hasseDeriv d (map φ f) = map φ (hasseDeriv d f) := by
  ext m
  simp

/-- The composition rule `∂^a ∘ ∂^b = (∏ⱼ (aⱼ + bⱼ choose aⱼ)) • ∂^(a + b)`. -/
theorem hasseDeriv_comp (a b : σ →₀ ℕ) :
    (hasseDeriv a).comp (hasseDeriv b) =
      (a.prod fun j k ↦ (k + b j).choose k) •
        (hasseDeriv (a + b) : MvPowerSeries σ R →ₗ[R] _) := by
  classical
  ext f m
  -- The binomial identity behind the composition rule is the same as for polynomials, so it is
  -- read off from `MvPolynomial.hasseDeriv_comp` over `ℕ`, applied to the monomial `X^(m + a + b)`.
  have key := congrArg (fun p : MvPolynomial σ ℕ ↦ p.coeff m) <| LinearMap.congr_fun
    (MvPolynomial.hasseDeriv_comp (R := ℕ) a b) (MvPolynomial.monomial (m + a + b) 1)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, MvPolynomial.hasseDeriv_coeff,
    MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, Nat.cast_id, add_assoc, ite_true,
    mul_one, smul_eq_mul] at key
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_nsmul, coeff_hasseDeriv]
  rw [nsmul_eq_mul, ← mul_assoc, ← mul_assoc, add_assoc]
  exact_mod_cast congrArg (fun c : ℕ ↦ (c : R) * coeff (m + (a + b)) f) key

/-- Hasse derivatives commute: `∂^a ∘ ∂^b = ∂^b ∘ ∂^a`. In particular Hasse derivatives in
different variables commute. -/
theorem hasseDeriv_comm (a b : σ →₀ ℕ) :
    (hasseDeriv a).comp (hasseDeriv b) =
      ((hasseDeriv b).comp (hasseDeriv a) : MvPowerSeries σ R →ₗ[R] _) := by
  rw [hasseDeriv_comp, hasseDeriv_comp, prod_choose_add_comm, add_comm]

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- On polynomials, the Hasse derivative of power series is `MvPolynomial.hasseDeriv`. -/
@[simp]
theorem hasseDeriv_coe (d : σ →₀ ℕ) (P : MvPolynomial σ R) :
    hasseDeriv d (P : MvPowerSeries σ R) = (MvPolynomial.hasseDeriv d P : MvPowerSeries σ R) := by
  ext m
  simp [MvPolynomial.hasseDeriv_coeff]

/-- The coefficients of `∂^d f` of exponent at most `n` only depend on the coefficients of `f` of
exponent at most `n + d`. -/
theorem trunc'_hasseDeriv [DecidableEq σ] (n d : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    trunc' R n (hasseDeriv d f) = MvPolynomial.hasseDeriv d (trunc' R (n + d) f) := by
  ext m
  simp only [coeff_trunc', MvPolynomial.hasseDeriv_coeff, coeff_hasseDeriv, add_le_add_iff_right]
  split_ifs <;> simp

/-- The **Leibniz rule** for Hasse derivatives: `∂^d (f g) = ∑_{a + b = d} ∂^a f · ∂^b g`. -/
theorem hasseDeriv_mul [DecidableEq σ] (d : σ →₀ ℕ) (f g : MvPowerSeries σ R) :
    hasseDeriv d (f * g) =
      ∑ x ∈ Finset.antidiagonal d, hasseDeriv x.1 f * hasseDeriv x.2 g := by
  ext m
  -- Both sides only see the coefficients of `f` and `g` of exponent at most `N = m + d`, so `f`
  -- and `g` may be replaced by their truncations, to which the polynomial Leibniz rule applies.
  set N := m + d
  have htrunc (h : MvPowerSeries σ R) {e u : σ →₀ ℕ} (he : e ≤ d) (hu : u ≤ m) :
      coeff u (hasseDeriv e (trunc' R N h : MvPowerSeries σ R)) = coeff u (hasseDeriv e h) := by
    rw [coeff_hasseDeriv, coeff_hasseDeriv, MvPolynomial.coeff_coe, coeff_trunc',
      ite_eq_left_iff.2 fun h' ↦ absurd (add_le_add hu he) h']
  have hterm (x : (σ →₀ ℕ) × (σ →₀ ℕ)) (hx : x ∈ Finset.antidiagonal d) :
      coeff m (hasseDeriv x.1 (trunc' R N f : MvPowerSeries σ R) *
          hasseDeriv x.2 (trunc' R N g : MvPowerSeries σ R)) =
        coeff m (hasseDeriv x.1 f * hasseDeriv x.2 g) := by
    rw [Finset.mem_antidiagonal] at hx
    simp only [coeff_mul]
    refine Finset.sum_congr rfl fun uv huv ↦ ?_
    rw [Finset.mem_antidiagonal] at huv
    rw [htrunc f (hx ▸ le_self_add) (huv ▸ le_self_add),
      htrunc g (hx ▸ le_add_self) (huv ▸ le_add_self)]
  rw [map_sum, ← Finset.sum_congr rfl hterm, coeff_hasseDeriv,
    ← coeff_trunc'_mul_trunc'_eq_coeff_mul N f g le_rfl, ← MvPolynomial.hasseDeriv_coeff,
    MvPolynomial.hasseDeriv_mul, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [hasseDeriv_coe, hasseDeriv_coe, ← MvPolynomial.coe_mul, MvPolynomial.coeff_coe]

/-- Differentiating `∂^(k eᵢ) f` in `Xᵢ` gives `(k + 1) ∂^((k + 1) eᵢ) f`. -/
@[simp]
theorem pderiv_hasseDeriv_single (i : σ) (k : ℕ) (f : MvPowerSeries σ R) :
    pderiv i (hasseDeriv (single i k) f) = (k + 1) • hasseDeriv (single i (k + 1)) f := by
  ext n
  have hidx : n + single i 1 + single i k = n + single i (k + 1) := by
    rw [add_assoc, ← single_add, add_comm 1 k]
  -- `(nᵢ + 1 + k choose k) (nᵢ + 1) = (k + 1) (nᵢ + (k + 1) choose (k + 1))`: both sides are
  -- `(nᵢ + k + 1) (nᵢ + k choose k)`.
  have hchoose : (n i + 1 + k).choose k * (n i + 1) = (k + 1) * (n i + (k + 1)).choose (k + 1) := by
    have h₁ := Nat.choose_mul_succ_eq (n i + k) k
    have h₂ := Nat.add_one_mul_choose_eq (n i + k) k
    rw [show n i + k + 1 - k = n i + 1 by omega] at h₁
    rw [show n i + 1 + k = n i + k + 1 by omega, show n i + (k + 1) = n i + k + 1 by omega]
    linarith
  rw [map_nsmul, coeff_pderiv, coeff_hasseDeriv, coeff_hasseDeriv, hidx, nsmul_eq_mul]
  simp only [prod_single_index, Nat.choose_zero_right, Finsupp.add_apply, single_eq_same]
  rw [mul_right_comm, ← mul_assoc]
  congr 1
  exact_mod_cast congrArg (Nat.cast : ℕ → R) hchoose

/-- The Hasse derivative `∂^(k eᵢ)` is the `k`-th partial derivative in `Xᵢ` divided by `k!`:
`k! • ∂^(k eᵢ) f = (∂/∂Xᵢ)^[k] f`. -/
theorem factorial_smul_hasseDeriv_single (i : σ) (k : ℕ) (f : MvPowerSeries σ R) :
    k.factorial • hasseDeriv (single i k) f = (pderiv i)^[k] f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih, map_nsmul, pderiv_hasseDeriv_single, smul_smul,
      Nat.factorial_succ, mul_comm]

/-- The first Hasse derivative in `Xᵢ` is the partial derivative in `Xᵢ`. -/
@[simp]
theorem hasseDeriv_single_one (i : σ) (f : MvPowerSeries σ R) :
    hasseDeriv (single i 1) f = pderiv i f := by
  simpa using factorial_smul_hasseDeriv_single i 1 f

end CommSemiring

end MvPowerSeries

namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- On `R⟦X⟧ = MvPowerSeries Unit R`, the `k`-th Hasse derivative of power series is the
multivariate Hasse derivative of multi-index `single () k`. -/
theorem hasseDeriv_eq_mvPowerSeries_hasseDeriv (k : ℕ) (f : R⟦X⟧) :
    hasseDeriv k f = MvPowerSeries.hasseDeriv (Finsupp.single () k) f := by
  ext n
  rw [coeff_hasseDeriv]
  simp [coeff, MvPowerSeries.coeff_hasseDeriv, Finsupp.prod_single_index, ← Finsupp.single_add]

end PowerSeries
