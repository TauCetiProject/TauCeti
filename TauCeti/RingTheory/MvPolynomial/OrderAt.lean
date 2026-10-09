/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import TauCeti.Algebra.MvPolynomial.Equiv
public import TauCeti.RingTheory.MvPowerSeries.Derivative

/-!
# The order of vanishing of a multivariate polynomial at a point

`MvPolynomial.taylor a` is the Taylor shift `p ↦ p(X + a)`, which substitutes `Xᵢ + aᵢ` for
each variable `Xᵢ`; the coefficients of `taylor a p` are the Taylor coefficients of `p` at `a`.
The order of vanishing `p.orderAt a : ℕ∞` is the least total degree of a nonzero Taylor
coefficient of `p` at `a`, and `⊤` when `p = 0`. It is the order of `taylor a p` viewed as a
multivariate power series, so it is positive exactly at the zeros of `p`, and over a domain it
is additive on products.

This is the ambient order of `p` at `a`, computed in all variables at once. It is the invariant
of order-invariant cylindrical algebraic decompositions in McCallum's projection theory: there
each polynomial is required to have constant order on each cell, which is stronger than constant
sign.

Over a ring without additive torsion, such as `ℝ`, the order is detected by partial derivatives:
`p` has order at least `n` at `a` exactly when every iterated partial derivative of `p` of order
less than `n` vanishes at `a`; since a nonzero polynomial vanishes to order at most its total
degree, finitely many derivatives suffice. Substituting polynomials into `p` can only increase
the order at corresponding points, and renaming the variables along an injective map does not
change it.
The Taylor shift itself preserves the degree in each variable (`MvPolynomial.degreeOf_taylor`).

## Main definitions

* `MvPolynomial.taylor`: the Taylor shift `p ↦ p(X + a)`.
* `MvPolynomial.orderAt`: the order of vanishing of `p` at `a`.

## Main results

* `MvPolynomial.orderAt_eq_top_iff`: the order is `⊤` exactly for the zero polynomial.
* `MvPolynomial.orderAt_eq_zero_iff`, `MvPolynomial.orderAt_pos_iff`: the order is positive
  exactly at the zeros of `p`.
* `MvPolynomial.orderAt_mul`: over a domain, the order of a product is the sum of the orders.
* `MvPolynomial.succ_le_orderAt_iff`: `p` has order at least `n + 1` at `a` if and only if
  `p` vanishes at `a` and every partial derivative of `p` has order at least `n` there.
* `MvPolynomial.le_orderAt_iff_eval_foldl_pderiv`: the order is at least `n` if and only if
  every iterated partial derivative of order less than `n` vanishes at `a`.
* `MvPolynomial.orderAt_le_totalDegree`: a nonzero polynomial vanishes to order at most its
  total degree.
* `MvPolynomial.orderAt_eq_of_forall_eval_foldl_pderiv_eq_zero_iff`: the order at a point is
  determined by which iterated partial derivatives, up to the total degree, vanish there.
* `MvPolynomial.orderAt_le_orderAt_aeval`: substitution does not decrease the order.
* `MvPolynomial.orderAt_taylor`, `MvPolynomial.orderAt_map`: the order is unchanged by Taylor
  shifts, after translating the point, and by injective coefficient maps.
* `MvPolynomial.orderAt_rename`: renaming along an injective map preserves the order.
* `MvPolynomial.finSuccEquiv_taylor`, `MvPolynomial.coeff_taylor_cons`: singling out the
  variable `X₀` turns the Taylor shift at `a` into the univariate Taylor shift at `a₀` followed by
  the Taylor shift at the remaining coordinates.
* `MvPolynomial.optionEquivRight_rename_finSuccEquivLast_taylor`,
  `MvPolynomial.coeff_taylor_snoc`: moving the last variable `Xₙ` into the coefficients turns the
  Taylor shift at `Fin.snoc α β` into the Taylor shift at the first coordinates `α`, followed by
  the univariate Taylor shift at `β` of each coefficient.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  in *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998),
  pp. 242–268, Section 2 (order of a polynomial at a point, order-invariance).
-/

public section

namespace MvPolynomial

open Finsupp

variable {σ τ R : Type*}

section Taylor

variable [CommSemiring R]

/-- The Taylor shift of a multivariate polynomial at `a`: the substitution `p ↦ p(X + a)` of
`Xᵢ + aᵢ` for each variable `Xᵢ`. The coefficients of `taylor a p` are the Taylor coefficients
of `p` at `a`. -/
noncomputable def taylor (a : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i ↦ X i + C (a i)

theorem taylor_apply (a : σ → R) (p : MvPolynomial σ R) :
    taylor a p = aeval (fun i ↦ X i + C (a i)) p :=
  (rfl)

@[simp]
theorem taylor_X (a : σ → R) (i : σ) : taylor a (X i) = X i + C (a i) :=
  aeval_X _ _

theorem taylor_C (a : σ → R) (r : R) : taylor a (C r) = C r :=
  aeval_C _ _

/-- Taylor shifts commute with coefficient maps, with the center mapped along the same
homomorphism. -/
@[simp]
theorem map_taylor {S : Type*} [CommSemiring S] (p : MvPolynomial σ R) (a : σ → R)
    (f : R →+* S) :
    map f (taylor a p) = taylor (fun i ↦ f (a i)) (map f p) := by
  induction p using MvPolynomial.induction_on <;> simp_all

/-- Taylor coefficients depend polynomially on the center. Evaluate the formal center in
`taylor X (map C p)` at `a` to recover each coefficient of `taylor a p`. -/
@[simp]
theorem eval_coeff_taylor_map_C (p : MvPolynomial σ R) (a : σ → R) (v : σ →₀ ℕ) :
    eval a ((taylor (X : σ → MvPolynomial σ R) (map C p)).coeff v) =
      (taylor a p).coeff v := by
  rw [← coeff_map, map_taylor, map_map]
  have h : (eval a).comp (C : R →+* MvPolynomial σ R) = RingHom.id R := by
    ext r
    simp
  simp [h, map_id]

@[simp]
theorem eval_taylor (a x : σ → R) (p : MvPolynomial σ R) :
    eval x (taylor a p) = eval (x + a) p := by
  induction p using MvPolynomial.induction_on <;> simp_all

/-- The constant Taylor coefficient of `p` at `a` is the value of `p` at `a`. -/
@[simp]
theorem constantCoeff_taylor (a : σ → R) (p : MvPolynomial σ R) :
    constantCoeff (taylor a p) = eval a p := by
  rw [← eval_zero, eval_taylor, zero_add]

@[simp]
theorem taylor_zero (p : MvPolynomial σ R) : taylor 0 p = p := by
  induction p using MvPolynomial.induction_on <;> simp_all

theorem taylor_taylor (a b : σ → R) (p : MvPolynomial σ R) :
    taylor a (taylor b p) = taylor (a + b) p := by
  induction p using MvPolynomial.induction_on <;> simp_all [add_assoc]

/-- The Taylor shift does not increase the total degree. -/
theorem totalDegree_taylor_le (a : σ → R) (p : MvPolynomial σ R) :
    (taylor a p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [p.as_sum, map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd ↦ ?_)
  rw [taylor_apply, aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans (le_trans ?_ (le_totalDegree hd))
  refine Finset.sum_le_sum fun i _ ↦ (totalDegree_pow _ _).trans ?_
  refine (Nat.mul_le_mul_left _ ((totalDegree_add _ _).trans (max_le ?_ ?_))).trans_eq
    (mul_one _)
  · exact (totalDegree_monomial_le _ _).trans_eq (by simp)
  · simp

/-- Partial differentiation commutes with the Taylor shift. -/
@[simp]
theorem pderiv_taylor (a : σ → R) (i : σ) (p : MvPolynomial σ R) :
    pderiv i (taylor a p) = taylor a (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    obtain rfl | hj := eq_or_ne j i
    · simp [hp]
    · simp [hp, pderiv_X_of_ne hj]

/-- The Taylor shift does not increase the degree in any variable. -/
theorem degreeOf_taylor_le (a : σ → R) (i : σ) (p : MvPolynomial σ R) :
    (taylor a p).degreeOf i ≤ p.degreeOf i := by
  classical
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.elim (taylor a p) 0]
  conv_lhs => rw [p.as_sum, map_sum]
  refine (degreeOf_sum_le i _ _).trans (Finset.sup_le fun m hm ↦ ?_)
  rw [taylor_apply, aeval_monomial, algebraMap_eq]
  refine (degreeOf_C_mul_le _ i _).trans ((degreeOf_prod_le i _ _).trans ?_)
  calc ∑ j ∈ m.support, ((X j + C (a j)) ^ m j).degreeOf i
      ≤ ∑ j ∈ m.support, if i = j then m j else 0 := by
        refine Finset.sum_le_sum fun j _ ↦ (degreeOf_pow_le i _ _).trans ?_
        have : (X j + C (a j) : MvPolynomial σ R).degreeOf i ≤ if i = j then 1 else 0 :=
          (degreeOf_add_le i _ _).trans (by simp [degreeOf_X, degreeOf_C])
        split_ifs at this ⊢ <;> simpa using Nat.mul_le_mul_left (m j) this
    _ ≤ m i := by rw [Finset.sum_ite_eq]; split_ifs <;> simp
    _ ≤ p.degreeOf i := monomial_le_degreeOf i hm

/-- Singling out the variable `X₀` commutes with the Taylor shift: shifting `X₀` by `a₀` is the
Taylor shift of the resulting univariate polynomial at `a₀`, and the remaining variables are
shifted coefficientwise. -/
theorem finSuccEquiv_taylor {n : ℕ} (a : Fin (n + 1) → R) (p : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv R n (taylor a p) =
      (Polynomial.taylor (C (a 0)) (finSuccEquiv R n p)).map
        (taylor (Fin.tail a) : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) R) := by
  have hC (r : R) : finSuccEquiv R n (C r) = Polynomial.C (C r) := by simp [finSuccEquiv_apply]
  induction p using MvPolynomial.induction_on with
  | C r => simp [hC]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    cases i using Fin.cases with
    | zero => simp [hp, hC, finSuccEquiv_X_zero, Polynomial.taylor_mul, Polynomial.map_mul]
    | succ j =>
      simp [hp, hC, finSuccEquiv_X_succ, Polynomial.taylor_mul, Polynomial.map_mul, Fin.tail]

/-- The Taylor coefficients of `p` at `a`, read off after singling out the variable `X₀`: the
coefficient of `X₀ ^ i * Xᵘ` is the coefficient of `Xᵘ` in the Taylor shift at `Fin.tail a` of
the `i`-th coefficient of the univariate Taylor expansion at `a₀`. -/
theorem coeff_taylor_cons {n : ℕ} (a : Fin (n + 1) → R) (p : MvPolynomial (Fin (n + 1)) R)
    (i : ℕ) (u : Fin n →₀ ℕ) :
    (taylor a p).coeff (u.cons i) =
      (taylor (Fin.tail a)
        ((Polynomial.taylor (C (a 0)) (finSuccEquiv R n p)).coeff i)).coeff u := by
  rw [← finSuccEquiv_coeff_coeff, finSuccEquiv_taylor, Polynomial.coeff_map]
  rfl

/-- Moving the last variable `Xₙ` into the coefficients commutes with the Taylor shift: shifting
at `Fin.snoc α β` becomes the Taylor shift at the constant polynomials `α`, followed by the
univariate Taylor shift at `β` of every coefficient. -/
theorem optionEquivRight_rename_finSuccEquivLast_taylor {n : ℕ} (α : Fin n → R) (β : R)
    (f : MvPolynomial (Fin (n + 1)) R) :
    optionEquivRight R (Fin n) (rename finSuccEquivLast (taylor (Fin.snoc α β) f)) =
      map (Polynomial.taylorAlgHom β : Polynomial R →+* Polynomial R)
        (taylor (Polynomial.C ∘ α) (optionEquivRight R (Fin n) (rename finSuccEquivLast f))) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, taylor_X, rename_X]
    congr 1
    cases i using Fin.lastCases with
    | last => simp [Polynomial.taylor_X]
    | cast j => simp

/-- The Taylor coefficients of `f` at `Fin.snoc α β`, read off after moving the last variable
`Xₙ` into the coefficients: the coefficient of `Xᵘ * Xₙ ^ k` is the coefficient of `Xₙ ^ k` in
the univariate Taylor expansion at `β` of the coefficient of `Xᵘ` in the Taylor shift at `α`. -/
theorem coeff_taylor_snoc {n : ℕ} (α : Fin n → R) (β : R) (f : MvPolynomial (Fin (n + 1)) R)
    (u : Fin n →₀ ℕ) (k : ℕ) :
    (taylor (Fin.snoc α β) f).coeff (u.snoc k) =
      (Polynomial.taylor β ((taylor (Polynomial.C ∘ α)
        (optionEquivRight R (Fin n) (rename finSuccEquivLast f))).coeff u)).coeff k := by
  rw [← optionEquivRight_rename_finSuccEquivLast_coeff_coeff,
    optionEquivRight_rename_finSuccEquivLast_taylor, coeff_map]
  simp

end Taylor

section TaylorRing

variable [CommRing R]

@[simp]
theorem taylor_neg_taylor (a : σ → R) (p : MvPolynomial σ R) : taylor (-a) (taylor a p) = p := by
  rw [taylor_taylor, neg_add_cancel, taylor_zero]

/-- The Taylor shift preserves the total degree. -/
@[simp]
theorem totalDegree_taylor (a : σ → R) (p : MvPolynomial σ R) :
    (taylor a p).totalDegree = p.totalDegree :=
  (totalDegree_taylor_le a p).antisymm <| by simpa using totalDegree_taylor_le (-a) (taylor a p)

theorem taylor_injective (a : σ → R) : Function.Injective (taylor a) :=
  Function.LeftInverse.injective (taylor_neg_taylor a)

@[simp]
theorem taylor_eq_zero {a : σ → R} {p : MvPolynomial σ R} : taylor a p = 0 ↔ p = 0 :=
  map_eq_zero_iff _ (taylor_injective a)

/-- The Taylor shift preserves the degree in each variable. -/
@[simp]
theorem degreeOf_taylor (a : σ → R) (i : σ) (p : MvPolynomial σ R) :
    (taylor a p).degreeOf i = p.degreeOf i :=
  (degreeOf_taylor_le a i p).antisymm <| by
    simpa using degreeOf_taylor_le (-a) i (taylor a p)

end TaylorRing

section Substitution

variable [CommSemiring R]

/-- The constant coefficient of a polynomial viewed as a power series is its constant
coefficient as a polynomial. -/
@[simp]
theorem constantCoeff_coe (p : MvPolynomial σ R) :
    MvPowerSeries.constantCoeff (p : MvPowerSeries σ R) = constantCoeff p :=
  (rfl)

/-- Substituting polynomials without constant terms into a polynomial does not decrease its
order. -/
theorem order_coe_le_order_coe_aeval {h : σ → MvPolynomial τ R}
    (hh : ∀ i, constantCoeff (h i) = 0) (q : MvPolynomial σ R) :
    (q : MvPowerSeries σ R).order ≤ (aeval h q : MvPowerSeries τ R).order := by
  conv_rhs => rw [q.as_sum, map_sum, ← coeToMvPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_induction _
    (fun f : MvPowerSeries τ R ↦ (q : MvPowerSeries σ R).order ≤ f.order)
    (fun f g hf hg ↦ (le_min hf hg).trans (MvPowerSeries.min_order_le_add ..)) (by simp)
    fun d hd ↦ ?_
  refine (MvPowerSeries.order_le (d := d) (by simpa using hd)).trans ?_
  rw [aeval_monomial, map_mul, Finsupp.prod, map_prod, coeToMvPowerSeries.ringHom_apply]
  refine le_trans ?_ (le_add_self.trans (MvPowerSeries.le_order_mul ..))
  refine le_trans ?_ (MvPowerSeries.le_order_prod ..)
  rw [degree_apply, Nat.cast_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [map_pow, coeToMvPowerSeries.ringHom_apply]
  refine MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ ?_
  rw [constantCoeff_coe, hh i]

end Substitution

section OrderAt

section CommSemiring

variable [CommSemiring R] {p q : MvPolynomial σ R} {a : σ → R}

/-- The order of vanishing of `p` at `a`: the least total degree of a nonzero Taylor coefficient
of `p` at `a`, and `⊤` if there is none. -/
noncomputable def orderAt (p : MvPolynomial σ R) (a : σ → R) : ℕ∞ :=
  (taylor a p : MvPowerSeries σ R).order

theorem orderAt_def (p : MvPolynomial σ R) (a : σ → R) :
    p.orderAt a = (taylor a p : MvPowerSeries σ R).order :=
  (rfl)

/-- `p` has order at least `n` at `a` exactly when every Taylor coefficient of `p` at `a` of
total degree less than `n` vanishes. -/
theorem le_orderAt_iff {n : ℕ∞} :
    n ≤ p.orderAt a ↔ ∀ d : σ →₀ ℕ, (d.degree : ℕ∞) < n → (taylor a p).coeff d = 0 := by
  refine ⟨fun h d hd ↦ ?_, fun h ↦ MvPowerSeries.le_order fun d hd ↦ by simpa using h d hd⟩
  simpa using MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le hd h)

theorem orderAt_le {d : σ →₀ ℕ} (h : (taylor a p).coeff d ≠ 0) : p.orderAt a ≤ d.degree :=
  MvPowerSeries.order_le (by simpa using h)

/-- `p` has order exactly `n` at `a` when `n` is the least total degree of a nonzero Taylor
coefficient of `p` at `a`: some Taylor coefficient of total degree `n` is nonzero, and every
Taylor coefficient of smaller total degree vanishes. -/
theorem orderAt_eq_coe_iff {n : ℕ} :
    p.orderAt a = n ↔ (∃ d, (taylor a p).coeff d ≠ 0 ∧ d.degree = n) ∧
      ∀ d : σ →₀ ℕ, d.degree < n → (taylor a p).coeff d = 0 := by
  simp [orderAt_def, MvPowerSeries.order_eq_nat]

@[simp]
theorem orderAt_zero (a : σ → R) : (0 : MvPolynomial σ R).orderAt a = ⊤ := by
  simp [orderAt_def]

/-- The order of `p` at `a` is zero exactly when `p` does not vanish at `a`. -/
theorem orderAt_eq_zero_iff : p.orderAt a = 0 ↔ eval a p ≠ 0 := by
  rw [← not_iff_not, not_not, ← Ne, orderAt_def,
    MvPowerSeries.order_ne_zero_iff_constCoeff_eq_zero, constantCoeff_coe, constantCoeff_taylor]

/-- The order of `p` at `a` is positive exactly when `p` vanishes at `a`. -/
theorem orderAt_pos_iff : 0 < p.orderAt a ↔ eval a p = 0 := by
  rw [pos_iff_ne_zero, Ne, orderAt_eq_zero_iff, not_not]

theorem orderAt_C_of_ne_zero {r : R} (hr : r ≠ 0) (a : σ → R) : (C r).orderAt a = 0 :=
  orderAt_eq_zero_iff.mpr (by simpa using hr)

@[simp]
theorem orderAt_one [Nontrivial R] (a : σ → R) : (1 : MvPolynomial σ R).orderAt a = 0 := by
  simpa using orderAt_C_of_ne_zero (one_ne_zero (α := R)) a

theorem min_orderAt_le_orderAt_add (p q : MvPolynomial σ R) (a : σ → R) :
    min (p.orderAt a) (q.orderAt a) ≤ (p + q).orderAt a := by
  simpa [orderAt_def] using MvPowerSeries.min_order_le_add

theorem le_orderAt_mul (p q : MvPolynomial σ R) (a : σ → R) :
    p.orderAt a + q.orderAt a ≤ (p * q).orderAt a := by
  simpa [orderAt_def] using MvPowerSeries.le_order_mul

/-- The order of the Taylor shift of `p` at `a` is the order of `p` at the translated point. -/
@[simp]
theorem orderAt_taylor (a b : σ → R) (p : MvPolynomial σ R) :
    (taylor a p).orderAt b = p.orderAt (b + a) := by
  rw [orderAt_def, orderAt_def, taylor_taylor]

/-- Mapping the coefficients along an injective ring homomorphism does not change the order, at
the image of the point. -/
theorem orderAt_map {S : Type*} [CommSemiring S] {f : R →+* S} (hf : Function.Injective f)
    (p : MvPolynomial σ R) (a : σ → R) :
    (map f p).orderAt (fun i ↦ f (a i)) = p.orderAt a := by
  refine eq_of_forall_le_iff fun n ↦ ?_
  simp only [le_orderAt_iff, ← map_taylor, coeff_map, map_eq_zero_iff f hf]

end CommSemiring

section CommRing

variable [CommRing R] {p q : MvPolynomial σ R} {a : σ → R}

/-- Only the zero polynomial has infinite order at a point. -/
@[simp]
theorem orderAt_eq_top_iff : p.orderAt a = ⊤ ↔ p = 0 := by
  simp [orderAt_def, MvPowerSeries.order_eq_top_iff, coe_eq_zero_iff]

/-- A nonzero polynomial vanishes at each point to order at most its total degree. -/
theorem orderAt_le_totalDegree (hp : p ≠ 0) (a : σ → R) : p.orderAt a ≤ p.totalDegree := by
  obtain ⟨d, hd⟩ := ne_zero_iff.1 (taylor_eq_zero.not.2 hp : taylor a p ≠ 0)
  calc p.orderAt a ≤ d.degree := orderAt_le hd
    _ ≤ p.totalDegree := by
      exact_mod_cast totalDegree_taylor a p ▸ le_totalDegree (mem_support_iff.2 hd)

@[simp]
theorem orderAt_neg (p : MvPolynomial σ R) (a : σ → R) : (-p).orderAt a = p.orderAt a := by
  simp only [orderAt_def, map_neg, ← coeToMvPowerSeries.ringHom_apply, MvPowerSeries.order_neg]

/-- The coordinate function `Xᵢ - aᵢ` vanishes to order one at `a`. -/
theorem orderAt_X_sub_C [Nontrivial R] (a : σ → R) (i : σ) : (X i - C (a i)).orderAt a = 1 := by
  rw [orderAt_def, map_sub, taylor_X, taylor_C, add_sub_cancel_right, coe_X, MvPowerSeries.X_def,
    MvPowerSeries.order_monomial_of_ne_zero one_ne_zero, degree_single, Nat.cast_one]

/-- Over a domain, the order of a product is the sum of the orders. -/
theorem orderAt_mul [NoZeroDivisors R] (p q : MvPolynomial σ R) (a : σ → R) :
    (p * q).orderAt a = p.orderAt a + q.orderAt a := by
  simp [orderAt_def, MvPowerSeries.order_mul]

/-- Over a domain, the order of `p ^ n` at `a` is `n` times the order of `p` at `a`. -/
theorem orderAt_pow [NoZeroDivisors R] [Nontrivial R] (p : MvPolynomial σ R) (a : σ → R)
    (n : ℕ) : (p ^ n).orderAt a = n • p.orderAt a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, orderAt_mul, ih, succ_nsmul]

/-- Over a domain, the order of a finite product is the sum of the orders of its factors. -/
theorem orderAt_prod [NoZeroDivisors R] [Nontrivial R] {ι : Type*}
    (p : ι → MvPolynomial σ R) (s : Finset ι) (a : σ → R) :
    (∏ i ∈ s, p i).orderAt a = ∑ i ∈ s, (p i).orderAt a := by
  simpa only [orderAt_def, ← coeToMvPowerSeries.ringHom_apply, map_prod] using
    MvPowerSeries.order_prod (fun i ↦ (taylor a (p i) : MvPowerSeries σ R)) s

/-- Substitution does not decrease the order: if `g` maps the point `b` to `a`, that is,
`eval b (g i) = a i` for every `i`, then the order of `aeval g p` at `b` is at least the order
of `p` at `a`. -/
theorem orderAt_le_orderAt_aeval (g : σ → MvPolynomial τ R) (b : τ → R)
    (p : MvPolynomial σ R) : p.orderAt (fun i ↦ eval b (g i)) ≤ (aeval g p).orderAt b := by
  set a : σ → R := fun i ↦ eval b (g i)
  -- The Taylor shift of `aeval g p` at `b` is a substitution, without constant terms, into the
  -- Taylor shift of `p` at `a`.
  set h : σ → MvPolynomial τ R := fun i ↦ taylor b (g i) - C (a i)
  have key : taylor b (aeval g p) = aeval h (taylor a p) := by
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
    congr 1
    ext i : 1
    simp [h, taylor]
  rw [orderAt_def, orderAt_def, key]
  exact order_coe_le_order_coe_aeval (fun i ↦ by simp [h, a]) _

/-- Renaming the variables along an injective map does not change the order. -/
theorem orderAt_rename {f : σ → τ} (hf : Function.Injective f) (p : MvPolynomial σ R)
    (b : τ → R) : (rename f p).orderAt b = p.orderAt (b ∘ f) := by
  refine le_antisymm ?_ ?_
  · -- Undo the renaming by substituting `Xᵢ` for `X_{f i}` and `b j` for the other variables.
    let g : τ → MvPolynomial σ R := Function.extend f X (fun j ↦ C (b j))
    have hg : (fun j ↦ eval (b ∘ f) (g j)) = b := by
      funext j
      by_cases hj : ∃ i, f i = j
      · obtain ⟨i, rfl⟩ := hj
        simp [g, hf.extend_apply]
      · simp [g, Function.extend_apply' _ _ _ hj]
    have hgf : aeval g (rename f p) = p := by
      rw [aeval_rename]
      convert aeval_X_left_apply p
      funext i
      simp [g, hf.extend_apply]
    simpa [hg, hgf] using orderAt_le_orderAt_aeval g (b ∘ f) (rename f p)
  · have := orderAt_le_orderAt_aeval (X ∘ f) b p
    simp only [Function.comp_apply, eval_X] at this
    rwa [rename_eq_aeval]

end CommRing

section Derivative

variable [CommRing R] [IsAddTorsionFree R] {p : MvPolynomial σ R} {a : σ → R}

/-- Over a ring without additive torsion, `p` has order at least `n + 1` at `a`, for `n : ℕ∞`,
if and only if `p` vanishes at `a` and every partial derivative has order at least `n` there. -/
theorem succ_le_orderAt_iff {n : ℕ∞} :
    n + 1 ≤ p.orderAt a ↔
      eval a p = 0 ∧ ∀ i, n ≤ (pderiv i p).orderAt a := by
  rw [orderAt_def, MvPowerSeries.succ_le_order_iff, constantCoeff_coe, constantCoeff_taylor]
  simp only [orderAt_def, MvPowerSeries.pderiv_coe, pderiv_taylor]

/-- A zero at which some partial derivative is nonzero has ambient order one. -/
theorem orderAt_eq_one_of_eval_pderiv_ne_zero (hp : eval a p = 0) {i : σ}
    (hi : eval a (pderiv i p) ≠ 0) : p.orderAt a = 1 := by
  apply le_antisymm
  · apply ENat.lt_two_iff.mp
    apply lt_of_not_ge
    intro h
    have hder := (succ_le_orderAt_iff (n := 1)).mp h
    have hpos := hder.2 i
    rw [Order.one_le_iff_pos, orderAt_pos_iff] at hpos
    exact hi hpos
  · simpa only [Order.one_le_iff_pos, orderAt_pos_iff] using hp

open Classical in
/-- If the fiber through a point is separable, its ambient order is one at a zero
and zero otherwise. No degree preservation in nearby fibers is needed. -/
@[simp]
theorem orderAt_eq_ite_of_separable_map_finSuccEquiv [Nontrivial R] {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) R) (a : Fin (n + 1) → R)
    (hsep : ((finSuccEquiv R n p).map (eval (Fin.tail a))).Separable) :
    p.orderAt a = if eval a p = 0 then 1 else 0 := by
  classical
  split_ifs with hp
  · apply orderAt_eq_one_of_eval_pderiv_ne_zero hp (i := 0)
    rw [← Fin.cons_self_tail a, eval_eq_eval_mv_eval', ← finSuccEquiv'_zero,
      finSuccEquiv'_pderiv, finSuccEquiv'_zero, ← Polynomial.derivative_map]
    have hroot : ((finSuccEquiv R n p).map (eval (Fin.tail a))).eval (a 0) = 0 := by
      rwa [← eval_eq_eval_mv_eval', Fin.cons_self_tail]
    simpa using hsep.eval₂_derivative_ne_zero (RingHom.id R) hroot
  · exact orderAt_eq_zero_iff.mpr hp

/-- Over a ring without additive torsion, `p` has order at least `n` at `a` if and only if, for
every list `l` of fewer than `n` variables, the iterated partial derivative of `p` along `l`
vanishes at `a`. -/
theorem le_orderAt_iff_eval_foldl_pderiv {n : ℕ} :
    (n : ℕ∞) ≤ p.orderAt a ↔
      ∀ l : List σ, l.length < n → eval a (l.foldl (fun q i ↦ pderiv i q) p) = 0 := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one, succ_le_orderAt_iff, ih]
    refine ⟨fun ⟨h0, h⟩ l hl ↦ ?_, fun h ↦ ⟨h [] (by simp), fun i l hl ↦
      h (i :: l) (by simpa using hl)⟩⟩
    cases l with
    | nil => exact h0
    | cons i l => exact h i l (by simpa using hl)

/-- Over a ring without additive torsion, the order of `p` at a point is determined by which
iterated partial derivatives of `p`, of order at most the total degree of `p`, vanish there: if
the same ones vanish at `a` and at `b`, then `p` has the same order at `a` and at `b`. -/
theorem orderAt_eq_of_forall_eval_foldl_pderiv_eq_zero_iff {b : σ → R}
    (h : ∀ l : List σ, l.length ≤ p.totalDegree →
      (eval a (l.foldl (fun q i ↦ pderiv i q) p) = 0 ↔
        eval b (l.foldl (fun q i ↦ pderiv i q) p) = 0)) :
    p.orderAt a = p.orderAt b := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  -- Up to the total degree, the order is detected by the iterated derivatives in `h`, and the
  -- order of a nonzero polynomial never exceeds its total degree.
  have key {m : ℕ} (hm : m ≤ p.totalDegree) :
      (m : ℕ∞) ≤ p.orderAt a ↔ (m : ℕ∞) ≤ p.orderAt b := by
    simp only [le_orderAt_iff_eval_foldl_pderiv]
    exact forall_congr' fun l ↦ forall_congr' fun hl ↦ h l (by omega)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (orderAt_eq_top_iff.not.2 hp : p.orderAt a ≠ ⊤)
  obtain ⟨k', hk'⟩ := ENat.ne_top_iff_exists.1 (orderAt_eq_top_iff.not.2 hp : p.orderAt b ≠ ⊤)
  have hka : k ≤ p.totalDegree := by exact_mod_cast hk ▸ orderAt_le_totalDegree hp a
  have hkb : k' ≤ p.totalDegree := by exact_mod_cast hk' ▸ orderAt_le_totalDegree hp b
  rw [← hk, ← hk'] at key ⊢
  exact le_antisymm ((key hka).1 le_rfl) ((key hkb).2 le_rfl)

end Derivative

end OrderAt

end MvPolynomial
