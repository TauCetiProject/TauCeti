/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Coefficient maps, swap degrees, and evaluation of bivariate polynomials

Evaluating a bivariate polynomial at a point `(x, y)` is `eval₂` of the evaluation at `x`
of its coefficients, read at `y`. The bivariate-to-multivariate equivalence also commutes
with coefficient maps and evaluation. The coefficients of `f(X + Y)` are binomial multiples of
those of `f`.

Swapping the two indeterminates via `Polynomial.Bivariate.swap` transposes the coefficient table,
so `(Bivariate.swap Q).natDegree` is the least upper bound on the degrees of the coefficients of
`Q`. Substitution `aevalAeval x y` into multivariate polynomials respects evaluation and total
degree, and invertible 2 × 2 linear substitutions are injective. Over an integral domain, an
irreducible bivariate polynomial of positive outer degree cannot vanish identically on any vertical
fiber `X = β`.

## Main results

* `Polynomial.aevalAeval_eq_eval₂`: `φ(x, y) = eval₂ (aeval x) y φ`.
* `Polynomial.Bivariate.coeff_coeff_swap`, `Polynomial.Bivariate.natDegree_swap_le_iff`,
  `Polynomial.Bivariate.natDegree_coeff_le_natDegree_swap`: coefficient transposition and inner
  degree bounds via `Bivariate.swap`.
* `Polynomial.totalDegree_aevalAeval_le`, `Polynomial.eval_aevalAeval`,
  `Polynomial.eval_eval_aeval_C`: total-degree bound and pointwise evaluation for substituting
  multivariate polynomials into a bivariate polynomial.
* `Polynomial.aevalAeval_linear_injective`: injectivity of invertible 2 × 2 linear coordinate
  substitutions into `MvPolynomial (Fin 2) R`.
* `Irreducible.map_evalRingHom_ne_zero`: an irreducible bivariate polynomial of positive outer
  degree over an integral domain does not vanish identically on any vertical fiber.
* `Polynomial.coeff_coeff_aeval_C_X_add_Y`: the coefficient of `X ^ a * Y ^ b` in `f(X + Y)` is
  `(a + b).choose b * f_{a+b}`.
-/

public section

open scoped Polynomial.Bivariate

namespace Polynomial

/-- Evaluating a bivariate polynomial at `(x, y)` evaluates its coefficients at `x` and the
resulting polynomial at `y`. -/
theorem aevalAeval_eq_eval₂ {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (x y : A) (p : R[X][Y]) : aevalAeval x y p = eval₂ (aeval x).toRingHom y p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, eval₂_add]
  | monomial n a => simp [← C_mul_X_pow_eq_monomial]

/-- The bivariate-to-multivariate equivalence commutes with coefficient maps. -/
@[simp]
theorem Bivariate.equivMvPolynomial_symm_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (φ : MvPolynomial (Fin 2) R) :
    (Bivariate.equivMvPolynomial S).symm (φ.map f) =
      ((Bivariate.equivMvPolynomial R).symm φ).map (mapRingHom f) := by
  induction φ using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => fin_cases i <;> simp [hp]

/-- Evaluation is unchanged by converting a two-variable polynomial to bivariate form. -/
@[simp]
theorem Bivariate.aevalAeval_comp_equivMvPolynomial_symm {R A : Type*}
    [CommSemiring R] [CommSemiring A] [Algebra R A] (x y : A) :
    (aevalAeval x y).comp
        ((Bivariate.equivMvPolynomial R).symm : MvPolynomial (Fin 2) R →ₐ[R] R[X][Y]) =
      MvPolynomial.aeval ![x, y] :=
  MvPolynomial.algHom_ext fun i ↦ by fin_cases i <;> simp

/-- Swapping the two indeterminates of `R[X][Y]` transposes the coefficient table. -/
@[simp]
theorem Bivariate.coeff_coeff_swap {R : Type*} [CommSemiring R] (Q : R[X][Y]) (m n : ℕ) :
    ((Bivariate.swap Q).coeff m).coeff n = (Q.coeff n).coeff m := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb =>
      rw [(monomial k).map_add, map_add, coeff_add, coeff_add, coeff_add, ha, hb]
      simp [coeff_monomial]
    | monomial l r =>
      rw [Bivariate.swap_monomial_monomial, coeff_monomial, coeff_monomial]
      by_cases hlm : l = m <;> by_cases hkn : k = n <;> simp [hlm, hkn]

/-- The outer degree of `Bivariate.swap Q` bounds the degree of every coefficient of `Q`. -/
theorem Bivariate.natDegree_swap_le_iff {R : Type*} [CommSemiring R] {Q : R[X][Y]} {d : ℕ} :
    (Bivariate.swap Q).natDegree ≤ d ↔ ∀ n, (Q.coeff n).natDegree ≤ d := by
  refine ⟨fun h n ↦ natDegree_le_iff_coeff_eq_zero.mpr fun m hm ↦ ?_,
    fun h ↦ natDegree_le_iff_coeff_eq_zero.mpr fun m hm ↦ ?_⟩
  · rw [← Bivariate.coeff_coeff_swap, natDegree_le_iff_coeff_eq_zero.mp h m hm, coeff_zero]
  · ext n
    rw [coeff_zero, Bivariate.coeff_coeff_swap, natDegree_le_iff_coeff_eq_zero.mp (h n) m hm]

/-- Every coefficient of `Q : R[X][Y]` has degree at most `(Bivariate.swap Q).natDegree`. -/
theorem Bivariate.natDegree_coeff_le_natDegree_swap {R : Type*} [CommSemiring R] (Q : R[X][Y])
    (n : ℕ) : (Q.coeff n).natDegree ≤ (Bivariate.swap Q).natDegree :=
  Bivariate.natDegree_swap_le_iff.mp le_rfl n

/-- Substituting `x, y : MvPolynomial σ R` into a bivariate polynomial `p : R[X][Y]` gives a
multivariate polynomial of total degree at most
`(Bivariate.swap p).natDegree * x.totalDegree + p.natDegree * y.totalDegree`. -/
theorem totalDegree_aevalAeval_le {R σ : Type*} [CommSemiring R]
    (x y : MvPolynomial σ R) (p : R[X][Y]) :
    (aevalAeval x y p).totalDegree ≤
      (Bivariate.swap p).natDegree * x.totalDegree + p.natDegree * y.totalDegree := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun k hk ↦ ?_
  have hk_le : k ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [map_mul, map_pow, aevalAeval_C, aevalAeval_Y]
  refine (MvPolynomial.totalDegree_mul _ _).trans (add_le_add ?_
    ((MvPolynomial.totalDegree_pow y k).trans (Nat.mul_le_mul_right _ hk_le)))
  conv_lhs => rw [(p.coeff k).as_sum_range_C_mul_X_pow]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun j hj ↦ ?_
  have hj_le : j ≤ (Bivariate.swap p).natDegree :=
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans
      (Bivariate.natDegree_coeff_le_natDegree_swap p k)
  rw [map_mul, map_pow, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  exact (MvPolynomial.totalDegree_smul_le _ _).trans
    ((MvPolynomial.totalDegree_pow x j).trans (Nat.mul_le_mul_right _ hj_le))

/-- Evaluating `aevalAeval x y p` at `f : σ → R` agrees with bivariate evaluation `evalEval`
of `p` at `(MvPolynomial.eval f x, MvPolynomial.eval f y)`. -/
theorem eval_aevalAeval {R σ : Type*} [CommSemiring R] (f : σ → R)
    (x y : MvPolynomial σ R) (p : R[X][Y]) :
    MvPolynomial.eval f (aevalAeval x y p) =
      p.evalEval (MvPolynomial.eval f x) (MvPolynomial.eval f y) := by
  rw [← coe_aevalAeval_eq_evalEval]
  have hhom : (MvPolynomial.aeval f).comp (aevalAeval x y) =
      aevalAeval (MvPolynomial.eval f x) (MvPolynomial.eval f y) :=
    (aevalAevalEquiv R R).symm.injective (by simp)
  simpa using AlgHom.congr_fun hhom p

/-- Simp form of `Polynomial.eval_aevalAeval` matching the expanded expression
`eval x (aeval (C y) p)` produced by `Polynomial.aevalAevalEquiv_apply_apply`. -/
@[simp]
theorem eval_eval_aeval_C {R σ : Type*} [CommSemiring R] (f : σ → R)
    (x y : MvPolynomial σ R) (p : R[X][Y]) :
    MvPolynomial.eval f
        (eval x (let := Polynomial.algebra (R := R) (A := MvPolynomial σ R); aeval (C y) p)) =
      p.evalEval (MvPolynomial.eval f x) (MvPolynomial.eval f y) := by
  simpa only [aevalAevalEquiv_apply_apply] using eval_aevalAeval f x y p

/-- Substituting an invertible linear pair `(a X₀ + b X₁, c X₀ + d X₁)` with
`IsUnit (a * d - b * c)` into bivariate polynomials `R[X][Y]` is injective. -/
theorem aevalAeval_linear_injective {R : Type*} [CommRing R] {a b c d : R}
    (hdet : IsUnit (a * d - b * c)) :
    Function.Injective
      (aevalAeval (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1)
        (MvPolynomial.C c * MvPolynomial.X 0 + MvPolynomial.C d * MvPolynomial.X 1) :
        R[X][Y] →ₐ[R] MvPolynomial (Fin 2) R) := by
  obtain ⟨u, hu⟩ := hdet
  let f : R →+* R[X][Y] := algebraMap R R[X][Y]
  let U₀ : R[X][Y] := f ((u⁻¹ : Rˣ) * d) * C X - f ((u⁻¹ : Rˣ) * b) * Y
  let U₁ : R[X][Y] := -(f ((u⁻¹ : Rˣ) * c) * C X) + f ((u⁻¹ : Rˣ) * a) * Y
  let invHom : MvPolynomial (Fin 2) R →ₐ[R] R[X][Y] := MvPolynomial.aeval ![U₀, U₁]
  have hcomp : invHom.comp (aevalAeval
      (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1)
      (MvPolynomial.C c * MvPolynomial.X 0 + MvPolynomial.C d * MvPolynomial.X 1)) =
      AlgHom.id R R[X][Y] := by
    refine (aevalAevalEquiv R R[X][Y]).symm.injective (Prod.ext ?_ ?_)
    · simp only [aevalAevalEquiv_symm_apply, AlgHom.comp_apply, AlgHom.id_apply, aevalAeval_X,
        invHom, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      calc f a * U₀ + f b * U₁
          = f ((u⁻¹ : Rˣ) * (a * d - b * c)) * C X := by
            simp only [U₀, U₁, map_mul, map_sub]; ring
        _ = C X := by rw [← hu, u.inv_mul, map_one, one_mul]
    · simp only [aevalAevalEquiv_symm_apply, AlgHom.comp_apply, AlgHom.id_apply, aevalAeval_Y,
        invHom, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      calc f c * U₀ + f d * U₁
          = f ((u⁻¹ : Rˣ) * (a * d - b * c)) * Y := by
            simp only [U₀, U₁, map_mul, map_sub]; ring
        _ = Y := by rw [← hu, u.inv_mul, map_one, one_mul]
  exact Function.LeftInverse.injective (g := invHom) fun P ↦ DFunLike.congr_fun hcomp P

/-- An irreducible bivariate polynomial of positive outer degree over an integral domain cannot
vanish identically on any vertical fiber `X = β`. -/
theorem _root_.Irreducible.map_evalRingHom_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {Q : R[X][Y]} (hQ : Irreducible Q) (hdeg : 0 < Q.natDegree) (β : R) :
    Q.map (evalRingHom β) ≠ 0 := by
  intro h0
  have hdvd : C (X - C β) ∣ Q := by
    rw [C_dvd_iff_dvd_coeff]
    intro k
    rw [dvd_iff_isRoot, IsRoot.def]
    have hk0 : (Q.map (evalRingHom β)).coeff k = 0 := by simp [h0]
    rwa [coeff_map] at hk0
  obtain ⟨R₀, hQR⟩ := hdvd
  rcases hQ.isUnit_or_isUnit hQR with hu | hu
  · exact not_isUnit_X_sub_C β (isUnit_C.mp hu)
  · have hR₀ : R₀.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
    have hQ0 : Q.natDegree ≤ 0 := by
      rw [hQR]
      exact natDegree_mul_le.trans (by simp [hR₀])
    omega

/-- The coefficient of `X ^ a * Y ^ b` in `f(X + Y)` is `(a + b).choose b * f_{a+b}`. -/
@[simp]
theorem coeff_coeff_aeval_C_X_add_Y {R : Type*} [CommSemiring R] (f : R[X]) (a b : ℕ) :
    ((aeval (C X + Y : R[X][Y]) f).coeff b).coeff a =
      ((a + b).choose b : R) * f.coeff (a + b) := by
  -- `f(X + Y)` is the Taylor expansion of `f(Y)` at `X`, whose coefficients are the Hasse
  -- derivatives of `f`.
  have h : aeval (C X + Y : R[X][Y]) f = taylor X (f.map C) := by
    rw [taylor_apply, comp, eval₂_map, aeval_def, add_comm,
      IsScalarTower.algebraMap_eq R R[X] R[X][X], algebraMap_eq, algebraMap_eq]
  rw [h, taylor_coeff, hasseDeriv_map, eval_map, eval₂_C_X, hasseDeriv_coeff]

end Polynomial
