/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import TauCeti.NumberTheory.ModularForms.LevelOne.ModularPolynomial.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.NumberTheory.ModularForms.LevelOne.WeaklyHolomorphic
import TauCeti.NumberTheory.ModularForms.QExpansion.Order

/-!
# The diagonal modular polynomial and integrality of `j` at imaginary quadratic points

Along the diagonal `Y = X`, the modular polynomial `modularPolynomial n` specializes to
`diagModularPolynomial n = Φ_n(X, X) ∈ ℤ[X]`, whose evaluation at `j(τ)` is
`∏ (j(τ) - j(A • τ))` over `FixedDetMatrices.primitiveReps n`.

When `n` is not a square, `a d = n` prevents `a² = n`, so in every factor one of `j(τ)` (order `-n`
in `q_n`, leading coefficient `1`) and `-j(A • τ)` (order `-a²` in `q_n`, leading coefficient
`-ζ_n^{-a b}`) strictly dominates the other at `i∞`. The product therefore has leading coefficient
of absolute value `1`, forcing `Φ_n(X, X)` to be nonzero with leading coefficient `±1`, so all of
its roots are integral over `ℤ`. Every imaginary quadratic point `τ ∈ ℍ` is fixed by an explicit
primitive integral matrix of non-square positive determinant, making `j(τ)` a root of `Φ_n(X, X)`
and hence an algebraic integer (`TauCeti.ModularForm.isIntegral_j_of_quadratic`).

## Main definitions

* `TauCeti.ModularForm.diagModularPolynomial n`: the diagonal specialization `Φ_n(X, X) ∈ ℤ[X]`.

## Main results

* `TauCeti.ModularForm.diagModularPolynomial_one`: `Φ_1(X, X) = 0`.
* `TauCeti.ModularForm.aeval_j_diagModularPolynomial_eq_zero_iff`: `Φ_n(j(τ), j(τ)) = 0` holds
  exactly when `τ` is fixed by some primitive integral matrix of determinant `n`.
* `TauCeti.ModularForm.isUnit_leadingCoeff_diagModularPolynomial`: when `n` is not a square, the
  leading coefficient of `Φ_n(X, X)` is a unit in `ℤ` (`±1`), so its roots in any commutative ring
  are integral over `ℤ` (`isIntegral_of_aeval_diagModularPolynomial_eq_zero`).
* `TauCeti.ModularForm.isIntegral_j_of_quadratic`: if `τ ∈ ℍ` satisfies `a τ² + b τ + c = 0` with
  `a, b, c ∈ ℤ` and `a ≠ 0`, then `j(τ)` is an algebraic integer (`IsIntegral ℤ (j τ)`).

## References

* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §11.C and Theorem 11.1
  (integrality of singular moduli).
* S. Lang, *Elliptic Functions*, 2nd ed., Graduate Texts in Mathematics 112, Springer, 1987,
  Chapter 5, §3 (`Φ_m(X, X)` for non-square `m` and integrality of `j(τ)`).
-/

public noncomputable section

open Complex Matrix Polynomial
open UpperHalfPlane hiding I
open scoped MatrixGroups Polynomial.Bivariate Real

local notation "𝕢" => Function.Periodic.qParam

namespace TauCeti.ModularForm

open FixedDetMatrices

variable (n : ℕ) [NeZero n]

/-- **The diagonal modular polynomial `Φ_n(X, X) ∈ ℤ[X]`**, whose roots are the `j`-invariants of
elliptic curves admitting a cyclic `n`-endomorphism. -/
noncomputable def diagModularPolynomial : ℤ[X] :=
  (modularPolynomial n).eval X

/-- At `n = 1 = 1²`, the diagonal modular polynomial vanishes (`Y - X` evaluated at `Y = X`),
showing that the non-square hypothesis in `diagModularPolynomial_ne_zero` is sharp. -/
@[simp]
theorem diagModularPolynomial_one : diagModularPolynomial 1 = 0 := by
  simp [diagModularPolynomial]

/-- Evaluating `diagModularPolynomial n` at `z` evaluates `modularPolynomial n` at `(z, z)`. -/
@[simp]
theorem aeval_diagModularPolynomial {A : Type*} [CommRing A] (z : A) :
    aeval z (diagModularPolynomial n) = aevalAeval z z (modularPolynomial n) :=
  Polynomial.aeval_eval_X z (modularPolynomial n)

variable {n}

/-- `Φ_n(j(τ), j(τ)) = 0` holds exactly when `τ` is fixed by a primitive integral matrix of
determinant `n`. -/
theorem aeval_j_diagModularPolynomial_eq_zero_iff (τ : ℍ) :
    aeval (j τ) (diagModularPolynomial n) = 0 ↔
      ∃ A : FixedDetMatrix (Fin 2) ℤ n,
        TauCeti.IsPrimitive A.1 ∧ toGLReal (NeZero.ne (n : ℤ)) A • τ = τ := by
  rw [aeval_diagModularPolynomial, aevalAeval_j_modularPolynomial_eq_zero_iff]

/-- The `k`-th power of the width-one Laurent `q`-expansion of `j` has order `-k` and leading
coefficient `1`. -/
private theorem orderTop_and_leadingCoeff_laurentQExpansion_j_pow (k : ℕ) :
    ((UpperHalfPlane.laurentQExpansion 1 j) ^ k).orderTop = (-k : ℤ) ∧
      ((UpperHalfPlane.laurentQExpansion 1 j) ^ k).leadingCoeff = 1 := by
  set J := UpperHalfPlane.laurentQExpansion 1 j
  have hJ_ord : J.orderTop = (-1 : ℤ) := orderTop_laurentQExpansion_j
  have hne : J ≠ 0 := by
    rw [← HahnSeries.orderTop_ne_top, hJ_ord]
    exact WithTop.coe_ne_top
  have hJ_lc : J.leadingCoeff = 1 := by
    rw [HahnSeries.leadingCoeff_eq,
      WithTop.coe_injective ((HahnSeries.order_eq_orderTop_of_ne_zero hne).trans hJ_ord),
      laurentQExpansion_j_coeff_neg_one]
  induction k with
  | zero => simp [HahnSeries.leadingCoeff_one]
  | succ k ih =>
    rw [pow_succ, HahnSeries.orderTop_mul, ih.1, hJ_ord, HahnSeries.leadingCoeff_mul,
      ih.2, hJ_lc, mul_one, ← WithTop.coe_add]
    exact ⟨WithTop.coe_inj.2 (by push_cast; ring), rfl⟩

/-- For a nonzero polynomial `P : ℤ[X]`, the leading coefficient of the width-one Laurent
`q`-expansion of `P(j)` is `(P.leadingCoeff : ℂ)`. -/
private theorem leadingCoeff_laurentQExpansion_aeval_j {P : ℤ[X]} (hP : P ≠ 0) :
    (UpperHalfPlane.laurentQExpansion 1 (fun τ : ℍ ↦ aeval (j τ) P)).leadingCoeff =
      (P.leadingCoeff : ℂ) := by
  rw [Polynomial.laurentQExpansion_aeval_j]
  set J := UpperHalfPlane.laurentQExpansion 1 j
  set ev : ℤ[X] →+* LaurentSeries ℂ := eval₂RingHom (HahnSeries.C.comp (algebraMap ℤ ℂ)) J
  -- Fold `eval₂ (HahnSeries.C.comp (algebraMap ℤ ℂ)) J P` into `ev P` so `map_add`/`map_sum` apply.
  change (ev P).leadingCoeff = (P.leadingCoeff : ℂ)
  set N := P.natDegree
  have hc0 : (P.leadingCoeff : ℂ) ≠ 0 := Int.cast_ne_zero.2 (leadingCoeff_ne_zero.2 hP)
  have htop_lead : (ev (C P.leadingCoeff * X ^ N)).orderTop = (-N : ℤ) ∧
      (ev (C P.leadingCoeff * X ^ N)).leadingCoeff = (P.leadingCoeff : ℂ) := by
    simp only [ev, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_X_pow, RingHom.comp_apply]
    have hC_ord : (HahnSeries.C (algebraMap ℤ ℂ P.leadingCoeff) : LaurentSeries ℂ).orderTop =
        (0 : ℤ) := by
      rw [eq_intCast, HahnSeries.C_apply, HahnSeries.orderTop_single hc0]
    rw [HahnSeries.orderTop_mul, hC_ord, (orderTop_and_leadingCoeff_laurentQExpansion_j_pow N).1,
      ← WithTop.coe_add, zero_add, HahnSeries.leadingCoeff_mul, eq_intCast, HahnSeries.C_apply,
      HahnSeries.leadingCoeff_of_single, (orderTop_and_leadingCoeff_laurentQExpansion_j_pow N).2,
      mul_one]
    exact ⟨rfl, rfl⟩
  have herase_ord : ((-N : ℤ) : WithTop ℤ) < (ev P.eraseLead).orderTop := by
    by_cases he0 : P.eraseLead = 0
    · rw [he0, map_zero, HahnSeries.orderTop_zero]
      exact WithTop.coe_lt_top _
    · have hlt : P.eraseLead.natDegree < N :=
        P.eraseLead_natDegree_lt_or_eraseLead_eq_zero.resolve_right he0
      have hle : ((-(N - 1 : ℕ) : ℤ) : WithTop ℤ) ≤ (ev P.eraseLead).orderTop := by
        rw [P.eraseLead.as_sum_range' N hlt, map_sum]
        refine Finset.sum_induction _ (fun s : LaurentSeries ℂ ↦
          ((-(N - 1 : ℕ) : ℤ) : WithTop ℤ) ≤ s.orderTop)
          (fun x y hx hy ↦ (le_min hx hy).trans HahnSeries.min_orderTop_le_orderTop_add)
          (by simp) fun i hi ↦ ?_
        rw [Finset.mem_range] at hi
        simp only [ev, coe_eval₂RingHom, ← C_mul_X_pow_eq_monomial, eval₂_mul, eval₂_C,
          eval₂_X_pow, RingHom.comp_apply]
        rw [eq_intCast]
        by_cases hci : (P.eraseLead.coeff i : ℂ) = 0
        · simp [hci]
        · rw [HahnSeries.orderTop_mul, HahnSeries.C_apply, HahnSeries.orderTop_single hci,
            (orderTop_and_leadingCoeff_laurentQExpansion_j_pow i).1, ← WithTop.coe_add, zero_add]
          exact WithTop.coe_le_coe.2 (by omega)
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 (by omega)) hle
  conv_lhs => rw [← P.eraseLead_add_C_mul_X_pow]
  rw [map_add, HahnSeries.leadingCoeff_add_eq_right (htop_lead.1 ▸ herase_ord), htop_lead.2]

/-- The width-`n` cusp function of `j` is meromorphic at `0`. -/
private theorem meromorphicAt_cuspFunction_nat_j : MeromorphicAt (cuspFunction n j) 0 := by
  have han := TauCeti.analyticAt_cuspFunction_nat_mul one_ne_zero (NeZero.pos n)
    periodic_qParam_mul_j_comp_ofComplex analyticAt_cuspFunction_qParam_mul_j
  have hq : (fun τ : ℍ ↦ 𝕢 ((n : ℕ) * (1 : ℝ)) τ ^ n * j τ) = fun τ : ℍ ↦ 𝕢 1 τ * j τ := by
    ext τ
    rw [TauCeti.Periodic.qParam_nat_mul_pow (NeZero.ne n)]
  rw [← hq, mul_one] at han
  exact UpperHalfPlane.meromorphicAt_cuspFunction_qParam_pow_mul_iff.1 han.meromorphicAt

/-- For `A ∈ reps n`, the width-`n` Laurent `q`-expansion of `j(A • τ)` has order `-a²` and leading
coefficient of norm `1`. -/
private theorem orderTop_and_norm_leadingCoeff_laurentQExpansion_j_toGLReal_smul
    {A : FixedDetMatrix (Fin 2) ℤ n} (hAr : A ∈ reps (n : ℤ)) :
    (UpperHalfPlane.laurentQExpansion n
      (fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ))).orderTop =
        (-((A.1 0 0).natAbs ^ 2 : ℕ) : ℤ) ∧
    ‖(UpperHalfPlane.laurentQExpansion n
      (fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ))).leadingCoeff‖ = 1 := by
  let a := (A.1 0 0).natAbs
  let b := (A.1 0 1).natAbs
  let ζ := cexp (2 * π * I / n)
  let u : ℂˣ := Units.mk0 (ζ ^ (a * b)) (pow_ne_zero _ (Complex.exp_ne_zero _))
  have hJ_ord : (UpperHalfPlane.laurentQExpansion 1 j).orderTop = ((-1 : ℤ) : WithTop ℤ) :=
    orderTop_laurentQExpansion_j
  refine ⟨?_, ?_⟩
  · rw [laurentQExpansion_j_toGLReal_smul hAr]
    set d : ℕ+ := ⟨(A.1 0 0).natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hAr.2.1.ne') 2⟩
    have hd : (d : ℕ) = (A.1 0 0).natAbs ^ 2 := rfl
    rw [LaurentSeries.orderTop_expand, HahnSeries.orderTop_twistEquiv, hJ_ord,
      ← WithTop.coe_nsmul, nsmul_eq_mul]
    exact WithTop.coe_inj.2 (by rw [hd]; ring)
  · rw [laurentQExpansion_j_toGLReal_smul hAr]
    set d : ℕ+ := ⟨(A.1 0 0).natAbs ^ 2, pow_pos (Int.natAbs_pos.2 hAr.2.1.ne') 2⟩
    rw [LaurentSeries.leadingCoeff_expand]
    have htw_ord_top : (HahnSeries.twistEquiv (zpowersHom ℂˣ u)
        (UpperHalfPlane.laurentQExpansion 1 j)).orderTop = ((-1 : ℤ) : WithTop ℤ) :=
      (HahnSeries.orderTop_twistEquiv _ _).trans hJ_ord
    have htw_ne : HahnSeries.twistEquiv (zpowersHom ℂˣ u)
        (UpperHalfPlane.laurentQExpansion 1 j) ≠ 0 :=
      HahnSeries.orderTop_ne_top.1 (htw_ord_top.trans_ne WithTop.coe_ne_top)
    have htw_ord : (HahnSeries.twistEquiv (zpowersHom ℂˣ u)
        (UpperHalfPlane.laurentQExpansion 1 j)).order = -1 :=
      WithTop.coe_injective ((HahnSeries.order_eq_orderTop_of_ne_zero htw_ne).trans htw_ord_top)
    rw [HahnSeries.leadingCoeff_eq, htw_ord, HahnSeries.coeff_twistEquiv,
      laurentQExpansion_j_coeff_neg_one, mul_one]
    have hζ_arg : 2 * (π : ℂ) * I / n = ↑(2 * π / (n : ℝ)) * I := by push_cast; ring
    have hζ1 : ‖ζ‖ = 1 := by dsimp only [ζ]; rw [hζ_arg, Complex.norm_exp_ofReal_mul_I]
    -- Expose the `Multiplicative ℤ` argument of `zpowersHom` before simplifying the unit power.
    change ‖((zpowersHom ℂˣ u (Multiplicative.ofAdd (-1 : ℤ)) : ℂˣ) : ℂ)‖ = 1
    rw [zpowersHom_apply, toAdd_ofAdd, _root_.zpow_neg, zpow_one, Units.val_inv_eq_inv_val,
      Units.val_mk0, norm_inv, norm_pow, hζ1, one_pow, inv_one]

/-- For non-square `n` and `A ∈ reps n`, the width-`n` Laurent `q`-expansion of `j - (j ∘ (A • ·))`
has leading coefficient of norm `1`. -/
private theorem norm_leadingCoeff_laurentQExpansion_j_sub_smul (hn : ¬ IsSquare n)
    {A : FixedDetMatrix (Fin 2) ℤ n} (hAr : A ∈ reps (n : ℤ)) :
    ‖(UpperHalfPlane.laurentQExpansion n
      (j - fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ))).leadingCoeff‖ = 1 := by
  rw [UpperHalfPlane.laurentQExpansion_sub meromorphicAt_cuspFunction_nat_j
    (meromorphicAt_cuspFunction_j_toGLReal_smul hAr), sub_eq_add_neg]
  let d : ℕ+ := ⟨n, NeZero.pos n⟩
  have hexp_j := UpperHalfPlane.laurentQExpansion_pnat_mul periodic_j_comp_ofComplex
    meromorphicAt_cuspFunction_j d
  have hd_mul : ((d : ℕ) : ℝ) * 1 = n := mul_one _
  rw [hd_mul] at hexp_j
  have hJ_lc := (orderTop_and_leadingCoeff_laurentQExpansion_j_pow 1).2
  rw [pow_one] at hJ_lc
  have hord_j : (UpperHalfPlane.laurentQExpansion n j).orderTop = (-n : ℤ) := by
    rw [hexp_j, LaurentSeries.orderTop_expand, orderTop_laurentQExpansion_j]
    exact WithTop.coe_inj.2 (mul_neg_one _)
  have hlc_j : (UpperHalfPlane.laurentQExpansion n j).leadingCoeff = 1 := by
    rw [hexp_j, LaurentSeries.leadingCoeff_expand, hJ_lc]
  obtain ⟨hord_A, hnorm_A⟩ := orderTop_and_norm_leadingCoeff_laurentQExpansion_j_toGLReal_smul hAr
  have ha2_ne : (A.1 0 0).natAbs ^ 2 ≠ n := fun hsq ↦ hn ⟨(A.1 0 0).natAbs, by rw [← sq, hsq]⟩
  rcases lt_or_gt_of_ne ha2_ne with hlt | hgt
  · have hlt' : (UpperHalfPlane.laurentQExpansion n j).orderTop <
        (-UpperHalfPlane.laurentQExpansion n
          fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)).orderTop := by
      rw [HahnSeries.orderTop_neg, hord_j, hord_A]
      exact WithTop.coe_lt_coe.2 (by omega)
    rw [HahnSeries.leadingCoeff_add_eq_left hlt', hlc_j, norm_one]
  · have hgt' : (-UpperHalfPlane.laurentQExpansion n
          fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)).orderTop <
        (UpperHalfPlane.laurentQExpansion n j).orderTop := by
      rw [HahnSeries.orderTop_neg, hord_j, hord_A]
      exact WithTop.coe_lt_coe.2 (by omega)
    rw [HahnSeries.leadingCoeff_add_eq_right hgt', HahnSeries.leadingCoeff_neg, norm_neg, hnorm_A]

/-- At width `n`, the Laurent `q`-expansion of `∏ A ∈ primitiveReps n, (j(τ) - j(A • τ))` has
leading coefficient of norm `1` whenever `n` is not a square. -/
private theorem norm_leadingCoeff_laurentQExpansion_diag_eq_one (hn : ¬ IsSquare n) :
    ‖(UpperHalfPlane.laurentQExpansion n
      (fun τ : ℍ ↦ aeval (j τ) (diagModularPolynomial n))).leadingCoeff‖ = 1 := by
  classical
  have hfun : (fun τ : ℍ ↦ aeval (j τ) (diagModularPolynomial n)) =
      ∏ A ∈ primitiveReps (n : ℤ),
        (j - fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) := by
    ext τ
    rw [aeval_diagModularPolynomial, aevalAeval_j_modularPolynomial,
      cyclicIsogenyPolynomial_def, eval_prod, Finset.prod_apply]
    exact Finset.prod_congr rfl fun A _ ↦ by simp
  have hprod : ∀ s : Finset (FixedDetMatrix (Fin 2) ℤ n), (∀ A ∈ s, A ∈ reps (n : ℤ)) →
      MeromorphicAt (cuspFunction n
        (∏ A ∈ s, (j - fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)))) 0 ∧
      ‖(UpperHalfPlane.laurentQExpansion n
        (∏ A ∈ s, (j - fun τ : ℍ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)))).leadingCoeff‖ = 1 := by
    intro s hs
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨UpperHalfPlane.meromorphicAt_cuspFunction_const _, ?_⟩
      simp [HahnSeries.leadingCoeff_one]
    | @insert A s hAs ih =>
      have hAr := hs A (Finset.mem_insert_self A s)
      have hs' : ∀ B ∈ s, B ∈ reps (n : ℤ) := fun B hB ↦ hs B (Finset.mem_insert_of_mem hB)
      have hmA := UpperHalfPlane.meromorphicAt_cuspFunction_sub meromorphicAt_cuspFunction_nat_j
        (meromorphicAt_cuspFunction_j_toGLReal_smul hAr)
      rw [Finset.prod_insert hAs]
      refine ⟨UpperHalfPlane.meromorphicAt_cuspFunction_mul hmA (ih hs').1, ?_⟩
      rw [UpperHalfPlane.laurentQExpansion_mul hmA (ih hs').1, HahnSeries.leadingCoeff_mul,
        norm_mul, (ih hs').2, mul_one, norm_leadingCoeff_laurentQExpansion_j_sub_smul hn hAr]
  rw [hfun]
  exact (hprod _ fun _ hA ↦ (mem_primitiveReps.1 hA).1).2

/-- When `n` is not a square, `diagModularPolynomial n` is nonzero. -/
theorem diagModularPolynomial_ne_zero (hn : ¬ IsSquare n) :
    diagModularPolynomial n ≠ 0 := by
  intro h0
  have h := norm_leadingCoeff_laurentQExpansion_diag_eq_one hn
  simp [h0] at h

/-- **When `n` is not a square, the leading coefficient of `Φ_n(X, X)` is `±1`**, a unit in `ℤ`. -/
theorem isUnit_leadingCoeff_diagModularPolynomial (hn : ¬ IsSquare n) :
    IsUnit (diagModularPolynomial n).leadingCoeff := by
  set P := diagModularPolynomial n
  have hP : P ≠ 0 := diagModularPolynomial_ne_zero hn
  have hper : Function.Periodic ((fun τ : ℍ ↦ aeval (j τ) P) ∘ ofComplex) 1 :=
    periodic_j_comp_ofComplex.comp fun z : ℂ ↦ aeval z P
  let d : ℕ+ := ⟨n, NeZero.pos n⟩
  have hexp := UpperHalfPlane.laurentQExpansion_pnat_mul hper
    (Polynomial.meromorphicAt_cuspFunction_aeval_j P) d
  have hd_mul : ((d : ℕ) : ℝ) * 1 = n := mul_one _
  rw [hd_mul] at hexp
  have hnorm := norm_leadingCoeff_laurentQExpansion_diag_eq_one hn
  rw [hexp, LaurentSeries.leadingCoeff_expand, leadingCoeff_laurentQExpansion_aeval_j hP,
    Complex.norm_intCast] at hnorm
  exact Int.isUnit_iff_abs_eq.2 (by exact_mod_cast hnorm)

/-- **Every root of `Φ_n(X, X)` for non-square `n` is an algebraic integer.** -/
theorem isIntegral_of_aeval_diagModularPolynomial_eq_zero {A : Type*} [CommRing A]
    (hn : ¬ IsSquare n) {x : A} (hx : aeval x (diagModularPolynomial n) = 0) :
    IsIntegral ℤ x := by
  obtain ⟨u, hu⟩ := isUnit_leadingCoeff_diagModularPolynomial hn
  have h := (integralClosure ℤ A).smul_mem
    (isIntegral_leadingCoeff_smul (diagModularPolynomial n) x hx) (↑u⁻¹ : ℤ)
  rwa [smul_smul, ← hu, Units.inv_mul, one_smul] at h

/-- Dividing three integers `(a, b, c)` (`a ≠ 0`) by `g = gcd(a, gcd(b, c))` yields a triple with
an explicit Bézout relation `u * (a / g) + v * (b / g) + w * (c / g) = 1`. -/
private theorem exists_bezout_of_ediv_gcd {a b c : ℤ} (ha : a ≠ 0) :
    let g : ℕ := a.gcd (b.gcd c)
    ∃ u v w : ℤ, u * (a / g) + v * (b / g) + w * (c / g) = 1 := by
  let h : ℕ := b.gcd c
  let g : ℕ := a.gcd h
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.2 ha)
  have hda : (g : ℤ) * (a / g) = a := Int.mul_ediv_cancel' (Int.gcd_dvd_left a h)
  have hgh : (g : ℤ) ∣ (h : ℤ) := Int.gcd_dvd_right a h
  have hdb : (g : ℤ) * (b / g) = b := Int.mul_ediv_cancel' (hgh.trans (Int.gcd_dvd_left b c))
  have hdc : (g : ℤ) * (c / g) = c := Int.mul_ediv_cancel' (hgh.trans (Int.gcd_dvd_right b c))
  have h1 : (g : ℤ) = a * Int.gcdA a h + (h : ℤ) * Int.gcdB a h := Int.gcd_eq_gcd_ab a h
  have h2 : (h : ℤ) = b * Int.gcdA b c + c * Int.gcdB b c := Int.gcd_eq_gcd_ab b c
  refine ⟨Int.gcdA a h, Int.gcdB a h * Int.gcdA b c, Int.gcdB a h * Int.gcdB b c,
    mul_left_cancel₀ (Nat.cast_ne_zero.2 hg_pos.ne') ?_⟩
  linear_combination -h1 - Int.gcdB a h * h2 + Int.gcdA a h * hda +
    Int.gcdB a h * Int.gcdA b c * hdb + Int.gcdB a h * Int.gcdB b c * hdc

/-- Every integral quadratic relation `a τ² + b τ + c = 0` (`a ≠ 0`) for `τ ∈ ℍ` can be divided by
`±gcd(a, b, c)` to obtain a primitive relation with `a' > 0` and `4 a' c' - b'^2 > 0`. -/
private theorem exists_primitive_pos_quadratic {τ : ℍ} {a b c : ℤ} (ha : a ≠ 0)
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    ∃ a' b' c' : ℤ, 0 < a' ∧ (∃ u v w : ℤ, u * a' + v * b' + w * c' = 1) ∧
      0 < 4 * a' * c' - b' ^ 2 ∧ (a' : ℂ) * τ ^ 2 + b' * τ + c' = 0 := by
  wlog ha_pos : 0 < a generalizing a b c
  · exact @this (-a) (-b) (-c) (neg_ne_zero.2 ha) (by push_cast; linear_combination -hτ) (by omega)
  let h : ℕ := b.gcd c
  let g : ℕ := a.gcd h
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.2 ha)
  let a' := a / g; let b' := b / g; let c' := c / g
  have hda : (g : ℤ) * a' = a := Int.mul_ediv_cancel' (Int.gcd_dvd_left a h)
  have hgh : (g : ℤ) ∣ (h : ℤ) := Int.gcd_dvd_right a h
  have hdb : (g : ℤ) * b' = b := Int.mul_ediv_cancel' (hgh.trans (Int.gcd_dvd_left b c))
  have hdc : (g : ℤ) * c' = c := Int.mul_ediv_cancel' (hgh.trans (Int.gcd_dvd_right b c))
  have ha'_pos : 0 < a' := pos_of_mul_pos_right (hda.symm ▸ ha_pos) (by positivity)
  have hτ' : (a' : ℂ) * τ ^ 2 + b' * τ + c' = 0 := by
    have hmul : (g : ℂ) * ((a' : ℂ) * τ ^ 2 + b' * τ + c') = 0 := by
      have haC : (g : ℂ) * a' = a := by exact_mod_cast hda
      have hbC : (g : ℂ) * b' = b := by exact_mod_cast hdb
      have hcC : (g : ℂ) * c' = c := by exact_mod_cast hdc
      linear_combination hτ + τ ^ 2 * haC + τ * hbC + hcC
    exact (mul_eq_zero.1 hmul).resolve_left (Nat.cast_ne_zero.2 hg_pos.ne')
  have hD_pos : 0 < 4 * a' * c' - b' ^ 2 := by
    have him := congrArg Complex.im hτ'
    have hre := congrArg Complex.re hτ'
    simp only [sq, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      zero_mul, add_zero, coe_re, coe_im, Complex.zero_im] at him
    simp only [sq, Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      zero_mul, sub_zero, coe_re, coe_im, Complex.zero_re] at hre
    have him_pos : 0 < τ.im := τ.im_pos
    have haR : (0 : ℝ) < a' := Int.cast_pos.2 ha'_pos
    have hlin : (2 * (a' : ℝ) * τ.re + b') * τ.im = 0 := by linarith
    have h2ab : 2 * (a' : ℝ) * τ.re + b' = 0 := (mul_eq_zero.1 hlin).resolve_right him_pos.ne'
    have hDR : (0 : ℝ) < ((4 * a' * c' - b' ^ 2 : ℤ) : ℝ) := by
      push_cast; nlinarith [mul_pos haR him_pos]
    exact Int.cast_pos.1 hDR
  exact ⟨a', b', c', ha'_pos, exists_bezout_of_ediv_gcd ha, hD_pos, hτ'⟩

/-- Every point `τ ∈ ℍ` satisfying a primitive equation `a' τ² + b' τ + c' = 0` (`a' > 0`) is fixed
by a primitive integral matrix of non-square positive determinant. -/
private theorem exists_primitive_fixedDetMatrix_nonsquare_fixing {τ : ℍ} {a' b' c' : ℤ}
    (hbez : ∃ u v w : ℤ, u * a' + v * b' + w * c' = 1) (hD_pos : 0 < 4 * a' * c' - b' ^ 2)
    (hτ' : (a' : ℂ) * τ ^ 2 + b' * τ + c' = 0) :
    ∃ (m : ℕ) (_ : NeZero m), ¬ IsSquare m ∧
      ∃ A : FixedDetMatrix (Fin 2) ℤ m,
        TauCeti.IsPrimitive A.1 ∧ toGLReal (NeZero.ne (m : ℤ)) A • τ = τ := by
  obtain ⟨u₀, v₀, w₀, hbez⟩ := hbez
  set D : ℤ := 4 * a' * c' - b' ^ 2
  set k : ℤ := |b'| + D
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![k - b', -c'; a', k]
  have h4det : 4 * M.det = (2 * k - b') ^ 2 + D := by simp only [M, det_fin_two_of, D]; ring
  have h2k : D < 2 * k - b' := by dsimp only [k]; linarith [le_abs_self b', abs_nonneg b']
  have hdet_pos : 0 < M.det := by nlinarith
  set m : ℕ := M.det.natAbs
  have hm_eq : (m : ℤ) = M.det := Int.natAbs_of_nonneg hdet_pos.le
  have : NeZero m := ⟨Int.natAbs_ne_zero.2 hdet_pos.ne'⟩
  refine ⟨m, inferInstance, ?_, ⟨M, hm_eq.symm⟩, ?_, ?_⟩
  · rintro ⟨r, hm_sq⟩
    have hm_r : M.det = (r : ℤ) * r := by rw [← hm_eq, hm_sq]; push_cast; rfl
    have hr1 : 2 * k - b' < 2 * (r : ℤ) := by nlinarith [hm_r]
    have hr2 : 2 * (r : ℤ) < 2 * k - b' + 1 := by nlinarith [hm_r]
    omega
  · let L : Matrix (Fin 2) (Fin 2) ℤ →ₗ[ℤ] ℤ :=
      (-v₀) • (entryAddMonoidHom ℤ 0 0).toIntLinearMap +
        (-w₀) • (entryAddMonoidHom ℤ 0 1).toIntLinearMap +
        u₀ • (entryAddMonoidHom ℤ 1 0).toIntLinearMap +
        v₀ • (entryAddMonoidHom ℤ 1 1).toIntLinearMap
    refine isPrimitive_def.2 ⟨L, ?_⟩
    simp only [L, M, LinearMap.add_apply, LinearMap.smul_apply, AddMonoidHom.coe_toIntLinearMap,
      entryAddMonoidHom_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
    linear_combination hbez
  · set A : FixedDetMatrix (Fin 2) ℤ m := ⟨M, hm_eq.symm⟩
    apply UpperHalfPlane.ext
    have hdet : 0 < (toGLReal (NeZero.ne (m : ℤ)) A).det.val := by
      rw [det_toGLReal]; exact_mod_cast Int.natAbs_pos.2 hdet_pos.ne'
    rw [coe_smul_of_det_pos hdet, div_eq_iff (denom_ne_zero _ τ),
      UpperHalfPlane.num, UpperHalfPlane.denom]
    have h00 : (toGLReal (NeZero.ne (m : ℤ)) A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (k : ℝ) - b' := by
      rw [toGLReal_apply]; simp [A, M]
    have h01 : (toGLReal (NeZero.ne (m : ℤ)) A : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -(c' : ℝ) := by
      rw [toGLReal_apply]; simp [A, M]
    have h10 : (toGLReal (NeZero.ne (m : ℤ)) A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = (a' : ℝ) := by
      rw [toGLReal_apply]; simp [A, M]
    have h11 : (toGLReal (NeZero.ne (m : ℤ)) A : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (k : ℝ) := by
      rw [toGLReal_apply]; simp [A, M]
    rw [h00, h01, h10, h11]
    push_cast
    linear_combination -hτ'

/-- **Integrality of `j` at imaginary quadratic points.** If `τ ∈ ℍ` satisfies an integral quadratic
equation `a τ² + b τ + c = 0` with `a ≠ 0`, then `j(τ)` is integral over `ℤ`. -/
theorem isIntegral_j_of_quadratic {τ : ℍ} {a b c : ℤ} (ha : a ≠ 0)
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) : IsIntegral ℤ (j τ) := by
  obtain ⟨a', b', c', -, hbez, hD_pos, hτ'⟩ := exists_primitive_pos_quadratic ha hτ
  obtain ⟨m, _, hm_nsq, A, hA_prim, hfix⟩ :=
    exists_primitive_fixedDetMatrix_nonsquare_fixing hbez hD_pos hτ'
  exact isIntegral_of_aeval_diagModularPolynomial_eq_zero hm_nsq
    ((aeval_j_diagModularPolynomial_eq_zero_iff τ).2 ⟨A, hA_prim, hfix⟩)

end TauCeti.ModularForm
