/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Algebraic.Integral
import TauCeti.Analysis.Analytic.Germ
import TauCeti.Analysis.MvPolynomial.Jacobian
import TauCeti.Order.Filter.Germ.MvPolynomial

/-!
# Derivatives of Nash germs

The directional derivative `y ↦ Df(y) v` of a Nash germ `f` at `x` is again a Nash germ at `x`
(`TauCeti.IsNashAt.fderiv_apply`), and so are all its iterated derivatives
(`TauCeti.IsNashAt.iteratedFDeriv_apply`). In particular the partial derivatives of a Nash germ are
Nash germs.

The proof is implicit differentiation, carried out in the ring of analytic germs at `x`, which is
an integral domain (`TauCeti.analyticGerms.instIsDomain`). Choose a nonzero relation
`P (y, f y) = 0` of least degree in the value variable. Differentiating it in the direction `v`
gives
`P_t (y, f y) * Df(y) v + (D_v P) (y, f y) = 0`,
where `P_t` is the derivative of `P` in the value variable and `D_v P` differentiates the
coefficients of `P` in the direction `v`. Both `P_t (y, f y)` and `(D_v P) (y, f y)` are polynomial
expressions in the germ of `f`, hence algebraic over the coordinate polynomials. The germ of
`P_t (y, f y)` is nonzero by the minimality of `P`, since `P_t` is a nonzero polynomial of smaller
degree, so in the domain of analytic germs the germ of `Df(y) v` is algebraic as well
(`IsAlgebraic.of_mul`). No squarefreeness of `P` and no analysis of the locus where `P_t (y, f y)`
vanishes is needed: the division takes place among germs.

## Main results

* `TauCeti.IsNashAt.fderiv_apply`: directional derivatives of Nash germs are Nash germs.
* `TauCeti.IsNashAt.iteratedFDeriv_apply`: iterated directional derivatives of Nash germs are Nash
  germs.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Section 8.1 (Nash functions).
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §1.
-/

public section

open Filter Polynomial Topology

namespace TauCeti

variable {σ : Type*} [Fintype σ] {f : (σ → ℝ) → ℝ} {x : σ → ℝ}

attribute [local instance] Germ.mvPolynomialAlgebra

/-- The analytic germs at `x`, as a subalgebra over the coordinate polynomials of the ring of all
function germs at `x`. -/
private noncomputable def analyticGermSubalgebra (x : σ → ℝ) :
    Subalgebra (MvPolynomial σ ℝ) (Germ (𝓝 x) ℝ) :=
  { (analyticGerms ℝ x).toSubsemiring with
    algebraMap_mem' p := by
      rw [Germ.mvPolynomialAlgebra_algebraMap_apply]
      exact coe_mem_analyticGerms.2 (AnalyticOnNhd.eval_mvPolynomial p x (Set.mem_univ x)) }

private instance : NoZeroDivisors (analyticGermSubalgebra x) where
  eq_zero_or_eq_zero_of_mul_eq_zero {φ ψ} h := by
    have h' : (⟨φ, φ.2⟩ : analyticGerms ℝ x) * ⟨ψ, ψ.2⟩ = 0 := Subtype.ext (congrArg Subtype.val h)
    exact (mul_eq_zero.1 h').imp (fun h0 ↦ Subtype.ext (congrArg Subtype.val h0))
      (fun h0 ↦ Subtype.ext (congrArg Subtype.val h0))

/-- The derivative of `y ↦ ∑ k < N, c_k(y) * f(y) ^ k` in the direction `v`, for polynomial
coefficients `c_k`, is `(∑ k < N, k * c_k(y) * f(y) ^ (k - 1)) * Df(y) v` plus
`∑ k < N, (D_v c_k)(y) * f(y) ^ k`. -/
private theorem fderiv_sum_eval_mul_pow_apply (c : ℕ → MvPolynomial σ ℝ) (N : ℕ) {y : σ → ℝ}
    (hfy : DifferentiableAt ℝ f y) (v : σ → ℝ) :
    fderiv ℝ (fun z ↦ ∑ k ∈ Finset.range N, MvPolynomial.eval z (c k) * f z ^ k) y v =
      (∑ k ∈ Finset.range N, MvPolynomial.eval y (c k) * k * f y ^ (k - 1)) * fderiv ℝ f y v +
        ∑ k ∈ Finset.range N,
          MvPolynomial.eval y (∑ j, MvPolynomial.C (v j) * MvPolynomial.pderiv j (c k)) *
            f y ^ k := by
  have hd := HasFDerivAt.fun_sum (u := Finset.range N) fun k _ ↦
    ((c k).hasFDerivAt_eval y).fun_mul (hfy.hasFDerivAt.pow k)
  rw [hd.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, map_sum, map_mul, MvPolynomial.eval_C,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- The polynomial obtained from `P` by differentiating its coefficients in the direction `v`. -/
private noncomputable def derivCoeffs (v : σ → ℝ) (P : (MvPolynomial σ ℝ)[X]) :
    (MvPolynomial σ ℝ)[X] :=
  ∑ k ∈ Finset.range (P.natDegree + 1),
    monomial k (∑ j, MvPolynomial.C (v j) * MvPolynomial.pderiv j (P.coeff k))

/-- **Implicit differentiation.** If `P (y, f y) = 0` near `x`, then near `x`,
`P_t (y, f y) * Df(y) v + (D_v P) (y, f y) = 0`. -/
private theorem eventually_eval_derivative_mul_fderiv_add_eval_derivCoeffs
    (hf : AnalyticAt ℝ f x) {P : (MvPolynomial σ ℝ)[X]}
    (hP : ∀ᶠ y in 𝓝 x, (P.map (MvPolynomial.eval y)).eval (f y) = 0) (v : σ → ℝ) :
    ∀ᶠ y in 𝓝 x, ((derivative P).map (MvPolynomial.eval y)).eval (f y) * fderiv ℝ f y v +
      ((derivCoeffs v P).map (MvPolynomial.eval y)).eval (f y) = 0 := by
  set N := P.natDegree + 1
  have hPsum : P = ∑ k ∈ Finset.range N, monomial k (P.coeff k) :=
    as_sum_range' P N (Nat.lt_succ_self _)
  have hrel : ∀ᶠ y in 𝓝 x,
      ∑ k ∈ Finset.range N, MvPolynomial.eval y (P.coeff k) * f y ^ k = 0 := by
    filter_upwards [hP] with y hy
    rw [hPsum] at hy
    simpa [Polynomial.map_sum, eval_finsetSum] using hy
  filter_upwards [hrel.eventually_nhds, hf.eventually_analyticAt] with y hy hfy
  have h0 := fderiv_sum_eval_mul_pow_apply (fun k ↦ P.coeff k) N hfy.differentiableAt v
  rw [Filter.EventuallyEq.fderiv_eq (f := 0) hy, fderiv_zero, Pi.zero_apply, zero_apply] at h0
  nth_rewrite 1 [hPsum]
  simp only [derivCoeffs, derivative_sum, derivative_monomial, Polynomial.map_sum,
    Polynomial.map_monomial, map_mul, map_natCast]
  rw [eval_finsetSum, eval_finsetSum]
  simp only [eval_monomial]
  rw [h0]

/-- Nonzero polynomials define nonzero germs: the coordinate polynomials embed into the analytic
germs at `x`. -/
private theorem algebraMap_analyticGermSubalgebra_injective :
    Function.Injective (algebraMap (MvPolynomial σ ℝ) (analyticGermSubalgebra x)) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp ↦ ?_
  have hc : (fun y ↦ MvPolynomial.eval y p) =ᶠ[𝓝 x] 0 := by
    rw [← Germ.coe_eq, Germ.coe_zero, ← Germ.mvPolynomialAlgebra_algebraMap_apply]
    exact congrArg Subtype.val hp
  have hc0 := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (AnalyticOnNhd.eval_mvPolynomial _) isPreconnected_univ (Set.mem_univ x) hc
  exact MvPolynomial.funext fun y ↦ by simpa using hc0 (Set.mem_univ y)

/-- An algebraic analytic germ `F` satisfies a polynomial relation `P (F) = 0` whose derivative in
the value variable does not vanish at `F`: take a nonzero relation of least degree. -/
private theorem exists_aeval_eq_zero_and_aeval_derivative_ne_zero
    {F : analyticGermSubalgebra x} (hF : IsAlgebraic (MvPolynomial σ ℝ) F) :
    ∃ P : (MvPolynomial σ ℝ)[X], aeval F P = 0 ∧ aeval F (derivative P) ≠ 0 := by
  classical
  have hex : ∃ n, ∃ P : (MvPolynomial σ ℝ)[X], P ≠ 0 ∧ P.natDegree = n ∧ aeval F P = 0 := by
    obtain ⟨P, hP, hPF⟩ := hF
    exact ⟨_, P, hP, rfl, hPF⟩
  obtain ⟨P, hP0, hPdeg, hPF⟩ := Nat.find_spec hex
  have hdeg : P.natDegree ≠ 0 := by
    intro h0
    rw [eq_C_of_natDegree_eq_zero h0, aeval_C] at hPF
    rw [eq_C_of_natDegree_eq_zero h0, ne_eq, C_eq_zero] at hP0
    exact hP0 (algebraMap_analyticGermSubalgebra_injective (hPF.trans (map_zero _).symm))
  exact ⟨P, hPF, fun h ↦ Nat.find_min hex (hPdeg ▸ natDegree_derivative_lt hdeg)
    ⟨_, derivative_ne_zero.2 hdeg, rfl, h⟩⟩

/-- **Derivatives of Nash germs.** The derivative of a Nash germ in any fixed direction `v` is a
Nash germ. -/
theorem IsNashAt.fderiv_apply (hf : IsNashAt f x) (v : σ → ℝ) :
    IsNashAt (fun y ↦ fderiv ℝ f y v) x := by
  set S := analyticGermSubalgebra (σ := σ) x
  have hfa := hf.analyticAt
  have hDa : AnalyticAt ℝ (fun y ↦ fderiv ℝ f y v) x :=
    ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _).comp hfa.fderiv
  let F : S := ⟨f, coe_mem_analyticGerms.2 hfa⟩
  let G : S := ⟨fun y ↦ fderiv ℝ f y v, coe_mem_analyticGerms.2 hDa⟩
  have hval (Q : (MvPolynomial σ ℝ)[X]) : ((aeval F Q : S) : Germ (𝓝 x) ℝ) =
      ((fun y ↦ (Q.map (MvPolynomial.eval y)).eval (f y) : (σ → ℝ) → ℝ) : Germ (𝓝 x) ℝ) := by
    rw [← Germ.aeval_coe]
    exact (aeval_algHom_apply S.val F Q).symm
  have hFalg : IsAlgebraic (MvPolynomial σ ℝ) F :=
    (isAlgebraic_algHom_iff S.val Subtype.val_injective).1
      (Germ.isAlgebraic_coe_iff.2 (isNashAt_iff.1 hf).2)
  -- Every polynomial expression in `F` is algebraic.
  have halg (Q : (MvPolynomial σ ℝ)[X]) : IsAlgebraic (MvPolynomial σ ℝ) (aeval F Q) :=
    (Subalgebra.mem_algebraicClosure _ _).1 <|
      Algebra.adjoin_le (Set.singleton_subset_iff.2 hFalg) (aeval_mem_adjoin_singleton _ _)
  obtain ⟨P, hPF, hb0⟩ := exists_aeval_eq_zero_and_aeval_derivative_ne_zero hFalg
  -- Differentiating `P (F) = 0` gives `P_t (F) * G = -(D_v P) (F)`.
  have hid : aeval F (derivative P) * G = -aeval F (derivCoeffs v P) := by
    rw [eq_neg_iff_add_eq_zero]
    apply Subtype.ext
    rw [Subalgebra.coe_add, Subalgebra.coe_mul, hval, hval, ZeroMemClass.coe_zero, ← Germ.coe_mul,
      ← Germ.coe_add, ← Germ.coe_zero, Germ.coe_eq]
    exact eventually_eval_derivative_mul_fderiv_add_eval_derivCoeffs hfa
      (Germ.coe_eq.1 ((hval P).symm.trans (congrArg Subtype.val hPF))) v
  have hG : IsAlgebraic (MvPolynomial σ ℝ) G :=
    IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hb0) (halg _) (hid ▸ (halg _).neg)
  exact isNashAt_iff.2 ⟨hDa, Germ.isAlgebraic_coe_iff.1 (hG.algHom S.val)⟩

/-- **Iterated derivatives of Nash germs.** The `n`-th derivative of a Nash germ, evaluated at
fixed directions `m`, is a Nash germ. -/
theorem IsNashAt.iteratedFDeriv_apply (hf : IsNashAt f x) (n : ℕ) (m : Fin n → σ → ℝ) :
    IsNashAt (fun y ↦ iteratedFDeriv ℝ n f y m) x := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    refine ((ih (Fin.tail m)).fderiv_apply (m 0)).congr ?_
    filter_upwards [hf.analyticAt.eventually_analyticAt] with y hy
    obtain ⟨U, hU, hfU⟩ := hy.exists_mem_nhds_analyticOnNhd
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y :=
      ((hfU.iteratedFDeriv n) y (mem_of_mem_nhds hU)).differentiableAt
    rw [iteratedFDeriv_succ_apply_left, fderiv_continuousMultilinear_apply_const_apply hd]

end TauCeti
