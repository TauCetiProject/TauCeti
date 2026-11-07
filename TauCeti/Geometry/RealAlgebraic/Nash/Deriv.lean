/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Algebraic.Integral
import TauCeti.Analysis.Analytic.Germ
import TauCeti.Analysis.MvPolynomial.Jacobian
import TauCeti.Order.Filter.Germ.MvPolynomial
import TauCeti.RingTheory.Algebraic.Basic

/-!
# Derivatives of Nash germs

The directional derivative `y ↦ Df(y) v` of a Nash germ `f` at `x` is again a Nash germ at `x`
(`TauCeti.IsNashAt.fderiv_apply`), and so are all its iterated derivatives
(`TauCeti.IsNashAt.iteratedFDeriv_apply`). In particular the partial derivatives of a Nash germ are
Nash germs. Closure under differentiation lets one describe the order of vanishing of a Nash germ,
for instance the multiplicity of a root along a line, through its successive derivatives, all of
which are again Nash germs.

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

/-- **Derivatives of Nash germs.** The derivative of a Nash germ in any fixed direction `v` is a
Nash germ. -/
theorem IsNashAt.fderiv_apply (hf : IsNashAt f x) (v : σ → ℝ) :
    IsNashAt (fun y ↦ fderiv ℝ f y v) x := by
  -- Implicit differentiation, carried out in the analytic germs at `x`, which have no zero
  -- divisors. Choose a relation `P (y, f y) = 0` whose `t`-derivative `P_t (y, f y)` has a nonzero
  -- germ. Differentiating it in the direction `v` gives
  -- `P_t (y, f y) * Df(y) v + (D_v P) (y, f y) = 0`, and both `P_t (y, f y)` and
  -- `(D_v P) (y, f y)` are polynomial expressions in the germ of `f`, hence algebraic. Dividing
  -- by the nonzero germ of `P_t (y, f y)` shows that the germ of `Df(y) v` is algebraic.
  set S := analyticGermSubalgebra (σ := σ) (𝕜 := ℝ) x
  have hfa := hf.analyticAt
  have hDa : AnalyticAt ℝ (fun y ↦ fderiv ℝ f y v) x :=
    ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _).comp hfa.fderiv
  let F : S := ⟨f, mem_analyticGermSubalgebra.2 (coe_mem_analyticGerms.2 hfa)⟩
  let G : S := ⟨fun y ↦ fderiv ℝ f y v, mem_analyticGermSubalgebra.2 (coe_mem_analyticGerms.2 hDa)⟩
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
  obtain ⟨P, hPF, hb0⟩ := hFalg.exists_aeval_eq_zero_and_aeval_derivative_ne_zero
    (analyticGermSubalgebra.algebraMap_injective x)
  -- Differentiating `P (F) = 0` gives `P_t (F) * G = -(D_v P) (F)`.
  have hid : aeval F (derivative P) * G = -aeval F (derivCoeffs v P) := by
    rw [eq_neg_iff_add_eq_zero]
    apply Subtype.ext
    rw [Subalgebra.coe_add, Subalgebra.coe_mul, hval, hval, ZeroMemClass.coe_zero, ← Germ.coe_mul,
      ← Germ.coe_add, ← Germ.coe_zero, Germ.coe_eq]
    exact eventually_eval_derivative_mul_fderiv_add_eval_derivCoeffs
      (hfa.eventually_analyticAt.mono fun _ hy ↦ hy.differentiableAt)
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
