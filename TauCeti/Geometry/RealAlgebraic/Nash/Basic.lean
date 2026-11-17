/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Analytic.Constructions
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.RingTheory.Algebraic.Integral
import TauCeti.Analysis.Analytic.Germ
import TauCeti.Order.Filter.Germ.MvPolynomial

/-!
# Nash germs

A real function `f` on `σ → ℝ` is a *Nash germ* at `x` (`TauCeti.IsNashAt`) if it is analytic at
`x` and satisfies a nonzero polynomial relation `P (y, f y) = 0` for all `y` near `x`. The
relation `P` is a polynomial in the value variable `t` whose coefficients are polynomials in the
coordinates `y`, that is, an element `P : (MvPolynomial σ ℝ)[X]` of `ℝ[y][t] ≃ ℝ[y, t]`. Both the
polynomial and the neighbourhood may depend on `x`. A function on an open set is a Nash function
when its germ at every point is a Nash germ. Nash functions are the analytic functions of real
algebraic geometry; classically, an analytic function on an open semialgebraic set is Nash exactly
when its graph is semialgebraic (Bochnak–Coste–Roy, Section 8.1), a criterion not proved
here.

This file proves that being a Nash germ is a property of the germ, that it propagates to nearby
points, and that Nash germs form a subring of the analytic germs that is closed under inverses of
nonvanishing germs and under exact division inside analytic germs:

* polynomial functions, in particular constants, coordinate functions, and linear functionals, are
  Nash germs;
* sums, negations, differences, products, powers, finite sums, finite products, and evaluations of
  monic polynomials with Nash coefficients at Nash arguments are Nash germs;
* the inverse and quotients of Nash germs are Nash germs where the denominator does not vanish,
  and an analytic quotient of a Nash germ by a nonzero Nash germ is again a Nash germ.

The algebraic closure properties come from Mathlib's algebraic elements of an algebra over a
domain (`IsAlgebraic.add`, `IsAlgebraic.mul`, `IsAlgebraic.invOf`, `IsAlgebraic.of_mul`): a
polynomial relation near `x` is exactly algebraicity of the germ of `f` at `x` over `ℝ[y]`, where
polynomials act on germs as polynomial functions (`Filter.Germ.isAlgebraic_coe_iff` and
`TauCeti.analyticGerms.isAlgebraic_ofAnalyticAt_iff`), and the ring of analytic germs
`TauCeti.analyticGerms ℝ x` is an integral domain by the identity principle.

## Main declarations

* `TauCeti.IsNashAt f x`: `f` is a Nash germ at `x`.
* `TauCeti.isNashAt_iff_exists_mem_nhds`: the neighbourhood form, an analytic function with a
  polynomial relation on a whole neighbourhood of `x`.
* `TauCeti.IsNashAt.congr`: Nash germs depend only on the germ.
* `TauCeti.IsNashAt.eventually_isNashAt`: a Nash germ at `x` is a Nash germ at every nearby point.
* `MvPolynomial.isNashAt_eval`, `LinearMap.isNashAt`, `ContinuousLinearMap.isNashAt`,
  `LinearMap.isNashAt_apply`, `ContinuousLinearMap.isNashAt_apply`: polynomial and linear Nash
  germs.
* `TauCeti.IsNashAt.add`, `TauCeti.IsNashAt.mul`, `TauCeti.IsNashAt.eval_monicOfCoeff`,
  `TauCeti.IsNashAt.inv`, `TauCeti.IsNashAt.div`, `TauCeti.IsNashAt.of_eventuallyEq_mul_left`,
  `TauCeti.IsNashAt.of_eventuallyEq_mul_right`: the algebraic and exact-division closure
  properties.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 36, Springer, 1998, Section 8.1 (Nash functions).
* J. M. Ruiz, *The Basic Theory of Power Series*, Advanced Lectures in Mathematics, Vieweg, 1993,
  Chapter III.
-/

public section

open Filter Polynomial Topology

namespace TauCeti

variable {σ : Type*} [Fintype σ] {f g : (σ → ℝ) → ℝ} {x : σ → ℝ}

/-- A real function `f` on `σ → ℝ` is a *Nash germ* at `x` if it is analytic at `x` and satisfies
a nonzero polynomial relation `P (y, f y) = 0` for all `y` near `x`. Here
`P : (MvPolynomial σ ℝ)[X]` is a polynomial in the value variable whose coefficients are
polynomials in the coordinates, and `P (y, t)` is `(P.map (MvPolynomial.eval y)).eval t`. -/
def IsNashAt (f : (σ → ℝ) → ℝ) (x : σ → ℝ) : Prop :=
  AnalyticAt ℝ f x ∧ ∃ P : (MvPolynomial σ ℝ)[X], P ≠ 0 ∧
    ∀ᶠ y in 𝓝 x, (P.map (MvPolynomial.eval y)).eval (f y) = 0

/-- Unfolding `TauCeti.IsNashAt`. -/
theorem isNashAt_iff : IsNashAt f x ↔ AnalyticAt ℝ f x ∧ ∃ P : (MvPolynomial σ ℝ)[X], P ≠ 0 ∧
    ∀ᶠ y in 𝓝 x, (P.map (MvPolynomial.eval y)).eval (f y) = 0 :=
  Iff.rfl

/-- A Nash germ is analytic. -/
theorem IsNashAt.analyticAt (hf : IsNashAt f x) : AnalyticAt ℝ f x :=
  hf.1

/-- A Nash germ at `x` is an analytic function on a neighbourhood `U` of `x` satisfying a single
nonzero polynomial relation `P (y, f y) = 0` at every point `y ∈ U`. -/
theorem isNashAt_iff_exists_mem_nhds : IsNashAt f x ↔ ∃ U ∈ 𝓝 x, AnalyticOnNhd ℝ f U ∧
    ∃ P : (MvPolynomial σ ℝ)[X], P ≠ 0 ∧ ∀ y ∈ U, (P.map (MvPolynomial.eval y)).eval (f y) = 0 := by
  constructor
  · rintro ⟨hf, P, hP, hrel⟩
    exact ⟨_, hf.eventually_analyticAt.and hrel, fun y hy ↦ hy.1, P, hP, fun y hy ↦ hy.2⟩
  · rintro ⟨U, hU, hf, P, hP, hrel⟩
    exact ⟨hf x (mem_of_mem_nhds hU), P, hP, eventually_of_mem hU hrel⟩

/-- Being a Nash germ depends only on the germ of the function. -/
theorem IsNashAt.congr (hf : IsNashAt f x) (hg : f =ᶠ[𝓝 x] g) : IsNashAt g x := by
  obtain ⟨hfa, P, hP, hrel⟩ := hf
  exact ⟨hfa.congr hg, P, hP, (hrel.and hg).mono fun y hy ↦ hy.2 ▸ hy.1⟩

/-- Functions with the same germ at `x` are Nash germs at `x` together. -/
theorem _root_.Filter.EventuallyEq.isNashAt_iff (hg : f =ᶠ[𝓝 x] g) :
    IsNashAt f x ↔ IsNashAt g x :=
  ⟨fun hf ↦ hf.congr hg, fun hg' ↦ hg'.congr hg.symm⟩

/-- A Nash germ at `x` is a Nash germ at every point near `x`. -/
theorem IsNashAt.eventually_isNashAt (hf : IsNashAt f x) : ∀ᶠ y in 𝓝 x, IsNashAt f y := by
  obtain ⟨hfa, P, hP, hrel⟩ := hf
  filter_upwards [hfa.eventually_analyticAt, hrel.eventually_nhds] with y hy hy'
  exact ⟨hy, P, hP, hy'⟩

/-! ### Nash germs as algebraic germs -/

attribute [local instance] Germ.mvPolynomialAlgebra

private theorem IsNashAt.isAlgebraic (hf : IsNashAt f x) :
    IsAlgebraic (MvPolynomial σ ℝ) (f : Germ (𝓝 x) ℝ) :=
  Germ.isAlgebraic_coe_iff.2 hf.2

private theorem IsNashAt.of_isAlgebraic (hfa : AnalyticAt ℝ f x)
    (hf : IsAlgebraic (MvPolynomial σ ℝ) (f : Germ (𝓝 x) ℝ)) : IsNashAt f x :=
  ⟨hfa, Germ.isAlgebraic_coe_iff.1 hf⟩

/-! ### Polynomial functions -/

/-- Polynomial functions are Nash germs at every point. -/
theorem _root_.MvPolynomial.isNashAt_eval (p : MvPolynomial σ ℝ) :
    IsNashAt (fun y ↦ MvPolynomial.eval y p) x := by
  refine .of_isAlgebraic ?_ ?_
  · exact AnalyticOnNhd.eval_mvPolynomial p x (Set.mem_univ x)
  · rw [← Germ.mvPolynomialAlgebra_algebraMap_apply]
    exact isAlgebraic_algebraMap p

/-- Constant functions are Nash germs. -/
theorem isNashAt_const (c : ℝ) : IsNashAt (fun _ : σ → ℝ ↦ c) x := by
  simpa using (MvPolynomial.C c : MvPolynomial σ ℝ).isNashAt_eval (x := x)

/-- Coordinate functions are Nash germs. -/
theorem isNashAt_apply (i : σ) : IsNashAt (fun y : σ → ℝ ↦ y i) x := by
  simpa using (MvPolynomial.X i : MvPolynomial σ ℝ).isNashAt_eval (x := x)

/-! ### Ring operations -/

/-- The sum of two Nash germs is a Nash germ. -/
@[to_fun]
theorem IsNashAt.add (hf : IsNashAt f x) (hg : IsNashAt g x) : IsNashAt (f + g) x :=
  .of_isAlgebraic (hf.analyticAt.add hg.analyticAt) <| by
    rw [Germ.coe_add]
    exact hf.isAlgebraic.add hg.isAlgebraic

/-- The negation of a Nash germ is a Nash germ. -/
@[to_fun]
theorem IsNashAt.neg (hf : IsNashAt f x) : IsNashAt (-f) x :=
  .of_isAlgebraic hf.analyticAt.neg <| by
    rw [Germ.coe_neg]
    exact hf.isAlgebraic.neg

/-- The difference of two Nash germs is a Nash germ. -/
@[to_fun]
theorem IsNashAt.sub (hf : IsNashAt f x) (hg : IsNashAt g x) : IsNashAt (f - g) x := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- The product of two Nash germs is a Nash germ. -/
@[to_fun]
theorem IsNashAt.mul (hf : IsNashAt f x) (hg : IsNashAt g x) : IsNashAt (f * g) x :=
  .of_isAlgebraic (hf.analyticAt.mul hg.analyticAt) <| by
    rw [Germ.coe_mul]
    exact hf.isAlgebraic.mul hg.isAlgebraic

/-- Powers of a Nash germ are Nash germs. -/
@[to_fun]
theorem IsNashAt.pow (hf : IsNashAt f x) (n : ℕ) : IsNashAt (f ^ n) x :=
  .of_isAlgebraic (hf.analyticAt.pow n) <| by
    rw [Germ.coe_pow]
    exact hf.isAlgebraic.pow n

/-- Finite sums of Nash germs are Nash germs. -/
@[to_fun]
theorem _root_.Finset.isNashAt_sum {ι : Type*} {F : ι → (σ → ℝ) → ℝ} (N : Finset ι)
    (h : ∀ i ∈ N, IsNashAt (F i) x) : IsNashAt (∑ i ∈ N, F i) x :=
  Finset.sum_induction _ (IsNashAt · x) (fun _ _ ↦ .add) (isNashAt_const 0) h

/-- Finite products of Nash germs are Nash germs. -/
@[to_fun]
theorem _root_.Finset.isNashAt_prod {ι : Type*} {F : ι → (σ → ℝ) → ℝ} (N : Finset ι)
    (h : ∀ i ∈ N, IsNashAt (F i) x) : IsNashAt (∏ i ∈ N, F i) x :=
  Finset.prod_induction _ (IsNashAt · x) (fun _ _ ↦ .mul) (isNashAt_const 1) h

/-- Evaluating a monic polynomial whose lower coefficients are Nash germs at `x` on a Nash germ
`g` at `x` produces a Nash germ at `x`. -/
theorem IsNashAt.eval_monicOfCoeff {d : ℕ} {c : Fin d → (σ → ℝ) → ℝ} {g : (σ → ℝ) → ℝ}
    {x : σ → ℝ} (hc : ∀ i, IsNashAt (c i) x) (hg : IsNashAt g x) :
    IsNashAt (fun y ↦ (Polynomial.monicOfCoeff (fun i ↦ c i y)).eval (g y)) x := by
  have heq : (fun y ↦ (Polynomial.monicOfCoeff (fun i ↦ c i y)).eval (g y)) =
      (fun y ↦ g y ^ d) + ∑ i : Fin d, fun y ↦ c i y * g y ^ (i : ℕ) := by
    ext y
    simp [Polynomial.eval_monicOfCoeff, Finset.sum_apply]
  rw [heq]
  exact (hg.fun_pow d).add
    (Finset.univ.isNashAt_sum fun i _ ↦ (hc i).fun_mul (hg.fun_pow (i : ℕ)))

/-! ### Linear maps -/

/-- A linear functional on a finite-dimensional real coordinate space is a Nash germ. -/
theorem _root_.LinearMap.isNashAt (L : (σ → ℝ) →ₗ[ℝ] ℝ) : IsNashAt L x := by
  classical
  have hlin : (L : (σ → ℝ) → ℝ) = ∑ i : σ, fun y ↦ y i * L fun j ↦ if i = j then 1 else 0 := by
    ext y
    simpa [Finset.sum_apply] using L.pi_apply_eq_sum_univ y
  rw [hlin]
  exact Finset.univ.isNashAt_sum fun i _ ↦ (isNashAt_apply i).fun_mul (isNashAt_const _)

/-- A continuous linear functional on a finite-dimensional real coordinate space is a Nash germ. -/
theorem _root_.ContinuousLinearMap.isNashAt (L : (σ → ℝ) →L[ℝ] ℝ) : IsNashAt L x :=
  L.toLinearMap.isNashAt

/-- Every coordinate of a linear map from a finite-dimensional real coordinate space is a Nash
germ. -/
theorem _root_.LinearMap.isNashAt_apply {τ : Type*} (L : (σ → ℝ) →ₗ[ℝ] (τ → ℝ)) (j : τ) :
    IsNashAt (fun y ↦ L y j) x :=
  ((LinearMap.proj (R := ℝ) j).comp L).isNashAt

/-- Every coordinate of a continuous linear map from a finite-dimensional real coordinate space is
a Nash germ. -/
theorem _root_.ContinuousLinearMap.isNashAt_apply {τ : Type*} (L : (σ → ℝ) →L[ℝ] (τ → ℝ)) (j : τ) :
    IsNashAt (fun y ↦ L y j) x :=
  L.toLinearMap.isNashAt_apply j

/-! ### Inverses and exact division -/

/-- The inverse of a Nash germ which does not vanish at `x` is a Nash germ at `x`. -/
@[to_fun]
theorem IsNashAt.inv (hf : IsNashAt f x) (h0 : f x ≠ 0) : IsNashAt f⁻¹ x := by
  have hmul : (f : Germ (𝓝 x) ℝ) * ↑f⁻¹ = 1 := by
    rw [← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq]
    filter_upwards [hf.analyticAt.continuousAt.eventually_ne h0] with y hy
    simp [hy]
  let : Invertible (f : Germ (𝓝 x) ℝ) := invertibleOfRightInverse _ _ hmul
  refine .of_isAlgebraic (hf.analyticAt.inv h0) ?_
  rw [← invOf_eq_right_inv hmul]
  exact hf.isAlgebraic.invOf

/-- The quotient of Nash germs is a Nash germ where the denominator does not vanish. -/
@[to_fun]
theorem IsNashAt.div (hf : IsNashAt f x) (hg : IsNashAt g x) (h0 : g x ≠ 0) :
    IsNashAt (f / g) x := by
  simpa [div_eq_mul_inv] using hf.mul (hg.inv h0)

attribute [local instance] analyticGerms.mvPolynomialAlgebra

/-- **Exact division of Nash germs.** If `g =ᶠ[𝓝 x] f * u` with `f` and `g` Nash germs at `x`,
`f` not identically zero near `x`, and `u` real analytic at `x`, then `u` is a Nash germ at `x`. -/
theorem IsNashAt.of_eventuallyEq_mul_left {u : (σ → ℝ) → ℝ}
    (hg : IsNashAt g x) (hf : IsNashAt f x) (hf0 : ¬ f =ᶠ[𝓝 x] 0)
    (hu : AnalyticAt ℝ u x) (h : g =ᶠ[𝓝 x] f * u) : IsNashAt u x := by
  let fG := analyticGerms.ofAnalyticAt f hf.analyticAt
  let uG := analyticGerms.ofAnalyticAt u hu
  have hfg : fG * uG = analyticGerms.ofAnalyticAt g hg.analyticAt := by
    rw [← analyticGerms.ofAnalyticAt_mul]
    exact analyticGerms.ofAnalyticAt_congr h.symm
  have hfG_nz : fG ∈ nonZeroDivisors (analyticGerms ℝ x) :=
    mem_nonZeroDivisors_of_ne_zero (mt analyticGerms.ofAnalyticAt_eq_zero_iff.1 hf0)
  have hfG_alg : IsAlgebraic (MvPolynomial σ ℝ) fG :=
    analyticGerms.isAlgebraic_ofAnalyticAt_iff.2 hf.2
  have hfuG_alg : IsAlgebraic (MvPolynomial σ ℝ) (fG * uG) := by
    rw [hfg]
    exact analyticGerms.isAlgebraic_ofAnalyticAt_iff.2 hg.2
  exact ⟨hu, analyticGerms.isAlgebraic_ofAnalyticAt_iff.1
    (IsAlgebraic.of_mul hfG_nz hfG_alg hfuG_alg)⟩

/-- Right-factor version of `TauCeti.IsNashAt.of_eventuallyEq_mul_left`: if `g =ᶠ[𝓝 x] u * f` with
`f` and `g` Nash germs at `x`, `f` not identically zero near `x`, and `u` real analytic at `x`,
then `u` is a Nash germ at `x`. -/
theorem IsNashAt.of_eventuallyEq_mul_right {u : (σ → ℝ) → ℝ}
    (hg : IsNashAt g x) (hf : IsNashAt f x) (hf0 : ¬ f =ᶠ[𝓝 x] 0)
    (hu : AnalyticAt ℝ u x) (h : g =ᶠ[𝓝 x] u * f) : IsNashAt u x :=
  hg.of_eventuallyEq_mul_left hf hf0 hu
    (h.trans (Eventually.of_forall fun y ↦ mul_comm (u y) (f y)))

end TauCeti
