/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Lazard.Uniform
public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Limits of roots along Lazard monomial curves

Let `p` be a polynomial in variables `Fin n` with coefficients in `𝕜[T]`, and let `a` be a
point in `𝕜ⁿ`. Restricting the outer variables to the monomial curve `a + y ^ c` gives a
polynomial in `T` for each `y`. This file shows that if `r y` is a root in `T` for all nonzero
`y` near zero and `r y` tends to `z`, then `z` is a root of the Lazard evaluation at `a`.
Along an evaluator curve, the Lazard evaluation is the lowest-order coefficient in `y`, after
factoring out the corresponding power of `y`.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), Section 5.1.
-/

public section

open Filter Finsupp Polynomial Topology

namespace Polynomial

/-- If `y` and `r y` tend to `y₀` and `x₀`, respectively, then evaluating a polynomial with
polynomial coefficients first at `C y` and then at `r y` tends to its value at `(y₀, x₀)`. -/
theorem tendsto_eval_C_eval {α : Type*} [TopologicalSpace α] {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] {l : Filter α} (R : Polynomial (Polynomial 𝕜))
    {y r : α → 𝕜} {y₀ x₀ : 𝕜} (hy : Tendsto y l (𝓝 y₀)) (hr : Tendsto r l (𝓝 x₀)) :
    Tendsto (fun t ↦ (R.eval (C (y t))).eval (r t)) l
      (𝓝 ((R.eval (C y₀)).eval x₀)) := by
  have heq (t : α) : (R.eval (C (y t))).eval (r t) =
      ∑ j ∈ R.support, (R.coeff j).eval (r t) * y t ^ j := by
    rw [Polynomial.eval_eq_sum (p := R)]
    simp only [Polynomial.sum_def, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C]
  have heq₀ : (R.eval (C y₀)).eval x₀ =
      ∑ j ∈ R.support, (R.coeff j).eval x₀ * y₀ ^ j := by
    rw [Polynomial.eval_eq_sum (p := R)]
    simp only [Polynomial.sum_def, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C]
  rw [heq₀]
  simp only [heq]
  refine tendsto_finsetSum _ fun j hj ↦ ?_
  exact ((R.coeff j).continuousAt.tendsto.comp hr).mul (hy.pow j)

end Polynomial

namespace MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- A finite limit of roots in `T` of the polynomial restricted to a monomial curve is a root
of the Lazard evaluation at the center. The weights must separate the removed exponent from
every higher Taylor exponent; no constancy of ordinary specializations is required. -/
theorem isRoot_lazardEval_of_tendsto_deformed_roots
    (p : MvPolynomial (Fin n) (Polynomial 𝕜)) (a : Fin n → 𝕜)
    (c : Fin n → ℕ) (r : 𝕜 → 𝕜)
    (hc : TauCeti.IsLazardEvaluator {p.lazardExponent (Polynomial.C ∘ a)} c)
    {z : 𝕜} (hr : Tendsto r (𝓝[≠] 0) (𝓝 z))
    (hroot : ∀ᶠ y in 𝓝[≠] (0 : 𝕜),
      ((aeval (monomialCurve (Polynomial.C ∘ a) c) p).eval (Polynomial.C y)).eval (r y) = 0) :
    (p.lazardEval (Polynomial.C ∘ a)).IsRoot z := by
  let v := p.lazardExponent (Polynomial.C ∘ a)
  obtain ⟨Q, hQ⟩ := p.exists_aeval_monomialCurve_eq_pow_mul
    (S := {Polynomial.C ∘ a}) (V := {v}) (v := v) (c := c)
    (by simp [v]) hc (by
      intro b hb u hu
      subst b
      exact coeff_taylor_eq_zero_of_lt_lazardExponent hu)
  have hfactor := hQ (Polynomial.C ∘ a) (by simp)
  let q : Polynomial 𝕜 := (taylor (Polynomial.C ∘ a) p).coeff v
  let R : Polynomial (Polynomial 𝕜) := Q.map (eval (Polynomial.C ∘ a))
  have hzero : ∀ᶠ y in 𝓝[≠] (0 : 𝕜),
      q.eval (r y) + y * (R.eval (Polynomial.C y)).eval (r y) = 0 := by
    filter_upwards [hroot, self_mem_nhdsWithin] with y hy hy0
    rw [hfactor] at hy
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_C] at hy
    have hy0' : y ≠ 0 := by simpa using hy0
    have h := mul_eq_zero.mp hy
    rcases h with h | h
    · exact False.elim (pow_ne_zero _ hy0' h)
    · simpa [q, R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X] using h
  have hRlim : Tendsto (fun y : 𝕜 ↦ (R.eval (Polynomial.C y)).eval (r y))
      (𝓝[≠] 0) (𝓝 ((R.eval (Polynomial.C 0)).eval z)) :=
    Polynomial.tendsto_eval_C_eval R (tendsto_id.mono_left nhdsWithin_le_nhds) hr
  have hy : Tendsto id (𝓝[≠] (0 : 𝕜)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim' : Tendsto (fun y ↦ q.eval (r y) +
      y * (R.eval (Polynomial.C y)).eval (r y)) (𝓝[≠] 0) (𝓝 (q.eval z)) := by
    simpa using ((q.continuousAt.tendsto.comp hr).add (hy.mul hRlim))
  have heq : (fun y ↦ q.eval (r y) + y * (R.eval (Polynomial.C y)).eval (r y))
      =ᶠ[𝓝[≠] (0 : 𝕜)] (fun _ ↦ (0 : 𝕜)) := hzero
  have hlim : Tendsto (fun y ↦ q.eval (r y) +
      y * (R.eval (Polynomial.C y)).eval (r y)) (𝓝[≠] (0 : 𝕜)) (𝓝 (0 : 𝕜)) :=
    tendsto_const_nhds.congr' heq.symm
  have hzero0 : q.eval z = 0 := tendsto_nhds_unique hlim' hlim
  have hcoeff := coeff_taylor_lazardExponent p (Polynomial.C ∘ a)
  simpa only [Polynomial.IsRoot, q, v, hcoeff] using hzero0

end MvPolynomial
