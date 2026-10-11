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

For a nonzero polynomial, the first nonzero Taylor coefficient in lexicographic order is
the Lazard evaluation. Along a monomial curve chosen by an evaluator, it is the leading
coefficient in the curve parameter. Consequently, every finite limit of roots of the deformed
polynomial is a root of the Lazard evaluation. This is the algebraic link between
Puiseux branches away from the exceptional hyperplane and roots over its center.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), Section 5.1.
-/

public section

open Filter Finsupp Polynomial Topology

namespace MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- A finite limit of roots of a monomial deformation is a root of the Lazard evaluation
at the center. The weights must separate the removed exponent from every higher Taylor
exponent; no constancy of ordinary specializations is required. -/
theorem isRoot_lazardEval_of_tendsto_deformed_roots
    (p : MvPolynomial (Fin n) (Polynomial 𝕜)) (a : Fin n → 𝕜)
    (c : Fin n → ℕ) (r : 𝕜 → 𝕜)
    (hc : TauCeti.IsLazardEvaluator {p.lazardExponent (Polynomial.C ∘ a)} c)
    (hr : ContinuousAt r 0)
    (hroot : ∀ᶠ y in 𝓝[≠] (0 : 𝕜),
      ((aeval (monomialCurve (Polynomial.C ∘ a) c) p).eval (Polynomial.C y)).eval (r y) = 0) :
    (p.lazardEval (Polynomial.C ∘ a)).eval (r 0) = 0 := by
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
  have hRcont : ContinuousAt (fun y : 𝕜 ↦ (R.eval (Polynomial.C y)).eval (r y)) 0 := by
    have heq (y : 𝕜) : (R.eval (Polynomial.C y)).eval (r y) =
        ∑ j ∈ R.support, (R.coeff j).eval (r y) * y ^ j := by
      rw [Polynomial.eval_eq_sum (p := R)]
      simp only [Polynomial.sum_def, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C]
    simp only [heq]
    fun_prop (disch := assumption)
  have hcont : ContinuousAt (fun y ↦ q.eval (r y) +
      y * (R.eval (Polynomial.C y)).eval (r y)) 0 :=
    (q.continuousAt.comp hr).add (continuousAt_id.mul hRcont)
  have heq : (fun y ↦ q.eval (r y) + y * (R.eval (Polynomial.C y)).eval (r y))
      =ᶠ[𝓝[≠] (0 : 𝕜)] (fun _ ↦ (0 : 𝕜)) := hzero
  have hlim : Tendsto (fun y ↦ q.eval (r y) +
      y * (R.eval (Polynomial.C y)).eval (r y)) (𝓝[≠] (0 : 𝕜)) (𝓝 (0 : 𝕜)) :=
    tendsto_const_nhds.congr' heq.symm
  have hzero0 : q.eval (r 0) + 0 * (R.eval (Polynomial.C 0)).eval (r 0) = 0 :=
    tendsto_nhds_unique (hcont.mono_left nhdsWithin_le_nhds) hlim
  have hcoeff := coeff_taylor_lazardExponent p (Polynomial.C ∘ a)
  simpa only [zero_mul, add_zero, q, v, hcoeff] using hzero0

end MvPolynomial
