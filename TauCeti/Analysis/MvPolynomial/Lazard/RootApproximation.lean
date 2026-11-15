/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Lazard.Uniform
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
import TauCeti.Analysis.Polynomial.ContinuityOfRoots.Approximation
import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Approximating Lazard roots by roots of monomial deformations

Every root of the nonzero Lazard evaluation at a base point is approximated by roots
of ordinary fibers along an evaluator's monomial curve. Ordinary specialization at
the center may be nullified. Divide out the common curve power using the polynomial
Taylor expansion, then apply finite-root approximation to the resulting polynomial
family, whose central fiber is the Lazard evaluation. Its degree need not be constant.

This gives root coverage in the passage from Laurent branches of a monomial
deformation to the roots of a Lazard evaluation.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), §5.1–5.2,
Proposition 5.6 and the proof of Theorem 5.1.
-/

public section

open Filter Finsupp Polynomial Topology

namespace TauCeti

/-- Every root of a Lazard evaluation is approached by ordinary roots along any monomial
curve whose evaluator separates the removed base exponent. Nullified ordinary fibers
at the center and degree drops in the divided deformation are allowed. -/
theorem eventually_exists_isRoot_monomialCurve_norm_sub_lt
    {K : Type*} [NormedField K] [IsAlgClosed K] [ProperSpace K] {n : ℕ}
    (p : MvPolynomial (Fin n) K[X]) (hp : p ≠ 0) (a : Fin n → K)
    {V : Set (Fin n →₀ ℕ)} {c : Fin n → ℕ}
    (hv : p.lazardExponent (Polynomial.C ∘ a) ∈ V) (hc : IsLazardEvaluator V c)
    {z : K} (hz : (p.lazardEval (Polynomial.C ∘ a)).IsRoot z)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝[≠] (0 : K), ∃ w : K,
      (MvPolynomial.eval (fun i ↦ Polynomial.C (a i + y ^ c i)) p).IsRoot w ∧
        ‖z - w‖ < ε := by
  classical
  let α : Fin n → K[X] := Polynomial.C ∘ a
  obtain ⟨Q, hQ⟩ := p.exists_aeval_monomialCurve_eq_pow_mul
    (S := {α}) hv hc (fun b hb u hu ↦ by
      obtain rfl := Set.mem_singleton_iff.mp hb
      exact MvPolynomial.coeff_taylor_eq_zero_of_lt_lazardExponent hu)
  let P : Polynomial K[X] :=
    Polynomial.C (p.lazardEval α) + Polynomial.X * Q.map (MvPolynomial.eval α)
  let F : K → K[X] := fun y ↦ (Polynomial.Bivariate.swap P).map (Polynomial.evalRingHom y)
  -- Swap the variables so the divided deformation has a fixed degree bound in the root
  -- variable and coefficients polynomial in the curve parameter.
  have hF (y : K) : F y = P.eval (Polynomial.C y) := by
    simpa only [F, Polynomial.coe_mapAlgHom, Polynomial.coe_aeval_eq_evalRingHom,
      Polynomial.aeval_def, Polynomial.algebraMap_def, Algebra.algebraMap_self,
      Polynomial.mapRingHom_id, Polynomial.eval₂_id]
      using (Polynomial.Bivariate.aeval_eq_map_swap y P).symm
  have hF0 : F 0 = p.lazardEval α := by simp [hF, P]
  have hcoeff (i : ℕ) : ContinuousAt (fun y ↦ (F y).coeff i) 0 := by
    simp only [F, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
    exact Polynomial.continuousAt _
  have happrox := eventually_exists_isRoot_norm_sub_lt (F := F)
    (d := (Polynomial.Bivariate.swap P).natDegree) (fun i _ ↦ hcoeff i)
    (.of_forall fun y ↦ Polynomial.natDegree_map_le)
    (by rw [hF0]; exact MvPolynomial.lazardEval_ne_zero hp α)
    (by rwa [hF0]) hε
  -- Evaluating the uniform expansion reconstructs the ordinary deformation as a scalar
  -- multiple of the divided family, so its roots include the approximating roots.
  have hcurve (y : K) :
      MvPolynomial.eval (fun i ↦ Polynomial.C (a i + y ^ c i)) p =
        Polynomial.C (y ^ weight c (p.lazardExponent α)) * F y := by
    have h := congrArg (Polynomial.eval (Polynomial.C y)) (hQ α (Set.mem_singleton α))
    have heval : Polynomial.eval (Polynomial.C y)
        (MvPolynomial.aeval (MvPolynomial.monomialCurve α c) p) =
        MvPolynomial.eval (fun i ↦ Polynomial.C (a i + y ^ c i)) p := by
      rw [← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply]
      simp [MvPolynomial.monomialCurve_apply, MvPolynomial.aeval_eq_eval, α]
    rw [heval, MvPolynomial.coeff_taylor_lazardExponent] at h
    simpa only [hF, P, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.C_pow] using h
  filter_upwards [happrox.filter_mono nhdsWithin_le_nhds] with y hy
  obtain ⟨w, hw, hzw⟩ := hy
  refine ⟨w, ?_, hzw⟩
  simp only [IsRoot.def, hcurve, Polynomial.eval_mul, hw.eq_zero, mul_zero]

end TauCeti
