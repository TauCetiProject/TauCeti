/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.CurveOrder
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Ambient order in reciprocal polynomial coordinates

For a polynomial family `p` in one distinguished variable, reflection at a fixed degree
bound represents `z ^ N * p(x, z⁻¹)`. Away from `z = 0`, reciprocal coordinates preserve
ambient polynomial order. This compares the order in all variables, rather than only the
multiplicity of a root in a fiber. It allows section-order conclusions in reciprocal
coordinates to be transported back to the original polynomial family.

The bound is chosen before specialization: no preservation of the fiber degree is required.
Reversal is the specialization to the formal degree of the family.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  in *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998),
  Sections 2–3 (ambient order and delineability).
-/

public section

open Filter MvPolynomial Topology

namespace Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n N : ℕ}

private theorem orderAt_reflect_le (p : Polynomial (MvPolynomial (Fin n) 𝕜))
    (hN : p.natDegree ≤ N) (a : Fin n → 𝕜) {z : 𝕜} (hz : z ≠ 0) :
    ((finSuccEquiv 𝕜 n).symm (p.reflect N)).orderAt (Fin.cons z⁻¹ a) ≤
      ((finSuccEquiv 𝕜 n).symm p).orderAt (Fin.cons z a) := by
  let g : (Fin (n + 1) → 𝕜) → Fin (n + 1) → 𝕜 :=
    fun x ↦ Fin.cons (x 0)⁻¹ (Fin.tail x)
  have hcoord (i : Fin (n + 1)) :
      AnalyticAt 𝕜 (fun x : Fin (n + 1) → 𝕜 ↦ x i) (Fin.cons z a) :=
    by
      convert (ContinuousLinearMap.proj (R := 𝕜)
        (φ := fun _ : Fin (n + 1) ↦ 𝕜) i).analyticAt (Fin.cons z a) using 1
      ext x
      exact (ContinuousLinearMap.proj_apply i x).symm
  have hg (i : Fin (n + 1)) : AnalyticAt 𝕜 (fun x ↦ g x i) (Fin.cons z a) := by
    cases i using Fin.cases with
    | zero => simpa only [g, Fin.cons_zero, Pi.inv_def] using (hcoord 0).inv hz
    | succ i => simpa only [g, Fin.cons_succ, Fin.tail] using hcoord i.succ
  have hu : AnalyticAt 𝕜 (fun x : Fin (n + 1) → 𝕜 ↦ x 0 ^ N) (Fin.cons z a) :=
    (hcoord 0).pow N
  have heq : ∀ᶠ x : Fin (n + 1) → 𝕜 in 𝓝 (Fin.cons z a),
      MvPolynomial.eval (g x) ((finSuccEquiv 𝕜 n).symm (p.reflect N)) * x 0 ^ N =
        MvPolynomial.eval x ((finSuccEquiv 𝕜 n).symm p) := by
    filter_upwards [(continuous_apply 0).continuousAt.eventually_ne hz] with x hx
    let : Invertible (x 0) := invertibleOfNonzero hx
    rw [eval_eq_eval_mv_eval', AlgEquiv.apply_symm_apply]
    have hpoint : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
    conv_rhs => rw [hpoint, eval_eq_eval_mv_eval', AlgEquiv.apply_symm_apply]
    simpa only [eval_map, invOf_eq_inv] using
      eval₂_reflect_mul_pow (MvPolynomial.eval (Fin.tail x)) (x 0) N p hN
  simpa only [g, Fin.cons_zero, Fin.tail_cons] using
    MvPolynomial.orderAt_le_of_analyticAt_mul_eq
      ((finSuccEquiv 𝕜 n).symm (p.reflect N)) ((finSuccEquiv 𝕜 n).symm p)
      (Fin.cons z a) hg hu heq

/-- Reflection at a fixed bound preserves the ambient order at reciprocal nonzero
coordinates. The bound concerns the formal polynomial, not its specialized fibers. -/
@[simp]
theorem orderAt_reflect (p : Polynomial (MvPolynomial (Fin n) 𝕜))
    (hN : p.natDegree ≤ N) (a : Fin n → 𝕜) {z : 𝕜} (hz : z ≠ 0) :
    ((finSuccEquiv 𝕜 n).symm (p.reflect N)).orderAt (Fin.cons z⁻¹ a) =
      ((finSuccEquiv 𝕜 n).symm p).orderAt (Fin.cons z a) := by
  apply le_antisymm (orderAt_reflect_le p hN a hz)
  have hbound : (p.reflect N).natDegree ≤ N :=
    p.natDegree_reflect_le.trans (max_le le_rfl hN)
  simpa only [reflect_reflect, inv_inv] using
    orderAt_reflect_le (p.reflect N) hbound a (inv_ne_zero hz)

/-- Reversing a polynomial family preserves ambient order under inversion of its
nonzero distinguished coordinate, even when the fiber degree drops. -/
@[simp]
theorem orderAt_reverse (p : Polynomial (MvPolynomial (Fin n) 𝕜))
    (a : Fin n → 𝕜) {z : 𝕜} (hz : z ≠ 0) :
    ((finSuccEquiv 𝕜 n).symm p.reverse).orderAt (Fin.cons z⁻¹ a) =
      ((finSuccEquiv 𝕜 n).symm p).orderAt (Fin.cons z a) :=
  by simpa only [reverse] using p.orderAt_reflect le_rfl a hz

end Polynomial
