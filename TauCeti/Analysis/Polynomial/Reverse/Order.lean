/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.CurveOrder
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.Polynomial.IntegralNormalization
import TauCeti.RingTheory.Polynomial.Resultant.RootCoordinates

/-!
# Ambient order in reciprocal polynomial coordinates

For a polynomial family `p` in one distinguished variable, reflection at a fixed degree
bound represents `z ^ N * p(x, z⁻¹)`. Away from `z = 0`, reciprocal coordinates preserve
ambient polynomial order. This compares the order in all variables, rather than only the
multiplicity of a root in a fiber. It allows section-order conclusions in reciprocal
coordinates to be transported back to the original polynomial family.

The bound is chosen before specialization: no preservation of the fiber degree is required.
Reversal is the specialization to the formal degree of the family.

Integral normalization also preserves ambient order, once the distinguished coordinate is
rescaled by the leading coefficient at base points where that coefficient does not vanish.
Translating to a center `τ`, reversing and normalizing turns a family whose leading
coefficient may vanish into a monic one; its leading coefficient becomes the value `p(τ)`.
Ambient orders of the monic family at the image of a point `(t, x)` with `t ≠ τ` and
`p(τ)(x) ≠ 0` are the ambient orders of `p` at `(t, x)`.

## Main results

* `Polynomial.orderAt_reflect`, `Polynomial.orderAt_reverse`: reciprocal coordinates preserve
  ambient order.
* `Polynomial.orderAt_integralNormalization`: integral normalization preserves ambient order
  after rescaling the distinguished coordinate by the leading coefficient.
* `Polynomial.orderAt_integralNormalization_reverse_comp_X_add_C`: normalized reciprocal
  coordinates centered at `τ` preserve ambient order.

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

/-- Rescaling the distinguished coordinate by an analytic factor, together with multiplication
by an analytic function, cannot lower ambient order. The identity is required only for base
points near `a`. -/
private theorem orderAt_le_of_eval_cons_mul_mul_eq
    (f g : MvPolynomial (Fin (n + 1)) 𝕜) {l μ : (Fin n → 𝕜) → 𝕜} {a : Fin n → 𝕜} (z : 𝕜)
    (hl : AnalyticAt 𝕜 l a) (hμ : AnalyticAt 𝕜 μ a)
    (h : ∀ᶠ y in 𝓝 a, ∀ t,
      MvPolynomial.eval (Fin.cons (l y * t) y) f * μ y = MvPolynomial.eval (Fin.cons t y) g) :
    f.orderAt (Fin.cons (l a * z) a) ≤ g.orderAt (Fin.cons z a) := by
  let T : (Fin (n + 1) → 𝕜) →L[𝕜] Fin n → 𝕜 :=
    ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj i.succ
  have hT (x : Fin (n + 1) → 𝕜) : T x = Fin.tail x := rfl
  have hTa : T (Fin.cons z a) = a := by rw [hT, Fin.tail_cons]
  have hlT : AnalyticAt 𝕜 (fun x ↦ l (T x)) (Fin.cons z a) :=
    hl.comp_of_eq (T.analyticAt _) hTa
  have hμT : AnalyticAt 𝕜 (fun x ↦ μ (T x)) (Fin.cons z a) :=
    hμ.comp_of_eq (T.analyticAt _) hTa
  have hcoord (i : Fin (n + 1)) :
      AnalyticAt 𝕜 (fun x : Fin (n + 1) → 𝕜 ↦ x i) (Fin.cons z a) :=
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin (n + 1) ↦ 𝕜) i).analyticAt _
  have hg (i : Fin (n + 1)) : AnalyticAt 𝕜
      (fun x ↦ (Fin.cons (l (T x) * x 0) (T x) : Fin (n + 1) → 𝕜) i) (Fin.cons z a) := by
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      exact hlT.fun_mul (hcoord 0)
    | succ i => simpa only [Fin.cons_succ, hT, Fin.tail] using hcoord i.succ
  have heq : ∀ᶠ x in 𝓝 (Fin.cons z a : Fin (n + 1) → 𝕜),
      MvPolynomial.eval (Fin.cons (l (T x) * x 0) (T x)) f * μ (T x) = MvPolynomial.eval x g := by
    filter_upwards [T.continuous.continuousAt.preimage_mem_nhds (hTa ▸ h)] with x hx
    rw [hx (x 0), hT, Fin.cons_self_tail]
  simpa only [hTa, Fin.cons_zero] using
    orderAt_le_of_analyticAt_mul_eq f g (Fin.cons z a) hg hμT heq

/-- Integral normalization preserves ambient order when its distinguished coordinate is
rescaled by the leading coefficient: at a base point `a` where the leading coefficient of `p`
does not vanish, the order of `p.integralNormalization` at `(p.leadingCoeff(a) * z, a)` is the
order of `p` at `(z, a)`. -/
theorem orderAt_integralNormalization (p : Polynomial (MvPolynomial (Fin n) 𝕜))
    {a : Fin n → 𝕜} (ha : MvPolynomial.eval a p.leadingCoeff ≠ 0) (z : 𝕜) :
    ((finSuccEquiv 𝕜 n).symm p.integralNormalization).orderAt
        (Fin.cons (MvPolynomial.eval a p.leadingCoeff * z) a) =
      ((finSuccEquiv 𝕜 n).symm p).orderAt (Fin.cons z a) := by
  have hev (q : Polynomial (MvPolynomial (Fin n) 𝕜)) (t : 𝕜) (y : Fin n → 𝕜) :
      MvPolynomial.eval (Fin.cons t y) ((finSuccEquiv 𝕜 n).symm q) =
        q.eval₂ (MvPolynomial.eval y) t := by
    rw [MvPolynomial.eval_eq_eval_mv_eval', AlgEquiv.apply_symm_apply, eval_map]
  rcases Nat.eq_zero_or_pos p.natDegree with hp | hp
  · -- A constant family normalizes to `1`; both orders vanish.
    rw [eq_C_of_natDegree_eq_zero hp] at ha ⊢
    rw [leadingCoeff_C] at ha
    rw [integralNormalization_C fun h ↦ ha (by rw [h, map_zero]), map_one, orderAt_one,
      eq_comm, orderAt_eq_zero_iff, hev, eval₂_C]
    exact ha
  let l : (Fin n → 𝕜) → 𝕜 := fun y ↦ MvPolynomial.eval y p.leadingCoeff
  have hl : AnalyticAt 𝕜 l a := by
    have h := AnalyticAt.aeval_mvPolynomial (fun i ↦ (ContinuousLinearMap.proj
      (R := 𝕜) (φ := fun _ : Fin n ↦ 𝕜) i).analyticAt a) p.leadingCoeff
    simp only [ContinuousLinearMap.proj_apply, MvPolynomial.aeval_eq_eval] at h
    exact h
  have hl0 : l a ≠ 0 := ha
  have hla : ∀ᶠ y in 𝓝 a, l y ≠ 0 := hl.continuousAt.eventually_ne ha
  -- Evaluating the normalization at rescaled coordinates multiplies by a power of `l`.
  have hnorm (y : Fin n → 𝕜) (t : 𝕜) :
      MvPolynomial.eval (Fin.cons (l y * t) y) ((finSuccEquiv 𝕜 n).symm p.integralNormalization) =
        l y ^ (p.natDegree - 1) * MvPolynomial.eval (Fin.cons t y) ((finSuccEquiv 𝕜 n).symm p) := by
    rw [hev, hev]
    exact integralNormalization_eval₂_leadingCoeff_mul hp _ t
  apply le_antisymm
  · refine orderAt_le_of_eval_cons_mul_mul_eq (μ := fun y ↦ (l y ^ (p.natDegree - 1))⁻¹) _ _ z
      hl ((hl.fun_pow _).fun_inv (pow_ne_zero _ hl0)) ?_
    filter_upwards [hla] with y hy t
    rw [hnorm, mul_comm, inv_mul_cancel_left₀ (pow_ne_zero _ hy)]
  · have h := orderAt_le_of_eval_cons_mul_mul_eq (l := fun y ↦ (l y)⁻¹)
      (μ := fun y ↦ l y ^ (p.natDegree - 1)) ((finSuccEquiv 𝕜 n).symm p)
      ((finSuccEquiv 𝕜 n).symm p.integralNormalization) (l a * z) (hl.fun_inv hl0)
      (hl.fun_pow _) <| by
        filter_upwards [hla] with y hy t
        rw [mul_comm, ← hnorm, mul_inv_cancel_left₀ hy]
    rw [inv_mul_cancel_left₀ hl0] at h
    exact h

/-- Normalized reciprocal coordinates centered at `τ` preserve ambient order. If the value
`c = p(τ)` of the family does not vanish at the base point `a`, then the normalized reversal
`(p.comp (X + C τ)).reverse.integralNormalization` has order at `(c(a) / (t - τ), a)` equal to
the order of `p` at `(t, a)`, for every `t ≠ τ`. -/
theorem orderAt_integralNormalization_reverse_comp_X_add_C
    (p : Polynomial (MvPolynomial (Fin n) 𝕜)) {τ : 𝕜} {a : Fin n → 𝕜}
    (ha : MvPolynomial.eval a (p.eval (MvPolynomial.C τ)) ≠ 0) {t : 𝕜} (ht : t ≠ τ) :
    ((finSuccEquiv 𝕜 n).symm
        (p.comp (X + C (MvPolynomial.C τ))).reverse.integralNormalization).orderAt
        (Fin.cons (MvPolynomial.eval a (p.eval (MvPolynomial.C τ)) * (t - τ)⁻¹) a) =
      ((finSuccEquiv 𝕜 n).symm p).orderAt (Fin.cons t a) := by
  have hlead := p.leadingCoeff_reverse_comp_X_add_C fun h ↦ ha (by rw [h, map_zero])
  rw [← hlead] at ha ⊢
  rw [orderAt_integralNormalization _ ha, orderAt_reverse _ _ (sub_ne_zero.2 ht),
    orderAt_comp_X_add_C, sub_add_cancel]

end Polynomial
