/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedForm.Basic

/-!
# Relatively bounded perturbations of closed forms (KLMN)

Let `q` be a bounded sesquilinear form on a form domain `V` with a continuous injective dense
inclusion `j : V →L[𝕜] H`, satisfying the shifted coercivity bound
`c * ‖u‖ ^ 2 ≤ re (q u u) + ω * ‖j u‖ ^ 2` with `0 < c`, so that `q` is a closed semibounded form
whose form norm is equivalent to the norm of `V`. Let `b` be a second bounded sesquilinear form on
`V` that is *relatively form bounded* with respect to `q` with bound `a < 1`: for some real shift
`α` and some `C`,

`‖b u u‖ ≤ a * re (q_α u u) + C * ‖j u‖ ^ 2`, where `q_α = ContinuousLinearMap.shiftedForm j q α`.

The **KLMN theorem** (Kato, Lions, Lax, Milgram, Nelson) says that the sum `q + b` is again a
closed semibounded form on the same form domain: it satisfies the shifted coercivity bound
`(1 - a) * c * ‖u‖ ^ 2 ≤ re ((q + b) u u) + ((1 - a) * ω + a * α + C) * ‖j u‖ ^ 2`
(`ContinuousLinearMap.mul_norm_sq_le_re_add_self`). Consequently, when `q` and `b` are Hermitian,
the operator represented by `q + b` (`ContinuousLinearMap.closedFormOperator` of `q + b`) is
self-adjoint and bounded below by `-((1 - a) * ω + a * α + C)`, and it is the unique self-adjoint
operator whose graph is described by `q + b`
(`ContinuousLinearMap.existsUnique_selfAdjoint_of_closed_form_add`).

The represented operator is described by its graph through the sum form. It is not identified here
with an algebraic sum of operators: that needs a theorem on the domains of the summands.

## Main results

* `ContinuousLinearMap.mul_norm_sq_le_re_add_self`: shifted coercivity of the sum form.
* `ContinuousLinearMap.isSelfAdjoint_closedFormOperator_add`: the operator of the sum form is
  self-adjoint.
* `ContinuousLinearMap.neg_mul_norm_sq_le_re_inner_closedFormOperator_add`: its lower bound.
* `ContinuousLinearMap.existsUnique_selfAdjoint_of_closed_form_add`: the KLMN theorem.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics II*, Theorem X.17.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Chapter VI, §1.6,
  Theorem 1.33.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace ContinuousLinearMap

section Coercive

variable {𝕜 V H : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Coercivity of a relatively form-bounded perturbation.** If
`c * ‖u‖ ^ 2 ≤ re (q u u) + ω * ‖j u‖ ^ 2` and `b` is form bounded relative to `q` with bound
`a < 1`, that is `‖b u u‖ ≤ a * re (q_α u u) + C * ‖j u‖ ^ 2`, then `q + b` satisfies the shifted
coercivity bound with constant `(1 - a) * c` and shift `(1 - a) * ω + a * α + C`. -/
theorem mul_norm_sq_le_re_add_self (j : V →L[𝕜] H) {q b : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {ω α a C c : ℝ} (ha : a < 1)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + ω * ‖j u‖ ^ 2)
    (hb : ∀ u, ‖b u u‖ ≤ a * RCLike.re (shiftedForm j q α u u) + C * ‖j u‖ ^ 2) (u : V) :
    (1 - a) * c * ‖u‖ ^ 2 ≤
      RCLike.re ((q + b) u u) + ((1 - a) * ω + a * α + C) * ‖j u‖ ^ 2 := by
  have hq := mul_le_mul_of_nonneg_left (hcoercive u) (sub_nonneg.2 ha.le)
  have hbu := hb u
  rw [re_shiftedForm_self] at hbu
  have hre : -‖b u u‖ ≤ RCLike.re (b u u) := (abs_le.1 (RCLike.abs_re_le_norm _)).1
  rw [add_apply, add_apply, map_add]
  nlinarith

end Coercive

section LowerBound

variable {𝕜 V H : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **KLMN, lower bound.** Under the hypotheses of the KLMN theorem, the operator represented by
`q + b` is bounded below by `-((1 - a) * ω + a * α + C)`. -/
theorem neg_mul_norm_sq_le_re_inner_closedFormOperator_add (j : V →L[𝕜] H)
    (hj : Function.Injective j) (hdense : DenseRange j) {q b : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    {ω α a C c : ℝ} (hc : 0 ≤ c) (ha : a < 1)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + ω * ‖j u‖ ^ 2)
    (hb : ∀ u, ‖b u u‖ ≤ a * RCLike.re (shiftedForm j q α u u) + C * ‖j u‖ ^ 2)
    (x : (closedFormOperator j hj hdense (q + b)).domain) :
    -((1 - a) * ω + a * α + C) * ‖(x : H)‖ ^ 2 ≤
      RCLike.re ⟪closedFormOperator j hj hdense (q + b) x, (x : H)⟫_𝕜 :=
  neg_mul_norm_sq_le_re_inner_closedFormOperator j hj hdense (q + b)
    (mul_nonneg (sub_nonneg.2 ha.le) hc) (mul_norm_sq_le_re_add_self j ha hcoercive hb) x

end LowerBound

section Representation

variable {𝕜 V H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Under the hypotheses of the KLMN theorem, the Fréchet--Riesz operator of the sum form shifted by
`(1 - a) * ω + a * α + C` is invertible. -/
theorem isUnit_continuousLinearMapOfBilin_shiftedForm_add (j : V →L[𝕜] H)
    {q b : V →L⋆[𝕜] V →L[𝕜] 𝕜} {ω α a C c : ℝ} (hc : 0 < c) (ha : a < 1)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + ω * ‖j u‖ ^ 2)
    (hb : ∀ u, ‖b u u‖ ≤ a * RCLike.re (shiftedForm j q α u u) + C * ‖j u‖ ^ 2) :
    IsUnit (InnerProductSpace.continuousLinearMapOfBilin
      (shiftedForm j (q + b) ((1 - a) * ω + a * α + C))) :=
  isUnit_continuousLinearMapOfBilin_shiftedForm j (mul_pos (sub_pos.2 ha) hc) le_rfl
    (mul_norm_sq_le_re_add_self j ha hcoercive hb)

variable [CompleteSpace H]

/-- **KLMN, self-adjointness.** For Hermitian `q` and `b` with `b` form bounded relative to the
shifted-coercive form `q` with bound `a < 1`, the operator represented by `q + b` is
self-adjoint. -/
theorem isSelfAdjoint_closedFormOperator_add (j : V →L[𝕜] H) (hj : Function.Injective j)
    (hdense : DenseRange j) {q b : V →L⋆[𝕜] V →L[𝕜] 𝕜}
    (hq : ∀ u v, q u v = star (q v u)) (hb_herm : ∀ u v, b u v = star (b v u))
    {ω α a C c : ℝ} (hc : 0 < c) (ha : a < 1)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + ω * ‖j u‖ ^ 2)
    (hb : ∀ u, ‖b u u‖ ≤ a * RCLike.re (shiftedForm j q α u u) + C * ‖j u‖ ^ 2) :
    IsSelfAdjoint (closedFormOperator j hj hdense (q + b)) :=
  isSelfAdjoint_closedFormOperator j hj hdense (q + b)
    (fun u v => by simp only [add_apply, star_add, ← hq, ← hb_herm])
    (isUnit_continuousLinearMapOfBilin_shiftedForm_add j hc ha hcoercive hb)

end Representation

/-- **The KLMN theorem** (Reed–Simon, Theorem X.17; Kato, Chapter VI, Theorem 1.33). Let `q` be
a bounded Hermitian form on a complete inner-product space `V`, with a continuous injective dense
inclusion `j : V →L[𝕜] H` into a Hilbert space and a shifted coercivity bound
`c * ‖u‖ ^ 2 ≤ re (q u u) + ω * ‖j u‖ ^ 2` (`0 < c`). Let `b` be a bounded Hermitian form on `V`
with `‖b u u‖ ≤ a * re (q_α u u) + C * ‖j u‖ ^ 2` for some `a < 1`. Then `q + b` represents a
unique self-adjoint partial operator on `H`, bounded below by `-((1 - a) * ω + a * α + C)`. -/
theorem existsUnique_selfAdjoint_of_closed_form_add
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
    (j : V →L[𝕜] H) (hj : Function.Injective j) (hdense : DenseRange j)
    (q b : V →L⋆[𝕜] V →L[𝕜] 𝕜)
    (hq : ∀ u v, q u v = star (q v u)) (hb_herm : ∀ u v, b u v = star (b v u))
    (ω α a C c : ℝ) (hc : 0 < c) (ha : a < 1)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ RCLike.re (q u u) + ω * ‖j u‖ ^ 2)
    (hb : ∀ u, ‖b u u‖ ≤ a * RCLike.re (shiftedForm j q α u u) + C * ‖j u‖ ^ 2) :
    ∃! A : H →ₗ.[𝕜] H, IsSelfAdjoint A ∧
      (∀ x : A.domain, -((1 - a) * ω + a * α + C) * ‖(x : H)‖ ^ 2 ≤
        RCLike.re ⟪A x, (x : H)⟫_𝕜) ∧
      ∀ x h : H, (x, h) ∈ A.graph ↔
        ∃ u : V, j u = x ∧ ∀ v : V, q u v + b u v = ⟪h, j v⟫_𝕜 :=
  ⟨closedFormOperator j hj hdense (q + b),
    ⟨isSelfAdjoint_closedFormOperator_add j hj hdense hq hb_herm hc ha hcoercive hb,
      neg_mul_norm_sq_le_re_inner_closedFormOperator_add j hj hdense hc.le ha hcoercive hb,
      fun x h => mem_graph_closedFormOperator_iff j hj hdense (q + b) (p := (x, h))⟩,
    fun _ ⟨_, _, hA⟩ => eq_closedFormOperator_of_mem_graph_iff j hj hdense (q + b) hA⟩

end ContinuousLinearMap
