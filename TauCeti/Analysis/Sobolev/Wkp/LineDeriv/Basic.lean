/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Sobolev.W1p.Symmetry
import TauCeti.Analysis.Sobolev.WeakDeriv.Coordinates
import TauCeti.Analysis.Sobolev.WeakDeriv.NormalTangential
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import TauCeti.Analysis.InnerProductSpace.OrthogonalSpanSingleton
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Directional derivatives of higher-order Sobolev functions

A function `u ∈ Lᵖ(Ω)` lies in `W^{k+1,p}(Ω)` exactly when, in every direction `v`, it has a weak
derivative `∂_v u` lying in `W^{k,p}(Ω)`; it suffices to check the directions of one orthonormal
basis. This is the description of the Sobolev scale by first derivatives,
`W^{k+1,p}(Ω) = {u ∈ Lᵖ(Ω) : ∂ᵢu ∈ W^{k,p}(Ω) for every i}`, and it is what lets a statement about
`W^{k,p}` be proved by induction on `k` one derivative at a time.

`TauCeti.Wkp` records the derivatives of `u` from the bottom up: the gradient first, and then the
weak Fréchet derivative of the previous field. The fields of `∂_v u` are therefore those of `u`
with `v` substituted in the innermost slot, the one belonging to the gradient. At the first level
this substitution is `A ↦ A† v`, since the gradient is identified with a vector through the inner
product. Conversely, the fields of `u` are reassembled from those of the `∂ᵢu` by inserting
`⟪eᵢ, ·⟫` in the innermost slot. Neither direction uses the symmetry of weak second derivatives,
which is proved separately: since weak derivatives commute, the weak Hessian is symmetric, and weak
directional differentiation commutes with `Wkp.iteratedGradient` at every order, identifying the
top derivative of `Wkp.lineDerivL v (j + 1) u` with evaluation of the outermost slot of
`Wkp.iteratedGradient (j + 1) u` at `v`.

No boundedness or boundary regularity of `Ω` is assumed.

## Main declarations

* `TauCeti.Wkp.exists_hasWeakLineDerivOn_value`: every directional weak derivative of an element
  of `W^{k+1,p}(Ω)` lies in `W^{k,p}(Ω)`.
* `TauCeti.Wkp.exists_hasWeakLineDerivOn_value_and_inner_gradient_ae_eq`: the first derivatives
  of an element of `W^{2,p}(Ω)` lie in `W^{1,p}(Ω)`, with gradients given by the weak Hessian.
* `TauCeti.Wkp.lineDerivL`: the directional weak derivative as a bounded operator
  `W^{k+1,p}(Ω) → W^{k,p}(Ω)`, characterised by `TauCeti.Wkp.hasWeakLineDerivOn_lineDerivL`, and
  bundled bilinearly in the direction and function as `TauCeti.Wkp.lineDerivBilinL`.
* `TauCeti.Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn`: if the weak derivatives of
  `u ∈ Lᵖ(Ω)` along an orthonormal basis lie in `W^{k,p}(Ω)`, then `u ∈ W^{k+1,p}(Ω)`.
* `TauCeti.Wkp.exists_value_eq_iff_forall_exists_hasWeakLineDerivOn`: the two combined.
* `TauCeti.Wkp.exists_value_ae_eq_of_forall_hasWeakLineDerivOn`: the reverse direction for a
  function representative, with weak derivatives in every direction.
* `TauCeti.W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn`: the second-order case in the
  form a difference-quotient argument supplies, with `Lᵖ` weak derivatives of the components
  `⟪∇u, eⱼ⟫` of the weak gradient.
* `TauCeti.W1p.exists_lowerOrder_eq_of_gradient_eq_of_hasWeakLineDerivOn`: the same on an open
  subdomain `V ≤ Ω`, for any `u ∈ W^{1,p}(V)` whose weak gradient agrees on `V` with that of a
  function on `Ω` whose gradient components are weakly differentiable.
* `TauCeti.Wkp.norm_iteratedGradient_one_le_sum`: the `Lᵖ` norm of the weak Hessian is at most
  the sum of the `Lᵖ` norms of the derivatives `∂ᵢ ⟪∇u, eⱼ⟫`.
* `TauCeti.Wkp.inner_iteratedGradient_one_apply_ae_eq`: the weak Hessian is symmetric.
* `TauCeti.Wkp.adjoint_iteratedGradient_one_ae_eq`: the weak Hessian is self-adjoint almost
  everywhere.
* `TauCeti.Wkp.lineDerivL_comm`: bundled directional derivatives commute at every Sobolev order.
* `TauCeti.Wkp.hasWeakLineDerivOn_inner_iteratedGradient_one_comm`: weak derivatives of the
  entries of the weak Hessian commute with its slots.
* `TauCeti.Wkp.exists_hasWeakLineDerivOn_inner_iteratedGradient_one_of_normal_of_tangential`: the
  third weak derivatives of an element of `W^{2,p}(Ω)` lie in `Lᵖ(Ω)` once those with a direction
  orthogonal to `ν` and the purely normal one `∂_ν ∂_ν ∂_ν u` do.
* `TauCeti.Wkp.hasWeakLineDerivOn_iteratedGradient`: weak directional differentiation commutes
  with `Wkp.iteratedGradient`.
* `TauCeti.Wkp.toOrderL_lineDerivL`: commutation of `lineDerivL` with order truncation
  `Wkp.toOrderL`.
* `TauCeti.Wkp.iteratedGradient_lineDerivL` and `TauCeti.Wkp.iteratedGradient_lineDerivL_ae`:
  the top weak derivative of `Wkp.lineDerivL v (j + 1) u` evaluates the outermost slot of
  `Wkp.iteratedGradient (j + 1) u` at `v`.
* `TauCeti.Wkp.iteratedGradient_lineDerivL_eq_zero_of_eq_zero`: vanishing of the top weak
  derivative is inherited by every directional derivative `Wkp.lineDerivL v (j + 1) u`.
* `TauCeti.Wkp.norm_lineDerivL_zero_apply_le`, `TauCeti.Wkp.norm_iteratedGradient_lineDerivL_le`,
  `TauCeti.Wkp.norm_lineDerivL_le_of_exponent_two`, `TauCeti.Wkp.norm_lineDerivL_le`, and
  `TauCeti.Wkp.norm_lineDerivBilinL_le`: sharp componentwise (`1`) and Sobolev graph-norm (`1` at
  `k = 0` or `p = 2`, `√2` in general) bounds for `lineDerivL` and `lineDerivBilinL`.
* `TauCeti.Wkp.value_lineDerivL_lineDerivL_ae_eq` and
  `TauCeti.Wkp.ae_inner_gradient_firstOrder_lineDerivL_eq`: every second derivative of `U` from
  the purely normal one `∂_e ∂_e U` and the derivatives of the tangential derivatives of `U`.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Substituting and inserting a direction in the innermost slot -/

/-- Substitute `v` in the innermost slot of an iterated gradient. At order one this is
`A ↦ A† v`, the vector `w` with `⟪w, h⟫ = ⟪v, A h⟫`; at higher orders it acts on the value of
the outer slots. -/
private def contractL (v : E) : (j : ℕ) → IteratedGradient E (j + 1) →L[ℝ] IteratedGradient E j
  | 0 => LinearMap.toContinuousLinearMap
      { toFun := fun A : E →L[ℝ] E => ContinuousLinearMap.adjoint A v
        map_add' := fun A B => by simp
        map_smul' := fun c A => by simp }
  | j + 1 => ContinuousLinearMap.compL ℝ E _ _ (contractL v j)

/-- Insert the functional `⟪w, ·⟫` with value `e` in the innermost slot of an iterated gradient:
at order zero `w ↦ (h ↦ ⟪w, h⟫ e)`, and at higher orders the same on the value of the outer
slots. -/
private def insertL (e : E) : (j : ℕ) → IteratedGradient E j →L[ℝ] IteratedGradient E (j + 1)
  | 0 => LinearMap.toContinuousLinearMap
      { toFun := fun w : E => (innerSL ℝ w).smulRight e
        map_add' := fun w w' => by ext; simp [add_smul]
        map_smul' := fun c w => by ext; simp [smul_smul] }
  | j + 1 => ContinuousLinearMap.compL ℝ E _ _ (insertL e j)

private theorem inner_contractL_zero (v : E) (A : E →L[ℝ] E) (h : E) :
    ⟪contractL v 0 A, h⟫_ℝ = ⟪v, A h⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_left A h v

private theorem insertL_zero_apply (e w h : E) : insertL e 0 w h = ⟪w, h⟫_ℝ • e :=
  (rfl)

private theorem contractL_succ_apply (v : E) (j : ℕ) (A : IteratedGradient E (j + 2)) :
    contractL v (j + 1) A = (contractL v j).comp A :=
  (rfl)

private theorem insertL_succ_apply (e : E) (j : ℕ) (A : IteratedGradient E (j + 1)) :
    insertL e (j + 1) A = (insertL e j).comp A :=
  (rfl)

variable [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### From `W^{k+1,p}` to the directional derivatives -/

/-- The first-order case of `TauCeti.Wkp.exists_wkp_lineDeriv`: a directional derivative of an
element of `W^{2,p}(Ω)` lies in `W^{1,p}(Ω)`, with gradient obtained by substituting the
direction in the innermost slot of the Hessian field. -/
private theorem Wkp.exists_wkp_lineDeriv_zero (v : E) (w : Wkp mu Omega p 2) :
    ∃ d : Wkp mu Omega p 1, HasWeakLineDerivOn mu Omega (Wkp.value 2 w) (Wkp.value 1 d) v ∧
      Wkp.iteratedGradient 0 d = (contractL v 0).compLp (Wkp.iteratedGradient 1 w) := by
  set w₁ := Wkp.lowerOrder 1 w
  have hH := Wkp.hasWeakFDerivOn_iteratedGradient 0 w
  -- the candidate value `⟪v, ∇u⟫` and its weak gradient `(D²u)† v`
  have hd : HasWeakFDerivOn mu Omega ((innerSL ℝ v).compLp (Wkp.iteratedGradient 0 w₁))
      (fun x => innerSL ℝ ((contractL v 0).compLp (Wkp.iteratedGradient 1 w) x)) := by
    refine ((hH.clm_comp (innerSL ℝ v)).congr_ae ?_).congr_ae_deriv ?_
    · filter_upwards [(innerSL ℝ v).coeFn_compLp (Wkp.iteratedGradient 0 w₁)] with x hx
      rw [hx]
    · filter_upwards [(contractL v 0).coeFn_compLp (Wkp.iteratedGradient 1 w)] with x hx
      ext h
      rw [hx, innerSL_apply_apply, inner_contractL_zero, ContinuousLinearMap.comp_apply,
        innerSL_apply_apply]
  refine ⟨W1p.mk _ _ hd, ?_, (Wkp.iteratedGradient_zero _).trans (W1p.gradient_mk _ _ hd)⟩
  rw [Wkp.value_one (W1p.mk _ _ hd), W1p.value_mk, Wkp.value_succ]
  have hu := (Wkp.hasWeakFDerivOn_value w₁).hasWeakLineDerivOn v
  refine hu.congr_ae_deriv ?_
  filter_upwards [(innerSL ℝ v).coeFn_compLp (Wkp.iteratedGradient 0 w₁)] with x hx
  rw [hx, innerSL_apply_apply, innerSL_apply_apply, real_inner_comm]

/-- A directional derivative of an element of `W^{k+2,p}(Ω)` lies in `W^{k+1,p}(Ω)`, and its
highest derivative is obtained by substituting the direction in the innermost slot of the
highest derivative of the original function. -/
private theorem Wkp.exists_wkp_lineDeriv (v : E) :
    ∀ (k : ℕ) (w : Wkp mu Omega p (k + 2)), ∃ d : Wkp mu Omega p (k + 1),
      HasWeakLineDerivOn mu Omega (Wkp.value (k + 2) w) (Wkp.value (k + 1) d) v ∧
        Wkp.iteratedGradient k d = (contractL v k).compLp (Wkp.iteratedGradient (k + 1) w)
  | 0, w => Wkp.exists_wkp_lineDeriv_zero v w
  | k + 1, w => by
      obtain ⟨d, hd, hdk⟩ := Wkp.exists_wkp_lineDeriv v k (Wkp.lowerOrder (k + 2) w)
      have hD : HasWeakFDerivOn mu Omega (Wkp.iteratedGradient k d)
          ((contractL v (k + 1)).compLp (Wkp.iteratedGradient (k + 2) w)) := by
        rw [hdk]
        refine (((Wkp.hasWeakFDerivOn_iteratedGradient (k + 1) w).clm_comp
          (contractL v k)).congr_ae ?_).congr_ae_deriv ?_
        · exact Filter.EventuallyEq.symm ((contractL v k).coeFn_compLp _)
        · filter_upwards [(contractL v (k + 1)).coeFn_compLp (Wkp.iteratedGradient (k + 2) w)]
            with x hx
          rw [hx, contractL_succ_apply]
      refine ⟨Wkp.mk k d _ hD, ?_, Wkp.iteratedGradient_mk k d _ hD⟩
      rw [Wkp.value_mk, Wkp.value_succ (k + 2) w]
      exact hd

/-- The first-order case of `TauCeti.Wkp.exists_hasWeakLineDerivOn_value`: the derivative of an
element of `W^{1,p}(Ω)` in the direction `v` is the component `⟪v, ∇u⟫` of its weak gradient. -/
theorem Wkp.hasWeakLineDerivOn_value_innerSL_compLp (v : E) (w : Wkp mu Omega p 1) :
    HasWeakLineDerivOn mu Omega (Wkp.value 1 w)
      (Wkp.value 0 ((innerSL ℝ v).compLp (Wkp.iteratedGradient 0 w))) v := by
  rw [Wkp.value_zero]
  refine ((Wkp.hasWeakFDerivOn_value w).hasWeakLineDerivOn v).congr_ae_deriv ?_
  filter_upwards [(innerSL ℝ v).coeFn_compLp (Wkp.iteratedGradient 0 w)] with x hx
  rw [hx, innerSL_apply_apply, innerSL_apply_apply, real_inner_comm]

/-- **Directional derivatives of Sobolev functions are Sobolev.** In every direction `v`, an
element of `W^{k+1,p}(Ω)` has a weak derivative which is the value of an element of
`W^{k,p}(Ω)`. -/
theorem Wkp.exists_hasWeakLineDerivOn_value :
    ∀ (k : ℕ) (w : Wkp mu Omega p (k + 1)) (v : E), ∃ d : Wkp mu Omega p k,
      HasWeakLineDerivOn mu Omega (Wkp.value (k + 1) w) (Wkp.value k d) v
  | 0, w, v => ⟨_, Wkp.hasWeakLineDerivOn_value_innerSL_compLp v w⟩
  | k + 1, w, v => (Wkp.exists_wkp_lineDeriv v k w).imp fun _ h => h.1

/-- **First derivatives of a `W^{2,p}` function.** In every direction `v`, an element `u` of
`W^{2,p}(Ω)` has a weak derivative `∂ᵥu` which is the value of an element of `W^{1,p}(Ω)`, whose
weak derivative in a direction `w` is the entry `⟪D²u w, v⟫ = ∂_w ∂ᵥu` of the weak Hessian. -/
theorem Wkp.exists_hasWeakLineDerivOn_value_and_inner_gradient_ae_eq (u : Wkp mu Omega p 2)
    (v : E) :
    ∃ d : W1p mu Omega p, HasWeakLineDerivOn mu Omega (Wkp.value 2 u) (W1p.value d) v ∧
      ∀ w, (fun x => ⟪W1p.gradient d x, w⟫_ℝ) =ᵐ[mu.restrict Omega]
        fun x => ⟪Wkp.iteratedGradient 1 u x w, v⟫_ℝ := by
  obtain ⟨d, hd, hdg⟩ := Wkp.exists_wkp_lineDeriv_zero v u
  refine ⟨d, by simpa only [Wkp.value_one] using hd, fun w => ?_⟩
  rw [Wkp.iteratedGradient_zero] at hdg
  filter_upwards [(contractL v 0).coeFn_compLp (Wkp.iteratedGradient 1 u)] with x hx
  rw [hdg, hx, inner_contractL_zero, real_inner_comm]

/-! ### The directional derivative as a bounded operator -/

/-- An element of `W^{k,p}(Ω)` is determined by being a weak derivative of a given function in a
given direction. -/
theorem Wkp.eq_of_hasWeakLineDerivOn {k : ℕ} {u : E → ℝ} {v : E} {d d' : Wkp mu Omega p k}
    (h : HasWeakLineDerivOn mu Omega u (Wkp.value k d) v)
    (h' : HasWeakLineDerivOn mu Omega u (Wkp.value k d') v) : d = d' :=
  Wkp.ext k (Lp.ext (h.ae_eq h'))

/-- The directional derivative `W^{k+1,p}(Ω) → W^{k,p}(Ω)` is bounded: its graph norm is
controlled by the graph norm of the function, one order higher. -/
private theorem Wkp.exists_norm_le_of_hasWeakLineDerivOn (v : E) :
    ∀ k : ℕ, ∃ C : ℝ≥0, ∀ (w : Wkp mu Omega p (k + 1)) (d : Wkp mu Omega p k),
      HasWeakLineDerivOn mu Omega (Wkp.value (k + 1) w) (Wkp.value k d) v → ‖d‖ ≤ C * ‖w‖
  | 0 => by
    refine ⟨‖innerSL ℝ v‖₊, fun w d h => ?_⟩
    rw [Wkp.eq_of_hasWeakLineDerivOn h (Wkp.hasWeakLineDerivOn_value_innerSL_compLp v w),
      coe_nnNorm]
    exact ((innerSL ℝ v).norm_compLp_le _).trans
      (mul_le_mul_of_nonneg_left (Wkp.norm_iteratedGradient_le 0 w) (norm_nonneg _))
  | k + 1 => by
    obtain ⟨C, hC⟩ := Wkp.exists_norm_le_of_hasWeakLineDerivOn v k
    refine ⟨C + ‖contractL v k‖₊, fun w d h => ?_⟩
    obtain ⟨d', hd', hdk⟩ := Wkp.exists_wkp_lineDeriv v k w
    obtain rfl := Wkp.eq_of_hasWeakLineDerivOn h hd'
    rw [Wkp.value_succ (k + 1) w, Wkp.value_succ k d] at h
    have hlow := (hC _ _ h).trans
      (mul_le_mul_of_nonneg_left (Wkp.norm_lowerOrder_le (k + 1) w) C.coe_nonneg)
    have htop : ‖Wkp.iteratedGradient k d‖ ≤ ‖contractL v k‖ * ‖w‖ := by
      rw [hdk]
      exact ((contractL v k).norm_compLp_le _).trans
        (mul_le_mul_of_nonneg_left (Wkp.norm_iteratedGradient_le (k + 1) w) (norm_nonneg _))
    calc ‖d‖ ≤ ‖Wkp.lowerOrder k d‖ + ‖Wkp.iteratedGradient k d‖ :=
          Wkp.norm_le_norm_lowerOrder_add_norm_iteratedGradient k d
      _ ≤ C * ‖w‖ + ‖contractL v k‖ * ‖w‖ := add_le_add hlow htop
      _ = ↑(C + ‖contractL v k‖₊) * ‖w‖ := by push_cast; ring

/-- **The directional derivative as a bounded operator.** The weak derivative in the direction
`v`, as a continuous linear map `W^{k+1,p}(Ω) → W^{k,p}(Ω)`; it is characterised by
`TauCeti.Wkp.hasWeakLineDerivOn_lineDerivL`. -/
def Wkp.lineDerivL (v : E) (k : ℕ) : Wkp mu Omega p (k + 1) →L[ℝ] Wkp mu Omega p k :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun w => (Wkp.exists_hasWeakLineDerivOn_value k w v).choose
      map_add' := fun w w' => by
        refine Wkp.eq_of_hasWeakLineDerivOn
          (Wkp.exists_hasWeakLineDerivOn_value k (w + w') v).choose_spec ?_
        refine (((Wkp.exists_hasWeakLineDerivOn_value k w v).choose_spec.add
          (Wkp.exists_hasWeakLineDerivOn_value k w' v).choose_spec).congr_ae ?_).congr_ae_deriv ?_
        · rw [Wkp.value_add]
          exact (Lp.coeFn_add _ _).symm
        · rw [Wkp.value_add]
          exact (Lp.coeFn_add _ _).symm
      map_smul' := fun c w => by
        refine Wkp.eq_of_hasWeakLineDerivOn
          (Wkp.exists_hasWeakLineDerivOn_value k (c • w) v).choose_spec ?_
        refine (((Wkp.exists_hasWeakLineDerivOn_value k w v).choose_spec.const_smul
          c).congr_ae ?_).congr_ae_deriv ?_
        · rw [Wkp.value_smul]
          exact (Lp.coeFn_smul _ _).symm
        · rw [RingHom.id_apply, Wkp.value_smul]
          exact (Lp.coeFn_smul _ _).symm }
    (by
      obtain ⟨C, hC⟩ := Wkp.exists_norm_le_of_hasWeakLineDerivOn (mu := mu) (Omega := Omega)
        (p := p) v k
      exact ⟨C, fun w => hC w _ (Wkp.exists_hasWeakLineDerivOn_value k w v).choose_spec⟩)

/-- The value of `TauCeti.Wkp.lineDerivL v k w` is a weak derivative of the value of `w` in the
direction `v`. -/
theorem Wkp.hasWeakLineDerivOn_lineDerivL (v : E) (k : ℕ) (w : Wkp mu Omega p (k + 1)) :
    HasWeakLineDerivOn mu Omega (Wkp.value (k + 1) w) (Wkp.value k (Wkp.lineDerivL v k w)) v :=
  (Wkp.exists_hasWeakLineDerivOn_value k w v).choose_spec

/-- An element of `W^{k,p}(Ω)` whose value is a weak derivative of the value of `w` in the
direction `v` is `TauCeti.Wkp.lineDerivL v k w`. -/
theorem Wkp.lineDerivL_eq_of_hasWeakLineDerivOn {v : E} {k : ℕ} {w : Wkp mu Omega p (k + 1)}
    {d : Wkp mu Omega p k}
    (h : HasWeakLineDerivOn mu Omega (Wkp.value (k + 1) w) (Wkp.value k d) v) :
    Wkp.lineDerivL v k w = d :=
  Wkp.eq_of_hasWeakLineDerivOn (Wkp.hasWeakLineDerivOn_lineDerivL v k w) h

/-- Scaling the direction scales `TauCeti.Wkp.lineDerivL` by the same scalar. -/
@[simp]
theorem Wkp.lineDerivL_smul_left (c : ℝ) (v : E) (k : ℕ) :
    Wkp.lineDerivL (mu := mu) (Omega := Omega) (p := p) (c • v) k =
      c • Wkp.lineDerivL v k := by
  refine ContinuousLinearMap.ext fun w => Wkp.lineDerivL_eq_of_hasWeakLineDerivOn (p := p) ?_
  refine ((Wkp.hasWeakLineDerivOn_lineDerivL v k w).smul_direction c).congr_ae_deriv ?_
  rw [smul_apply, Wkp.value_smul]
  exact (Lp.coeFn_smul c (Wkp.value k (Wkp.lineDerivL v k w))).symm

/-- Differentiating in the zero direction is the zero operator. -/
@[simp]
theorem Wkp.lineDerivL_zero_left (k : ℕ) :
    Wkp.lineDerivL (mu := mu) (Omega := Omega) (p := p) (0 : E) k = 0 := by
  have h := Wkp.lineDerivL_smul_left (mu := mu) (Omega := Omega) (p := p) 0 (0 : E) k
  rwa [zero_smul, zero_smul] at h

/-- The bundled directional derivative is additive in the direction. -/
@[simp]
theorem Wkp.lineDerivL_add_left (v₁ v₂ : E) (k : ℕ) :
    Wkp.lineDerivL (mu := mu) (Omega := Omega) (p := p) (v₁ + v₂) k =
      Wkp.lineDerivL v₁ k + Wkp.lineDerivL v₂ k := by
  refine ContinuousLinearMap.ext fun w => Wkp.lineDerivL_eq_of_hasWeakLineDerivOn (p := p) ?_
  refine ((Wkp.hasWeakLineDerivOn_lineDerivL v₁ k w).add_direction
    (Wkp.hasWeakLineDerivOn_lineDerivL v₂ k w)).congr_ae_deriv ?_
  rw [add_apply, Wkp.value_add]
  exact (Lp.coeFn_add _ _).symm

/-- Negating the direction negates `TauCeti.Wkp.lineDerivL`. -/
@[simp]
theorem Wkp.lineDerivL_neg_left (v : E) (k : ℕ) :
    Wkp.lineDerivL (mu := mu) (Omega := Omega) (p := p) (-v) k =
      -Wkp.lineDerivL v k := by
  have h := Wkp.lineDerivL_smul_left (mu := mu) (Omega := Omega) (p := p) (-1) v k
  rwa [neg_one_smul, neg_one_smul] at h

/-- Subtracting directions subtracts the corresponding directional derivative operators. -/
@[simp]
theorem Wkp.lineDerivL_sub_left (v₁ v₂ : E) (k : ℕ) :
    Wkp.lineDerivL (mu := mu) (Omega := Omega) (p := p) (v₁ - v₂) k =
      Wkp.lineDerivL v₁ k - Wkp.lineDerivL v₂ k := by
  rw [sub_eq_add_neg, Wkp.lineDerivL_add_left, Wkp.lineDerivL_neg_left, sub_eq_add_neg]

/-- **The directional derivative, bundled in both the direction and the function.** Because `E` is
finite-dimensional, the linear dependence `v ↦ TauCeti.Wkp.lineDerivL v k` is continuous. -/
def Wkp.lineDerivBilinL (k : ℕ) :
    E →L[ℝ] Wkp mu Omega p (k + 1) →L[ℝ] Wkp mu Omega p k :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Wkp.lineDerivL v k
      map_add' := fun v₁ v₂ => Wkp.lineDerivL_add_left v₁ v₂ k
      map_smul' := fun c v => Wkp.lineDerivL_smul_left c v k }

-- Not `@[simp]`: unfolding `Wkp mu Omega p (k + 1)` in `DiscrTree.mkPath` introduces
-- `sobolevStage.match_1` (`Key.other`) inside `DFunLike.coe`, so `simpNF` rejects
-- `lineDerivBilinL_apply` (it does not simplify its own LHS).
theorem Wkp.lineDerivBilinL_apply (k : ℕ) (v : E) :
    Wkp.lineDerivBilinL (mu := mu) (Omega := Omega) (p := p) k v = Wkp.lineDerivL v k :=
  (rfl)

/-- At order zero, `TauCeti.Wkp.lineDerivL` pairs the weak gradient with the direction `v` in
`Lᵖ(Ω)`. -/
theorem Wkp.lineDerivL_zero_apply (v : E) (w : Wkp mu Omega p 1) :
    Wkp.lineDerivL v 0 w = (innerSL ℝ v).compLp (Wkp.iteratedGradient 0 w) :=
  Wkp.lineDerivL_eq_of_hasWeakLineDerivOn (Wkp.hasWeakLineDerivOn_value_innerSL_compLp v w)

/-- Two Sobolev functions of possibly different positive orders with the same `Lᵖ` value have the
same `Lᵖ` directional derivative in every direction. -/
theorem Wkp.value_lineDerivL_eq_of_value_eq {k₁ k₂ : ℕ} {u₁ : Wkp mu Omega p (k₁ + 1)}
    {u₂ : Wkp mu Omega p (k₂ + 1)} (h : Wkp.value (k₁ + 1) u₁ = Wkp.value (k₂ + 1) u₂) (v : E) :
    Wkp.value k₁ (Wkp.lineDerivL v k₁ u₁) = Wkp.value k₂ (Wkp.lineDerivL v k₂ u₂) := by
  apply Lp.ext
  have h₁ := Wkp.hasWeakLineDerivOn_lineDerivL v k₁ u₁
  rw [h] at h₁
  exact h₁.ae_eq (Wkp.hasWeakLineDerivOn_lineDerivL v k₂ u₂)

/-- Order truncation commutes with `TauCeti.Wkp.lineDerivL`. -/
theorem Wkp.toOrderL_lineDerivL (v : E) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p (k + 1)) :
    Wkp.toOrderL h (Wkp.lineDerivL v k u) =
      Wkp.lineDerivL v j (Wkp.toOrderL (Nat.succ_le_succ h) u) :=
  Wkp.ext j ((Wkp.value_toOrderL h _).trans
    (Wkp.value_lineDerivL_eq_of_value_eq (Wkp.value_toOrderL (Nat.succ_le_succ h) u).symm v))

/-- Operator form of `TauCeti.Wkp.toOrderL_lineDerivL`. -/
theorem Wkp.toOrderL_comp_lineDerivL (v : E) {j k : ℕ} (h : j ≤ k) :
    (Wkp.toOrderL (mu := mu) (Omega := Omega) (p := p) h).comp (Wkp.lineDerivL v k) =
      (Wkp.lineDerivL v j).comp (Wkp.toOrderL (Nat.succ_le_succ h)) :=
  ContinuousLinearMap.ext fun u => Wkp.toOrderL_lineDerivL v h u

/-- Forgetting the highest weak derivative commutes with `TauCeti.Wkp.lineDerivL`. -/
theorem Wkp.lowerOrder_lineDerivL (v : E) (k : ℕ) (w : Wkp mu Omega p (k + 2)) :
    Wkp.lowerOrder k (Wkp.lineDerivL v (k + 1) w) =
      Wkp.lineDerivL v k (Wkp.lowerOrder (k + 1) w) := by
  rw [← Wkp.lowerOrderL_apply, ← Wkp.lowerOrderL_apply,
    ← Wkp.toOrderL_le_succ k (Nat.le_succ k),
    ← Wkp.toOrderL_le_succ (k + 1) (Nat.le_succ (k + 1)),
    Wkp.toOrderL_lineDerivL]

/-- Operator form of `TauCeti.Wkp.lowerOrder_lineDerivL`. -/
theorem Wkp.lowerOrderL_comp_lineDerivL (v : E) (k : ℕ) :
    (Wkp.lowerOrderL k).comp (Wkp.lineDerivL (mu := mu) (Omega := Omega) (p := p) v (k + 1)) =
      (Wkp.lineDerivL v k).comp (Wkp.lowerOrderL (k + 1)) := by
  rw [← Wkp.toOrderL_le_succ k (Nat.le_succ k),
    ← Wkp.toOrderL_le_succ (k + 1) (Nat.le_succ (k + 1)),
    Wkp.toOrderL_comp_lineDerivL]

/-- At every positive order, the `Lᵖ` value of `TauCeti.Wkp.lineDerivL v k w` is the `v`-component
of the weak gradient of the first-order part of `w`. -/
theorem Wkp.value_lineDerivL (v : E) (k : ℕ) (w : Wkp mu Omega p (k + 1)) :
    Wkp.value k (Wkp.lineDerivL v k w) =
      (innerSL ℝ v).compLp (W1p.gradient (Wkp.firstOrder k w)) := by
  rw [← Wkp.toOrderL_zero_left_apply k (Nat.zero_le k),
    Wkp.toOrderL_lineDerivL v (Nat.zero_le k) w,
    Wkp.lineDerivL_zero_apply, Wkp.iteratedGradient_zero, Wkp.toOrderL_one_left_apply]

/-- Almost-everywhere pointwise form of `TauCeti.Wkp.value_lineDerivL`. -/
theorem Wkp.value_lineDerivL_ae (v : E) (k : ℕ) (w : Wkp mu Omega p (k + 1)) :
    ∀ᵐ x ∂mu.restrict Omega,
      Wkp.value k (Wkp.lineDerivL v k w) x = ⟪W1p.gradient (Wkp.firstOrder k w) x, v⟫_ℝ := by
  rw [Wkp.value_lineDerivL]
  filter_upwards [(innerSL ℝ v).coeFn_compLp (W1p.gradient (Wkp.firstOrder k w))] with x hx
  rw [hx, innerSL_apply_apply, real_inner_comm]

/-! ### From the directional derivatives to `W^{k+1,p}` -/

section Assembly

variable {ι : Type*} [Fintype ι]

/-- The first-order case of `TauCeti.Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn`: weak
derivatives in `Lᵖ(Ω)` along an orthonormal basis assemble into a weak gradient. -/
private theorem W1p.exists_value_eq_gradient_eq (b : OrthonormalBasis ι ℝ E)
    (u : Lp ℝ p (mu.restrict Omega)) (d : ι → Lp ℝ p (mu.restrict Omega))
    (hd : ∀ i, HasWeakLineDerivOn mu Omega u (d i) (b i)) :
    ∃ w : W1p mu Omega p, W1p.value w = u ∧
      W1p.gradient w = ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (d i) := by
  classical
  set g := ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (d i)
  have hg : ∀ k, (fun x => innerSL ℝ (g x) (b k)) =ᵐ[mu.restrict Omega] d k := by
    intro k
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      fun i => (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (d i),
      ae_all_iff.mpr fun i => (ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLp (d i)]
      with x hsum hcomp
    rw [hsum, innerSL_apply_apply, sum_inner]
    simp [hcomp, inner_smul_left, OrthonormalBasis.inner_eq_ite]
  have hu : LocallyIntegrableOn (u : E → ℝ) Omega mu :=
    Lp.locallyIntegrableOn u Fact.out
  have hw : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (g x)) :=
    b.toBasis.hasWeakFDerivOn_of_forall hu fun k => by
      simpa only [OrthonormalBasis.coe_toBasis] using (hd k).congr_ae_deriv (hg k).symm
  exact ⟨W1p.mk u g hw, W1p.value_mk u g hw, W1p.gradient_mk u g hw⟩

/-- The second-order case of `TauCeti.Wkp.exists_wkp_succ_of_forall`. -/
private theorem Wkp.exists_wkp_two_of_forall (b : OrthonormalBasis ι ℝ E)
    (u : Lp ℝ p (mu.restrict Omega)) (d : ι → Wkp mu Omega p 1)
    (hd : ∀ i, HasWeakLineDerivOn mu Omega u (Wkp.value 1 (d i)) (b i)) :
    ∃ w : Wkp mu Omega p 2, Wkp.value 2 w = u ∧ Wkp.iteratedGradient 1 w =
      ∑ i, (insertL (b i) 0).compLp (Wkp.iteratedGradient 0 (d i)) := by
  obtain ⟨w₁, hw₁, hg₁⟩ := W1p.exists_value_eq_gradient_eq b u _ hd
  set D := ∑ i, (insertL (b i) 0).compLp (Wkp.iteratedGradient 0 (d i))
  -- `∇u = ∑ᵢ (∂ᵢu) eᵢ`, and each summand has weak derivative `h ↦ ⟪∇∂ᵢu, h⟫ eᵢ`
  have hD : HasWeakFDerivOn mu Omega (Wkp.iteratedGradient 0 w₁) D := by
    have hsum := HasWeakFDerivOn.sum Finset.univ fun i _ =>
      (Wkp.hasWeakFDerivOn_value (d i)).clm_comp (ContinuousLinearMap.toSpanSingleton ℝ (b i))
    rw [Wkp.iteratedGradient_zero w₁, hg₁]
    refine (hsum.congr_ae ?_).congr_ae_deriv ?_
    · filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        fun i => (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (Wkp.value 1 (d i)),
        ae_all_iff.mpr fun i =>
          (ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLp (Wkp.value 1 (d i))]
        with x hsum hcomp
      simp only [hsum, hcomp]
    · filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        fun i => (insertL (b i) 0).compLp (Wkp.iteratedGradient 0 (d i)),
        ae_all_iff.mpr fun i => (insertL (b i) 0).coeFn_compLp (Wkp.iteratedGradient 0 (d i))]
        with x hsum hcomp
      refine (Finset.sum_congr rfl fun i _ => ?_).trans hsum.symm
      ext h
      rw [hcomp i, insertL_zero_apply]
      simp
  refine ⟨Wkp.mk 0 w₁ D hD, ?_, Wkp.iteratedGradient_mk 0 w₁ D hD⟩
  rw [Wkp.value_mk 0 w₁ D hD, Wkp.value_one w₁, hw₁]

/-- Elements of `W^{k+1,p}(Ω)` that are weak derivatives of `u` along an orthonormal basis assemble
into an element of `W^{k+2,p}(Ω)` with value `u`, whose highest derivative is obtained by
inserting the basis functionals in the innermost slot. -/
private theorem Wkp.exists_wkp_succ_of_forall (b : OrthonormalBasis ι ℝ E)
    (u : Lp ℝ p (mu.restrict Omega)) :
    ∀ (k : ℕ) (d : ι → Wkp mu Omega p (k + 1)),
      (∀ i, HasWeakLineDerivOn mu Omega u (Wkp.value (k + 1) (d i)) (b i)) →
      ∃ w : Wkp mu Omega p (k + 2), Wkp.value (k + 2) w = u ∧ Wkp.iteratedGradient (k + 1) w =
        ∑ i, (insertL (b i) k).compLp (Wkp.iteratedGradient k (d i))
  | 0, d, hd => Wkp.exists_wkp_two_of_forall b u d hd
  | k + 1, d, hd => by
      obtain ⟨w, hw, hwk⟩ := Wkp.exists_wkp_succ_of_forall b u k
        (fun i => Wkp.lowerOrder (k + 1) (d i)) fun i => by
          simpa only [← Wkp.value_succ] using hd i
      set D := ∑ i, (insertL (b i) (k + 1)).compLp (Wkp.iteratedGradient (k + 1) (d i))
      have hD : HasWeakFDerivOn mu Omega (Wkp.iteratedGradient (k + 1) w) D := by
        have hsum := HasWeakFDerivOn.sum Finset.univ fun i _ =>
          (Wkp.hasWeakFDerivOn_iteratedGradient k (d i)).clm_comp (insertL (b i) k)
        rw [hwk]
        refine (hsum.congr_ae ?_).congr_ae_deriv ?_
        · filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun i => (insertL (b i) k).compLp
            (Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) (d i))),
            ae_all_iff.mpr fun i => (insertL (b i) k).coeFn_compLp
              (Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) (d i)))]
            with x hsum hcomp
          simp only [hsum, hcomp]
        · filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun i =>
            (insertL (b i) (k + 1)).compLp (Wkp.iteratedGradient (k + 1) (d i)),
            ae_all_iff.mpr fun i => (insertL (b i) (k + 1)).coeFn_compLp
              (Wkp.iteratedGradient (k + 1) (d i))]
            with x hsum hcomp
          rw [hsum]
          exact Finset.sum_congr rfl fun i _ => by rw [hcomp i, insertL_succ_apply]
      refine ⟨Wkp.mk (k + 1) w D hD, ?_, Wkp.iteratedGradient_mk (k + 1) w D hD⟩
      rw [Wkp.value_mk, hw]

/-- **Sobolev functions from their directional derivatives.** If, along every vector of an
orthonormal basis, `u ∈ Lᵖ(Ω)` has a weak derivative which is the value of an element of
`W^{k,p}(Ω)`, then `u` is the value of an element of `W^{k+1,p}(Ω)`. -/
theorem Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn (b : OrthonormalBasis ι ℝ E)
    (u : Lp ℝ p (mu.restrict Omega)) :
    ∀ k : ℕ, (∀ i, ∃ d : Wkp mu Omega p k,
      HasWeakLineDerivOn mu Omega u (Wkp.value k d) (b i)) →
      ∃ w : Wkp mu Omega p (k + 1), Wkp.value (k + 1) w = u
  | 0, h => by
      choose d hd using h
      obtain ⟨w, hw, -⟩ := W1p.exists_value_eq_gradient_eq b u d fun i => by
        simpa only [Wkp.value_zero] using hd i
      exact ⟨w, (Wkp.value_one w).trans hw⟩
  | k + 1, h => by
      choose d hd using h
      obtain ⟨w, hw, -⟩ := Wkp.exists_wkp_succ_of_forall b u k d hd
      exact ⟨w, hw⟩

end Assembly

/-- **The Sobolev scale by first derivatives.** A function `u ∈ Lᵖ(Ω)` is the value of an element
of `W^{k+1,p}(Ω)` exactly when, in every direction, it has a weak derivative which is the value of
an element of `W^{k,p}(Ω)`. -/
theorem Wkp.exists_value_eq_iff_forall_exists_hasWeakLineDerivOn (k : ℕ)
    (u : Lp ℝ p (mu.restrict Omega)) :
    (∃ w : Wkp mu Omega p (k + 1), Wkp.value (k + 1) w = u) ↔
      ∀ v : E, ∃ d : Wkp mu Omega p k, HasWeakLineDerivOn mu Omega u (Wkp.value k d) v := by
  refine ⟨fun ⟨w, hw⟩ v => hw ▸ Wkp.exists_hasWeakLineDerivOn_value k w v, fun h => ?_⟩
  exact Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn (stdOrthonormalBasis ℝ E) u k
    fun i => h _

/-- A function `w` in `Lᵖ(Ω)` whose weak derivative on `Ω` in every direction `v` is the value of
an element `d v` of `W^{k,p}(Ω)` agrees almost everywhere on `Ω` with the value of an element of
`W^{k+1,p}(Ω)`. This is `TauCeti.Wkp.exists_value_eq_iff_forall_exists_hasWeakLineDerivOn` for a
function representative rather than an element of `Lᵖ`. -/
theorem Wkp.exists_value_ae_eq_of_forall_hasWeakLineDerivOn (k : ℕ) {w : E → ℝ}
    (hw : MemLp w p (mu.restrict Omega)) (d : E → Wkp mu Omega p k)
    (hd : ∀ v, HasWeakLineDerivOn mu Omega w (Wkp.value k (d v)) v) :
    ∃ W : Wkp mu Omega p (k + 1), Wkp.value (k + 1) W =ᵐ[mu.restrict Omega] w := by
  obtain ⟨W, hW⟩ := (Wkp.exists_value_eq_iff_forall_exists_hasWeakLineDerivOn k
    (hw.toLp w)).2 fun v => ⟨d v, (hd v).congr_ae hw.coeFn_toLp.symm⟩
  exact ⟨W, hW ▸ hw.coeFn_toLp⟩

/-- The first-order case of `TauCeti.Wkp.exists_value_ae_eq_of_forall_hasWeakLineDerivOn`: a
function `w` in `Lᵖ(Ω)` whose weak derivative on `Ω` in every direction `v` is a function `w' v`
in `Lᵖ(Ω)` agrees almost everywhere on `Ω` with the value of an element of `W^{1,p}(Ω)`. -/
theorem Wkp.exists_value_one_ae_eq_of_forall_hasWeakLineDerivOn {w : E → ℝ}
    (hw : MemLp w p (mu.restrict Omega)) (w' : E → E → ℝ)
    (hw' : ∀ v, MemLp (w' v) p (mu.restrict Omega))
    (h : ∀ v, HasWeakLineDerivOn mu Omega w (w' v) v) :
    ∃ W : Wkp mu Omega p 1, Wkp.value 1 W =ᵐ[mu.restrict Omega] w :=
  Wkp.exists_value_ae_eq_of_forall_hasWeakLineDerivOn 0 hw (fun v => (hw' v).toLp (w' v))
    fun v => by
      rw [Wkp.value_zero]
      exact (h v).congr_ae_deriv (hw' v).coeFn_toLp.symm

/-! ### Second order from the components of the gradient -/

/-- **Second-order weak differentiability from directional derivatives.** Fix an orthonormal
basis `e` of `E`. If, for every pair of indices `i, j`, the scalar component `⟪∇u, eⱼ⟫` of the
weak gradient of `u ∈ W^{1,p}(Ω)` has a weak derivative in `Lᵖ(Ω)` in the direction `eᵢ`, then
`u` is the first-order part of an element of `W^{2,p}(Ω)`.

This is how a difference-quotient argument, which produces exactly these componentwise
derivatives, certifies membership in the second-order Sobolev space. -/
theorem W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn {ι : Type*} [Fintype ι]
    (u : W1p mu Omega p) (b : OrthonormalBasis ι ℝ E)
    (h : ∀ i j : ι, ∃ g : Lp ℝ p (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient u x, b j⟫_ℝ) g (b i)) :
    ∃ U : Wkp mu Omega p 2, Wkp.lowerOrder 1 U = u := by
  have hgrad : ∀ j, (fun x => ⟪W1p.gradient u x, b j⟫_ℝ) =ᵐ[mu.restrict Omega]
      (innerSL ℝ (b j)).compLp (W1p.gradient u) := fun j => by
    filter_upwards [(innerSL ℝ (b j)).coeFn_compLp (W1p.gradient u)] with x hx
    rw [hx, innerSL_apply_apply, real_inner_comm]
  -- each component `∂ⱼu = ⟪∇u, eⱼ⟫` lies in `W^{1,p}(Ω)`, so `u ∈ W^{2,p}(Ω)`
  have hcomp : ∀ j, ∃ d : Wkp mu Omega p 1,
      HasWeakLineDerivOn mu Omega (W1p.value u) (Wkp.value 1 d) (b j) := fun j => by
    obtain ⟨d, hd⟩ := Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn b
      ((innerSL ℝ (b j)).compLp (W1p.gradient u)) 0 fun i =>
        (h i j).imp fun _ hg => by simpa only [Wkp.value_zero] using hg.congr_ae (hgrad j)
    refine ⟨d, ?_⟩
    rw [hd]
    exact ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (b j)).congr_ae_deriv (hgrad j)
  obtain ⟨U, hU⟩ := Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn b (W1p.value u) 1 hcomp
  exact ⟨U, W1p.ext_value (((Wkp.value_one _).symm.trans (Wkp.value_succ 1 U).symm).trans hU)⟩

/-- **Second-order weak differentiability on a subdomain.** Let `w ∈ W^{1,p}(Ω)` and let
`V ≤ Ω` be open. Suppose that the components `⟪∇w, eⱼ⟫` of the weak gradient of `w` along an
orthonormal basis `e` have weak derivatives in `Lᵖ(Ω)` along every `eᵢ`. Then every `u ∈ W^{1,p}(V)`
whose weak gradient agrees almost everywhere on `V` with that of `w` is the first-order part of an
element of `W^{2,p}(V)`. -/
theorem W1p.exists_lowerOrder_eq_of_gradient_eq_of_hasWeakLineDerivOn {ι : Type*} [Fintype ι]
    {V : Opens E} {w : W1p mu Omega p} {u : W1p mu V p} (b : OrthonormalBasis ι ℝ E)
    (hV : V ≤ Omega)
    (hgrad : ∀ᵐ x ∂mu.restrict V, W1p.gradient w x = W1p.gradient u x)
    (h : ∀ i j : ι, ∃ g : Lp ℝ p (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪W1p.gradient w x, b j⟫_ℝ) g (b i)) :
    ∃ U : Wkp mu V p 2, Wkp.lowerOrder 1 U = u := by
  refine W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn u b fun i j => ?_
  obtain ⟨G, hG⟩ := h i j
  have hGm : MemLp G p (mu.restrict V) :=
    (Lp.memLp G).mono_measure (Measure.restrict_mono (SetLike.coe_subset_coe.mpr hV) le_rfl)
  refine ⟨hGm.toLp G, ((hG.mono hV).congr_ae ?_).congr_ae_deriv hGm.coeFn_toLp.symm⟩
  filter_upwards [hgrad] with x hx
  rw [hx]

/-- **The weak Hessian is controlled by its entries.** Let `U ∈ W^{2,p}(Ω)` and fix an orthonormal
basis `e` of `E`. If `gᵢⱼ ∈ Lᵖ(Ω)` is a weak derivative in the direction `eᵢ` of the component
`⟪∇U, eⱼ⟫` of the weak gradient, then the `Lᵖ` norm of the weak Hessian of `U` is at most
`∑ᵢ ∑ⱼ ‖gᵢⱼ‖`. Together with `TauCeti.Wkp.norm_le_norm_lowerOrder_add_norm_iteratedGradient`, this
bounds the norm of `U` in `W^{2,p}(Ω)` by the `W^{1,p}(Ω)` norm of its first-order part plus
`∑ᵢ ∑ⱼ ‖gᵢⱼ‖`; `TauCeti.W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn` supplies such a `U`
from these componentwise second weak derivatives. -/
theorem Wkp.norm_iteratedGradient_one_le_sum {ι : Type*} [Fintype ι] (U : Wkp mu Omega p 2)
    (b : OrthonormalBasis ι ℝ E) {g : ι → ι → Lp ℝ p (mu.restrict Omega)}
    (hg : ∀ i j, HasWeakLineDerivOn mu Omega
      (fun x => ⟪W1p.gradient (Wkp.lowerOrder 1 U) x, b j⟫_ℝ) (g i j) (b i)) :
    ‖Wkp.iteratedGradient 1 U‖ ≤ ∑ i, ∑ j, ‖g i j‖ := by
  -- The entries `⟪D²U eᵢ, eⱼ⟫` of the weak Hessian are the given derivatives `gᵢⱼ`.
  have hH := Wkp.hasWeakFDerivOn_iteratedGradient 0 U
  rw [Wkp.iteratedGradient_zero] at hH
  have hent : ∀ i j, (fun x => ⟪Wkp.iteratedGradient 1 U x (b i), b j⟫_ℝ) =ᵐ[mu.restrict Omega]
      g i j := fun i j =>
    HasWeakLineDerivOn.ae_eq (by simpa only [innerSL_apply_apply, real_inner_comm] using
      (hH.hasWeakLineDerivOn (b i)).clm_comp (innerSL ℝ (b j))) (hg i j)
  -- Pointwise, the operator norm is at most the sum of the absolute values of the entries.
  have hpt : ∀ᵐ x ∂mu.restrict Omega,
      ‖Wkp.iteratedGradient 1 U x‖ ≤ ‖∑ i, ∑ j, ‖g i j x‖‖ := by
    filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hent i j] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    refine ((Wkp.iteratedGradient 1 U x).opNorm_le_sum_norm_apply_orthonormalBasis b).trans
      (Finset.sum_le_sum fun i _ => ?_)
    rw [← innerSL_apply_norm ℝ]
    refine ((innerSL ℝ (Wkp.iteratedGradient 1 U x (b i))).opNorm_le_sum_norm_apply_orthonormalBasis
      b).trans_eq (Finset.sum_congr rfl fun j _ => ?_)
    rw [innerSL_apply_apply, hx i j]
  -- Integrate, using the triangle inequality in `Lᵖ` for the finite sums.
  have hsum : eLpNorm (fun x => ∑ i, ∑ j, ‖g i j x‖) p (mu.restrict Omega) ≤
      ∑ i, ∑ j, eLpNorm (g i j) p (mu.restrict Omega) := by
    have h₁ := eLpNorm_sum_le (μ := mu.restrict Omega) (s := Finset.univ)
      (f := fun i x => ∑ j, ‖g i j x‖) (Fact.out : 1 ≤ p)
    rw [Finset.sum_fn] at h₁
    refine h₁.trans (Finset.sum_le_sum fun i _ => ?_)
    have h₂ := eLpNorm_sum_le (μ := mu.restrict Omega) (s := Finset.univ)
      (f := fun j x => ‖g i j x‖) (Fact.out : 1 ≤ p)
    rw [Finset.sum_fn] at h₂
    exact h₂.trans_eq (Finset.sum_congr rfl fun j _ => eLpNorm_norm _ (Lp.aestronglyMeasurable _))
  rw [Lp.norm_def]
  refine (ENNReal.toReal_mono (by simp [ENNReal.sum_eq_top, Lp.eLpNorm_ne_top])
    ((eLpNorm_mono_ae (Lp.aestronglyMeasurable _) hpt).trans hsum)).trans_eq ?_
  simp only [ENNReal.toReal_sum fun _ _ => ENNReal.sum_ne_top.2 fun _ _ => Lp.eLpNorm_ne_top _,
    ENNReal.toReal_sum fun _ _ => Lp.eLpNorm_ne_top _, Lp.norm_def]

/-! ### Commutativity of directional derivatives -/

/-- **Bundled directional derivatives commute.** For `u ∈ W^{k+2,p}(Ω)` and directions `v, w : E`,
differentiating in direction `w` and then `v` gives the same element of `W^{k,p}(Ω)` as
differentiating in direction `v` and then `w`. -/
theorem Wkp.lineDerivL_comm (v w : E) (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    Wkp.lineDerivL v k (Wkp.lineDerivL w (k + 1) u) =
      Wkp.lineDerivL w k (Wkp.lineDerivL v (k + 1) u) := by
  have hv := Wkp.hasWeakLineDerivOn_lineDerivL v (k + 1) u
  have hw := Wkp.hasWeakLineDerivOn_lineDerivL w (k + 1) u
  have hvw := Wkp.hasWeakLineDerivOn_lineDerivL w k (Wkp.lineDerivL v (k + 1) u)
  exact Wkp.lineDerivL_eq_of_hasWeakLineDerivOn (hv.comm hvw hw)

/-- Operator form of `TauCeti.Wkp.lineDerivL_comm`. -/
theorem Wkp.lineDerivL_comp_lineDerivL_comm (v w : E) (k : ℕ) :
    (Wkp.lineDerivL (mu := mu) (Omega := Omega) (p := p) v k).comp (Wkp.lineDerivL w (k + 1)) =
      (Wkp.lineDerivL w k).comp (Wkp.lineDerivL v (k + 1)) :=
  ContinuousLinearMap.ext fun u => Wkp.lineDerivL_comm v w k u

/-! ### Commutativity of directional derivatives with `iteratedGradient` -/

/-- **Weak directional derivatives commute with `Wkp.iteratedGradient`.** If the value of `g` is a
weak derivative of the value of `f` in the direction `w` on `Ω`, then at every recorded order `j`
the highest weak derivative `Wkp.iteratedGradient j g` is a weak derivative of
`Wkp.iteratedGradient j f` in the direction `w`. -/
theorem Wkp.hasWeakLineDerivOn_iteratedGradient :
    ∀ (j : ℕ) {f g : Wkp mu Omega p (j + 1)} {w : E},
      HasWeakLineDerivOn mu Omega (Wkp.value (j + 1) f) (Wkp.value (j + 1) g) w →
      HasWeakLineDerivOn mu Omega (Wkp.iteratedGradient j f) (Wkp.iteratedGradient j g) w
  | 0, f, g, w, h => by
      refine hasWeakLineDerivOn_of_forall_clm_comp
        (Lp.locallyIntegrableOn _ Fact.out) (Lp.locallyIntegrableOn _ Fact.out)
        (fun z : E ↦ innerSL ℝ z) (fun y y' hy ↦ ext_inner_left ℝ fun z ↦ hy z) fun z ↦ ?_
      have hf : HasWeakLineDerivOn mu Omega (Wkp.value 1 f)
          (fun x ↦ innerSL ℝ z (Wkp.iteratedGradient 0 f x)) z := by
        simpa only [innerSL_apply_apply, real_inner_comm] using
          (Wkp.hasWeakFDerivOn_value f).hasWeakLineDerivOn z
      have hg : HasWeakLineDerivOn mu Omega (Wkp.value 1 g)
          (fun x ↦ innerSL ℝ z (Wkp.iteratedGradient 0 g x)) z := by
        simpa only [innerSL_apply_apply, real_inner_comm] using
          (Wkp.hasWeakFDerivOn_value g).hasWeakLineDerivOn z
      exact h.comm hg hf
  | j + 1, f, g, w, h => by
      have ih := Wkp.hasWeakLineDerivOn_iteratedGradient j
        (f := Wkp.lowerOrder (j + 1) f) (g := Wkp.lowerOrder (j + 1) g)
        (by simpa only [Wkp.value_succ] using h)
      refine hasWeakLineDerivOn_of_forall_clm_comp
        (Lp.locallyIntegrableOn _ Fact.out) (Lp.locallyIntegrableOn _ Fact.out)
        (fun z : E ↦ ContinuousLinearMap.apply ℝ (IteratedGradient E j) z)
        (fun A B hAB ↦ ContinuousLinearMap.ext hAB) fun z ↦ ?_
      exact ih.comm ((Wkp.hasWeakFDerivOn_iteratedGradient j g).hasWeakLineDerivOn z)
        ((Wkp.hasWeakFDerivOn_iteratedGradient j f).hasWeakLineDerivOn z)

/-- **Top weak derivative of a directional derivative.** Because weak derivatives commute, the
highest weak derivative of `Wkp.lineDerivL v (j + 1) u` is obtained by evaluating the outermost
direction slot of `Wkp.iteratedGradient (j + 1) u` at `v`. -/
theorem Wkp.iteratedGradient_lineDerivL (v : E) (j : ℕ) (u : Wkp mu Omega p (j + 2)) :
    Wkp.iteratedGradient j (Wkp.lineDerivL v (j + 1) u) =
      (ContinuousLinearMap.apply ℝ (IteratedGradient E j) v).compLp
        (Wkp.iteratedGradient (j + 1) u) := by
  have h1 : HasWeakLineDerivOn mu Omega
      (Wkp.iteratedGradient j (Wkp.lowerOrder (j + 1) u))
      (Wkp.iteratedGradient j (Wkp.lineDerivL v (j + 1) u)) v :=
    Wkp.hasWeakLineDerivOn_iteratedGradient j (f := Wkp.lowerOrder (j + 1) u)
      (by simpa only [Wkp.value_succ] using Wkp.hasWeakLineDerivOn_lineDerivL v (j + 1) u)
  have h2 := (Wkp.hasWeakFDerivOn_iteratedGradient j u).hasWeakLineDerivOn v
  apply Lp.ext
  refine (h1.ae_eq h2).trans (Filter.EventuallyEq.symm ?_)
  exact (ContinuousLinearMap.apply ℝ (IteratedGradient E j) v).coeFn_compLp _

/-- If the highest weak derivative of `u ∈ W^{j+2,p}(Ω)` vanishes, then so does the highest weak
derivative of every directional derivative `Wkp.lineDerivL v (j + 1) u`. -/
theorem Wkp.iteratedGradient_lineDerivL_eq_zero_of_eq_zero (v : E) {j : ℕ}
    {u : Wkp mu Omega p (j + 2)} (hu : Wkp.iteratedGradient (j + 1) u = 0) :
    Wkp.iteratedGradient j (Wkp.lineDerivL v (j + 1) u) = 0 := by
  rw [Wkp.iteratedGradient_lineDerivL, hu]
  exact ((ContinuousLinearMap.apply ℝ (IteratedGradient E j) v).compLpₗ p
    (mu.restrict Omega)).map_zero

/-- A directional component of the gradient of an order-`k + 1` Sobolev function
has an order-`k` Sobolev representative. -/
theorem Wkp.exists_value_ae_eq_gradient_inner (k : ℕ) {u : W1p mu Omega p}
    (U : Wkp mu Omega p (k + 1)) (hU : Wkp.value (k + 1) U = W1p.value u) (v : E) :
    ∃ D : Wkp mu Omega p k, Wkp.value k D =ᵐ[mu.restrict Omega]
      fun x ↦ ⟪W1p.gradient u x, v⟫_ℝ := by
  obtain ⟨D, hD⟩ := Wkp.exists_hasWeakLineDerivOn_value k U v
  rw [hU] at hD
  exact ⟨D, hD.ae_eq (W1p.hasWeakLineDerivOn_inner_gradient u v)⟩

/-- Sobolev representatives for a unit normal derivative and all orthogonal derivatives
give a Sobolev representative for every directional derivative. -/
theorem Wkp.exists_hasWeakLineDerivOn_of_normal_and_tangential (k : ℕ)
    {e : E} (he : ‖e‖ = 1) {q : E → ℝ} {N : Wkp mu Omega p k}
    (hN : HasWeakLineDerivOn mu Omega q (Wkp.value k N) e)
    (hT : ∀ τ : E, ⟪τ, e⟫_ℝ = 0 → ∃ T : Wkp mu Omega p k,
      HasWeakLineDerivOn mu Omega q (Wkp.value k T) τ) (v : E) :
    ∃ D : Wkp mu Omega p k, HasWeakLineDerivOn mu Omega q (Wkp.value k D) v := by
  let P := (ℝ ∙ e)ᗮ.starProjection
  obtain ⟨T, hT⟩ := hT (P v) (by simp [P])
  have hsplit : P v + ⟪e, v⟫_ℝ • e = v := by
    simpa only [Submodule.starProjection_singleton, he, one_pow, RCLike.ofReal_real_eq_id,
      id_eq, div_one, add_comm, P] using
      (ℝ ∙ e).starProjection_add_starProjection_orthogonal v
  have hd := hT.add_direction (hN.smul_direction ⟪e, v⟫_ℝ)
  rw [hsplit] at hd
  refine ⟨T + ⟪e, v⟫_ℝ • N, hd.congr_ae_deriv ?_⟩
  filter_upwards [Wkp.value_add_ae k T (⟪e, v⟫_ℝ • N), Wkp.value_smul_ae k ⟪e, v⟫_ℝ N]
    with x h₁ h₂
  simp only [h₁, h₂, Pi.add_apply]

/-- Almost-everywhere pointwise form of `TauCeti.Wkp.iteratedGradient_lineDerivL`. -/
theorem Wkp.iteratedGradient_lineDerivL_ae (v : E) (j : ℕ) (u : Wkp mu Omega p (j + 2)) :
    ∀ᵐ x ∂mu.restrict Omega,
      Wkp.iteratedGradient j (Wkp.lineDerivL v (j + 1) u) x =
        Wkp.iteratedGradient (j + 1) u x v := by
  rw [Wkp.iteratedGradient_lineDerivL]
  filter_upwards [(ContinuousLinearMap.apply ℝ (IteratedGradient E j) v).coeFn_compLp
    (Wkp.iteratedGradient (j + 1) u)] with x hx
  rw [hx, ContinuousLinearMap.apply_apply]

/-! ### Symmetry of the weak Hessian -/

/-- **The weak Hessian is symmetric.** For `u ∈ W^{2,p}(Ω)` and directions `v` and `w`, the mixed
weak derivatives `⟪D²u v, w⟫ = ∂_v ∂_w u` and `⟪D²u w, v⟫ = ∂_w ∂_v u` agree almost everywhere on
`Ω`. Here `D²u` is the highest recorded weak derivative `TauCeti.Wkp.iteratedGradient 1 u`. -/
theorem Wkp.inner_iteratedGradient_one_apply_ae_eq (u : Wkp mu Omega p 2) (v w : E) :
    (fun x => ⟪Wkp.iteratedGradient 1 u x v, w⟫_ℝ) =ᵐ[mu.restrict Omega]
      fun x => ⟪Wkp.iteratedGradient 1 u x w, v⟫_ℝ := by
  have hcomm := Wkp.lineDerivL_comm w v 0 u
  rw [Wkp.lineDerivL_zero_apply, Wkp.lineDerivL_zero_apply] at hcomm
  filter_upwards
    [(innerSL ℝ w).coeFn_compLp (Wkp.iteratedGradient 0 (Wkp.lineDerivL v 1 u)),
     (innerSL ℝ v).coeFn_compLp (Wkp.iteratedGradient 0 (Wkp.lineDerivL w 1 u)),
     Wkp.iteratedGradient_lineDerivL_ae v 0 u,
     Wkp.iteratedGradient_lineDerivL_ae w 0 u] with x h1 h2 h3 h4
  have hx : ((innerSL ℝ w).compLp (Wkp.iteratedGradient 0 (Wkp.lineDerivL v 1 u)) : E → ℝ) x =
      ((innerSL ℝ v).compLp (Wkp.iteratedGradient 0 (Wkp.lineDerivL w 1 u)) : E → ℝ) x := by
    rw [hcomm]
  simpa only [h1, h2, h3, h4, innerSL_apply_apply, real_inner_comm] using hx

/-- **The weak Hessian is self-adjoint.** For `u ∈ W^{2,p}(Ω)`, the weak Hessian
`D²u(x) = TauCeti.Wkp.iteratedGradient 1 u x` is a self-adjoint endomorphism of `E` for almost
every `x ∈ Ω`. -/
theorem Wkp.adjoint_iteratedGradient_one_ae_eq (u : Wkp mu Omega p 2) :
    ∀ᵐ x ∂mu.restrict Omega,
      (Wkp.iteratedGradient 1 u x).adjoint = Wkp.iteratedGradient 1 u x := by
  set b := stdOrthonormalBasis ℝ E
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
    Wkp.inner_iteratedGradient_one_apply_ae_eq u (b i) (b j)] with x hx
  -- symmetry along an orthonormal basis gives self-adjointness
  refine (ContinuousLinearMap.coe_injective ?_).symm
  rw [← ContinuousLinearMap.adjoint_toLinearMap]
  refine (LinearMap.eq_adjoint_iff_basis b.toBasis b.toBasis _ _).2 fun i j => ?_
  simpa only [ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis] using
    (hx i j).trans (real_inner_comm _ _).symm

/-- **Symmetry of the third weak derivatives.** For `u ∈ W^{2,p}(Ω)`, if the entry
`⟪D²u w, v⟫ = ∂_w ∂_v u` of the weak Hessian has the weak derivative `G` in the direction `z`,
then the entry `⟪D²u z, v⟫ = ∂_z ∂_v u` has the same weak derivative `G` in the direction `w`.
Together with `TauCeti.Wkp.inner_iteratedGradient_one_apply_ae_eq` this makes the third weak
derivatives `∂_z ∂_w ∂_v u` symmetric in all three directions. -/
theorem Wkp.hasWeakLineDerivOn_inner_iteratedGradient_one_comm (u : Wkp mu Omega p 2)
    {v w z : E} {G : E → ℝ}
    (hG : HasWeakLineDerivOn mu Omega (fun x => ⟪Wkp.iteratedGradient 1 u x w, v⟫_ℝ) G z) :
    HasWeakLineDerivOn mu Omega (fun x => ⟪Wkp.iteratedGradient 1 u x z, v⟫_ℝ) G w := by
  -- `∂_v u ∈ W^{1,p}(Ω)`, whose gradient components are the entries `⟪D²u ·, v⟫`
  obtain ⟨d, -, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value_and_inner_gradient_ae_eq u v
  exact (W1p.hasWeakLineDerivOn_inner_gradient_comm (hG.congr_ae (hd w).symm)).congr_ae (hd z)

/-- **Third derivatives from the tangential ones and the purely normal one.** Let
`u ∈ W^{2,p}(Ω)` with weak Hessian `D²u`. Suppose that `⟪D²u ν, ν⟫` has an `Lᵖ(Ω)` weak
derivative in the direction `ν`, and that every entry `⟪D²u v, τ⟫` with `τ` orthogonal to `ν` has
an `Lᵖ(Ω)` weak derivative in every direction. Then every entry `⟪D²u w, v⟫` has an `Lᵖ(Ω)` weak
derivative in every direction. -/
theorem Wkp.exists_hasWeakLineDerivOn_inner_iteratedGradient_one_of_normal_of_tangential
    (u : Wkp mu Omega p 2) {ν : E}
    (hnor : ∃ G : Lp ℝ p (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪Wkp.iteratedGradient 1 u x ν, ν⟫_ℝ) G ν)
    (htan : ∀ τ v w, ⟪τ, ν⟫_ℝ = 0 → ∃ G : Lp ℝ p (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪Wkp.iteratedGradient 1 u x v, τ⟫_ℝ) G w)
    (v w z : E) : ∃ G : Lp ℝ p (mu.restrict Omega),
      HasWeakLineDerivOn mu Omega (fun x => ⟪Wkp.iteratedGradient 1 u x w, v⟫_ℝ) G z := by
  -- `T v w z`: the entry `⟪D²u w, v⟫` has an `Lᵖ(Ω)` weak derivative in the direction `z`.
  let T : E → E → E → Prop := fun v w z => ∃ G : Lp ℝ p (mu.restrict Omega),
    HasWeakLineDerivOn mu Omega (fun x => ⟪Wkp.iteratedGradient 1 u x w, v⟫_ℝ) G z
  -- `T` is symmetric in `v, w`, since the weak Hessian is, and in `w, z`, since weak derivatives
  -- commute.
  have hvw : ∀ {v w z}, T v w z → T w v z := by
    rintro v w z ⟨G, h⟩
    exact ⟨G, h.congr_ae (Wkp.inner_iteratedGradient_one_apply_ae_eq u w v)⟩
  have hwz : ∀ {v w z}, T v w z → T v z w := by
    rintro v w z ⟨G, h⟩
    exact ⟨G, Wkp.hasWeakLineDerivOn_inner_iteratedGradient_one_comm u h⟩
  have htan' : ∀ v w τ, ⟪τ, ν⟫_ℝ = 0 → T v w τ := fun v w τ hτ => hwz (hvw (htan τ v w hτ))
  -- Split the directions along `ν` and its orthogonal complement, one slot at a time.
  have hνν : ∀ z, T ν ν z := exists_hasWeakLineDerivOn_of_normal_of_tangential hnor (htan' ν ν)
  have hν : ∀ w z, T ν w z := fun w =>
    exists_hasWeakLineDerivOn_of_normal_of_tangential (hwz (hνν w)) (htan' ν w)
  exact exists_hasWeakLineDerivOn_of_normal_of_tangential (hvw (hwz (hvw (hν w v)))) (htan' v w) z

/-! ### Componentwise and graph-norm bounds -/

/-- Componentwise `Lᵖ` bound at order zero: `‖∂_v u‖_{Lᵖ} ≤ ‖v‖ ‖∇u‖_{Lᵖ}`. -/
theorem Wkp.norm_lineDerivL_zero_apply_le (v : E) (u : Wkp mu Omega p 1) :
    ‖Wkp.lineDerivL v 0 u‖ ≤ ‖v‖ * ‖Wkp.iteratedGradient 0 u‖ := by
  rw [Wkp.lineDerivL_zero_apply]
  exact ((innerSL ℝ v).norm_compLp_le _).trans_eq (by rw [innerSL_apply_norm])

/-- Pointwise graph-norm bound at order zero: `‖lineDerivL v 0 u‖ ≤ ‖v‖ * ‖u‖`. -/
theorem Wkp.norm_lineDerivL_zero_apply_le_mul_norm (v : E) (u : Wkp mu Omega p 1) :
    ‖Wkp.lineDerivL v 0 u‖ ≤ ‖v‖ * ‖u‖ :=
  (Wkp.norm_lineDerivL_zero_apply_le v u).trans
    (mul_le_mul_of_nonneg_left (Wkp.norm_iteratedGradient_le 0 u) (norm_nonneg v))

/-- Operator-norm bound `‖lineDerivL v 0‖ ≤ ‖v‖` from `W^{1,p}(Ω)` to `Lᵖ(Ω)`. -/
theorem Wkp.norm_lineDerivL_zero_le (v : E) :
    ‖Wkp.lineDerivL (mu := mu) (Omega := Omega) (p := p) v 0‖ ≤ ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v)
    (Wkp.norm_lineDerivL_zero_apply_le_mul_norm v)

/-- The `Lᵖ` norm of the value of `lineDerivL v k u` is at most `‖v‖` times the `Lᵖ` norm of the
weak gradient of `firstOrder k u`. -/
theorem Wkp.norm_value_lineDerivL_le (v : E) (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    ‖Wkp.value k (Wkp.lineDerivL v k u)‖ ≤ ‖v‖ * ‖W1p.gradient (Wkp.firstOrder k u)‖ := by
  rw [← Wkp.toOrderL_zero_left_apply k (Nat.zero_le k),
    Wkp.toOrderL_lineDerivL v (Nat.zero_le k) u]
  refine (Wkp.norm_lineDerivL_zero_apply_le v _).trans_eq ?_
  rw [Wkp.iteratedGradient_zero, Wkp.toOrderL_one_left_apply]

/-- Componentwise `Lᵖ` bound on the highest weak derivative of `lineDerivL v (j + 1) u`. -/
theorem Wkp.norm_iteratedGradient_lineDerivL_le (v : E) (j : ℕ) (u : Wkp mu Omega p (j + 2)) :
    ‖Wkp.iteratedGradient j (Wkp.lineDerivL v (j + 1) u)‖ ≤
      ‖v‖ * ‖Wkp.iteratedGradient (j + 1) u‖ := by
  rw [Wkp.iteratedGradient_lineDerivL]
  have hv : ‖ContinuousLinearMap.apply ℝ (IteratedGradient E j) v‖ ≤ ‖v‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun G =>
      (G.le_opNorm v).trans_eq (mul_comm _ _)
  exact ((ContinuousLinearMap.apply ℝ (IteratedGradient E j) v).norm_compLp_le _).trans
    (mul_le_mul_of_nonneg_right hv (norm_nonneg _))

/-- Euclidean-stage induction step for `lineDerivL` graph-norm bounds. -/
private theorem Wkp.norm_lineDerivL_succ_apply_le_of_norm_sq {C : ℝ} (hC : 1 ≤ C) (v : E) (k : ℕ)
    (u : Wkp mu Omega p (k + 2))
    (hlow : ‖Wkp.lineDerivL v k (Wkp.lowerOrder (k + 1) u)‖ ≤
      C * ‖v‖ * ‖Wkp.lowerOrder (k + 1) u‖)
    (hd_sq : ‖Wkp.lineDerivL v (k + 1) u‖ ^ 2 =
      ‖Wkp.lowerOrder k (Wkp.lineDerivL v (k + 1) u)‖ ^ 2 +
        ‖Wkp.iteratedGradient k (Wkp.lineDerivL v (k + 1) u)‖ ^ 2) :
    ‖Wkp.lineDerivL v (k + 1) u‖ ≤ C * ‖v‖ * ‖u‖ := by
  have : 0 ≤ C := zero_le_one.trans hC
  have h1C : 1 ≤ C ^ 2 := by nlinarith
  have hlow' : ‖Wkp.lowerOrder k (Wkp.lineDerivL v (k + 1) u)‖ ≤
      C * ‖v‖ * ‖Wkp.lowerOrder (k + 1) u‖ := by
    rwa [Wkp.lowerOrder_lineDerivL]
  have hlow_sq := pow_le_pow_left₀ (norm_nonneg _) hlow' 2
  have htop_sq : ‖Wkp.iteratedGradient k (Wkp.lineDerivL v (k + 1) u)‖ ^ 2 ≤
      C ^ 2 * ‖v‖ ^ 2 * ‖Wkp.iteratedGradient (k + 1) u‖ ^ 2 := by
    refine (pow_le_pow_left₀ (norm_nonneg _)
      (Wkp.norm_iteratedGradient_lineDerivL_le v k u) 2).trans ?_
    rw [mul_pow, mul_assoc]
    exact le_mul_of_one_le_left (by positivity) h1C
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, mul_pow,
    Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u]
  rw [mul_pow, mul_pow] at hlow_sq
  linarith

/-- At exponent `p = 2`, `lineDerivL v k` has graph-norm bound `‖v‖ * ‖u‖` at every order `k`. -/
theorem Wkp.norm_lineDerivL_apply_le_of_exponent_two (v : E) :
    ∀ (k : ℕ) (u : Wkp mu Omega 2 (k + 1)), ‖Wkp.lineDerivL v k u‖ ≤ ‖v‖ * ‖u‖
  | 0, u => Wkp.norm_lineDerivL_zero_apply_le_mul_norm v u
  | k + 1, u => by
      simpa only [one_mul] using Wkp.norm_lineDerivL_succ_apply_le_of_norm_sq le_rfl v k u
        (by simpa only [one_mul] using
          Wkp.norm_lineDerivL_apply_le_of_exponent_two v k (Wkp.lowerOrder (k + 1) u))
        (Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq k _)

/-- Operator-norm bound `‖lineDerivL v k‖ ≤ ‖v‖` at `p = 2` for every order `k`. -/
theorem Wkp.norm_lineDerivL_le_of_exponent_two (v : E) (k : ℕ) :
    ‖Wkp.lineDerivL (mu := mu) (Omega := Omega) (p := 2) v k‖ ≤ ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v)
    (Wkp.norm_lineDerivL_apply_le_of_exponent_two v k)

private theorem Wkp.norm_lineDerivL_one_apply_le (v : E) (u : Wkp mu Omega p 2) :
    ‖Wkp.lineDerivL v 1 u‖ ≤ √2 * ‖v‖ * ‖u‖ := by
  let d := Wkp.lineDerivL v 1 u
  have hlow : ‖Wkp.lowerOrder 0 d‖ ≤ ‖v‖ * ‖Wkp.lowerOrder 1 u‖ := by
    rw [Wkp.lowerOrder_lineDerivL]
    exact Wkp.norm_lineDerivL_zero_apply_le_mul_norm v (Wkp.lowerOrder 1 u)
  have htop := Wkp.norm_iteratedGradient_lineDerivL_le v 0 u
  have hd := Wkp.norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 d
  have hsum : ‖d‖ ≤ ‖v‖ * (‖Wkp.lowerOrder 1 u‖ + ‖Wkp.iteratedGradient 1 u‖) := by linarith
  have hsum_sq := pow_le_pow_left₀ (norm_nonneg d) hsum 2
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, mul_pow, Real.sq_sqrt zero_le_two,
    Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ 0 u]
  nlinarith [sq_nonneg (‖Wkp.lowerOrder 1 u‖ - ‖Wkp.iteratedGradient 1 u‖), sq_nonneg ‖v‖]

/-- **Uniform graph-norm bound for `lineDerivL`.** For every exponent `1 ≤ p ≤ ∞` and every order
`k`, `‖lineDerivL v k u‖ ≤ √2 * ‖v‖ * ‖u‖`. Because every stage from order two upwards uses a
Euclidean product norm on `(lowerOrder, iteratedGradient)`, the factor `√2` from `W^{1,p}` does not
compound at higher orders. -/
theorem Wkp.norm_lineDerivL_apply_le (v : E) :
    ∀ (k : ℕ) (u : Wkp mu Omega p (k + 1)), ‖Wkp.lineDerivL v k u‖ ≤ √2 * ‖v‖ * ‖u‖
  | 0, u => by
      rw [mul_assoc]
      exact (Wkp.norm_lineDerivL_zero_apply_le_mul_norm v u).trans
        (le_mul_of_one_le_left (by positivity) (Real.one_le_sqrt.2 one_le_two))
  | 1, u => Wkp.norm_lineDerivL_one_apply_le v u
  | k + 2, u =>
      Wkp.norm_lineDerivL_succ_apply_le_of_norm_sq (Real.one_le_sqrt.2 one_le_two) v (k + 1) u
        (Wkp.norm_lineDerivL_apply_le v (k + 1) (Wkp.lowerOrder (k + 2) u))
        (Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k _)

/-- Uniform operator-norm bound `‖lineDerivL v k‖ ≤ √2 * ‖v‖` for every `k` and `1 ≤ p ≤ ∞`. -/
theorem Wkp.norm_lineDerivL_le (v : E) (k : ℕ) :
    ‖Wkp.lineDerivL (mu := mu) (Omega := Omega) (p := p) v k‖ ≤ √2 * ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (Wkp.norm_lineDerivL_apply_le v k)

/-- Uniform operator-norm bound `‖lineDerivBilinL k‖ ≤ √2` for the bilinear directional
derivative. -/
theorem Wkp.norm_lineDerivBilinL_le (k : ℕ) :
    ‖Wkp.lineDerivBilinL (E := E) (mu := mu) (Omega := Omega) (p := p) k‖ ≤ √2 :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg 2) fun v => by
    rw [Wkp.lineDerivBilinL_apply]
    exact Wkp.norm_lineDerivL_le v k

/-! ### Second derivatives from the normal and the tangential ones -/

/-- **Second derivatives from the normal one and the tangential ones.** Let `e` be a unit vector,
`P` the orthogonal projection onto the hyperplane orthogonal to `e`, and `U ∈ W^{k+2,p}(Ω)` with
weak derivatives `T τ ∈ W^{k+2,p}(Ω)` along every `τ` orthogonal to `e`. Then the second weak
derivative `∂_w ∂_y U` is `⟪e, y⟫ (⟪e, w⟫ ∂_e ∂_e U + ∂_e T (P w)) + ∂_w T (P y)`. -/
theorem Wkp.value_lineDerivL_lineDerivL_ae_eq {e : E} (he : ‖e‖ = 1) {k : ℕ}
    {U : Wkp mu Omega p (k + 2)} {T : E → Wkp mu Omega p (k + 2)}
    (hT : ∀ τ, ⟪τ, e⟫_ℝ = 0 →
      HasWeakLineDerivOn mu Omega (Wkp.value (k + 2) U) (Wkp.value (k + 2) (T τ)) τ)
    (w y : E) :
    (Wkp.value k (Wkp.lineDerivL w k (Wkp.lineDerivL y (k + 1) U)) : E → ℝ)
      =ᵐ[mu.restrict Omega] fun x =>
        ⟪e, y⟫_ℝ * (⟪e, w⟫_ℝ *
            Wkp.value k (Wkp.lineDerivL e k (Wkp.lineDerivL e (k + 1) U)) x +
          Wkp.value (k + 1) (Wkp.lineDerivL e (k + 1) (T ((ℝ ∙ e)ᗮ.starProjection w))) x) +
        Wkp.value (k + 1) (Wkp.lineDerivL w (k + 1) (T ((ℝ ∙ e)ᗮ.starProjection y))) x := by
  set P := (ℝ ∙ e)ᗮ.starProjection
  have hP : ∀ z, ⟪P z, e⟫_ℝ = 0 := inner_starProjection_orthogonal_singleton_eq_zero ℝ e
  have hLp : ∀ (c : ℝ) (X Y : Lp ℝ p (mu.restrict Omega)),
      (⇑(c • X + Y) : E → ℝ) =ᵐ[mu.restrict Omega] c • ⇑X + ⇑Y := fun c X Y => by
    filter_upwards [Lp.coeFn_add (c • X) Y, Lp.coeFn_smul c X] with x h₁ h₂
    rw [h₁, Pi.add_apply, h₂, Pi.add_apply]
  have hDe := Wkp.hasWeakLineDerivOn_lineDerivL e (k + 1) U
  -- `∂_y U = ⟪e, y⟫ ∂_e U + T (P y)`.
  have h₁ := (Wkp.hasWeakLineDerivOn_lineDerivL y (k + 1) U).ae_eq
    (hDe.smul_add_of_normal_tangential he (hT _ (hP y)))
  -- `∂_w ∂_e U = ⟪e, w⟫ ∂_e ∂_e U + ∂_e T (P w)`, since `∂_{P w} ∂_e U = ∂_e ∂_{P w} U`.
  have hDew := (Wkp.hasWeakLineDerivOn_lineDerivL e k
    (Wkp.lineDerivL e (k + 1) U)).smul_add_of_normal_tangential he
    ((hT _ (hP w)).comm (Wkp.hasWeakLineDerivOn_lineDerivL e (k + 1) (T (P w))) hDe)
  have h₂ := ((hDew.const_smul ⟪e, y⟫_ℝ).add
    (Wkp.hasWeakLineDerivOn_lineDerivL w (k + 1) (T (P y)))).congr_ae (h₁.trans (hLp _ _ _)).symm
  filter_upwards [(Wkp.hasWeakLineDerivOn_lineDerivL w k (Wkp.lineDerivL y (k + 1) U)).ae_eq h₂,
    hLp ⟪e, w⟫_ℝ (Wkp.value k (Wkp.lineDerivL e k (Wkp.lineDerivL e (k + 1) U)))
      (Wkp.value (k + 1) (Wkp.lineDerivL e (k + 1) (T (P w))))] with x hx hx'
  rw [hx, Pi.add_apply, Pi.smul_apply, hx', Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]

/-- **Second derivatives through the weak gradient.** Under the hypotheses of
`TauCeti.Wkp.value_lineDerivL_lineDerivL_ae_eq`, the component along `w` of the weak gradient of
the first derivative `∂_y U ∈ W^{1,p}(Ω)` is
`⟪e, w⟫ ⟪e, y⟫ ∂_e ∂_e U + ⟪e, y⟫ ∂_e T (P w) + ∂_w T (P y)`. -/
theorem Wkp.ae_inner_gradient_firstOrder_lineDerivL_eq {e : E} (he : ‖e‖ = 1) {k : ℕ}
    {U : Wkp mu Omega p (k + 2)} {T : E → Wkp mu Omega p (k + 2)}
    (hT : ∀ τ, ⟪τ, e⟫_ℝ = 0 →
      HasWeakLineDerivOn mu Omega (Wkp.value (k + 2) U) (Wkp.value (k + 2) (T τ)) τ)
    (w y : E) :
    ∀ᵐ x ∂mu.restrict Omega,
      ⟪W1p.gradient (Wkp.firstOrder k (Wkp.lineDerivL y (k + 1) U)) x, w⟫_ℝ =
        ⟪e, w⟫_ℝ * ⟪e, y⟫_ℝ * Wkp.value k (Wkp.lineDerivL e k (Wkp.lineDerivL e (k + 1) U)) x +
          Wkp.value (k + 1) (⟪e, y⟫_ℝ • Wkp.lineDerivL e (k + 1) (T ((ℝ ∙ e)ᗮ.starProjection w)) +
            Wkp.lineDerivL w (k + 1) (T ((ℝ ∙ e)ᗮ.starProjection y))) x := by
  have h :=
    (W1p.hasWeakFDerivOn (Wkp.firstOrder k (Wkp.lineDerivL y (k + 1) U))).hasWeakLineDerivOn w
  rw [Wkp.value_firstOrder] at h
  filter_upwards [h.ae_eq (Wkp.hasWeakLineDerivOn_lineDerivL w k (Wkp.lineDerivL y (k + 1) U)),
    Wkp.value_lineDerivL_lineDerivL_ae_eq he hT w y,
    Wkp.value_add_ae (k + 1)
      (⟪e, y⟫_ℝ • Wkp.lineDerivL e (k + 1) (T ((ℝ ∙ e)ᗮ.starProjection w)))
      (Wkp.lineDerivL w (k + 1) (T ((ℝ ∙ e)ᗮ.starProjection y))),
    Wkp.value_smul_ae (k + 1) ⟪e, y⟫_ℝ
      (Wkp.lineDerivL e (k + 1) (T ((ℝ ∙ e)ᗮ.starProjection w)))] with x h₁ h₂ h₃ h₄
  rw [← innerSL_apply_apply, h₁, h₂, h₃, Pi.add_apply, h₄, Pi.smul_apply, smul_eq_mul]
  ring

end TauCeti
