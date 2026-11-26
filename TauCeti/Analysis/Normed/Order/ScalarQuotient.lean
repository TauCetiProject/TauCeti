/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Order.StateSpace
public import TauCeti.Analysis.Normed.Module.Dual.Quotient
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic

/-!
# The scalar quotient of an order-unit space

The norm modulo the scalar line is half the oscillation of the evaluation function on the weak-*
state space. Subtracting the midpoint of the extreme evaluations gives a norm-minimizing
representative.

The continuous dual of this quotient is the annihilator of the order unit, by
`Submodule.quotientDualEquivAnnihilator`. Its closed ball of radius two consists exactly of
differences of states when pulled back to the original space. This normalization lets one compare
state distances with seminorm bounds on the quotient.

## References

* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, Lemma 2.1.
-/

public section

open Set WeakDual
open scoped Pointwise

namespace TauCeti

namespace IsOrderUnitNorm

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E}

private theorem quotient_norm_at_extrema (h : IsOrderUnitNorm e) (a : E)
    {φ ψ : OrderUnit.stateSpace e}
    (hφ : ∀ θ : OrderUnit.stateSpace e, θ.val a ≤ φ.val a)
    (hψ : ∀ θ : OrderUnit.stateSpace e, ψ.val a ≤ θ.val a) :
    ‖(Submodule.Quotient.mk a : E ⧸ (ℝ ∙ e))‖ = (φ.val a - ψ.val a) / 2 ∧
      ‖a - ((φ.val a + ψ.val a) / 2) • e‖ = (φ.val a - ψ.val a) / 2 := by
  let midpoint := (φ.val a + ψ.val a) / 2
  let radius := (φ.val a - ψ.val a) / 2
  have hr : 0 ≤ radius := by dsimp [radius]; linarith [hφ ψ]
  have eval_sub (θ : OrderUnit.stateSpace e) (c : ℝ) :
      θ.val (a - c • e) = θ.val a - c := by
    simp [OrderUnit.apply_eq_one_of_mem_stateSpace θ.property]
  have lower (c : ℝ) : radius ≤ ‖a - c • e‖ := by
    have hu := (abs_le.mp (h.abs_apply_le_of_mem_stateSpace φ.property (a - c • e))).2
    have hl := (abs_le.mp (h.abs_apply_le_of_mem_stateSpace ψ.property (a - c • e))).1
    rw [eval_sub] at hu hl
    dsimp [radius]
    linarith
  have upper : ‖a - midpoint • e‖ ≤ radius :=
    (h.norm_le_iff_forall_mem_stateSpace hr).2 fun θ hθ => by
      rw [eval_sub ⟨θ, hθ⟩, abs_le]
      dsimp [midpoint, radius]
      constructor
      · linarith [hψ ⟨θ, hθ⟩]
      · linarith [hφ ⟨θ, hθ⟩]
  have mk_sub (c : ℝ) :
      (Submodule.Quotient.mk (a - c • e) : E ⧸ (ℝ ∙ e)) = Submodule.Quotient.mk a := by
    have hc : c • e ∈ ℝ ∙ e := Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e)
    simp [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).mpr hc]
  refine ⟨le_antisymm ?_ ?_, le_antisymm upper (lower midpoint)⟩
  · rw [← mk_sub midpoint]
    exact (Submodule.Quotient.norm_mk_le _ _).trans upper
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨b, hb, hn⟩ := Submodule.Quotient.norm_mk_lt (Submodule.Quotient.mk (p := ℝ ∙ e) a) hε
    have hab : a - b ∈ ℝ ∙ e := (Submodule.Quotient.eq (ℝ ∙ e)).mp hb.symm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hab
    have : b = a - c • e := by rw [hc]; abel
    exact (this ▸ lower c : radius ≤ ‖b‖).trans hn.le

private theorem quotient_norm_formulas (h : IsOrderUnitNorm e) (a : E) :
    let upper := ⨆ φ : OrderUnit.stateSpace e, φ.val a
    let lower := ⨅ φ : OrderUnit.stateSpace e, φ.val a
    let q := (Submodule.Quotient.mk a : E ⧸ (ℝ ∙ e))
    ‖q‖ = (upper - lower) / 2 ∧ ‖a - ((upper + lower) / 2) • e‖ = ‖q‖ := by
  dsimp
  have hc : ContinuousOn (fun φ : WeakDual ℝ E => φ a) (OrderUnit.stateSpace e) :=
    (eval_continuous a).continuousOn
  obtain ⟨φ, hφ, hmax⟩ := h.isCompact_stateSpace.exists_isMaxOn h.stateSpace_nonempty hc
  obtain ⟨ψ, hψ, hmin⟩ := h.isCompact_stateSpace.exists_isMinOn h.stateSpace_nonempty hc
  have hs : (⨆ θ : OrderUnit.stateSpace e, θ.val a) = φ a :=
    IsGreatest.csSup_eq ⟨⟨⟨φ, hφ⟩, rfl⟩, by rintro _ ⟨θ, rfl⟩; exact hmax θ.property⟩
  have hi : (⨅ θ : OrderUnit.stateSpace e, θ.val a) = ψ a :=
    IsLeast.csInf_eq ⟨⟨⟨ψ, hψ⟩, rfl⟩, by rintro _ ⟨θ, rfl⟩; exact hmin θ.property⟩
  obtain ⟨hq, ha⟩ := h.quotient_norm_at_extrema a (φ := ⟨φ, hφ⟩) (ψ := ⟨ψ, hψ⟩)
    (fun θ => hmax θ.property) (fun θ => hmin θ.property)
  rw [hs, hi]
  exact ⟨hq, ha.trans hq.symm⟩

/-- The quotient norm modulo the order unit is half the oscillation over states. -/
theorem norm_quotient_mk_eq_half_sub (h : IsOrderUnitNorm e) (a : E) :
    ‖(Submodule.Quotient.mk a : E ⧸ (ℝ ∙ e))‖ =
      ((⨆ φ : OrderUnit.stateSpace e, φ.val a) - (⨅ φ : OrderUnit.stateSpace e, φ.val a)) / 2 :=
  (h.quotient_norm_formulas a).1

/-- The quotient norm is achieved by subtracting the midpoint of the extreme state evaluations. -/
theorem norm_sub_midpoint_smul_eq_norm_quotient_mk (h : IsOrderUnitNorm e) (a : E) :
    ‖a - (((⨆ φ : OrderUnit.stateSpace e, φ.val a) +
      (⨅ φ : OrderUnit.stateSpace e, φ.val a)) / 2) • e‖ =
      ‖(Submodule.Quotient.mk a : E ⧸ (ℝ ∙ e))‖ :=
  (h.quotient_norm_formulas a).2

/-- The line spanned by the order unit is closed in the order-unit norm. -/
theorem isClosed_span_singleton (h : IsOrderUnitNorm e) :
    IsClosed ((ℝ ∙ e : Submodule ℝ E) : Set E) := by
  have := h.orderClosedTopology
  exact (ℝ ∙ e).isClosed_of_finiteDimensional

/-- Differences of states are exactly the functionals vanishing at the order unit and of norm
at most two. -/
theorem stateSpace_sub_stateSpace (h : IsOrderUnitNorm e) :
    OrderUnit.stateSpace e - OrderUnit.stateSpace e =
      {f | f e = 0 ∧ ‖toStrongDual f‖ ≤ 2} := by
  ext f
  constructor
  · rintro ⟨φ, hφ, ψ, hψ, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← toStrongDual_apply (φ - ψ), map_sub]
      simp [OrderUnit.apply_eq_one_of_mem_stateSpace hφ,
        OrderUnit.apply_eq_one_of_mem_stateSpace hψ]
    · calc
        ‖toStrongDual (φ - ψ)‖ ≤ ‖toStrongDual φ‖ + ‖toStrongDual ψ‖ :=
          map_sub toStrongDual φ ψ ▸ norm_sub_le _ _
        _ = 2 := by rw [h.norm_toStrongDual_of_mem_stateSpace hφ,
          h.norm_toStrongDual_of_mem_stateSpace hψ]; norm_num
  · rintro ⟨hf, hn⟩
    by_contra hmem
    -- Weak-* separation would give an evaluation strictly larger than the state oscillation.
    have hconv := OrderUnit.convex_stateSpace (e := e)
    have hclosed : IsClosed (OrderUnit.stateSpace e - OrderUnit.stateSpace e) := by
      rw [← Set.sub_image_prod]
      exact ((h.isCompact_stateSpace.prod h.isCompact_stateSpace).image continuous_sub).isClosed
    obtain ⟨ℓ, u, hl, hlf⟩ := geometric_hahn_banach_closed_point
      (hconv.sub hconv) hclosed hmem
    obtain ⟨a, hℓ⟩ := exists_forall_apply_eq_apply ℓ
    rw [hℓ] at hlf
    let upper := ⨆ φ : OrderUnit.stateSpace e, φ.val a
    let lower := ⨅ ψ : OrderUnit.stateSpace e, ψ.val a
    let : Nonempty (OrderUnit.stateSpace e) := h.stateSpace_nonempty.to_subtype
    have hosc : upper - lower ≤ u := by
      rw [sub_le_iff_le_add]
      refine ciSup_le fun φ => ?_
      rw [← sub_le_iff_le_add']
      refine le_ciInf fun ψ => ?_
      have hlt := hl _ (Set.sub_mem_sub φ.property ψ.property)
      rw [map_sub, hℓ, hℓ] at hlt
      linarith
    -- Centering at the midpoint leaves the evaluation by `f` invariant.
    let b := a - ((upper + lower) / 2) • e
    have hb : ‖b‖ = (upper - lower) / 2 :=
      (h.norm_sub_midpoint_smul_eq_norm_quotient_mk a).trans (h.norm_quotient_mk_eq_half_sub a)
    have hfb : (toStrongDual f) b = f a := by simp [b, hf]
    have hbound := (toStrongDual f).le_of_opNorm_le_of_le hn (le_refl ‖b‖)
    rw [hfb, hb, Real.norm_eq_abs] at hbound
    linarith [le_abs_self (f a)]

/-- A functional on the scalar quotient pulls back to a difference of two states exactly when its
operator norm is at most two. -/
theorem quotientDualEquivAnnihilator_mem_stateSpace_sub_iff (h : IsOrderUnitNorm e)
    (f : StrongDual ℝ (E ⧸ (ℝ ∙ e))) :
    StrongDual.toWeakDual ((ℝ ∙ e).quotientDualEquivAnnihilator f : StrongDual ℝ E) ∈
      OrderUnit.stateSpace e - OrderUnit.stateSpace e ↔ ‖f‖ ≤ 2 := by
  have he : ((ℝ ∙ e).quotientDualEquivAnnihilator f : StrongDual ℝ E) e = 0 := by
    rw [Submodule.quotientDualEquivAnnihilator_apply,
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self e), map_zero]
  have hn : ‖((ℝ ∙ e).quotientDualEquivAnnihilator f : StrongDual ℝ E)‖ = ‖f‖ :=
    (ℝ ∙ e).quotientDualEquivAnnihilator.norm_map f
  simp only [h.stateSpace_sub_stateSpace, Set.mem_ofPred_eq, StrongDual.toWeakDual_apply,
    StrongDual.toStrongDual_toWeakDual, he, hn, true_and]

end IsOrderUnitNorm

end TauCeti
