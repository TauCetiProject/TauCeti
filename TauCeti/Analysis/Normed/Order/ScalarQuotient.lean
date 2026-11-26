/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Order.StateSpace
public import TauCeti.Analysis.Normed.Module.Dual.Quotient
import TauCeti.Analysis.Normed.Module.HahnBanach.Basic
import TauCeti.Analysis.Normed.Order.PositiveLinearMap
import TauCeti.MeasureTheory.Integral.RieszMarkovKakutani.Signed

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
open scoped CompactlySupported Pointwise

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
theorem isClosed_scalarLine (h : IsOrderUnitNorm e) :
    IsClosed ((ℝ ∙ e : Submodule ℝ E) : Set E) := by
  refine closure_subset_iff_isClosed.mp fun a ha => ?_
  have hq : ‖(Submodule.Quotient.mk a : E ⧸ (ℝ ∙ e))‖ = 0 :=
    QuotientAddGroup.norm_mk_eq_zero_iff_mem_closure.mpr ha
  let midpoint := ((⨆ φ : OrderUnit.stateSpace e, φ.val a) +
    (⨅ φ : OrderUnit.stateSpace e, φ.val a)) / 2
  have hn : ‖a - midpoint • e‖ ≤ 0 :=
    ((h.norm_sub_midpoint_smul_eq_norm_quotient_mk a).trans hq).le
  obtain ⟨hl, hu⟩ := (h.norm_le_iff (le_refl (0 : ℝ))).mp hn
  simp only [zero_smul, neg_zero] at hl hu
  have heq : a - midpoint • e = 0 := le_antisymm hu hl
  exact Submodule.mem_span_singleton.mpr ⟨midpoint, (sub_eq_zero.mp heq).symm⟩

private theorem exists_extension_stateSpaceEval (h : IsOrderUnitNorm e) (f : StrongDual ℝ E) :
    let := isCompact_iff_compactSpace.mp h.isCompact_stateSpace
    ∃ g : StrongDual ℝ C(OrderUnit.stateSpace e, ℝ),
      (∀ a, g (h.stateSpaceEval a) = f a) ∧ ‖g‖ = ‖f‖ := by
  let := isCompact_iff_compactSpace.mp h.isCompact_stateSpace
  let : NormedAddCommGroup E := .ofSeparation fun a ha => by
    obtain ⟨hl, hu⟩ := (h.norm_le_iff (le_refl (0 : ℝ))).mp ha.le
    simp only [zero_smul, neg_zero] at hl hu
    exact le_antisymm hu hl
  obtain ⟨g, hg, hg_norm⟩ := h.stateSpaceEval.exists_extension_norm_eq f
  exact ⟨g, fun a => DFunLike.congr_fun hg a, hg_norm⟩

private theorem exists_state_of_positive (h : IsOrderUnitNorm e) {ω : WeakDual ℝ E}
    (hω : ω ∈ OrderUnit.stateSpace e) (P : C_c(OrderUnit.stateSpace e, ℝ) →ₚ[ℝ] ℝ) :
    let := isCompact_iff_compactSpace.mp h.isCompact_stateSpace
    let v := CompactlySupportedContinuousMap.continuousMapEquiv
      (α := OrderUnit.stateSpace e) (β := ℝ)
    P (v 1) ≤ 1 → ∃ φ ∈ OrderUnit.stateSpace e, ∀ a,
      φ a = P (v (h.stateSpaceEval a)) + (1 - P (v 1)) * ω a := by
  dsimp only
  intro hp
  let := isCompact_iff_compactSpace.mp h.isCompact_stateSpace
  let v := CompactlySupportedContinuousMap.continuousMapEquiv (α := OrderUnit.stateSpace e)
    (β := ℝ)
  let slack := 1 - P (v 1)
  let p : E →ₚ[ℝ] ℝ :=
    { toLinearMap :=
        { toFun := fun a => P (v (h.stateSpaceEval a)) + slack * ω a
          map_add' := fun a b => by
            have hab : v (h.stateSpaceEval (a + b)) =
                v (h.stateSpaceEval a) + v (h.stateSpaceEval b) := by
              ext x
              simp [v]
            rw [hab, map_add, map_add, mul_add, add_add_add_comm]
          map_smul' := fun c a => by
            have hca : v (h.stateSpaceEval (c • a)) = c • v (h.stateSpaceEval a) := by
              ext x
              simp [v]
            rw [hca, map_smul, map_smul]
            simp only [smul_eq_mul, RingHom.id_apply]
            ring }
      monotone' := fun a b hab =>
        add_le_add (OrderHomClass.mono P (fun x => h.stateSpaceEval_le_stateSpaceEval.mpr hab x))
          (mul_le_mul_of_nonneg_left (OrderUnit.monotone_of_mem_stateSpace hω hab)
            (sub_nonneg.mpr hp)) }
  let φ : WeakDual ℝ E := StrongDual.toWeakDual
    ⟨p.toLinearMap, PositiveLinearMap.continuous_of_forall_le_norm_smul p h.le_norm_smul⟩
  have eval_φ (a : E) : φ a = P (v (h.stateSpaceEval a)) + slack * ω a := rfl
  refine ⟨φ, OrderUnit.mem_stateSpace_iff.mpr ⟨OrderHomClass.mono p, ?_⟩, eval_φ⟩
  rw [eval_φ, h.stateSpaceEval_orderUnit, OrderUnit.apply_eq_one_of_mem_stateSpace hω]
  simp [slack]

/- Extend the functional to the continuous real functions on the state space and use the Jordan
parts `RealRMK.posPart` and `RealRMK.negPart`. Both parts have the same value at the constant one,
so a common positive correction normalizes them and cancels in the difference. -/
private theorem exists_states_sub_eq (h : IsOrderUnitNorm e) {f : StrongDual ℝ E}
    (hf : f e = 0) (hn : ‖f‖ ≤ 2) :
    ∃ φ ∈ OrderUnit.stateSpace e, ∃ ψ ∈ OrderUnit.stateSpace e,
      φ - ψ = StrongDual.toWeakDual f := by
  let := isCompact_iff_compactSpace.mp h.isCompact_stateSpace
  obtain ⟨g, hg, hg_norm⟩ := h.exists_extension_stateSpaceEval f
  have hg1 : g 1 = 0 := by simpa [hf] using hg e
  let Λ : C_c(OrderUnit.stateSpace e, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun u => g u.toContinuousMap
      map_add' := fun u v => map_add g u.toContinuousMap v.toContinuousMap
      map_smul' := fun c u => map_smul g c u.toContinuousMap }
  have hΛ (u : C_c(OrderUnit.stateSpace e, ℝ)) : BddAbove (Λ '' Icc 0 u) := by
    refine ⟨‖g‖ * ‖u.toContinuousMap‖, ?_⟩
    rintro _ ⟨v, ⟨hv₀, hvu⟩, rfl⟩
    apply (le_abs_self _).trans ((g.le_opNorm v.toContinuousMap).trans ?_)
    refine mul_le_mul_of_nonneg_left ((ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_)
      (norm_nonneg g)
    rw [Real.norm_eq_abs, CompactlySupportedContinuousMap.coe_toContinuousMap,
      abs_of_nonneg (hv₀ x)]
    exact (hvu x).trans ((le_abs_self _).trans (u.toContinuousMap.norm_coe_le_norm x))
  let v := CompactlySupportedContinuousMap.continuousMapEquiv (α := OrderUnit.stateSpace e)
    (β := ℝ)
  let p := RealRMK.posPart Λ hΛ
  let n := RealRMK.negPart Λ hΛ
  have hp : p (v 1) ≤ 1 := by
    refine RealRMK.posPart_apply_le hΛ (fun x => zero_le_one) fun u hu hu₁ => ?_
    have htest : ‖(2 : ℝ) • u.toContinuousMap - 1‖ ≤ 1 := by
      refine (ContinuousMap.norm_le _ zero_le_one).2 fun x => ?_
      have h₀ : 0 ≤ u x := hu x
      have h₁ : u x ≤ 1 := hu₁ x
      simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
        CompactlySupportedContinuousMap.coe_toContinuousMap, smul_eq_mul, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hbound := g.le_of_opNorm_le_of_le (hg_norm ▸ hn) htest
    rw [map_sub, map_smul, smul_eq_mul, hg1, sub_zero] at hbound
    dsimp [Λ]
    linarith [(le_abs_self _).trans hbound, htest]
  have hp_eq : p (v 1) = n (v 1) := by
    have := RealRMK.posPart_sub_negPart_apply hΛ (v 1)
    have hz : Λ (v 1) = 0 := hg1
    exact sub_eq_zero.mp (this.trans hz)
  obtain ⟨ω, hω⟩ := h.stateSpace_nonempty
  obtain ⟨φ, hφ, hφa⟩ := h.exists_state_of_positive hω p hp
  obtain ⟨ψ, hψ, hψa⟩ := h.exists_state_of_positive hω n (hp_eq ▸ hp)
  refine ⟨φ, hφ, ψ, hψ, DFunLike.ext _ _ fun a => ?_⟩
  rw [← toStrongDual_apply (φ - ψ), map_sub, sub_apply, toStrongDual_apply, toStrongDual_apply,
    hφa, hψa, ← hp_eq, add_sub_add_right_eq_sub]
  rw [RealRMK.posPart_sub_negPart_apply hΛ]
  exact hg a

/-- Differences of states are exactly the functionals vanishing at the order unit and of norm
at most two. -/
theorem stateSpace_sub_stateSpace (h : IsOrderUnitNorm e) :
    OrderUnit.stateSpace e - OrderUnit.stateSpace e =
      {f | f e = 0 ∧ ‖toStrongDual f‖ ≤ 2} := by
  ext f
  constructor
  · rintro ⟨φ, hφ, ψ, hψ, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← toStrongDual_apply, map_sub, sub_apply, toStrongDual_apply,
        toStrongDual_apply, OrderUnit.apply_eq_one_of_mem_stateSpace hφ,
        OrderUnit.apply_eq_one_of_mem_stateSpace hψ, sub_self]
    · calc
        ‖toStrongDual (φ - ψ)‖ ≤ ‖toStrongDual φ‖ + ‖toStrongDual ψ‖ :=
          map_sub toStrongDual φ ψ ▸ norm_sub_le _ _
        _ = 2 := by rw [h.norm_toStrongDual_of_mem_stateSpace hφ,
          h.norm_toStrongDual_of_mem_stateSpace hψ]; norm_num
  · rintro ⟨hf, hn⟩
    obtain ⟨φ, hφ, ψ, hψ, heq⟩ := h.exists_states_sub_eq (f := toStrongDual f) hf hn
    exact ⟨φ, hφ, ψ, hψ, heq.trans (toWeakDual_toStrongDual f)⟩

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
