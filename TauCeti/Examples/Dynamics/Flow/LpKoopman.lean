/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.LpKoopman
public import TauCeti.Topology.Instances.AddCircle.Flow
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Checks: the `Lᵖ` pullback representation of the circle translations

For `ℝ` acting on `UnitAddCircle` by the unit-speed flow `t +ᵥ x = x + t`
(`AddCircle.translationFlow 1`) and `f = 1_[0,1/2)`:

* `‖π(t) f - f‖_p → 0` as `t → 0` for every `1 ≤ p < ∞`, in particular for `p = 2`;
* `‖π(t) f - f‖_∞ = 1` for `0 < |t| < 1/2`, so the orbit is not continuous in `L^∞`.

For a trivial action, `π(g) = 1` for every `g` (`TauCeti.lpKoopman_eq_one_of_forall_smul_eq`); this
is checked on the trivial action of any group on any measure space.
-/

public section

open MeasureTheory TauCeti Set Filter Topology
open scoped ENNReal symmDiff

namespace TauCeti.Examples.FlowLpKoopman

/-! ### The trivial action -/

section Trivial

variable {G X : Type*} [Group G] [MeasurableSpace X] (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure X)

/-- **Check.** For the trivial action of a group `G` on `X`, `g • x = x`, every `π(g)` is the
identity of `Lᵖ(X, μ)`. -/
theorem lpKoopman_trivial (g : G) :
    letI : MulAction G X := MulAction.compHom X (1 : G →* Function.End X)
    lpKoopman ℂ ℂ p μ (fun _ ↦ MeasurePreserving.id μ) g = 1 :=
  letI : MulAction G X := MulAction.compHom X (1 : G →* Function.End X)
  lpKoopman_eq_one_of_forall_smul_eq (fun _ _ ↦ rfl) g

end Trivial

/-! ### The circle translations -/

/-- The unit-speed flow on the circle preserves the Haar measure. -/
theorem measurePreserving_translationFlow (t : ℝ) :
    MeasurePreserving (AddCircle.translationFlow (1 : ℝ) t) volume volume := by
  have h : AddCircle.translationFlow (1 : ℝ) t = (· + (t : UnitAddCircle)) :=
    funext fun x ↦ AddCircle.translationFlow_apply 1 t x
  rw [h]
  exact measurePreserving_add_right volume _

/-- The arc `[0, 1/2)` of the circle. -/
noncomputable def halfArc : Set UnitAddCircle := ((↑) : ℝ → UnitAddCircle) '' Ico 0 (1 / 2)

/-- The arc `[0, 1/2)` is the open arc `(0, 1/2)` together with the point `0`. -/
theorem halfArc_eq :
    halfArc = ((↑) : ℝ → UnitAddCircle) '' Ioo 0 (1 / 2) ∪ {((0 : ℝ) : UnitAddCircle)} := by
  rw [halfArc, ← insert_left_Ioo (by norm_num : (0 : ℝ) < 1 / 2), image_insert_eq, insert_eq,
    union_comm]

/-- The arc `[0, 1/2)` is measurable. -/
theorem measurableSet_halfArc : MeasurableSet halfArc := by
  rw [halfArc_eq]
  exact (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo).measurableSet.union
    (measurableSet_singleton _)

/-- The indicator `1_[0,1/2)` as an `Lᵖ` class on the circle. -/
noncomputable abbrev halfArcLp (p : ℝ≥0∞) :
    Lp ℂ p (volume : Measure UnitAddCircle) :=
  indicatorConstLp p measurableSet_halfArc (measure_ne_top _ _) 1

/-- The pullback representation of the unit-speed flow on `Lᵖ(UnitAddCircle)`. -/
noncomputable abbrev circleKoopman (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ContRepresentation ℂ (Multiplicative ℝ) (Lp ℂ p (volume : Measure UnitAddCircle)) :=
  Flow.lpKoopman ℂ ℂ p volume (AddCircle.translationFlow 1) measurePreserving_translationFlow

/-- **Check.** For `1 ≤ p < ∞`, in particular `p = 2`, `‖π(t) 1_[0,1/2) - 1_[0,1/2)‖_p → 0` as
`t → 0`. -/
theorem tendsto_circleKoopman_halfArc (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Tendsto (fun t : ℝ ↦ ‖circleKoopman p (Multiplicative.ofAdd t) (halfArcLp p) - halfArcLp p‖)
      (𝓝 0) (𝓝 0) := by
  have h := (Flow.continuous_lpKoopman_apply hp (halfArcLp p)
    (ϕ := AddCircle.translationFlow 1) (hϕ := measurePreserving_translationFlow)
    (𝕜 := ℂ)).tendsto 0
  rw [ofAdd_zero, map_one, one_apply_eq_self] at h
  simpa using (tendsto_iff_norm_sub_tendsto_zero.1 h)

/-- For `0 < t < 1/2`, the open arc `(1/2, 1/2 + t)` lies in `(halfArc + t) \ halfArc`. -/
theorem image_Ioo_subset_symmDiff {t : ℝ} (ht₀ : 0 < t) (ht : t < 1 / 2) :
    ((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 2) (1 / 2 + t) ⊆
      (AddCircle.translationFlow 1 (-t) ⁻¹' halfArc) ∆ halfArc := by
  rintro _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
  refine Or.inl ⟨⟨x - t, ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
  · simp [sub_eq_add_neg]
  · rintro ⟨y, ⟨hy₁, hy₂⟩, hxy⟩
    rw [eq_comm, AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0)] at hxy
    · linarith
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨hy₁, by linarith⟩

/-- **Check.** In `L^∞`, `‖π(t) 1_[0,1/2) - 1_[0,1/2)‖ = 1` for `0 < t < 1/2`. -/
theorem norm_circleKoopman_halfArc_sub_top {t : ℝ} (ht₀ : 0 < t) (ht : t < 1 / 2) :
    ‖circleKoopman ∞ (Multiplicative.ofAdd t) (halfArcLp ∞) - halfArcLp ∞‖ = 1 := by
  rw [Flow.lpKoopman_apply, Lp.indicatorConstLp_compMeasurePreserving, ← dist_eq_norm,
    dist_indicatorConstLp_eq_norm, norm_indicatorConstLp_top, norm_one]
  exact (((QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo).measure_pos volume
    ((nonempty_Ioo.2 (by linarith)).image _)).trans_le
      (measure_mono (image_Ioo_subset_symmDiff ht₀ ht))).ne'

/-- **Check.** In `L^∞`, `‖π(t) 1_[0,1/2) - 1_[0,1/2)‖ = 1` for `0 < |t| < 1/2`. -/
theorem norm_circleKoopman_halfArc_sub_top_of_abs_lt {t : ℝ} (ht₀ : t ≠ 0) (ht : |t| < 1 / 2) :
    ‖circleKoopman ∞ (Multiplicative.ofAdd t) (halfArcLp ∞) - halfArcLp ∞‖ = 1 := by
  rcases ht₀.lt_or_gt with h | h
  · set U := circleKoopman ∞
    set f := halfArcLp ∞
    have hinv : U (Multiplicative.ofAdd (-t)) (U (Multiplicative.ofAdd t) f) = f := by
      rw [← mul_apply_eq_comp, ← Flow.lpKoopman_add, neg_add_cancel, Flow.lpKoopman_zero,
        one_apply_eq_self]
    rw [← Flow.norm_lpKoopman_apply (𝕜 := ℂ) (hϕ := measurePreserving_translationFlow)
      (Multiplicative.ofAdd (-t)), map_sub, hinv, norm_sub_rev]
    exact norm_circleKoopman_halfArc_sub_top (by linarith)
      (by rw [abs_of_neg h] at ht; linarith)
  · exact norm_circleKoopman_halfArc_sub_top h (by rwa [abs_of_pos h] at ht)

end TauCeti.Examples.FlowLpKoopman
