/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
-- Private: used only inside proofs.
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import TauCeti.Analysis.Calculus.Deriv.Growth
import TauCeti.Analysis.ODE.ExistUnique
import TauCeti.Analysis.ODE.GlobalSolution

/-!
# The orbit joining two consecutive equilibria of a scalar equation

Let `V : ℝ → ℝ` be a vector field on the line, `a < b` two zeros of `V`, and suppose `V > 0` on
`(a, b)`. Then the autonomous equation `x' = V x` has a solution joining the equilibrium `a` to the
equilibrium `b`, and only one up to translation of time:

* if `V` is Lipschitz on `[a, b]`, there is a solution defined on all of `ℝ`, strictly increasing,
  with values in `(a, b)`, which tends to `a` at `-∞` and to `b` at `+∞`
  (`TauCeti.exists_isIntegralCurve_tendsto_of_pos`);
* if `V` is locally Lipschitz on `(a, b)`, every solution tending to `a` at `-∞` and to `b` at
  `+∞` is a time translate of any solution with values in `(a, b)`
  (`TauCeti.exists_eq_comp_add_of_isIntegralCurve_of_tendsto`).

The solution is the global solution through the midpoint of the field `V` composed with the
projection onto `[a, b]`, which is globally Lipschitz and agrees with `V` on `[a, b]`. It cannot
reach `a` or `b`, where it would be constant, so it stays in `(a, b)` and is strictly increasing.
Its limits at `±∞` are zeros of `V` in `[a, b]`, hence `a` and `b`. For uniqueness, any solution
from `a` to `b` takes the value of the given solution at time `0`, by the intermediate value
theorem, and two solutions which agree once agree everywhere when the field is locally Lipschitz
along one of them.

In Morse theory, applied to `V = -h'` for a function `h` of one variable, this says that two
consecutive critical points of `h` are joined by exactly one unparametrized negative gradient
trajectory.
-/

public section

open Filter Set Topology
open scoped NNReal

namespace TauCeti

variable {V : ℝ → ℝ} {a b : ℝ}

/-- A monotone solution of `x' = W x`, for a continuous field `W`, with values in `(a, b)`, tends to
`a` at `-∞` and to `b` at `+∞` when `a` and `b` are the only zeros of `W` in `[a, b]`: its limits
exist by monotonicity and are zeros of `W`. -/
private theorem tendsto_atBot_and_tendsto_atTop_of_monotone {W γ : ℝ → ℝ} (hW : Continuous W)
    (hγd : ∀ t, HasDerivAt γ (W (γ t)) t) (hmono : Monotone γ) (hmem : ∀ t, γ t ∈ Ioo a b)
    (hzero : ∀ L ∈ Icc a b, W L = 0 → L = a ∨ L = b) :
    Tendsto γ atBot (𝓝 a) ∧ Tendsto γ atTop (𝓝 b) := by
  have hbdd : BddAbove (range γ) := ⟨b, by rintro _ ⟨t, rfl⟩; exact (hmem t).2.le⟩
  have hbdd' : BddBelow (range γ) := ⟨a, by rintro _ ⟨t, rfl⟩; exact (hmem t).1.le⟩
  have htop := tendsto_atTop_ciSup hmono hbdd
  have hbot := tendsto_atBot_ciInf hmono hbdd'
  have hsup : ⨆ t, γ t = b := by
    have h0 := apply_eq_zero_of_tendsto_atTop_of_hasDerivAt hW.continuousAt (.of_forall hγd) htop
    have hge : γ 0 ≤ ⨆ t, γ t := le_ciSup hbdd 0
    exact (hzero _ ⟨(hmem 0).1.le.trans hge, ciSup_le fun t ↦ (hmem t).2.le⟩ h0).resolve_left
      fun h ↦ not_le.2 (hmem 0).1 (h ▸ hge)
  have hinf : ⨅ t, γ t = a := by
    have h0 := apply_eq_zero_of_tendsto_atBot_of_hasDerivAt hW.continuousAt (.of_forall hγd) hbot
    have hle : ⨅ t, γ t ≤ γ 0 := ciInf_le hbdd' 0
    exact (hzero _ ⟨le_ciInf fun t ↦ (hmem t).1.le, hle.trans (hmem 0).2.le⟩ h0).resolve_right
      fun h ↦ not_le.2 (hmem 0).2 (h ▸ hle)
  exact ⟨hinf ▸ hbot, hsup ▸ htop⟩

/-- **The orbit joining two consecutive equilibria.** Let `V` be Lipschitz on `[a, b]`, with
`a < b`, vanishing at `a` and `b` and positive on `(a, b)`. Then `x' = V x` has a solution `γ`
defined on all of `ℝ`, strictly increasing, with values in `(a, b)`, tending to `a` at `-∞` and to
`b` at `+∞`. -/
theorem exists_isIntegralCurve_tendsto_of_pos {K : ℝ≥0} (hab : a < b)
    (hV : LipschitzOnWith K V (Icc a b)) (ha : V a = 0) (hb : V b = 0)
    (hpos : ∀ x ∈ Ioo a b, 0 < V x) :
    ∃ γ : ℝ → ℝ, IsIntegralCurve γ (fun _ ↦ V) ∧ StrictMono γ ∧ (∀ t, γ t ∈ Ioo a b) ∧
      Tendsto γ atBot (𝓝 a) ∧ Tendsto γ atTop (𝓝 b) := by
  -- The field `W = V ∘ projIcc` is globally Lipschitz and agrees with `V` on `[a, b]`.
  set W : ℝ → ℝ := fun x ↦ V (projIcc a b hab.le x) with hWdef
  have hW : LipschitzWith K W := LipschitzWith.of_dist_le_mul fun x y ↦ by
    have hproj := (LipschitzWith.projIcc hab.le).dist_le_mul x y
    rw [NNReal.coe_one, one_mul, Subtype.dist_eq] at hproj
    exact (hV.dist_le_mul _ (projIcc a b hab.le x).property _
      (projIcc a b hab.le y).property).trans (mul_le_mul_of_nonneg_left hproj K.coe_nonneg)
  have hWV : ∀ x ∈ Icc a b, W x = V x := fun x hx ↦ by simp [hWdef, projIcc_of_mem _ hx]
  have hc : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  set c := (a + b) / 2
  set γ := ODE.globalSolution W hW c with hγdef
  have hγd : ∀ t, HasDerivAt γ (W (γ t)) t := ODE.hasDerivAt_globalSolution W hW c
  have hγc : Continuous γ := ODE.continuous_globalSolution_apply W hW c
  -- `γ` never reaches an equilibrium `e` of `W`: from there it would stay at `e`, but `γ 0 = c`.
  have hne : ∀ e, W e = 0 → e ≠ c → ∀ t, γ t ≠ e := by
    intro e he hec t ht
    have hconst : (fun _ : ℝ ↦ e) = ODE.globalSolution W hW e :=
      ODE.eq_globalSolution W hW fun _ ↦ by simpa [he] using hasDerivAt_const _ e
    have h0 := ODE.globalSolution_add W hW c t (-t)
    rw [add_neg_cancel, ODE.globalSolution_zero] at h0
    rw [← hγdef, ht, ← hconst] at h0
    exact hec h0.symm
  -- Hence `γ` stays in `(a, b)`, by the intermediate value theorem.
  have hWa : W a = 0 := by rw [hWV a (left_mem_Icc.2 hab.le), ha]
  have hWb : W b = 0 := by rw [hWV b (right_mem_Icc.2 hab.le), hb]
  have hmem : ∀ t, γ t ∈ Ioo a b := by
    have hpre : IsPreconnected (range γ) := isPreconnected_range hγc
    have hc0 : c ∈ range γ := ⟨0, ODE.globalSolution_zero W hW c⟩
    intro t
    refine ⟨lt_of_not_ge fun hle ↦ ?_, lt_of_not_ge fun hle ↦ ?_⟩
    · obtain ⟨t', ht'⟩ := hpre.Icc_subset ⟨t, rfl⟩ hc0 ⟨hle, hc.1.le⟩
      exact hne a hWa hc.1.ne t' ht'
    · obtain ⟨t', ht'⟩ := hpre.Icc_subset hc0 ⟨t, rfl⟩ ⟨hc.2.le, hle⟩
      exact hne b hWb hc.2.ne' t' ht'
  -- On `(a, b)` the fields agree, so `γ` solves `x' = V x` and is strictly increasing.
  have hγV : ∀ t, HasDerivAt γ (V (γ t)) t := fun t ↦ by
    have := hγd t
    rwa [hWV _ (Ioo_subset_Icc_self (hmem t))] at this
  have hmono : StrictMono γ := strictMono_of_hasDerivAt_pos hγV fun t ↦ hpos _ (hmem t)
  -- Its limits at `±∞` are zeros of `W` in `[a, b]`, hence `a` and `b`.
  have hzero : ∀ L ∈ Icc a b, W L = 0 → L = a ∨ L = b := fun L hL hL0 ↦ by
    by_contra! h
    have := hpos L ⟨lt_of_le_of_ne hL.1 (Ne.symm h.1), lt_of_le_of_ne hL.2 h.2⟩
    rw [← hWV L hL, hL0] at this
    exact lt_irrefl _ this
  obtain ⟨hbot, htop⟩ :=
    tendsto_atBot_and_tendsto_atTop_of_monotone hW.continuous hγd hmono.monotone hmem hzero
  exact ⟨γ, hγV, hmono, hmem, hbot, htop⟩

/-- **The orbit joining two equilibria is unique up to translation.** Let `V` be locally
Lipschitz on `(a, b)`, and let `γ` be a solution of `x' = V x` with values in `(a, b)`. Then every
solution `δ` tending to `a` at `-∞` and to `b` at `+∞` is a time translate of `γ`. -/
theorem exists_eq_comp_add_of_isIntegralCurve_of_tendsto {γ δ : ℝ → ℝ}
    (hV : LocallyLipschitzOn (Ioo a b) V) (hγ : IsIntegralCurve γ (fun _ ↦ V))
    (hγab : ∀ t, γ t ∈ Ioo a b) (hδ : IsIntegralCurve δ (fun _ ↦ V))
    (hδa : Tendsto δ atBot (𝓝 a)) (hδb : Tendsto δ atTop (𝓝 b)) :
    ∃ τ, δ = fun t ↦ γ (t + τ) := by
  -- `δ` takes the value `γ 0` at some time `t₀`, by the intermediate value theorem.
  obtain ⟨t₀, ht₀⟩ : γ 0 ∈ range δ := by
    obtain ⟨u, hu⟩ := (hδa.eventually (gt_mem_nhds (hγab 0).1)).exists
    obtain ⟨w, hw⟩ := (hδb.eventually (lt_mem_nhds (hγab 0).2)).exists
    exact (isPreconnected_range hδ.continuous).Icc_subset ⟨u, rfl⟩ ⟨w, rfl⟩ ⟨hu.le, hw.le⟩
  -- The translate of `γ` agreeing with `δ` at `t₀` agrees with it everywhere, since `V` is
  -- locally Lipschitz along it.
  have hγ' : IsIntegralCurve (fun t ↦ γ (t + -t₀)) (fun _ ↦ V) := fun t ↦
    (hγ (t + -t₀)).comp_add_const t (-t₀)
  refine ⟨-t₀, funext fun t ↦ (isPreconnected_univ.ode_eqOn (V := fun p : ℝ × ℝ ↦ V p.2)
    (fun s _ ↦ ?_) (mem_univ t₀) (by simp [ht₀]) (fun s _ ↦ (hγ' s).hasDerivWithinAt)
    (fun s _ ↦ (hδ s).hasDerivWithinAt) (mem_univ t)).symm⟩
  obtain ⟨K, u, hu, hK⟩ := hV (hγab (s + -t₀))
  rw [isOpen_Ioo.nhdsWithin_eq (hγab _)] at hu
  exact ⟨K, univ ×ˢ u, prod_mem_nhds univ_mem hu, fun r ↦ hK.mono fun x hx ↦ hx.2⟩

end TauCeti
