/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import TauCeti.Dynamics.Flow.TimeDependent
import Mathlib.Topology.Order.ProjIcc
import TauCeti.Analysis.ODE.Gronwall.IntegralCurve

/-!
# Flows of time-dependent vector fields on a closed interval

`IsFlowOn v φ a b` records that `φ` starts at the identity at time `a` and each trajectory solves
the ODE for `v` on `[a, b]`. A uniform Lipschitz bound on `v` in space gives uniqueness and
exponential distance bounds in both time directions. These bounds give joint continuity on
the interval and control the distortion of each time map and its inverse.

On a Banach space, a field continuous in time and uniformly Lipschitz in space on `[a, b]`
admits a jointly continuous flow with bijective time maps. The existence proof extends the
field constantly in time at each endpoint and applies `ODE.nonautonomousSolution`. The flow
itself can then be extended constantly past the endpoints.
-/

public section

open Function Set
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A flow on `[a, b]` starts at the identity at time `a` and follows `v` on `[a, b]`.
Its values away from `[a, b]` are unrestricted except for the initial condition at `a`. -/
structure IsFlowOn (v φ : ℝ → E → E) (a b : ℝ) : Prop where
  /-- The initial map is the identity. -/
  initial (x : E) : φ a x = x
  /-- Each trajectory is an integral curve on the closed interval. -/
  isIntegralCurveOn (x : E) : IsIntegralCurveOn (φ · x) v (Icc a b)

variable {v φ ψ : ℝ → E → E} {a b : ℝ} {K : ℝ≥0}

namespace IsFlowOn

/-- Two flows of the same spatially Lipschitz field agree on the interval. -/
theorem eqOn (hφ : IsFlowOn v φ a b) (hψ : IsFlowOn v ψ a b)
    (hLip : ∀ s ∈ Icc a b, LipschitzWith K (v s)) :
    EqOn φ ψ (Icc a b) := by
  intro t ht
  funext x
  have h := (hφ.isIntegralCurveOn x).dist_le_mul_exp (hψ.isIntegralCurveOn x) hLip
    (left_mem_Icc.mpr (ht.1.trans ht.2)) ht
  simpa only [hφ.initial, hψ.initial, dist_self, zero_mul, dist_le_zero] using h

/-- The spatial Lipschitz constant of the time map at `t` is at most `exp (K * (t - a))`. -/
theorem lipschitzWith (hφ : IsFlowOn v φ a b) (hLip : ∀ s ∈ Icc a b, LipschitzWith K (v s))
    {t : ℝ} (ht : t ∈ Icc a b) :
    LipschitzWith (Real.exp (K * (t - a))).toNNReal (φ t) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have h := (hφ.isIntegralCurveOn x).dist_le_mul_exp (hφ.isIntegralCurveOn y) hLip
    (left_mem_Icc.mpr (ht.1.trans ht.2)) ht
  simpa only [hφ.initial, abs_of_nonneg (sub_nonneg.mpr ht.1), mul_comm (dist x y),
    Real.coe_toNNReal _ (Real.exp_nonneg _)] using h

/-- The reverse spatial distance bound has the same factor `exp (K * (t - a))`.
In particular, every time map is injective, including on incomplete spaces. -/
theorem antilipschitzWith (hφ : IsFlowOn v φ a b) (hLip : ∀ s ∈ Icc a b, LipschitzWith K (v s))
    {t : ℝ} (ht : t ∈ Icc a b) : AntilipschitzWith (Real.exp (K * (t - a))).toNNReal (φ t) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_
  have h := (hφ.isIntegralCurveOn x).dist_le_mul_exp (hφ.isIntegralCurveOn y) hLip ht
    (left_mem_Icc.mpr (ht.1.trans ht.2))
  simpa only [hφ.initial, abs_sub_comm a t, abs_of_nonneg (sub_nonneg.mpr ht.1),
    mul_comm (dist (φ t x) (φ t y)), Real.coe_toNNReal _ (Real.exp_nonneg _)] using h

/-- A flow of a uniformly spatially Lipschitz field is jointly continuous on `[a, b] × E`. -/
theorem continuousOn (hφ : IsFlowOn v φ a b) (hLip : ∀ s ∈ Icc a b, LipschitzWith K (v s)) :
    ContinuousOn (uncurry φ) (Icc a b ×ˢ univ) := by
  refine continuousOn_prod_of_continuousOn_lipschitzOnWith' (uncurry φ)
    (Real.exp (K * (b - a))).toNNReal (fun t ht ↦ ?_)
    fun x _ ↦ (hφ.isIntegralCurveOn x).continuousOn
  refine ((hφ.lipschitzWith hLip ht).weaken ?_).lipschitzOnWith
  gcongr
  exact ht.2

end IsFlowOn

section Complete

variable [CompleteSpace E]

/-- Construct a flow whose time maps on the interval are bijective. -/
private theorem exists_isFlowOn_continuous_bijective
    (hcont : ∀ x, ContinuousOn (v · x) (Icc a b)) (hLip : ∀ s ∈ Icc a b, LipschitzWith K (v s)) :
    ∃ φ : ℝ → E → E, IsFlowOn v φ a b ∧ Continuous (uncurry φ) ∧
      ∀ t ∈ Icc a b, Bijective (φ t) := by
  by_cases hab : a ≤ b
  · let clamp (t : ℝ) : ℝ := projIcc a b hab t
    have hc : Continuous clamp := continuous_subtypeVal.comp continuous_projIcc
    have hmem (t : ℝ) : clamp t ∈ Icc a b := (projIcc a b hab t).property
    have hfix {t : ℝ} (ht : t ∈ Icc a b) : clamp t = t := by
      simp only [clamp, projIcc_of_mem hab ht]
    have ha := hfix (left_mem_Icc.mpr hab)
    have hv (x : E) : Continuous (fun t ↦ v (clamp t) x) :=
      (hcont x).comp_continuous hc hmem
    let sol := ODE.nonautonomousSolution (fun t ↦ v (clamp t)) hv (fun t ↦ hLip _ (hmem t))
    have hsol : Continuous (fun p : ℝ × E × ℝ ↦ sol p.1 p.2.1 p.2.2) :=
      ODE.continuous_nonautonomousSolution _ _ _
    refine ⟨fun t x ↦ sol a x (clamp t), ⟨fun x ↦ ?_, fun x t ht ↦ ?_⟩,
      hsol.comp (continuous_const.prodMk (continuous_snd.prodMk (hc.comp continuous_fst))), ?_⟩
    · simp only [ha, sol, ODE.nonautonomousSolution_self]
    · have h := (ODE.hasDerivAt_nonautonomousSolution _ hv (fun s ↦ hLip _ (hmem s))
        a x t).hasDerivWithinAt (s := Icc a b)
      simpa only [hfix ht] using
        (h.congr_of_mem (fun _ hs ↦ congrArg (sol a x) (hfix hs)) ht)
    · intro t ht
      simp only [hfix ht]
      have htrans (r s u : ℝ) (x : E) : sol s (sol r x s) u = sol r x u :=
        ODE.nonautonomousSolution_trans _ _ _ r s u x
      have hself (s : ℝ) (x : E) : sol s x s = x := ODE.nonautonomousSolution_self _ _ _ s x
      have hleft : LeftInverse (fun y ↦ sol t y a) (fun x ↦ sol a x t) :=
        fun x ↦ (htrans a t a x).trans (hself a x)
      have hright : RightInverse (fun y ↦ sol t y a) (fun x ↦ sol a x t) :=
        fun x ↦ (htrans t a t x).trans (hself t x)
      exact ⟨hleft.injective, hright.surjective⟩
  · have hempty := Icc_eq_empty hab
    exact ⟨fun _ x ↦ x, ⟨fun _ ↦ rfl, fun _ t ht ↦ (hempty.subset ht).elim⟩, continuous_snd,
      fun _ ht ↦ (hempty.subset ht).elim⟩

/-- A field continuous in time and uniformly Lipschitz in space on `[a, b]` has a flow
jointly continuous on all of `ℝ × E`. -/
theorem exists_isFlowOn (hcont : ∀ x, ContinuousOn (v · x) (Icc a b))
    (hLip : ∀ s ∈ Icc a b, LipschitzWith K (v s)) :
    ∃ φ : ℝ → E → E, IsFlowOn v φ a b ∧ Continuous (uncurry φ) := by
  obtain ⟨φ, hφ, hc, _⟩ := exists_isFlowOn_continuous_bijective hcont hLip
  exact ⟨φ, hφ, hc⟩

/-- Every time map of a flow for a continuous-in-time, uniformly spatially Lipschitz field
on a Banach space is bijective. -/
theorem IsFlowOn.bijective (hφ : IsFlowOn v φ a b) (hcont : ∀ x, ContinuousOn (v · x) (Icc a b))
    (hLip : ∀ s ∈ Icc a b, LipschitzWith K (v s)) {t : ℝ} (ht : t ∈ Icc a b) :
    Bijective (φ t) := by
  obtain ⟨ψ, hψ, _, hb⟩ := exists_isFlowOn_continuous_bijective hcont hLip
  exact (hφ.eqOn hψ hLip ht).symm ▸ hb t ht

/-- A time map of a flow on a Banach space is a homeomorphism whose inverse is
`exp (K * (t - a))`-Lipschitz. -/
theorem IsFlowOn.exists_homeomorph (hφ : IsFlowOn v φ a b)
    (hcont : ∀ x, ContinuousOn (v · x) (Icc a b)) (hLip : ∀ s ∈ Icc a b, LipschitzWith K (v s))
    {t : ℝ} (ht : t ∈ Icc a b) :
    ∃ e : E ≃ₜ E, (e : E → E) = φ t ∧ LipschitzWith (Real.exp (K * (t - a))).toNNReal e.symm := by
  have hanti := hφ.antilipschitzWith hLip ht
  have hemb := hanti.isEmbedding (hφ.lipschitzWith hLip ht).continuous
  let e := hemb.toHomeomorphOfSurjective (hφ.bijective hcont hLip ht).surjective
  have he : (e : E → E) = φ t := funext fun x ↦ by simp [e]
  refine ⟨e, he, hanti.to_rightInverse fun x ↦ ?_⟩
  rw [← he, e.apply_symm_apply]

/-- The time-dependent flow of a field with globally Lipschitz suspension is a flow on every
closed interval with that initial time. -/
theorem isFlowOn_timeDependentFlow (hv : LipschitzWith K (timeDependentSuspension v)) :
    IsFlowOn v (timeDependentFlow v hv a) a b :=
  ⟨timeDependentFlow_self v hv a,
    fun x t _ ↦ (hasDerivAt_timeDependentFlow v hv a t x).hasDerivWithinAt⟩

end Complete

end TauCeti

end
