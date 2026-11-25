/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.NonlinearCaratheodory.Basic
import TauCeti.Analysis.Normed.Module.Ball.Retraction

/-!
# The nonlinear Carathéodory theorem on a ball

Let `E` be a Banach space, `x₀ : E`, `r ≥ 0`, and let `B` be the closed ball of radius `r` about
`x₀`. Let `F : ℝ → E → E` be such that, on the time interval `[t₀, T]`, every section
`t ↦ F t x` with `x ∈ B` is integrable, `F t` is Lipschitz on `B` with constant `L t` for almost
every `t`, and `‖F t x₀‖ ≤ m t` almost everywhere, with `L` and `m` integrable. If

`(∫ t in t₀..T, m t) exp (∫ t in t₀..T, L t) ≤ r`,

then the integral equation `x t = x₀ + ∫ s in t₀..t, F s (x s)` has a solution on `[t₀, T]` with
values in `B` (`TauCeti.exists_continuousOn_mapsTo_closedBall_forall_mem_Icc_eq_picard`), and two
solutions with values in `B` agree there
(`TauCeti.eqOn_of_mapsTo_closedBall_of_forall_mem_Icc_eq_picard`). If the inequality is strict,
every continuous solution on `[t₀, T]` takes values in `B`
(`TauCeti.mapsTo_closedBall_of_forall_mem_Icc_eq_picard`), so any two solutions agree.

The proof truncates `F` by the radial retraction `π` onto `B`
(`TauCeti.centeredRadialRetraction`). The field `G t y = F t (π y)` satisfies the hypotheses of
the global theorem (`TauCeti.exists_continuousOn_forall_mem_Icc_eq_picard_of_lipschitzWith`) with
the Lipschitz constant `2 L t`, and `‖G t y - G t x₀‖ ≤ L t ‖y - x₀‖` because `π` moves no point
farther from `x₀`. The a priori bound at the initial value
(`TauCeti.norm_sub_le_mul_exp_of_forall_mem_Icc_eq_picard_of_dist_le`) therefore keeps every
solution of the truncated equation in `B`, where `G = F`. For the strict inequality, a solution
leaving `B` reaches the sphere `‖x - x₀‖ = r` at a first time `t*`, and the same bound on
`[t₀, t*]`, where the solution solves the truncated equation, puts it strictly inside `B`.

## Main results

* `TauCeti.exists_continuousOn_mapsTo_closedBall_forall_mem_Icc_eq_picard`: existence of a
  solution with values in the ball.
* `TauCeti.eqOn_of_mapsTo_closedBall_of_forall_mem_Icc_eq_picard`: uniqueness among solutions with
  values in the ball.
* `TauCeti.mapsTo_closedBall_of_forall_mem_Icc_eq_picard`: under the strict inequality, every
  solution stays in the ball.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 2, §1.
-/

public section

open MeasureTheory Set Metric Real

open scoped NNReal Interval

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → E → E} {L : ℝ → ℝ≥0}
  {t₀ T r : ℝ} {x₀ : E} {m : ℝ → ℝ}

/-- The bound of the a priori estimate grows with the time interval: for `t ∈ [t₀, T]`,
`|∫ s in t₀..t, m s| exp |∫ s in t₀..t, L s| ≤ (∫ s in t₀..T, m s) exp (∫ s in t₀..T, L s)` when
`m ≥ 0` almost everywhere. -/
private theorem abs_integral_mul_exp_abs_integral_le (hm : IntegrableOn m (Icc t₀ T))
    (hm₀ : ∀ᵐ t ∂volume.restrict (Icc t₀ T), 0 ≤ m t)
    (hL : IntegrableOn (fun t ↦ (L t : ℝ)) (Icc t₀ T)) {t : ℝ} (ht : t ∈ Icc t₀ T) :
    |∫ s in t₀..t, m s| * exp |∫ s in t₀..t, (L s : ℝ)| ≤
      (∫ s in t₀..T, m s) * exp (∫ s in t₀..T, (L s : ℝ)) := by
  have hT : t₀ ≤ T := ht.1.trans ht.2
  have hsub : Ι t₀ t ⊆ Ι t₀ T := uIoc_subset_uIoc_of_uIcc_subset_uIcc
    (uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le hT]; exact ht))
  have hIoc : Ι t₀ T ⊆ Icc t₀ T := uIoc_subset_uIcc.trans (uIcc_of_le hT).le
  have hm₀' : 0 ≤ᵐ[volume.restrict (Ι t₀ T)] m := ae_restrict_of_ae_restrict_of_subset hIoc hm₀
  have hL₀' : 0 ≤ᵐ[volume.restrict (Ι t₀ T)] fun s ↦ (L s : ℝ) :=
    .of_forall fun s ↦ (L s).coe_nonneg
  have h1 := intervalIntegral.abs_integral_mono_interval hsub hm₀'
    ((hm.mono_set (uIcc_of_le hT).le).intervalIntegrable)
  have h2 := intervalIntegral.abs_integral_mono_interval hsub hL₀'
    ((hL.mono_set (uIcc_of_le hT).le).intervalIntegrable)
  rw [abs_of_nonneg (intervalIntegral.integral_nonneg_of_ae_restrict hT hm₀)] at h1
  have h2' : |∫ s in t₀..t, (L s : ℝ)| ≤ ∫ s in t₀..T, (L s : ℝ) :=
    h2.trans_eq (abs_of_nonneg (intervalIntegral.integral_nonneg hT fun s _ ↦ (L s).coe_nonneg))
  exact mul_le_mul h1 (exp_le_exp.2 h2') (exp_pos _).le
    ((abs_nonneg _).trans h1)

/-- The truncation `G t y = F t (π y)` of a field Lipschitz on the ball, by the radial retraction
`π` onto the ball, is Lipschitz with constant `2 L t` and satisfies the Lipschitz bound with
constant `L t` at the centre. -/
private theorem lipschitzWith_comp_centeredRadialRetraction (hr : 0 ≤ r)
    (hLip : ∀ᵐ t ∂volume.restrict (Icc t₀ T), LipschitzOnWith (L t) (F t) (closedBall x₀ r)) :
    (∀ᵐ t ∂volume.restrict (Icc t₀ T),
      LipschitzWith (L t * 2) (fun y ↦ F t (centeredRadialRetraction x₀ r y))) ∧
    ∀ᵐ t ∂volume.restrict (Icc t₀ T), ∀ y,
      dist (F t (centeredRadialRetraction x₀ r y)) (F t (centeredRadialRetraction x₀ r x₀)) ≤
        L t * dist y x₀ := by
  refine ⟨hLip.mono fun t ht ↦ ht.comp_centeredRadialRetraction hr, hLip.mono fun t ht y ↦ ?_⟩
  refine (ht.dist_le_mul _ (centeredRadialRetraction_mem_closedBall hr y) _
    (centeredRadialRetraction_mem_closedBall hr x₀)).trans
    (mul_le_mul_of_nonneg_left ?_ (L t).coe_nonneg)
  rw [centeredRadialRetraction_of_mem_closedBall (mem_closedBall_self hr),
    dist_centeredRadialRetraction hr]
  exact min_le_left _ _

/-- Along a curve with values in the ball on `[t₀, t]`, the integral equations of `F` and of its
truncation `G t y = F t (π y)` agree at `t`. -/
private theorem picard_comp_centeredRadialRetraction {x : ℝ → E} {t : ℝ}
    (hx : ∀ s ∈ uIcc t₀ t, x s ∈ closedBall x₀ r) :
    ODE.picard (fun s y ↦ F s (centeredRadialRetraction x₀ r y)) t₀ x₀ x t =
      ODE.picard F t₀ x₀ x t := by
  simp only [ODE.picard_apply]
  congr 1
  exact intervalIntegral.integral_congr fun s hs ↦ by
    simp only [centeredRadialRetraction_of_mem_closedBall (hx s hs)]

/-- **The nonlinear Carathéodory theorem on a ball: existence.** Let the sections `t ↦ F t x`,
`x ∈ closedBall x₀ r`, be integrable on `[t₀, T]`, let `F t` be Lipschitz on the ball with
constant `L t` and `‖F t x₀‖ ≤ m t` for almost every `t ∈ [t₀, T]`, with `L` and `m` integrable,
and let `(∫ t in t₀..T, m t) exp (∫ t in t₀..T, L t) ≤ r`. Then there is a curve `x` continuous on
`[t₀, T]`, with values in the ball, such that `x t = x₀ + ∫ s in t₀..t, F s (x s)` for
`t ∈ [t₀, T]`. -/
theorem exists_continuousOn_mapsTo_closedBall_forall_mem_Icc_eq_picard [CompleteSpace E]
    (hF : ∀ x ∈ closedBall x₀ r, IntegrableOn (fun t ↦ F t x) (Icc t₀ T))
    (hL : IntegrableOn (fun t ↦ (L t : ℝ)) (Icc t₀ T))
    (hLip : ∀ᵐ t ∂volume.restrict (Icc t₀ T), LipschitzOnWith (L t) (F t) (closedBall x₀ r))
    (hm : IntegrableOn m (Icc t₀ T)) (hFm : ∀ᵐ t ∂volume.restrict (Icc t₀ T), ‖F t x₀‖ ≤ m t)
    (hr : (∫ t in t₀..T, m t) * exp (∫ t in t₀..T, (L t : ℝ)) ≤ r) :
    ∃ x : ℝ → E, ContinuousOn x (Icc t₀ T) ∧ MapsTo x (Icc t₀ T) (closedBall x₀ r) ∧
      ∀ t ∈ Icc t₀ T, x t = ODE.picard F t₀ x₀ x t := by
  rcases lt_or_ge T t₀ with hT | hT
  · exact ⟨0, by simp [Icc_eq_empty_of_lt hT], by simp [Icc_eq_empty_of_lt hT, mapsTo_empty],
      by simp [Icc_eq_empty_of_lt hT]⟩
  have ht₀ : t₀ ∈ Icc t₀ T := left_mem_Icc.2 hT
  have hm₀ : ∀ᵐ t ∂volume.restrict (Icc t₀ T), 0 ≤ m t := hFm.mono fun _ h ↦ (norm_nonneg _).trans h
  have hr₀ : 0 ≤ r := (mul_nonneg (abs_nonneg _) (exp_pos _).le).trans
    ((abs_integral_mul_exp_abs_integral_le hm hm₀ hL ht₀).trans hr)
  set G : ℝ → E → E := fun t y ↦ F t (centeredRadialRetraction x₀ r y)
  obtain ⟨hGLip, hGx₀⟩ := lipschitzWith_comp_centeredRadialRetraction hr₀ hLip
  have hG (y : E) : IntegrableOn (fun t ↦ G t y) (Icc t₀ T) :=
    hF _ (centeredRadialRetraction_mem_closedBall hr₀ y)
  have hG₀ : centeredRadialRetraction x₀ r x₀ = x₀ :=
    centeredRadialRetraction_of_mem_closedBall (mem_closedBall_self hr₀)
  obtain ⟨x, hx, hxe⟩ := exists_continuousOn_forall_mem_Icc_eq_picard_of_lipschitzWith (F := G)
    hG (by
      have h : IntegrableOn (fun t ↦ (L t : ℝ) * 2) (Icc t₀ T) := hL.mul_const 2
      simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using h) hGLip ht₀ x₀
  have hB : MapsTo x (Icc t₀ T) (closedBall x₀ r) := fun t ht ↦ by
    rw [mem_closedBall, dist_eq_norm]
    refine (norm_sub_le_mul_exp_of_forall_mem_Icc_eq_picard_of_dist_le hL ht₀ hm
      (by simpa only [G, hG₀] using hFm) (by simpa only [G, hG₀] using hGx₀) hx hxe ht).trans ?_
    exact (abs_integral_mul_exp_abs_integral_le hm hm₀ hL ht).trans hr
  refine ⟨x, hx, hB, fun t ht ↦ (hxe t ht).trans ?_⟩
  exact picard_comp_centeredRadialRetraction fun s hs ↦
    hB (uIcc_subset_Icc ht₀ ht hs)

/-- **The nonlinear Carathéodory theorem on a ball: uniqueness.** Let the sections
`t ↦ F t x`, `x ∈ closedBall x₀ r`, be integrable on `[t₀, T]` and let `F t` be Lipschitz on the
ball with constant `L t` for almost every `t ∈ [t₀, T]`, with `L` integrable. Two curves continuous
on `[t₀, T]`, with values in the ball, that solve `x t = x₀ + ∫ s in t₀..t, F s (x s)` there agree
on `[t₀, T]`. -/
theorem eqOn_of_mapsTo_closedBall_of_forall_mem_Icc_eq_picard
    (hF : ∀ x ∈ closedBall x₀ r, IntegrableOn (fun t ↦ F t x) (Icc t₀ T))
    (hL : IntegrableOn (fun t ↦ (L t : ℝ)) (Icc t₀ T))
    (hLip : ∀ᵐ t ∂volume.restrict (Icc t₀ T), LipschitzOnWith (L t) (F t) (closedBall x₀ r))
    {x₁ x₂ : ℝ → E} (hx₁ : ContinuousOn x₁ (Icc t₀ T)) (hx₂ : ContinuousOn x₂ (Icc t₀ T))
    (hB₁ : MapsTo x₁ (Icc t₀ T) (closedBall x₀ r)) (hB₂ : MapsTo x₂ (Icc t₀ T) (closedBall x₀ r))
    (h₁ : ∀ t ∈ Icc t₀ T, x₁ t = ODE.picard F t₀ x₀ x₁ t)
    (h₂ : ∀ t ∈ Icc t₀ T, x₂ t = ODE.picard F t₀ x₀ x₂ t) :
    EqOn x₁ x₂ (Icc t₀ T) := by
  intro t ht
  have ht₀ : t₀ ∈ Icc t₀ T := left_mem_Icc.2 (ht.1.trans ht.2)
  have hr₀ : 0 ≤ r := dist_nonneg.trans (mem_closedBall.1 (hB₁ ht₀))
  obtain ⟨hGLip, -⟩ := lipschitzWith_comp_centeredRadialRetraction hr₀ hLip
  have hG (y : E) : IntegrableOn (fun t ↦ F t (centeredRadialRetraction x₀ r y)) (Icc t₀ T) :=
    hF _ (centeredRadialRetraction_mem_closedBall hr₀ y)
  have htrunc {x : ℝ → E} (hB : MapsTo x (Icc t₀ T) (closedBall x₀ r))
      (h : ∀ t ∈ Icc t₀ T, x t = ODE.picard F t₀ x₀ x t) (t : ℝ) (ht : t ∈ Icc t₀ T) :
      x t = ODE.picard (fun s y ↦ F s (centeredRadialRetraction x₀ r y)) t₀ x₀ x t :=
    (h t ht).trans (picard_comp_centeredRadialRetraction fun s hs ↦
      hB (uIcc_subset_Icc ht₀ ht hs)).symm
  exact eqOn_of_forall_mem_Icc_eq_picard_of_lipschitzWith hG
    (by
      have h : IntegrableOn (fun t ↦ (L t : ℝ) * 2) (Icc t₀ T) := hL.mul_const 2
      simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using h) hGLip ht₀ hx₁ hx₂
    (htrunc hB₁ h₁) (htrunc hB₂ h₂) ht

/-- **Solutions stay in the ball under the strict inequality.** Let `F t` be Lipschitz on
`closedBall x₀ r` with constant `L t` and `‖F t x₀‖ ≤ m t` for almost every `t ∈ [t₀, T]`, with
`L` and `m` integrable, and let `(∫ t in t₀..T, m t) exp (∫ t in t₀..T, L t) < r`. Then every curve
continuous on `[t₀, T]` with `x t = x₀ + ∫ s in t₀..t, F s (x s)` there takes values in the ball:
a solution leaving it would reach the sphere at a first time `t*`, where the a priori bound on
`[t₀, t*]` puts it strictly inside. -/
theorem mapsTo_closedBall_of_forall_mem_Icc_eq_picard
    (hL : IntegrableOn (fun t ↦ (L t : ℝ)) (Icc t₀ T))
    (hLip : ∀ᵐ t ∂volume.restrict (Icc t₀ T), LipschitzOnWith (L t) (F t) (closedBall x₀ r))
    (hm : IntegrableOn m (Icc t₀ T)) (hFm : ∀ᵐ t ∂volume.restrict (Icc t₀ T), ‖F t x₀‖ ≤ m t)
    (hr : (∫ t in t₀..T, m t) * exp (∫ t in t₀..T, (L t : ℝ)) < r) {x : ℝ → E}
    (hx : ContinuousOn x (Icc t₀ T)) (h : ∀ t ∈ Icc t₀ T, x t = ODE.picard F t₀ x₀ x t) :
    MapsTo x (Icc t₀ T) (closedBall x₀ r) := by
  by_contra hc
  obtain ⟨t₁, ht₁, ht₁B⟩ := not_forall₂.1 hc
  have ht₀ : t₀ ∈ Icc t₀ T := left_mem_Icc.2 (ht₁.1.trans ht₁.2)
  have hm₀ : ∀ᵐ t ∂volume.restrict (Icc t₀ T), 0 ≤ m t := hFm.mono fun _ h ↦ (norm_nonneg _).trans h
  have hr₀ : 0 < r := (mul_nonneg (abs_nonneg _) (exp_pos _).le).trans_lt
    ((abs_integral_mul_exp_abs_integral_le hm hm₀ hL ht₀).trans_lt hr)
  -- The first time `b` at which `x` reaches the sphere.
  set S := Icc t₀ T ∩ x ⁻¹' {y | r ≤ dist y x₀}
  have hSc : IsClosed S := hx.preimage_isClosed_of_isClosed isClosed_Icc
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have ht₁S : t₁ ∈ S := ⟨ht₁, (not_le.1 fun h' ↦ ht₁B (mem_closedBall.2 h')).le⟩
  set b := sInf S
  have hbdd : BddBelow S := ⟨t₀, fun u hu ↦ hu.1.1⟩
  have hbS : b ∈ S := hSc.csInf_mem ⟨t₁, ht₁S⟩ hbdd
  have hbI : b ∈ Icc t₀ T := hbS.1
  have hlt : ∀ s ∈ Ico t₀ b, dist (x s) x₀ < r := fun s hs ↦ not_le.1 fun h' ↦
    (csInf_le hbdd ⟨⟨hs.1, hs.2.le.trans hbI.2⟩, h'⟩).not_gt hs.2
  have htb : t₀ < b := lt_of_le_of_ne hbI.1 fun he ↦ by
    have hb : r ≤ dist (x b) x₀ := hbS.2
    have hx₀ : x t₀ = x₀ := by rw [h t₀ ht₀]; simp [ODE.picard_apply]
    rw [← he, hx₀, dist_self] at hb
    exact hb.not_gt hr₀
  -- On `[t₀, b]` the curve stays in the ball.
  have hsub : Icc t₀ b ⊆ Icc t₀ T := Icc_subset_Icc_right hbI.2
  have hBb : MapsTo x (Icc t₀ b) (closedBall x₀ r) := fun s hs ↦ by
    have hcl : s ∈ closure (Ico t₀ b) := (closure_Ico htb.ne).symm ▸ hs
    have hcw : ContinuousWithinAt x (Ico t₀ b) s :=
      (hx s (hsub hs)).mono (Ico_subset_Icc_self.trans hsub)
    refine isClosed_closedBall.closure_subset_iff.2 ?_ (hcw.mem_closure_image hcl)
    rintro _ ⟨u, hu, rfl⟩
    exact mem_closedBall.2 (hlt u hu).le
  obtain ⟨-, hGx₀⟩ := lipschitzWith_comp_centeredRadialRetraction hr₀.le hLip
  have hG₀ : centeredRadialRetraction x₀ r x₀ = x₀ :=
    centeredRadialRetraction_of_mem_closedBall (mem_closedBall_self hr₀.le)
  have hbound := norm_sub_le_mul_exp_of_forall_mem_Icc_eq_picard_of_dist_le
    (F := fun s y ↦ F s (centeredRadialRetraction x₀ r y)) (hL.mono_set hsub)
    (left_mem_Icc.2 htb.le) (hm.mono_set hsub)
    (by simpa only [hG₀] using ae_restrict_of_ae_restrict_of_subset hsub hFm)
    (by simpa only [hG₀] using ae_restrict_of_ae_restrict_of_subset hsub hGx₀)
    (hx.mono hsub) (fun s hs ↦ (h s (hsub hs)).trans
      (picard_comp_centeredRadialRetraction fun u hu ↦
        hBb (uIcc_subset_Icc (left_mem_Icc.2 htb.le) hs hu)).symm) (right_mem_Icc.2 htb.le)
  have := (hbound.trans (abs_integral_mul_exp_abs_integral_le hm hm₀ hL hbI)).trans_lt hr
  rw [← dist_eq_norm] at this
  exact this.not_ge (show r ≤ dist (x b) x₀ from hbS.2)

end TauCeti
