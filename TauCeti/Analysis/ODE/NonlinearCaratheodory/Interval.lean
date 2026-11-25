/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Analysis.ODE.NonlinearCaratheodory.Basic
public import TauCeti.Topology.Order.Interval

/-!
# The nonlinear Carathéodory theorem on an interval

Let `I ⊆ ℝ` be an interval (bounded or not, open, closed or half-open) containing `t₀`, and let
`F : ℝ → E → E` be a time-dependent vector field on a Banach space `E` such that every section
`t ↦ F t x` is integrable on compact subsets of `I` and, for almost every `t ∈ I`, `F t` is
Lipschitz with constant `L t`, where `L` is integrable on compact subsets of `I`. Then the
integral equation `x t = x₀ + ∫ s in t₀..t, F s (x s)` has exactly one solution continuous on `I`.

On each compact subinterval of `I` containing `t₀` this is the nonlinear Carathéodory theorem of
`TauCeti/Analysis/ODE/NonlinearCaratheodory/Basic.lean`. The solution on `I` takes at `t` the
value at `t` of the solution on `[min t₀ t, max t₀ t]`; solutions on two compact subintervals agree
on their overlap, by uniqueness, and each point of `I` has a compact interval neighbourhood in `I`
containing `t₀` (`Set.OrdConnected.exists_Icc_mem_nhdsWithin`), on which the glued curve is the
solution there, hence continuous.

## Main results

* `TauCeti.exists_continuousOn_forall_mem_eq_picard_of_lipschitzWith`: the integral equation has a
  solution continuous on `I`.
* `TauCeti.eqOn_of_forall_mem_eq_picard_of_lipschitzWith`: two such solutions agree on `I`.
* `TauCeti.absolutelyContinuousOnInterval_of_forall_mem_eq_picard_of_lipschitzWith`: a solution is
  absolutely continuous on every compact subinterval of `I`.
* `TauCeti.norm_sub_le_mul_exp_of_forall_mem_eq_picard_of_lipschitzWith` and
  `TauCeti.dist_le_mul_exp_of_forall_mem_eq_picard_of_lipschitzWith`: the a priori bound
  `‖x t - x₀‖ ≤ |∫ m| exp |∫ L|` and the dependence `dist x₀ y₀ exp |∫ L|` on the initial value.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 2, §1.
-/

public section

open Function MeasureTheory Set intervalIntegral
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → E → E} {L : ℝ → ℝ≥0}
  {t₀ : ℝ} {x₀ : E}

variable {I : Set ℝ}

/-- For `t₀` and `t` in an interval `I`, the closed interval between them contains both and lies
in `I`. -/
private theorem mem_Icc_min_max (hI : I.OrdConnected) (ht₀ : t₀ ∈ I) {t : ℝ} (ht : t ∈ I) :
    t₀ ∈ Icc (min t₀ t) (max t₀ t) ∧ t ∈ Icc (min t₀ t) (max t₀ t) ∧
      Icc (min t₀ t) (max t₀ t) ⊆ I := by
  rw [Icc_min_max]
  exact ⟨left_mem_uIcc, right_mem_uIcc, hI.uIcc_subset ht₀ ht⟩

variable (hF : ∀ x, LocallyIntegrableOn (fun t ↦ F t x) I)
  (hL : LocallyIntegrableOn (fun t ↦ (L t : ℝ)) I)
  (hLip : ∀ᵐ t ∂volume.restrict I, LipschitzWith (L t) (F t))

include hF hL hLip

/-- Solutions on a compact subinterval of `I` agree on the overlap of their intervals. -/
private theorem eqOn_inter_of_Icc_subset {a b a' b' : ℝ} (hab : Icc a b ⊆ I)
    (h₀ : t₀ ∈ Icc a b) (h₀' : t₀ ∈ Icc a' b') {x₁ x₂ : ℝ → E} (hx₁ : ContinuousOn x₁ (Icc a b))
    (hx₂ : ContinuousOn x₂ (Icc a' b')) (h₁ : ∀ t ∈ Icc a b, x₁ t = ODE.picard F t₀ x₀ x₁ t)
    (h₂ : ∀ t ∈ Icc a' b', x₂ t = ODE.picard F t₀ x₀ x₂ t) :
    EqOn x₁ x₂ (Icc a b ∩ Icc a' b') := by
  have hJ : Icc (max a a') (min b b') = Icc a b ∩ Icc a' b' := Icc_inter_Icc.symm
  have hsub : Icc (max a a') (min b b') ⊆ I := hJ.subset.trans (inter_subset_left.trans hab)
  intro t ht
  exact eqOn_of_forall_mem_Icc_eq_picard_of_lipschitzWith
    (fun x ↦ (hF x).integrableOn_compact_subset hsub isCompact_Icc)
    (hL.integrableOn_compact_subset hsub isCompact_Icc)
    (ae_restrict_of_ae_restrict_of_subset hsub hLip) (hJ.symm.subset ⟨h₀, h₀'⟩)
    (hx₁.mono (hJ.subset.trans inter_subset_left)) (hx₂.mono (hJ.subset.trans inter_subset_right))
    (fun s hs ↦ h₁ s (hJ.subset hs).1) (fun s hs ↦ h₂ s (hJ.subset hs).2) (hJ.symm.subset ht)

/-- **The nonlinear Carathéodory theorem on an interval: existence.** Let `I` be an interval
containing `t₀`, let every section `t ↦ F t x` be integrable on compact subsets of `I`, and let
`F t` be Lipschitz with constant `L t` for almost every `t ∈ I`, where `L` is integrable on compact
subsets of `I`. Then there is a curve `x` continuous on `I` with
`x t = x₀ + ∫ s in t₀..t, F s (x s)` for every `t ∈ I`. -/
theorem exists_continuousOn_forall_mem_eq_picard_of_lipschitzWith [CompleteSpace E]
    (hI : I.OrdConnected) (ht₀ : t₀ ∈ I) (x₀ : E) :
    ∃ x : ℝ → E, ContinuousOn x I ∧ ∀ t ∈ I, x t = ODE.picard F t₀ x₀ x t := by
  have hex (a b : ℝ) (h₀ : t₀ ∈ Icc a b) (hab : Icc a b ⊆ I) : ∃ y : ℝ → E,
      ContinuousOn y (Icc a b) ∧ ∀ t ∈ Icc a b, y t = ODE.picard F t₀ x₀ y t :=
    exists_continuousOn_forall_mem_Icc_eq_picard_of_lipschitzWith
      (fun x ↦ (hF x).integrableOn_compact_subset hab isCompact_Icc)
      (hL.integrableOn_compact_subset hab isCompact_Icc)
      (ae_restrict_of_ae_restrict_of_subset hab hLip) h₀ x₀
  choose! y hyc hye using hex
  -- the solution on any compact subinterval agrees with `x` there
  have hagree {a b : ℝ} (h₀ : t₀ ∈ Icc a b) (hab : Icc a b ⊆ I) {t : ℝ} (ht : t ∈ Icc a b) :
      y (min t₀ t) (max t₀ t) t = y a b t := by
    obtain ⟨h₀', htJ, hsub⟩ := mem_Icc_min_max hI ht₀ (hab ht)
    refine eqOn_inter_of_Icc_subset hF hL hLip hsub h₀' h₀ (hyc _ _ h₀' hsub)
      (hyc _ _ h₀ hab) (hye _ _ h₀' hsub) (hye _ _ h₀ hab) ⟨htJ, ht⟩
  refine ⟨fun t ↦ y (min t₀ t) (max t₀ t) t, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · obtain ⟨c, d, hcd, h₀, htcd, hnhds⟩ := hI.exists_Icc_mem_nhdsWithin ht₀ ht
    refine (((hyc c d h₀ hcd) t htcd).mono_of_mem_nhdsWithin hnhds).congr_of_eventuallyEq
      (Filter.mem_of_superset hnhds fun s hs ↦ hagree h₀ hcd hs) (hagree h₀ hcd htcd)
  · obtain ⟨h₀, htJ, hsub⟩ := mem_Icc_min_max hI ht₀ ht
    dsimp only
    rw [hye _ _ h₀ hsub t htJ, ODE.picard_apply, ODE.picard_apply]
    congr 1
    refine integral_congr fun s hs ↦ ?_
    have hs' : s ∈ Icc (min t₀ t) (max t₀ t) := by rwa [Icc_min_max]
    rw [hagree h₀ hsub hs']

/-- **The nonlinear Carathéodory theorem on an interval: uniqueness.** Under the hypotheses of
`TauCeti.exists_continuousOn_forall_mem_eq_picard_of_lipschitzWith`, two curves continuous on `I`
that solve `x t = x₀ + ∫ s in t₀..t, F s (x s)` on `I` agree on `I`. -/
theorem eqOn_of_forall_mem_eq_picard_of_lipschitzWith (hI : I.OrdConnected) (ht₀ : t₀ ∈ I)
    {x₁ x₂ : ℝ → E} (hx₁ : ContinuousOn x₁ I) (hx₂ : ContinuousOn x₂ I)
    (h₁ : ∀ t ∈ I, x₁ t = ODE.picard F t₀ x₀ x₁ t)
    (h₂ : ∀ t ∈ I, x₂ t = ODE.picard F t₀ x₀ x₂ t) :
    EqOn x₁ x₂ I := by
  intro t ht
  obtain ⟨h₀, htJ, hsub⟩ := mem_Icc_min_max hI ht₀ ht
  exact eqOn_inter_of_Icc_subset hF hL hLip hsub h₀ h₀ (hx₁.mono hsub) (hx₂.mono hsub)
    (fun s hs ↦ h₁ s (hsub hs)) (fun s hs ↦ h₂ s (hsub hs)) ⟨htJ, htJ⟩

/-- **Absolute continuity on an interval.** Under the hypotheses of
`TauCeti.exists_continuousOn_forall_mem_eq_picard_of_lipschitzWith`, a curve continuous on `I` that
solves `x t = x₀ + ∫ s in t₀..t, F s (x s)` on `I` is absolutely continuous on every compact
subinterval `[a, b] ⊆ I`. -/
theorem absolutelyContinuousOnInterval_of_forall_mem_eq_picard_of_lipschitzWith
    (hI : I.OrdConnected) (ht₀ : t₀ ∈ I) {x : ℝ → E} (hx : ContinuousOn x I)
    (h : ∀ t ∈ I, x t = ODE.picard F t₀ x₀ x t) {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) :
    AbsolutelyContinuousOnInterval x a b := by
  -- Work on the compact interval spanned by `a`, `b` and `t₀`.
  set a' := min (min a b) t₀
  set b' := max (max a b) t₀
  have ha' : a' ∈ I := by simp only [a', min_def]; split_ifs <;> assumption
  have hb' : b' ∈ I := by simp only [b', max_def]; split_ifs <;> assumption
  have hsub : Icc a' b' ⊆ I := hI.out ha' hb'
  have ht₀' : t₀ ∈ Icc a' b' := ⟨min_le_right _ _, le_max_right _ _⟩
  have hac := absolutelyContinuousOnInterval_of_forall_mem_Icc_eq_picard_of_lipschitzWith
    (fun y ↦ (hF y).integrableOn_compact_subset hsub isCompact_Icc)
    (hL.integrableOn_compact_subset hsub isCompact_Icc)
    (ae_restrict_of_ae_restrict_of_subset hsub hLip) ht₀' (hx.mono hsub)
    (fun t ht ↦ h t (hsub ht))
  have hab' : a' ≤ b' := ht₀'.1.trans ht₀'.2
  refine hac.mono ?_
  rw [uIcc_of_le hab']
  exact uIcc_subset_Icc ⟨(min_le_left _ _).trans (min_le_left _ _),
      (le_max_left _ _).trans (le_max_left _ _)⟩
    ⟨(min_le_left _ _).trans (min_le_right _ _), (le_max_right _ _).trans (le_max_left _ _)⟩

omit hF in
/-- **The a priori bound on an interval.** Under the hypotheses of
`TauCeti.exists_continuousOn_forall_mem_eq_picard_of_lipschitzWith`, if `‖F t x₀‖ ≤ m t` for almost
every `t ∈ I` with `m` integrable on compact subsets of `I`, then a solution on `I` satisfies
`‖x t - x₀‖ ≤ |∫ s in t₀..t, m s| exp |∫ s in t₀..t, L s|` for `t ∈ I`. -/
theorem norm_sub_le_mul_exp_of_forall_mem_eq_picard_of_lipschitzWith (hI : I.OrdConnected)
    (ht₀ : t₀ ∈ I) {m : ℝ → ℝ} (hm : LocallyIntegrableOn m I)
    (hFm : ∀ᵐ t ∂volume.restrict I, ‖F t x₀‖ ≤ m t) {x : ℝ → E} (hx : ContinuousOn x I)
    (h : ∀ t ∈ I, x t = ODE.picard F t₀ x₀ x t) {t : ℝ} (ht : t ∈ I) :
    ‖x t - x₀‖ ≤ |∫ s in t₀..t, m s| * Real.exp |∫ s in t₀..t, (L s : ℝ)| := by
  obtain ⟨h₀, htJ, hsub⟩ := mem_Icc_min_max hI ht₀ ht
  exact norm_sub_le_mul_exp_of_forall_mem_Icc_eq_picard_of_lipschitzWith
    (hL.integrableOn_compact_subset hsub isCompact_Icc)
    (ae_restrict_of_ae_restrict_of_subset hsub hLip) h₀
    (hm.integrableOn_compact_subset hsub isCompact_Icc)
    (ae_restrict_of_ae_restrict_of_subset hsub hFm) (hx.mono hsub) (fun s hs ↦ h s (hsub hs)) htJ

/-- **Dependence on the initial value on an interval.** Under the hypotheses of
`TauCeti.exists_continuousOn_forall_mem_eq_picard_of_lipschitzWith`, solutions on `I` from initial
values `x₀` and `y₀` satisfy `dist (x t) (y t) ≤ dist x₀ y₀ exp |∫ s in t₀..t, L s|` for
`t ∈ I`. -/
theorem dist_le_mul_exp_of_forall_mem_eq_picard_of_lipschitzWith (hI : I.OrdConnected)
    (ht₀ : t₀ ∈ I) {y₀ : E} {x y : ℝ → E} (hx : ContinuousOn x I) (hy : ContinuousOn y I)
    (hxe : ∀ t ∈ I, x t = ODE.picard F t₀ x₀ x t) (hye : ∀ t ∈ I, y t = ODE.picard F t₀ y₀ y t)
    {t : ℝ} (ht : t ∈ I) :
    dist (x t) (y t) ≤ dist x₀ y₀ * Real.exp |∫ s in t₀..t, (L s : ℝ)| := by
  obtain ⟨h₀, htJ, hsub⟩ := mem_Icc_min_max hI ht₀ ht
  exact dist_le_mul_exp_of_forall_mem_Icc_eq_picard_of_lipschitzWith
    (fun y ↦ (hF y).integrableOn_compact_subset hsub isCompact_Icc)
    (hL.integrableOn_compact_subset hsub isCompact_Icc)
    (ae_restrict_of_ae_restrict_of_subset hsub hLip) h₀ (hx.mono hsub) (hy.mono hsub)
    (fun s hs ↦ hxe s (hsub hs)) (fun s hs ↦ hye s (hsub hs)) htJ

end TauCeti
