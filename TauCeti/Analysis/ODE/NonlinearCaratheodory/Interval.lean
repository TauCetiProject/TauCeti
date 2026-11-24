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

end TauCeti
