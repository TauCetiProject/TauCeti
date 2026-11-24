/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Analysis.ODE.NonlinearCaratheodory

/-!
# The nonlinear Carathéodory theorem on an interval

Let `I ⊆ ℝ` be an interval (bounded or not, open, closed or half-open) containing `t₀`, and let
`F : ℝ → E → E` be a time-dependent vector field on a Banach space `E` such that every section
`t ↦ F t x` is integrable on compact subsets of `I` and, for almost every `t ∈ I`, `F t` is
Lipschitz with constant `L t`, where `L` is integrable on compact subsets of `I`. Then the
integral equation `x t = x₀ + ∫ s in t₀..t, F s (x s)` has exactly one solution continuous on `I`.

On each compact subinterval of `I` containing `t₀` this is the nonlinear Carathéodory theorem of
`TauCeti/Analysis/ODE/NonlinearCaratheodory.lean`. The solution on `I` takes at `t` the value at
`t` of the solution on `[min t₀ t, max t₀ t]`; solutions on two compact subintervals agree on their
overlap, by uniqueness, and each point of `I` has a compact interval neighbourhood in `I`
containing `t₀`, on which the glued curve is the solution there, hence continuous.

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

/-- A point `t` of an interval `I` containing `t₀` has a compact interval neighbourhood in `I`
that contains `t₀`. -/
private theorem exists_Icc_mem_nhdsWithin (hI : I.OrdConnected) (ht₀ : t₀ ∈ I) {t : ℝ}
    (ht : t ∈ I) :
    ∃ c d, Icc c d ⊆ I ∧ t₀ ∈ Icc c d ∧ t ∈ Icc c d ∧ Icc c d ∈ nhdsWithin t I := by
  have hmin : min t₀ t ∈ I := by rcases min_choice t₀ t with h | h <;> rw [h] <;> assumption
  have hmax : max t₀ t ∈ I := by rcases max_choice t₀ t with h | h <;> rw [h] <;> assumption
  obtain ⟨c, hcI, hc, hct⟩ : ∃ c ∈ I, c ≤ min t₀ t ∧ (c < t ∨ ∀ y ∈ I, c ≤ y) := by
    by_cases h : ∃ c ∈ I, c < min t₀ t
    · obtain ⟨c, hcI, hc⟩ := h
      exact ⟨c, hcI, hc.le, Or.inl (hc.trans_le (min_le_right _ _))⟩
    · exact ⟨_, hmin, le_rfl, Or.inr fun y hy ↦ not_lt.mp fun h' ↦ h ⟨y, hy, h'⟩⟩
  obtain ⟨d, hdI, hd, htd⟩ : ∃ d ∈ I, max t₀ t ≤ d ∧ (t < d ∨ ∀ y ∈ I, y ≤ d) := by
    by_cases h : ∃ d ∈ I, max t₀ t < d
    · obtain ⟨d, hdI, hd⟩ := h
      exact ⟨d, hdI, hd.le, Or.inl ((le_max_right _ _).trans_lt hd)⟩
    · exact ⟨_, hmax, le_rfl, Or.inr fun y hy ↦ not_lt.mp fun h' ↦ h ⟨y, hy, h'⟩⟩
  have hleft : ∀ᶠ y in nhds t, y ∈ I → c ≤ y := by
    rcases hct with hct | hct
    · exact (lt_mem_nhds hct).mono fun y hy _ ↦ hy.le
    · exact Filter.Eventually.of_forall hct
  have hright : ∀ᶠ y in nhds t, y ∈ I → y ≤ d := by
    rcases htd with htd | htd
    · exact (gt_mem_nhds htd).mono fun y hy _ ↦ hy.le
    · exact Filter.Eventually.of_forall htd
  exact ⟨c, d, hI.out hcI hdI, ⟨hc.trans (min_le_left _ _), (le_max_left _ _).trans hd⟩,
    ⟨hc.trans (min_le_right _ _), (le_max_right _ _).trans hd⟩,
    mem_nhdsWithin_iff_eventually.mpr
      ((hleft.and hright).mono fun y hy hyI ↦ ⟨hy.1 hyI, hy.2 hyI⟩)⟩

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
  have hsub : Icc a b ∩ Icc a' b' ⊆ I := inter_subset_left.trans hab
  rw [Icc_inter_Icc] at hsub ⊢
  have hJ : Icc (max a a') (min b b') = Icc a b ∩ Icc a' b' := (Icc_inter_Icc).symm
  refine eqOn_of_forall_mem_Icc_eq_picard_of_lipschitzWith
    (fun x ↦ (hF x).integrableOn_compact_subset hsub isCompact_Icc)
    (hL.integrableOn_compact_subset hsub isCompact_Icc)
    (ae_restrict_of_ae_restrict_of_subset hsub hLip) (hJ ▸ ⟨h₀, h₀'⟩)
    (hx₁.mono (hJ ▸ inter_subset_left)) (hx₂.mono (hJ ▸ inter_subset_right))
    (fun t ht ↦ h₁ t (hJ ▸ ht).1) fun t ht ↦ h₂ t (hJ ▸ ht).2

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
  have hJ {t : ℝ} (ht : t ∈ I) : t₀ ∈ Icc (min t₀ t) (max t₀ t) ∧
      Icc (min t₀ t) (max t₀ t) ⊆ I :=
    ⟨⟨min_le_left _ _, le_max_left _ _⟩, hI.uIcc_subset ht₀ ht⟩
  -- the solution on any compact subinterval agrees with `x` there
  have hagree {a b : ℝ} (h₀ : t₀ ∈ Icc a b) (hab : Icc a b ⊆ I) {t : ℝ} (ht : t ∈ Icc a b) :
      y (min t₀ t) (max t₀ t) t = y a b t := by
    have ht' := hJ (hab ht)
    refine eqOn_inter_of_Icc_subset hF hL hLip ht'.2 ht'.1 h₀ (hyc _ _ ht'.1 ht'.2)
      (hyc _ _ h₀ hab) (hye _ _ ht'.1 ht'.2) (hye _ _ h₀ hab)
      ⟨⟨min_le_right _ _, le_max_right _ _⟩, ht⟩
  refine ⟨fun t ↦ y (min t₀ t) (max t₀ t) t, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · obtain ⟨c, d, hcd, h₀, htcd, hnhds⟩ := exists_Icc_mem_nhdsWithin hI ht₀ ht
    refine (((hyc c d h₀ hcd) t htcd).mono_of_mem_nhdsWithin hnhds).congr_of_eventuallyEq
      (Filter.mem_of_superset hnhds fun s hs ↦ hagree h₀ hcd hs) (hagree h₀ hcd htcd)
  · obtain ⟨h₀, hsub⟩ := hJ ht
    have htJ : t ∈ Icc (min t₀ t) (max t₀ t) := ⟨min_le_right _ _, le_max_right _ _⟩
    dsimp only
    rw [hye _ _ h₀ hsub t htJ, ODE.picard_apply, ODE.picard_apply]
    congr 1
    refine integral_congr fun s hs ↦ ?_
    have hs' : s ∈ Icc (min t₀ t) (max t₀ t) := by simpa [uIcc] using hs
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
  have hsub : Icc (min t₀ t) (max t₀ t) ⊆ I := hI.uIcc_subset ht₀ ht
  have h₀ : t₀ ∈ Icc (min t₀ t) (max t₀ t) := ⟨min_le_left _ _, le_max_left _ _⟩
  exact eqOn_inter_of_Icc_subset hF hL hLip hsub h₀ h₀ (hx₁.mono hsub) (hx₂.mono hsub)
    (fun s hs ↦ h₁ s (hsub hs)) (fun s hs ↦ h₂ s (hsub hs))
    ⟨⟨min_le_right _ _, le_max_right _ _⟩, ⟨min_le_right _ _, le_max_right _ _⟩⟩


end TauCeti
