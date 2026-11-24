/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Triangle

/-!
# Variation of constants

Let `E` be a Banach space over `𝕜`, and let `P : ℝ → E →L[𝕜] E` and `F : ℝ → E` be integrable on
`[a, b]`. For `t₀ ∈ [a, b]` and `y₀ : E`, the solution of the inhomogeneous linear equation

`x t = y₀ + ∫ u in t₀..t, (P u (x u) + F u)`

on `[a, b]` is given by the propagator `N_P` (`TauCeti.propagator`):

`x t = N_P(t, t₀) y₀ + ∫ s in t₀..t, N_P(t, s) (F s)`.

The proof expands `N_P(t, s) (F s) = F s + ∫ u in s..t, P u (N_P(u, s) (F s))` and exchanges the
order of integration over the triangle between `t₀` and `t`
(`intervalIntegral.integral_integral_swap_triangle`). No continuity of `P` or `F` is needed.

## Main results

* `TauCeti.integral_propagator_apply_eq`: the Duhamel term
  `w t = ∫ s in t₀..t, N_P(t, s) (F s)` satisfies `w t = ∫ u in t₀..t, (P u (w u) + F u)`.
* `TauCeti.continuousOn_propagator_apply_add_integral`: the variation of constants formula is
  continuous on `[a, b]`.
* `TauCeti.propagator_apply_add_integral_eq`: it solves the inhomogeneous equation.
* `TauCeti.eq_propagator_apply_add_integral`: every continuous solution is given by it.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 1, §7.
-/

public section

open MeasureTheory Set intervalIntegral

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [CompleteSpace E] {P : ℝ → E →L[𝕜] E} {F : ℝ → E} {a b t₀ t : ℝ}

namespace VariationOfConstants

/-- `(u, s) ↦ P u (N_P(u, s) (F s))` is integrable on `[a, b]²`. -/
private theorem integrableOn_prod (hP : IntegrableOn P (Icc a b))
    (hF : IntegrableOn F (Icc a b)) :
    IntegrableOn (fun p : ℝ × ℝ ↦ P p.1 (propagator P p.1 p.2 (F p.2))) (Icc a b ×ˢ Icc a b) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (continuousOn_propagator hP)
  have hμ : (volume.restrict (Icc a b)).prod (volume.restrict (Icc a b)) =
      (volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc a b) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hN : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ propagator P p.1 p.2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) := by
    rw [hμ]
    exact (continuousOn_propagator hP).aestronglyMeasurable
      (measurableSet_Icc.prod measurableSet_Icc)
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ P p.1 (propagator P p.1 p.2 (F p.2)))
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) :=
    (ContinuousLinearMap.id 𝕜 (E →L[𝕜] E)).aestronglyMeasurable_comp₂
      hP.aestronglyMeasurable.comp_fst
      ((ContinuousLinearMap.id 𝕜 (E →L[𝕜] E)).aestronglyMeasurable_comp₂ hN
        hF.aestronglyMeasurable.comp_snd)
  have hbound : Integrable (fun p : ℝ × ℝ ↦ C * (‖P p.1‖ * ‖F p.2‖))
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))) :=
    (hP.norm.mul_prod hF.norm).const_mul C
  rw [IntegrableOn, ← hμ]
  refine hbound.mono' hmeas ?_
  rw [hμ, ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)]
  refine ae_of_all _ fun p hp ↦ ?_
  calc ‖P p.1 (propagator P p.1 p.2 (F p.2))‖
      ≤ ‖P p.1‖ * (‖propagator P p.1 p.2‖ * ‖F p.2‖) :=
        (P p.1).le_opNorm_of_le ((propagator P p.1 p.2).le_opNorm _)
    _ ≤ ‖P p.1‖ * (C * ‖F p.2‖) := by gcongr; exact hC p hp
    _ = C * (‖P p.1‖ * ‖F p.2‖) := by ring

/-- The iterated integral of `P u (N_P(u, s) (F s))` over the triangle between `t₀` and `t`, in
either order. -/
private theorem integral_integral_swap (hP : IntegrableOn P (Icc a b))
    (hF : IntegrableOn F (Icc a b)) (h₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∫ s in t₀..t, ∫ u in s..t, P u (propagator P u s (F s)) =
      ∫ u in t₀..t, ∫ s in t₀..u, P u (propagator P u s (F s)) := by
  have hsub : uIcc t₀ t ×ˢ uIcc t₀ t ⊆ Icc a b ×ˢ Icc a b :=
    prod_mono (uIcc_subset_Icc h₀ ht) (uIcc_subset_Icc h₀ ht)
  exact (integral_integral_swap_triangle (g := fun u s ↦ P u (propagator P u s (F s)))
    ((integrableOn_prod hP hF).mono_set hsub)).symm

end VariationOfConstants

open VariationOfConstants

/-- On `[a, b]`, the Duhamel term `∫ s in t₀..t, N_P(t, s) (F s)` is
`N_P(t, a) (∫ s in t₀..t, N_P(a, s) (F s))`. -/
private theorem integral_propagator_apply_eq_propagator_apply (hP : IntegrableOn P (Icc a b))
    (hF : IntegrableOn F (Icc a b)) (h₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∫ s in t₀..t, propagator P t s (F s) =
      propagator P t a (∫ s in t₀..t, propagator P a s (F s)) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, h₀.1.trans h₀.2⟩
  have hI : IntervalIntegrable (fun s ↦ propagator P a s (F s)) volume t₀ t :=
    ((hF.continuousOn_clm_apply (continuousOn_propagator_right hP ha) isCompact_Icc).mono_set
      (uIcc_subset_Icc h₀ ht)).intervalIntegrable
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hI]
  refine integral_congr fun s hs ↦ ?_
  rw [← ContinuousLinearMap.comp_apply,
    propagator_comp_propagator hP ha (uIcc_subset_Icc h₀ ht hs) ht]

/-- The Duhamel term `t ↦ ∫ s in t₀..t, N_P(t, s) (F s)` is continuous on `[a, b]`. -/
private theorem continuousOn_integral_propagator_apply (hP : IntegrableOn P (Icc a b))
    (hF : IntegrableOn F (Icc a b)) (h₀ : t₀ ∈ Icc a b) :
    ContinuousOn (fun t ↦ ∫ s in t₀..t, propagator P t s (F s)) (Icc a b) := by
  have hab : a ≤ b := h₀.1.trans h₀.2
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hG : ContinuousOn (fun t ↦ ∫ s in t₀..t, propagator P a s (F s)) (Icc a b) := by
    have := continuousOn_primitive_interval' (μ := volume) (a := t₀)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
        (hF.continuousOn_clm_apply (continuousOn_propagator_right hP ha) isCompact_Icc))
      (by rwa [uIcc_of_le hab])
    rwa [uIcc_of_le hab] at this
  exact ((continuousOn_propagator_left hP ha).clm_apply hG).congr fun t ht ↦
    integral_propagator_apply_eq_propagator_apply hP hF h₀ ht

/-- **The Duhamel term solves the inhomogeneous equation with zero initial value.** For `t₀, t` in
`[a, b]`, `w t = ∫ s in t₀..t, N_P(t, s) (F s)` satisfies
`w t = ∫ u in t₀..t, (P u (w u) + F u)`. -/
theorem integral_propagator_apply_eq (hP : IntegrableOn P (Icc a b))
    (hF : IntegrableOn F (Icc a b)) (h₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∫ s in t₀..t, propagator P t s (F s) =
      ∫ u in t₀..t, (P u (∫ s in t₀..u, propagator P u s (F s)) + F u) := by
  have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc h₀ ht
  have hFi : IntervalIntegrable F volume t₀ t := (hF.mono_set hsub).intervalIntegrable
  -- Expand `N_P(t, s) (F s) = F s + ∫ u in s..t, P u (N_P(u, s) (F s))`.
  have hexp : ∀ s ∈ uIcc t₀ t, propagator P t s (F s) =
      F s + ∫ u in s..t, P u (propagator P u s (F s)) := fun s hs ↦
    propagator_apply_eq_add_integral hP (hsub hs) ht (F s)
  have hinner : IntervalIntegrable (fun s ↦ ∫ u in s..t, P u (propagator P u s (F s)))
      volume t₀ t := by
    refine ((((hF.continuousOn_clm_apply (continuousOn_propagator_right hP ht)
      isCompact_Icc).mono_set hsub).intervalIntegrable).sub hFi).congr fun s hs ↦ ?_
    simp only [hexp s (uIoc_subset_uIcc hs), add_sub_cancel_left]
  -- Pull `P u` out of the inner integrals.
  have hpull : ∀ u ∈ uIcc t₀ t, ∫ s in t₀..u, P u (propagator P u s (F s)) =
      P u (∫ s in t₀..u, propagator P u s (F s)) := fun u hu ↦
    ContinuousLinearMap.intervalIntegral_comp_comm _
      ((hF.continuousOn_clm_apply (continuousOn_propagator_right hP (hsub hu))
        isCompact_Icc).mono_set
        (uIcc_subset_Icc h₀ (hsub hu))).intervalIntegrable
  have hw : IntervalIntegrable (fun u ↦ P u (∫ s in t₀..u, propagator P u s (F s))) volume t₀ t :=
    ((hP.clm_apply_continuousOn (continuousOn_integral_propagator_apply hP hF h₀)
      isCompact_Icc).mono_set hsub).intervalIntegrable
  rw [integral_congr hexp, integral_add hFi hinner, integral_integral_swap hP hF h₀ ht,
    integral_congr hpull, integral_add hw hFi, add_comm]

/-- The variation of constants formula `t ↦ N_P(t, t₀) y₀ + ∫ s in t₀..t, N_P(t, s) (F s)` is
continuous on `[a, b]`. -/
theorem continuousOn_propagator_apply_add_integral (hP : IntegrableOn P (Icc a b))
    (hF : IntegrableOn F (Icc a b)) (h₀ : t₀ ∈ Icc a b) (y₀ : E) :
    ContinuousOn (fun t ↦ propagator P t t₀ y₀ + ∫ s in t₀..t, propagator P t s (F s))
      (Icc a b) :=
  ((continuousOn_propagator_left hP h₀).clm_apply continuousOn_const).add
    (continuousOn_integral_propagator_apply hP hF h₀)

/-- **Variation of constants.** For `P` and `F` integrable on `[a, b]` and `t₀, t ∈ [a, b]`,
`x t = N_P(t, t₀) y₀ + ∫ s in t₀..t, N_P(t, s) (F s)` satisfies
`x t = y₀ + ∫ u in t₀..t, (P u (x u) + F u)`. -/
theorem propagator_apply_add_integral_eq (hP : IntegrableOn P (Icc a b))
    (hF : IntegrableOn F (Icc a b)) (h₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b) (y₀ : E) :
    propagator P t t₀ y₀ + ∫ s in t₀..t, propagator P t s (F s) =
      y₀ + ∫ u in t₀..t,
        (P u (propagator P u t₀ y₀ + ∫ s in t₀..u, propagator P u s (F s)) + F u) := by
  have hN := (continuousOn_propagator_left hP h₀).clm_apply (continuousOn_const (c := y₀))
  have hw := continuousOn_integral_propagator_apply hP hF h₀
  have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc h₀ ht
  rw [propagator_apply_eq_add_integral hP h₀ ht y₀, integral_propagator_apply_eq hP hF h₀ ht,
    add_assoc, ← integral_add
      (((hP.clm_apply_continuousOn hN isCompact_Icc).mono_set hsub).intervalIntegrable)
      ((((hP.clm_apply_continuousOn hw isCompact_Icc).mono_set hsub).intervalIntegrable).add
        (hF.mono_set hsub).intervalIntegrable)]
  congr 1
  refine integral_congr fun u _ ↦ ?_
  simp only [map_add, add_assoc]

/-- **Solutions of the inhomogeneous equation are given by variation of constants.** A curve `x`
continuous on `[a, b]` with `x r = x t₀ + ∫ u in t₀..r, (P u (x u) + F u)` for `r ∈ [a, b]`
satisfies `x t = N_P(t, t₀) (x t₀) + ∫ s in t₀..t, N_P(t, s) (F s)`. -/
theorem eq_propagator_apply_add_integral (hP : IntegrableOn P (Icc a b))
    (hF : IntegrableOn F (Icc a b)) (h₀ : t₀ ∈ Icc a b) (ht : t ∈ Icc a b) {x : ℝ → E}
    (hx : ContinuousOn x (Icc a b))
    (h : ∀ r ∈ Icc a b, x r = x t₀ + ∫ u in t₀..r, (P u (x u) + F u)) :
    x t = propagator P t t₀ (x t₀) + ∫ s in t₀..t, propagator P t s (F s) := by
  have hpicard (y : ℝ → E) (r : ℝ) : ODE.picard (fun u z ↦ (P u).restrictScalars ℝ z + F u) t₀
      (x t₀) y r = x t₀ + ∫ u in t₀..r, (P u (y u) + F u) := by
    simp [ODE.picard_apply]
  exact eqOn_of_forall_mem_Icc_eq_picard (M := fun u ↦ (P u).restrictScalars ℝ) (F := F)
    (x₀ := x t₀) h₀ ((ContinuousLinearMap.restrictScalarsL 𝕜 E E ℝ ℝ).integrable_comp hP) hF hx
    (continuousOn_propagator_apply_add_integral hP hF h₀ (x t₀))
    (fun r hr ↦ (h r hr).trans (hpicard x r).symm)
    (fun r hr ↦ (propagator_apply_add_integral_eq hP hF h₀ hr (x t₀)).trans
      (hpicard _ r).symm) ht

end TauCeti
