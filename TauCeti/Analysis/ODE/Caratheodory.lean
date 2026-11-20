/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import TauCeti.Analysis.ODE.Caratheodory.Integrable

/-!
# Linear differential equations with measurable coefficients

Let `E` be a real normed space and consider the linear initial value problem

`x' = M(t) x + F(t)`, `x(a) = x₀`

on `[a, b]`, where `M : ℝ → E →L[ℝ] E` is almost everywhere strongly measurable and essentially
bounded by `K` on `(a, b)`, and `F : ℝ → E` is integrable there. Neither `M` nor `F` need be
continuous in `t`, so Mathlib's Picard–Lindelöf theorem does not apply; the equation is understood
in Carathéodory's sense, as the integral equation

`x t = x₀ + ∫ s in a..t, (M s (x s) + F s)`,

that is `x = ODE.picard (fun s y ↦ M s y + F s) a x₀ x` on `[a, b]`, for `x` continuous on
`[a, b]`. This file proves that this equation has a solution
(`TauCeti.exists_continuousOn_eq_forall_mem_Icc_eq_picard`) and that the solution is unique
(`TauCeti.eqOn_of_forall_mem_Icc_eq_picard`). For continuous coefficients and classical
solutions on the whole line, `Continuous.eq_of_hasDerivAt_clm_apply` deduces uniqueness for
`v' = B(t) v` from Mathlib's `ODE_solution_unique_of_mem_Ioo`, and
`Continuous.eqOn_Ici_of_hasDerivAt_clm_apply` does the same in forward time on a half-line
`[a, ∞)` from `ODE_solution_unique_of_mem_Icc_right`.

Linear equations with merely measurable, bounded coefficients arise as the Galerkin
approximations of linear parabolic equations, whose coefficients are only measurable in time.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 2.
* Mathlib's `Mathlib/Analysis/ODE/PicardLindelof.lean` (Yury Kudryashov, Winston Yin). The
  existence and uniqueness proofs, in `TauCeti.Analysis.ODE.Caratheodory.Integrable` for integrable
  coefficients, follow its argument that some iterate of the Picard map is a contraction.
-/

public section

open Function MeasureTheory Set intervalIntegral
open scoped Nat NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : ℝ → E →L[ℝ] E} {F : ℝ → E}
  {a b K : ℝ} {x₀ : E}

/-- The right-hand side `s ↦ M s (x s) + F s` of a linear equation with essentially bounded
measurable `M` and integrable `F` on `(a, b)` is integrable on `(a, b)` along every curve `x`
continuous on `[a, b]`. -/
theorem integrableOn_clm_apply_add (hM : AEStronglyMeasurable M (volume.restrict (Ioo a b)))
    (hK : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ K) (hF : IntegrableOn F (Ioo a b))
    {x : ℝ → E} (hx : ContinuousOn x (Icc a b)) :
    IntegrableOn (fun s ↦ M s (x s) + F s) (Ioo a b) := by
  refine IntegrableOn.add ?_ hF
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  refine (integrable_const (max K 0 * max C 0)).mono'
    ((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).aestronglyMeasurable_comp₂ hM
      ((hx.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)) ?_
  filter_upwards [hK, ae_restrict_mem measurableSet_Ioo] with s hs hs'
  exact ((M s).le_opNorm _).trans (mul_le_mul (hs.trans (le_max_left _ _))
    ((hC s (Ioo_subset_Icc_self hs')).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _))

/-- An almost everywhere strongly measurable coefficient essentially bounded on `(a, b)` is
integrable on `[a, b]`. -/
private theorem integrableOn_Icc_of_ae_norm_le
    (hM : AEStronglyMeasurable M (volume.restrict (Ioo a b)))
    (hK : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ K) : IntegrableOn M (Icc a b) :=
  (integrableOn_Icc_iff_integrableOn_Ioo).2 (Integrable.of_bound hM K hK)

/-- **Carathéodory's existence theorem for linear equations.** Let `M : ℝ → E →L[ℝ] E` be almost
everywhere strongly measurable and essentially bounded on `(a, b)`, and let `F : ℝ → E` be
integrable on `(a, b)`. Then the linear equation `x' = M(t) x + F(t)` with `x(a) = x₀` has a
solution in Carathéodory's sense: a curve `x` continuous on `[a, b]` with `x a = x₀` and
`x t = x₀ + ∫ s in a..t, (M s (x s) + F s)` for every `t ∈ [a, b]`. -/
theorem exists_continuousOn_eq_forall_mem_Icc_eq_picard
    (hM : AEStronglyMeasurable M (volume.restrict (Ioo a b)))
    (hK : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ K) (hF : IntegrableOn F (Ioo a b)) (x₀ : E) :
    ∃ x : ℝ → E, ContinuousOn x (Icc a b) ∧ x a = x₀ ∧
      ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) a x₀ x t := by
  rcases lt_or_ge b a with hba | hab
  · exact ⟨fun _ ↦ x₀, continuousOn_const, rfl, by simp [Icc_eq_empty_of_lt hba]⟩
  obtain ⟨x, hx, h⟩ := exists_continuousOn_forall_mem_Icc_eq_add_integral (left_mem_Icc.2 hab) x₀
    (integrableOn_Icc_of_ae_norm_le hM hK) ((integrableOn_Icc_iff_integrableOn_Ioo).2 hF)
  exact ⟨x, hx, by simpa using h a (left_mem_Icc.2 hab), fun t ht ↦ by
    rw [ODE.picard_apply]; exact h t ht⟩

/-- **Uniqueness for linear equations with measurable coefficients.** Let `M : ℝ → E →L[ℝ] E` be
almost everywhere strongly measurable and essentially bounded on `(a, b)`, and let `F : ℝ → E` be
integrable on `(a, b)`. Two curves continuous on `[a, b]` that solve
`x t = x₀ + ∫ s in a..t, (M s (x s) + F s)` on `[a, b]` agree on `[a, b]`. -/
theorem eqOn_of_forall_mem_Icc_eq_picard
    (hM : AEStronglyMeasurable M (volume.restrict (Ioo a b)))
    (hK : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ K) (hF : IntegrableOn F (Ioo a b))
    {x₁ x₂ : ℝ → E} (hx₁ : ContinuousOn x₁ (Icc a b)) (hx₂ : ContinuousOn x₂ (Icc a b))
    (h₁ : ∀ t ∈ Icc a b, x₁ t = ODE.picard (fun s y ↦ M s y + F s) a x₀ x₁ t)
    (h₂ : ∀ t ∈ Icc a b, x₂ t = ODE.picard (fun s y ↦ M s y + F s) a x₀ x₂ t) :
    EqOn x₁ x₂ (Icc a b) := by
  rcases lt_or_ge b a with hba | hab
  · simp [Icc_eq_empty_of_lt hba]
  simp only [ODE.picard_apply] at h₁ h₂
  exact eqOn_of_forall_mem_Icc_eq_add_integral (left_mem_Icc.2 hab)
    (integrableOn_Icc_of_ae_norm_le hM hK) ((integrableOn_Icc_iff_integrableOn_Ioo).2 hF)
    hx₁ hx₂ h₁ h₂

end TauCeti

/-- **Uniqueness for time-dependent linear equations.** Two solutions of `v' = B(t) v` on the line,
for a continuous family `B` of bounded operators, that agree at one time agree everywhere. On a
bounded interval `B` is bounded, so the equation is uniformly Lipschitz there. -/
theorem Continuous.eq_of_hasDerivAt_clm_apply {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {B : ℝ → X →L[ℝ] X} (hB : Continuous B) {v w : ℝ → X}
    (hv : ∀ t, HasDerivAt v (B t (v t)) t) (hw : ∀ t, HasDerivAt w (B t (w t)) t) {t₀ : ℝ}
    (h : v t₀ = w t₀) : v = w := by
  funext t
  set a := min t t₀ - 1
  set b := max t t₀ + 1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hB.continuousOn (s := Icc a b))
  have hLip (s : ℝ) (hs : s ∈ Ioo a b) : LipschitzOnWith (Real.toNNReal C) (B s) univ :=
    ((B s).lipschitzWith.weaken (NNReal.le_toNNReal_of_coe_le (by
      simpa using hC s (Ioo_subset_Icc_self hs)))).lipschitzOnWith
  exact ODE_solution_unique_of_mem_Ioo (v := fun s ↦ B s) (s := fun _ ↦ univ) hLip
    (t₀ := t₀) ⟨by grind, by grind⟩ (fun s _ ↦ ⟨hv s, mem_univ _⟩)
    (fun s _ ↦ ⟨hw s, mem_univ _⟩) h ⟨by grind, by grind⟩

/-- **Forward uniqueness for time-dependent linear equations.** Two solutions of `v' = B(t) v` on
the half-line `[a, ∞)`, for a continuous family `B` of bounded operators, that agree at time `a`
agree on `[a, ∞)`. The equation is only required at times `t ≥ a` (with a two-sided derivative at
`a`), so the two solutions may come from equations that only agree on `[a, ∞)`. -/
theorem Continuous.eqOn_Ici_of_hasDerivAt_clm_apply {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {B : ℝ → X →L[ℝ] X} (hB : Continuous B) {v w : ℝ → X} {a : ℝ}
    (hv : ∀ t, a ≤ t → HasDerivAt v (B t (v t)) t) (hw : ∀ t, a ≤ t → HasDerivAt w (B t (w t)) t)
    (h : v a = w a) : EqOn v w (Ici a) := by
  intro t (ht : a ≤ t)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hB.continuousOn (s := Icc a t))
  have hLip (s : ℝ) (hs : s ∈ Ico a t) : LipschitzOnWith (Real.toNNReal C) (B s) univ :=
    ((B s).lipschitzWith.weaken (NNReal.le_toNNReal_of_coe_le (by
      simpa using hC s (Ico_subset_Icc_self hs)))).lipschitzOnWith
  exact ODE_solution_unique_of_mem_Icc_right (v := fun s ↦ B s) (s := fun _ ↦ univ) hLip
    (HasDerivAt.continuousOn fun s hs ↦ hv s hs.1) (fun s hs ↦ (hv s hs.1).hasDerivWithinAt)
    (fun _ _ ↦ mem_univ _) (HasDerivAt.continuousOn fun s hs ↦ hw s hs.1)
    (fun s hs ↦ (hw s hs.1).hasDerivWithinAt) (fun _ _ ↦ mem_univ _) h ⟨ht, le_rfl⟩
