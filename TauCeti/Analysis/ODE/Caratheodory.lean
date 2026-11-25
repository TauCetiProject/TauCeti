/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Analysis.ODE.Gronwall.Integrable
import TauCeti.Analysis.ODE.NonlinearCaratheodory.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Linear differential equations with integrable coefficients

Let `E` be a Banach space and consider the linear initial value problem

`x' = M(t) x + F(t)`, `x(t₀) = x₀`

on `[a, b]`, with `t₀ ∈ [a, b]`, where the coefficient `M : ℝ → E →L[ℝ] E` and the forcing term
`F : ℝ → E` are integrable on `[a, b]`. Neither need be continuous in `t`, and `M` need not be
essentially bounded, so Mathlib's Picard–Lindelöf theorem does not apply; the equation is
understood in Carathéodory's sense, as the integral equation

`x t = x₀ + ∫ s in t₀..t, (M s (x s) + F s)`,

that is `x = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x` on `[a, b]`, for `x` continuous on
`[a, b]`.

## Main results

* `TauCeti.exists_continuousOn_forall_mem_Icc_eq_picard`: the integral equation
  has a solution continuous on `[a, b]`.
* `TauCeti.eqOn_of_forall_mem_Icc_eq_picard`: two such solutions agree on
  `[a, b]`.
* `TauCeti.absolutelyContinuousOnInterval_of_forall_mem_Icc_eq_picard` and
  `TauCeti.ae_hasDerivAt_of_forall_mem_Icc_eq_picard`: every solution is absolutely continuous
  on `[a, b]`, with derivative `M t (x t) + F t` at almost every `t ∈ (a, b)`.
* `TauCeti.forall_mem_Icc_eq_picard_of_absolutelyContinuousOnInterval`: conversely, an absolutely
  continuous curve with `x t₀ = x₀` and this derivative almost everywhere solves the integral
  equation.
* `TauCeti.norm_le_mul_exp_of_forall_mem_Icc_eq_picard`: every solution satisfies
  `‖x t‖ ≤ (‖x₀‖ + |∫ s in t₀..t, ‖F s‖|) exp |∫ s in t₀..t, ‖M s‖|`.

Such equations arise as the Galerkin approximations of linear parabolic equations, whose
coefficients are only measurable in time; integrable but unbounded coefficients arise for Dirac and
Schrödinger systems with locally integrable potentials.
For continuous coefficients and classical solutions on the whole line,
`Continuous.eq_of_hasDerivAt_clm_apply` deduces uniqueness for `v' = B(t) v` from Mathlib's
`ODE_solution_unique_of_mem_Ioo`, and `Continuous.eqOn_Ici_of_hasDerivAt_clm_apply` does the same
in forward time on a half-line `[a, ∞)` from `ODE_solution_unique_of_mem_Icc_right`. A solution of
`v' = B(t) v` that lies at one time in a closed complemented subspace invariant under every `B(t)`
lies in it at all times (`Continuous.mem_of_hasDerivAt_clm_apply`).

## Implementation notes

The vector field `(t, z) ↦ M t z + F t` has integrable sections and is Lipschitz in `z` with the
integrable constant `‖M t‖`, so existence, uniqueness, absolute continuity and the derivative of
solutions are instances of the nonlinear Carathéodory theorem in
`TauCeti/Analysis/ODE/NonlinearCaratheodory/Basic.lean`
(`TauCeti.exists_continuousOn_forall_mem_Icc_eq_picard_of_lipschitzWith` and its companions). The
norm bound follows from Grönwall's inequality with an integrable kernel on either side of `t₀`
(`TauCeti.le_mul_exp_abs_integral_of_le_add_abs_integral_mul`).

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 2, §1.
* Mathlib's `Mathlib/Analysis/ODE/PicardLindelof.lean` (Yury Kudryashov, Winston Yin). The
  existence and uniqueness proofs, through the nonlinear Carathéodory theorem, follow its argument
  that some iterate of the Picard map is a contraction.
-/

public section

open Function MeasureTheory Set intervalIntegral Real
open scoped Nat NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : ℝ → E →L[ℝ] E} {F : ℝ → E}
  {a b t₀ : ℝ} {x₀ : E}

/-- The right-hand side `s ↦ M s (x s) + F s` of a linear equation whose coefficient `M` and
forcing term `F` are integrable on `[a, b]` is integrable on `[a, b]` along every curve `x`
continuous on `[a, b]`. -/
theorem integrableOn_Icc_clm_apply_add (hM : IntegrableOn M (Icc a b))
    (hF : IntegrableOn F (Icc a b)) {x : ℝ → E} (hx : ContinuousOn x (Icc a b)) :
    IntegrableOn (fun s ↦ M s (x s) + F s) (Icc a b) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  exact ((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).integrable_of_bilin_of_bdd_right C hM
    (hx.aestronglyMeasurable measurableSet_Icc)
    ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ hC))).add hF

/-- The right-hand side `s ↦ M s (x s) + F s` of a linear equation whose coefficient `M` and
forcing term `F` are integrable on `[a, b]`, with `a ≤ b`, is interval integrable on `a..b` along
every curve `x` continuous on `[a, b]`. -/
theorem intervalIntegrable_clm_apply_add (hab : a ≤ b) (hM : IntegrableOn M (Icc a b))
    (hF : IntegrableOn F (Icc a b)) {x : ℝ → E} (hx : ContinuousOn x (Icc a b)) :
    IntervalIntegrable (fun s ↦ M s (x s) + F s) volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 (integrableOn_Icc_clm_apply_add hM hF hx)

/-- The linear vector field `(t, z) ↦ M t z + F t` satisfies the hypotheses of the nonlinear
Carathéodory theorem `TauCeti.exists_continuousOn_forall_mem_Icc_eq_picard_of_lipschitzWith`, with
the Lipschitz constant `‖M t‖₊`. -/
private theorem integrableOn_and_lipschitzWith_clm_apply_add (hM : IntegrableOn M (Icc a b))
    (hF : IntegrableOn F (Icc a b)) :
    (∀ x, IntegrableOn (fun t ↦ M t x + F t) (Icc a b)) ∧
      IntegrableOn (fun t ↦ ((‖M t‖₊ : ℝ≥0) : ℝ)) (Icc a b) ∧
      ∀ᵐ t ∂volume.restrict (Icc a b), LipschitzWith ‖M t‖₊ fun z ↦ M t z + F t :=
  ⟨fun _ ↦ integrableOn_Icc_clm_apply_add hM hF continuousOn_const,
    by simp only [coe_nnNorm]; exact hM.norm,
    ae_of_all _ fun t ↦ (M t).lipschitzWith_add_const (F t)⟩

/-- **Carathéodory's existence theorem for linear equations with integrable coefficients.** Let
`M : ℝ → E →L[ℝ] E` and `F : ℝ → E` be integrable on `[a, b]` and let `t₀ ∈ [a, b]`. Then the
linear equation `x' = M(t) x + F(t)` with `x(t₀) = x₀` has a solution in Carathéodory's sense: a
curve `x` continuous on `[a, b]` with `x t = x₀ + ∫ s in t₀..t, (M s (x s) + F s)` for every
`t ∈ [a, b]`. -/
theorem exists_continuousOn_forall_mem_Icc_eq_picard [CompleteSpace E]
    (ht₀ : t₀ ∈ Icc a b) (hM : IntegrableOn M (Icc a b)) (hF : IntegrableOn F (Icc a b))
    (x₀ : E) :
    ∃ x : ℝ → E, ContinuousOn x (Icc a b) ∧
      ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x t :=
  have ⟨hG, hL, hLip⟩ := integrableOn_and_lipschitzWith_clm_apply_add hM hF
  exists_continuousOn_forall_mem_Icc_eq_picard_of_lipschitzWith hG hL hLip ht₀ x₀

/-- **Uniqueness for linear equations with integrable coefficients.** Let `M : ℝ → E →L[ℝ] E` and
`F : ℝ → E` be integrable on `[a, b]` and let `t₀ ∈ [a, b]`. Two curves continuous on `[a, b]`
that solve `x t = x₀ + ∫ s in t₀..t, (M s (x s) + F s)` on `[a, b]` agree on `[a, b]`. -/
theorem eqOn_of_forall_mem_Icc_eq_picard (ht₀ : t₀ ∈ Icc a b)
    (hM : IntegrableOn M (Icc a b)) (hF : IntegrableOn F (Icc a b)) {x₁ x₂ : ℝ → E}
    (hx₁ : ContinuousOn x₁ (Icc a b)) (hx₂ : ContinuousOn x₂ (Icc a b))
    (h₁ : ∀ t ∈ Icc a b, x₁ t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x₁ t)
    (h₂ : ∀ t ∈ Icc a b, x₂ t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x₂ t) :
    EqOn x₁ x₂ (Icc a b) :=
  have ⟨hG, hL, hLip⟩ := integrableOn_and_lipschitzWith_clm_apply_add hM hF
  eqOn_of_forall_mem_Icc_eq_picard_of_lipschitzWith hG hL hLip ht₀ hx₁ hx₂ h₁ h₂

/-- A solution of the linear integral equation `x t = x₀ + ∫ s in t₀..t, (M s (x s) + F s)` on
`[a, b]`, with `M` and `F` integrable on `[a, b]`, is absolutely continuous on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_of_forall_mem_Icc_eq_picard (ht₀ : t₀ ∈ Icc a b)
    (hM : IntegrableOn M (Icc a b)) (hF : IntegrableOn F (Icc a b)) {x : ℝ → E}
    (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x t) :
    AbsolutelyContinuousOnInterval x a b :=
  have ⟨hG, hL, hLip⟩ := integrableOn_and_lipschitzWith_clm_apply_add hM hF
  absolutelyContinuousOnInterval_of_forall_mem_Icc_eq_picard_of_lipschitzWith hG hL hLip ht₀ hx h

/-- A solution of the linear integral equation `x t = x₀ + ∫ s in t₀..t, (M s (x s) + F s)` on
`[a, b]`, with `M` and `F` integrable on `[a, b]`, has derivative `M t (x t) + F t` at almost
every `t ∈ (a, b)`. -/
theorem ae_hasDerivAt_of_forall_mem_Icc_eq_picard [CompleteSpace E] (ht₀ : t₀ ∈ Icc a b)
    (hM : IntegrableOn M (Icc a b)) (hF : IntegrableOn F (Icc a b)) {x : ℝ → E}
    (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x t) :
    ∀ᵐ t, t ∈ Ioo a b → HasDerivAt x (M t (x t) + F t) t :=
  have ⟨hG, hL, hLip⟩ := integrableOn_and_lipschitzWith_clm_apply_add hM hF
  ae_hasDerivAt_of_forall_mem_Icc_eq_picard_of_lipschitzWith hG hL hLip ht₀ hx h

/-- **Absolutely continuous solutions.** Let `M : ℝ → E →L[ℝ] E` and `F : ℝ → E` be integrable on
`[a, b]` and let `t₀ ∈ [a, b]`. A curve `x` absolutely continuous on `[a, b]` with `x t₀ = x₀` and
derivative `M t (x t) + F t` at almost every `t ∈ (a, b)` solves the integral equation
`x t = x₀ + ∫ s in t₀..t, (M s (x s) + F s)` on `[a, b]`. -/
theorem forall_mem_Icc_eq_picard_of_absolutelyContinuousOnInterval [CompleteSpace E]
    (ht₀ : t₀ ∈ Icc a b) (hM : IntegrableOn M (Icc a b)) (hF : IntegrableOn F (Icc a b))
    {x : ℝ → E} (hx : AbsolutelyContinuousOnInterval x a b) (hx₀ : x t₀ = x₀)
    (hd : ∀ᵐ t, t ∈ Ioo a b → HasDerivAt x (M t (x t) + F t) t) :
    ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x t := by
  have hab := ht₀.1.trans ht₀.2
  have hxc : ContinuousOn x (Icc a b) := by simpa [uIcc_of_le hab] using hx.continuousOn
  have hI := intervalIntegrable_clm_apply_add hab hM hF hxc
  have ht₀' : t₀ ∈ uIcc a b := by rwa [uIcc_of_le hab]
  -- `x` minus the primitive of its derivative is constant on `[a, b]`.
  obtain ⟨C, hC⟩ := (hx.sub (hI.absolutelyContinuousOnInterval_intervalIntegral' ht₀')
    ).const_of_ae_hasDerivAt_zero (by
      filter_upwards [hd, hI.ae_hasDerivAt_integral, Measure.ae_ne volume a,
        Measure.ae_ne volume b] with t hdt hit hta htb htI
      have htI' : t ∈ Icc a b := by rwa [uIcc_of_le hab] at htI
      simpa only [sub_self] using
        (hdt ⟨htI'.1.lt_of_ne' hta, htI'.2.lt_of_ne htb⟩).sub (hit htI t₀ ht₀'))
  intro t ht
  have h₁ := hC t (by rwa [uIcc_of_le hab])
  have h₂ := hC t₀ ht₀'
  simp only [Pi.sub_apply, integral_same, sub_zero, hx₀] at h₁ h₂
  rw [ODE.picard_apply, h₂, ← h₁, sub_add_cancel]

/-- **A priori bound for linear equations with integrable coefficients.** Let
`M : ℝ → E →L[ℝ] E` and `F : ℝ → E` be integrable on `[a, b]` and let `t₀ ∈ [a, b]`. A solution
of `x t = x₀ + ∫ s in t₀..t, (M s (x s) + F s)` on `[a, b]` satisfies
`‖x t‖ ≤ (‖x₀‖ + |∫ s in t₀..t, ‖F s‖|) exp |∫ s in t₀..t, ‖M s‖|` for every `t ∈ [a, b]`. -/
theorem norm_le_mul_exp_of_forall_mem_Icc_eq_picard (ht₀ : t₀ ∈ Icc a b)
    (hM : IntegrableOn M (Icc a b)) (hF : IntegrableOn F (Icc a b)) {x : ℝ → E}
    (hx : ContinuousOn x (Icc a b))
    (h : ∀ t ∈ Icc a b, x t = ODE.picard (fun s y ↦ M s y + F s) t₀ x₀ x t) {t : ℝ}
    (ht : t ∈ Icc a b) :
    ‖x t‖ ≤ (‖x₀‖ + |∫ s in t₀..t, ‖F s‖|) * exp |∫ s in t₀..t, ‖M s‖| := by
  have hsub : uIcc t₀ t ⊆ Icc a b := uIcc_subset_Icc ht₀ ht
  refine le_mul_exp_abs_integral_of_le_add_abs_integral_mul (u := fun s ↦ ‖x s‖)
    (IntegrableOn.mono_set hM.norm hsub) (ae_of_all _ fun _ ↦ norm_nonneg _)
    ((IntegrableOn.mono_set hM.norm hsub).mul_continuousOn (hx.mono hsub).norm isCompact_uIcc)
    (fun _ _ ↦ norm_nonneg _) fun s hs ↦ ?_
  have hsub' : uIcc t₀ s ⊆ Icc a b := uIcc_subset_Icc ht₀ (hsub hs)
  have hFi : IntervalIntegrable (fun r ↦ ‖F r‖) volume t₀ s :=
    (IntegrableOn.mono_set hF.norm hsub').intervalIntegrable
  have hMx : IntervalIntegrable (fun r ↦ ‖M r‖ * ‖x r‖) volume t₀ s :=
    ((IntegrableOn.mono_set hM.norm hsub').mul_continuousOn (hx.mono hsub').norm
      isCompact_uIcc).intervalIntegrable
  -- The integral of `‖F‖` grows with the interval.
  have hFmono : |∫ r in t₀..s, ‖F r‖| ≤ |∫ r in t₀..t, ‖F r‖| :=
    abs_integral_mono_interval (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc_left hs))
      (ae_of_all _ fun _ ↦ norm_nonneg _) (IntegrableOn.mono_set hF.norm hsub).intervalIntegrable
  rw [h s (hsub hs), ODE.picard_apply]
  calc ‖x₀ + ∫ r in t₀..s, (M r (x r) + F r)‖
      ≤ ‖x₀‖ + |∫ r in t₀..s, (‖F r‖ + ‖M r‖ * ‖x r‖)| := by
        refine (norm_add_le _ _).trans
          (add_le_add le_rfl (norm_integral_le_abs_of_norm_le (ae_of_all _ fun r ↦ ?_)
            (hFi.add hMx)))
        rw [add_comm ‖F r‖]
        exact (norm_add_le _ _).trans (add_le_add ((M r).le_opNorm _) le_rfl)
    _ ≤ ‖x₀‖ + |∫ r in t₀..t, ‖F r‖| + |∫ r in t₀..s, ‖M r‖ * ‖x r‖| := by
        rw [integral_add hFi hMx, add_assoc]
        exact add_le_add le_rfl ((abs_add_le _ _).trans (add_le_add hFmono le_rfl))

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

/-- **A linear equation preserves the invariant subspaces of its coefficients.** Let `V` be a
closed complemented subspace invariant under every operator of a continuous family `B`. A solution
of `w' = B(t) w` on the line that lies in `V` at one time lies in `V` at all times: for a continuous
projection `P` onto `V`, the component `w - P w` solves a linear equation and vanishes at that
time. -/
theorem Continuous.mem_of_hasDerivAt_clm_apply {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {B : ℝ → X →L[ℝ] X} (hB : Continuous B) {V : Submodule ℝ X}
    (hVc : V.ClosedComplemented) (hV : ∀ t, ∀ x ∈ V, B t x ∈ V) {w : ℝ → X}
    (hw : ∀ t, HasDerivAt w (B t (w t)) t) {t₀ : ℝ} (h : w t₀ ∈ V) (t : ℝ) : w t ∈ V := by
  obtain ⟨P, hP⟩ := hVc
  set Q := ContinuousLinearMap.id ℝ X - V.subtypeL ∘L P
  have hQV {x : X} (hx : x ∈ V) : Q x = 0 := by
    simp [Q, hP ⟨x, hx⟩]
  -- `Q w` solves `u' = Q B(t) u`, since `Q B(t)` kills `V`.
  have hQ (t : ℝ) (x : X) : Q (B t x) = (Q ∘L B t) (Q x) := by
    have hx : Q x = x - P x := by simp [Q]
    simp [hx, hQV (hV t _ (P x).property)]
  have hQw : (fun t ↦ Q (w t)) = fun _ ↦ 0 :=
    (continuous_const.clm_comp hB).eq_of_hasDerivAt_clm_apply (B := fun t ↦ Q ∘L B t)
      (fun t ↦ (Q.hasFDerivAt.comp_hasDerivAt t (hw t)).congr_deriv (hQ t (w t)))
      (fun t ↦ by simpa using hasDerivAt_const t (0 : X)) (hQV h)
  have h0 : w t - P (w t) = 0 := congrFun hQw t
  rw [sub_eq_zero] at h0
  rw [h0]
  exact (P (w t)).property
