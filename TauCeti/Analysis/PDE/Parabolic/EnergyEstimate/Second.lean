/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Galerkin
public import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.ODE.Gronwall.Integrable
import TauCeti.Analysis.Normed.Operator.Bilinear

/-!
# The second energy estimate for symmetric parabolic equations

Testing a parabolic equation against the time derivative controls that derivative in the
pivot space and the solution in the energy space, uniformly in the Galerkin dimension.
Here the energy form may depend differentiably on time. Its time derivative contributes
an additional integral; a form-relative bound and Grönwall absorb this term.

The estimates use derivatives within the time interval and square-integrable pivot-space
forcing. Only the energy inequality tested against the velocity is required, so projected
Galerkin equations suffice. The form-relative derivative bound involves no coordinate-space
norm and is preserved on non-isometric trial spaces. A coercive specialization supplies the
rate `M / α` from separate norm bounds.

Symmetry is essential to this argument. No estimate for a nonsymmetric energy form is
asserted. In the autonomous case, no coercivity is needed for the energy inequality itself.
The trial-map estimates apply to already constructed curves in a normed coordinate space
and allow a seminormed ambient energy space. The existence corollary also retains uniqueness.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.3, Theorem 5
  (the second Galerkin energy estimate).
* J.-L. Lions, *Équations différentielles opérationnelles et problèmes aux limites*,
  Chapter III.
-/

public section

open MeasureTheory Set
open scoped InnerProductSpace

namespace TauCeti.PDE

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
  {ι : V →L[ℝ] H} {A A' : ℝ → V →L[ℝ] StrongDual ℝ V}
  {u u' : ℝ → V} {f : ℝ → H} {a b K α M : ℝ}

private theorem continuousOn_secondEnergy_data {H₀ : Type*} [SeminormedAddCommGroup H₀]
    [NormedSpace ℝ H₀] {ι : V →L[ℝ] H₀} {S : Set ℝ}
    (hA : ∀ s ∈ S, HasDerivWithinAt A (A' s) S s) (hA' : ContinuousOn A' S)
    (hu : ∀ s ∈ S, HasDerivWithinAt u (u' s) S s) (hu' : ContinuousOn u' S) :
    ContinuousOn A S ∧ ContinuousOn u S ∧
      ContinuousOn (fun s ↦ ‖ι (u' s)‖ ^ 2) S ∧
      ContinuousOn (fun s ↦ A' s (u s) (u s)) S := by
  have hAc : ContinuousOn A S := fun s hs ↦
    HasDerivWithinAt.continuousWithinAt (F := V →L[ℝ] StrongDual ℝ V) (hA s hs)
  have huc : ContinuousOn u S := fun s hs ↦ (hu s hs).continuousWithinAt
  exact ⟨hAc, huc, (ι.continuous.comp_continuousOn hu').norm.pow 2,
    (hA'.clm_apply huc).clm_apply huc⟩

/-- **The second energy inequality before absorption.** The velocity-tested inequality
bounds terminal diagonal energy plus the accumulated squared pivot norm of the velocity
by initial energy, squared forcing, and the integral of the derivative of the form.
All differentiability and continuity assumptions are local to the time interval. -/
theorem apply_self_add_integral_norm_sq_le_add_integral
    (hA : ∀ s ∈ Icc a b, HasDerivWithinAt A (A' s) (Icc a b) s)
    (hA' : ContinuousOn A' (Icc a b))
    (hu : ∀ s ∈ Icc a b, HasDerivWithinAt u (u' s) (Icc a b) s)
    (hu' : ContinuousOn u' (Icc a b))
    (hf : IntervalIntegrable (fun s ↦ ‖f s‖ ^ 2) volume a b)
    (hsym : ∀ s ∈ Icc a b, ∀ x y, A s x y = A s y x)
    (heq : ∀ s ∈ Icc a b,
      ‖ι (u' s)‖ ^ 2 + A s (u s) (u' s) ≤ ⟪f s, ι (u' s)⟫_ℝ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    A t (u t) (u t) + (∫ s in a..t, ‖ι (u' s)‖ ^ 2) ≤
      A a (u a) (u a) + (∫ s in a..t, ‖f s‖ ^ 2) +
        ∫ s in a..t, A' s (u s) (u s) := by
  obtain ⟨hAc, huc, hD, hE'⟩ := continuousOn_secondEnergy_data (ι := ι) hA hA' hu hu'
  have hcross := ((hAc.clm_apply huc).clm_apply hu').const_mul 2
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hDi := (hD.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
  have hEi := (hE'.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
  have hCi := (hcross.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
  have hFi := hf.mono_set (uIcc_subset_uIcc_left (mem_uIcc_of_le ht.1 ht.2))
  have hid := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (((hAc.clm_apply huc).clm_apply huc).mono hsub)
    (fun s hs ↦ ((hA s (hsub ⟨hs.1.le, hs.2.le⟩)).clm_apply_self
      (hu s (hsub ⟨hs.1.le, hs.2.le⟩)) (hsym s (hsub ⟨hs.1.le, hs.2.le⟩))).hasDerivAt
        (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2)))
    (hEi.add hCi)
  have hpoint (s : ℝ) (hs : s ∈ Icc a t) :
      (A' s (u s) (u s) + 2 * A s (u s) (u' s)) +
        ‖ι (u' s)‖ ^ 2 ≤ ‖f s‖ ^ 2 + A' s (u s) (u s) := by
    have he := heq s (hsub hs)
    have hyoung := real_inner_le_norm (f s) (ι (u' s))
    nlinarith [sq_nonneg (‖f s‖ - ‖ι (u' s)‖)]
  have hint := intervalIntegral.integral_mono_on (μ := volume) ht.1
    ((hEi.add hCi).add hDi) (hFi.add hEi) hpoint
  rw [intervalIntegral.integral_add (hEi.add hCi) hDi, hid,
    intervalIntegral.integral_add hFi hEi] at hint
  linarith

/-- **The second parabolic energy estimate with a form-relative bound.** If the time
variation of the symmetric form along the curve is at most `K` times its diagonal energy,
where `K ≥ 0`, Grönwall bounds terminal energy and the squared velocity integral. No
coercivity or coordinate-space norm bound is required. -/
theorem apply_self_add_integral_norm_sq_le_mul_exp
    (hA : ∀ s ∈ Icc a b, HasDerivWithinAt A (A' s) (Icc a b) s)
    (hA' : ContinuousOn A' (Icc a b))
    (hu : ∀ s ∈ Icc a b, HasDerivWithinAt u (u' s) (Icc a b) s)
    (hu' : ContinuousOn u' (Icc a b))
    (hf : IntervalIntegrable (fun s ↦ ‖f s‖ ^ 2) volume a b)
    (hsym : ∀ s ∈ Icc a b, ∀ x y, A s x y = A s y x) (hK : 0 ≤ K)
    (hbound : ∀ s ∈ Icc a b, A' s (u s) (u s) ≤ K * A s (u s) (u s))
    (heq : ∀ s ∈ Icc a b,
      ‖ι (u' s)‖ ^ 2 + A s (u s) (u' s) ≤ ⟪f s, ι (u' s)⟫_ℝ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    A t (u t) (u t) + (∫ s in a..t, ‖ι (u' s)‖ ^ 2) ≤
      (A a (u a) (u a) + ∫ s in a..t, ‖f s‖ ^ 2) * Real.exp (K * (t - a)) := by
  let X : ℝ → ℝ := fun s ↦ A s (u s) (u s) + ∫ r in a..s, ‖ι (u' r)‖ ^ 2
  obtain ⟨hAc, huc, hD, hE'⟩ := continuousOn_secondEnergy_data (ι := ι) hA hA' hu hu'
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hFi := hf.mono_set (uIcc_subset_uIcc_left (mem_uIcc_of_le ht.1 ht.2))
  have hprim : ContinuousOn (fun s ↦ ∫ r in a..s, ‖ι (u' r)‖ ^ 2) (Icc a t) := by
    rw [← uIcc_of_le ht.1]
    exact intervalIntegral.continuousOn_primitive_interval
      (by simpa only [uIcc_of_le ht.1] using (hD.mono hsub).integrableOn_Icc (μ := volume))
  have hX : ContinuousOn X (Icc a t) :=
    (((hAc.clm_apply huc).clm_apply huc).mono hsub).add hprim
  have hEX (s : ℝ) (hs : s ∈ Icc a t) : A s (u s) (u s) ≤ X s :=
    le_add_of_nonneg_right (intervalIntegral.integral_nonneg hs.1 fun _ _ ↦ sq_nonneg _)
  have hgr : ∀ s ∈ Icc a t,
      X s ≤ (A a (u a) (u a) + ∫ r in a..t, ‖f r‖ ^ 2) + K * ∫ r in a..s, X r := by
    intro s hs
    have henergy := apply_self_add_integral_norm_sq_le_add_integral
      hA hA' hu hu' hf hsym heq (hsub hs)
    have hfmono := intervalIntegral.integral_mono_interval (μ := volume) le_rfl hs.1 hs.2
      (Filter.Eventually.of_forall fun r ↦ sq_nonneg ‖f r‖) hFi
    have hderivint := intervalIntegral.integral_mono_on (μ := volume) hs.1
      ((hE'.mono (Icc_subset_Icc_right (hs.2.trans ht.2))).intervalIntegrable_of_Icc hs.1)
      ((hX.const_mul K).mono (Icc_subset_Icc_right hs.2) |>.intervalIntegrable_of_Icc hs.1)
      (fun r hr ↦ (hbound r (hsub (Icc_subset_Icc_right hs.2 hr))).trans
        (mul_le_mul_of_nonneg_left (hEX r (Icc_subset_Icc_right hs.2 hr)) hK))
    rw [intervalIntegral.integral_const_mul] at hderivint
    exact henergy.trans (by linarith)
  have htt := right_mem_Icc.2 ht.1
  exact TauCeti.le_mul_exp_of_le_add_mul_integral hX.integrableOn_Icc hK
    (ae_restrict_of_forall_mem measurableSet_Icc hgr) htt (hgr t htt)

/-- The coercive specialization of the second energy estimate: coercivity with constant
`α > 0` and an upper derivative bound `M ‖v‖²`, with `M ≥ 0`, give the rate `M / α`. -/
theorem apply_self_add_integral_norm_sq_le_mul_exp_of_coercive
    (hA : ∀ s ∈ Icc a b, HasDerivWithinAt A (A' s) (Icc a b) s)
    (hA' : ContinuousOn A' (Icc a b))
    (hu : ∀ s ∈ Icc a b, HasDerivWithinAt u (u' s) (Icc a b) s)
    (hu' : ContinuousOn u' (Icc a b))
    (hf : IntervalIntegrable (fun s ↦ ‖f s‖ ^ 2) volume a b)
    (hsym : ∀ s ∈ Icc a b, ∀ x y, A s x y = A s y x) (hα : 0 < α) (hM : 0 ≤ M)
    (hcoer : ∀ s ∈ Icc a b, ∀ v, α * ‖v‖ ^ 2 ≤ A s v v)
    (hbound : ∀ s ∈ Icc a b, ∀ v, A' s v v ≤ M * ‖v‖ ^ 2)
    (heq : ∀ s ∈ Icc a b,
      ‖ι (u' s)‖ ^ 2 + A s (u s) (u' s) ≤ ⟪f s, ι (u' s)⟫_ℝ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    A t (u t) (u t) + (∫ s in a..t, ‖ι (u' s)‖ ^ 2) ≤
      (A a (u a) (u a) + ∫ s in a..t, ‖f s‖ ^ 2) * Real.exp (M / α * (t - a)) := by
  apply apply_self_add_integral_norm_sq_le_mul_exp hA hA' hu hu' hf hsym
    (div_nonneg hM hα.le) ?_ heq ht
  intro s hs
  calc
    A' s (u s) (u s) ≤ M * ‖u s‖ ^ 2 := hbound s hs (u s)
    _ ≤ M * (A s (u s) (u s) / α) := by
      gcongr
      exact (le_div_iff₀ hα).2 (by simpa [mul_comm] using hcoer s hs (u s))
    _ = M / α * A s (u s) (u s) := by ring

/-- **Autonomous second energy estimate.** For a fixed symmetric form, no coercivity is
needed to bound terminal diagonal energy plus the squared pivot velocity integral. -/
theorem apply_self_add_integral_norm_sq_le
    {B : V →L[ℝ] StrongDual ℝ V} (hsym : ∀ x y, B x y = B y x)
    (hu : ∀ s ∈ Icc a b, HasDerivWithinAt u (u' s) (Icc a b) s)
    (hu' : ContinuousOn u' (Icc a b))
    (hf : IntervalIntegrable (fun s ↦ ‖f s‖ ^ 2) volume a b)
    (heq : ∀ s ∈ Icc a b,
      ‖ι (u' s)‖ ^ 2 + B (u s) (u' s) ≤ ⟪f s, ι (u' s)⟫_ℝ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    B (u t) (u t) + (∫ s in a..t, ‖ι (u' s)‖ ^ 2) ≤
      B (u a) (u a) + ∫ s in a..t, ‖f s‖ ^ 2 := by
  simpa using apply_self_add_integral_norm_sq_le_add_integral
    (A := fun _ ↦ B) (A' := fun _ ↦ 0)
    (fun s _ ↦ hasDerivWithinAt_const s (Icc a b) B) continuousOn_const
    hu hu' hf (fun _ _ ↦ hsym) heq ht

section TrialMap

variable {V H F : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
  [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : V →L[ℝ] H} {B : V →L[ℝ] StrongDual ℝ V}
  {e : F →L[ℝ] V} {c c' : ℝ → F} {f : ℝ → H} {a b : ℝ}

/-- The unabsorbed second energy inequality on a trial space. The derivative of the ambient
form contributes its exact diagonal integral, without any coercivity or trial-map norm bound. -/
theorem apply_apply_self_add_integral_norm_sq_le_add_integral
    {A A' : ℝ → V →L[ℝ] StrongDual ℝ V}
    (hA : ∀ s ∈ Icc a b, HasDerivWithinAt A (A' s) (Icc a b) s)
    (hA' : ContinuousOn A' (Icc a b))
    (hc : ∀ s ∈ Icc a b, HasDerivWithinAt c (c' s) (Icc a b) s)
    (hc' : ContinuousOn c' (Icc a b))
    (hf : IntervalIntegrable (fun s ↦ ‖f s‖ ^ 2) volume a b)
    (hsym : ∀ s ∈ Icc a b, ∀ x y, A s x y = A s y x)
    (heq : ∀ s ∈ Icc a b,
      ‖ι (e (c' s))‖ ^ 2 + A s (e (c s)) (e (c' s)) ≤ ⟪f s, ι (e (c' s))⟫_ℝ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    A t (e (c t)) (e (c t)) + (∫ s in a..t, ‖ι (e (c' s))‖ ^ 2) ≤
      A a (e (c a)) (e (c a)) + (∫ s in a..t, ‖f s‖ ^ 2) +
        ∫ s in a..t, A' s (e (c s)) (e (c s)) := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.bilinearComp_apply] using
    apply_self_add_integral_norm_sq_le_add_integral
      (ι := ι.comp e) (A := fun s ↦ (A s).bilinearComp e e)
      (A' := fun s ↦ (A' s).bilinearComp e e)
      (fun s hs ↦ (hA s hs).bilinearComp e e) (hA'.bilinearComp e e) hc hc' hf
      (fun s hs v w ↦ hsym s hs (e v) (e w)) heq ht

/-- The autonomous second energy estimate for an already constructed trial curve. Only
testing the projected equation against its coordinate velocity is required. The trial map
need not be injective or isometric, and the ambient energy space may be seminormed. -/
theorem apply_apply_self_add_integral_norm_sq_le
    (hsym : ∀ x y, B x y = B y x)
    (hc : ∀ s ∈ Icc a b, HasDerivWithinAt c (c' s) (Icc a b) s)
    (hc' : ContinuousOn c' (Icc a b))
    (hf : IntervalIntegrable (fun s ↦ ‖f s‖ ^ 2) volume a b)
    (heq : ∀ s ∈ Icc a b,
      ‖ι (e (c' s))‖ ^ 2 + B (e (c s)) (e (c' s)) ≤ ⟪f s, ι (e (c' s))⟫_ℝ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    B (e (c t)) (e (c t)) + (∫ s in a..t, ‖ι (e (c' s))‖ ^ 2) ≤
      B (e (c a)) (e (c a)) + ∫ s in a..t, ‖f s‖ ^ 2 := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.bilinearComp_apply] using
    TauCeti.PDE.apply_self_add_integral_norm_sq_le
      (ι := ι.comp e) (B := B.bilinearComp e e)
      (fun v w ↦ hsym (e v) (e w)) hc hc' hf heq ht

/-- The time-dependent second energy estimate on a trial space, with a form-relative bound
in the ambient space. No coordinate norm, injectivity, or isometry of the trial map enters
the estimate, so the rate `K` is unchanged by restriction to a Galerkin space. -/
theorem apply_apply_self_add_integral_norm_sq_le_mul_exp
    {A A' : ℝ → V →L[ℝ] StrongDual ℝ V} {K : ℝ}
    (hA : ∀ s ∈ Icc a b, HasDerivWithinAt A (A' s) (Icc a b) s)
    (hA' : ContinuousOn A' (Icc a b))
    (hc : ∀ s ∈ Icc a b, HasDerivWithinAt c (c' s) (Icc a b) s)
    (hc' : ContinuousOn c' (Icc a b))
    (hf : IntervalIntegrable (fun s ↦ ‖f s‖ ^ 2) volume a b)
    (hsym : ∀ s ∈ Icc a b, ∀ x y, A s x y = A s y x) (hK : 0 ≤ K)
    (hbound : ∀ s ∈ Icc a b, A' s (e (c s)) (e (c s)) ≤ K * A s (e (c s)) (e (c s)))
    (heq : ∀ s ∈ Icc a b,
      ‖ι (e (c' s))‖ ^ 2 + A s (e (c s)) (e (c' s)) ≤ ⟪f s, ι (e (c' s))⟫_ℝ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    A t (e (c t)) (e (c t)) + (∫ s in a..t, ‖ι (e (c' s))‖ ^ 2) ≤
      (A a (e (c a)) (e (c a)) + ∫ s in a..t, ‖f s‖ ^ 2) * Real.exp (K * (t - a)) := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.bilinearComp_apply] using
    TauCeti.PDE.apply_self_add_integral_norm_sq_le_mul_exp
      (ι := ι.comp e) (A := fun s ↦ (A s).bilinearComp e e)
      (A' := fun s ↦ (A' s).bilinearComp e e)
      (fun s hs ↦ (hA s hs).bilinearComp e e) (hA'.bilinearComp e e) hc hc' hf
      (fun s hs v w ↦ hsym s hs (e v) (e w)) hK hbound heq ht

end TrialMap

/-- **Galerkin approximations with the second energy estimate.** For a fixed symmetric
energy form and continuous pivot-space forcing, a finite-dimensional trial map injective
into the pivot space admits a unique global classical Galerkin solution. Its terminal energy
plus the squared velocity integral is bounded by initial energy plus squared forcing, with
constant one independent of the trial space. -/
theorem existsUnique_galerkinSolution_apply_self_add_integral_norm_deriv_sq_le
    {V H F : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : V →L[ℝ] H} {f : ℝ → H}
    {B : V →L[ℝ] StrongDual ℝ V} (hsym : ∀ x y, B x y = B y x)
    (e : F →L[ℝ] V) (he : Function.Injective (ι.comp e)) (hf : Continuous f) (x : F) (a : ℝ) :
    ∃ c : ℝ → F, c a = x ∧ ContDiff ℝ 1 c ∧
      (∀ t v, ⟪ι (e (deriv c t)), ι (e v)⟫_ℝ + B (e (c t)) (e v) =
        ⟪f t, ι (e v)⟫_ℝ) ∧
      (∀ t ∈ Ici a, B (e (c t)) (e (c t)) +
          (∫ s in a..t, ‖ι (e (deriv c s))‖ ^ 2) ≤
        B (e x) (e x) + ∫ s in a..t, ‖f s‖ ^ 2) ∧
      ∀ d : ℝ → F, d a = x ∧ ContDiff ℝ 1 d ∧
        (∀ t v, ⟪ι (e (deriv d t)), ι (e v)⟫_ℝ + B (e (d t)) (e v) =
          ⟪f t, ι (e v)⟫_ℝ) → d = c := by
  obtain ⟨c, hc, huniq⟩ := existsUnique_galerkinSolution ι B e he
    (ι.gelfandDual.continuous.comp hf) x a
  have hceq (t : ℝ) (v : F) :
      ⟪ι (e (deriv c t)), ι (e v)⟫_ℝ + B (e (c t)) (e v) = ⟪f t, ι (e v)⟫_ℝ := by
    simpa only [Function.comp_apply, ContinuousLinearMap.gelfandDual_apply] using hc.2.2 t v
  refine ⟨c, hc.1, hc.2.1, hceq, (fun t ht ↦ ?_), ?_⟩
  · have henergy := apply_apply_self_add_integral_norm_sq_le
      (ι := ι) (B := B) (e := e) hsym
      (fun s _ ↦ (hc.2.1.differentiable one_ne_zero s).hasDerivAt.hasDerivWithinAt)
      hc.2.1.continuous_deriv_one.continuousOn (hf.norm.pow 2 |>.intervalIntegrable a t)
      (fun s _ ↦ by simpa only [real_inner_self_eq_norm_sq] using (hceq s (deriv c s)).le)
      (right_mem_Icc.2 ht)
    simpa only [hc.1] using henergy
  · intro d hd
    apply huniq d
    refine ⟨hd.1, hd.2.1, fun t v ↦ ?_⟩
    simpa only [Function.comp_apply, ContinuousLinearMap.gelfandDual_apply] using hd.2.2 t v

end TauCeti.PDE
