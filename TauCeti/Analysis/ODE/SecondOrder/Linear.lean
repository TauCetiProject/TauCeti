/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Analysis.ODE.NonlinearCaratheodory.Interval

/-!
# Second-order linear equations on an open interval

Let `I ⊆ ℝ` be an open interval and let `q : ℝ → 𝕜` be continuous on `I`, with `𝕜 = ℝ` or `ℂ`.
This file proves the basic theory of the scalar equation

  `w'' = q(x) w`

on `I`, for solutions that are `C²` on `I`, with the equation written with `iteratedDeriv 2`:
* a solution `(w, v)` of the first-order system `w' = v`, `v' = q w` on an open set is such a
  solution (`TauCeti.contDiffOn_two_of_hasDerivAt`);
* for every `t₀ ∈ I` and all `w₀, w₁ : 𝕜` there is a solution with `w(t₀) = w₀` and
  `w'(t₀) = w₁` (`TauCeti.exists_contDiffOn_iteratedDeriv_eq_mul`);
* two solutions with the same value and derivative at one point of `I` agree on `I`
  (`TauCeti.eqOn_of_iteratedDeriv_eq_mul`);
* if the Wronskian `u w' - u' w` of two solutions vanishes at a point where `u` does not vanish,
  then `w` is a constant multiple of `u` on all of `I`, including at the zeros of `u`
  (`TauCeti.eqOn_mul_of_wronskian_eq_zero`). The Wronskian itself is constant on `I` without any
  continuity of `q` (`TauCeti.wronskian_eq_of_iteratedDeriv_eq_mul`).

Nothing is assumed about `q` at the ends of `I`, which may be infinite. These are the facts about
the solution space used to compare solutions through their asymptotic behaviour at an end of `I`.

The proof writes the equation as the first-order system `(w, w')' = (w', q w)`, whose right side
is Lipschitz in the state with the locally integrable constant `‖q‖ + 1`, and applies the
Carathéodory theorem on an interval
(`TauCeti.exists_continuousOn_forall_mem_eq_picard_of_lipschitzWith` and
`TauCeti.eqOn_of_forall_mem_eq_picard_of_lipschitzWith`).

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, McGraw–Hill,
  1955, Chapter 3.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {I : Set ℝ} {q u w : ℝ → 𝕜}

/-- The first-order system `(w, w')' = (w', c w)` has Lipschitz constant `‖c‖ + 1`. -/
private lemma lipschitzWith_secondOrderSystem (c : 𝕜) :
    LipschitzWith (‖c‖₊ + 1) (fun p : 𝕜 × 𝕜 ↦ (p.2, c * p.1)) := by
  refine LipschitzWith.of_dist_le_mul fun p p' ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, Prod.norm_def, Prod.norm_def]
  simp only [Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub, ← mul_sub, norm_mul, NNReal.coe_add,
    coe_nnNorm, NNReal.coe_one]
  have h1 := le_max_left ‖p.1 - p'.1‖ ‖p.2 - p'.2‖
  have h2 := le_max_right ‖p.1 - p'.1‖ ‖p.2 - p'.2‖
  have hc := norm_nonneg c
  have hp := norm_nonneg (p.2 - p'.2)
  exact max_le (by nlinarith) (by nlinarith)

/-- **Solutions of the first-order system are `C²` solutions.** A function `w` with `w' = v` and
`v' = q w` on an open set, with `q` continuous there, is a `C²` solution of `w'' = q w` there.
This is the bridge from the first-order-system form of the equation to the `ContDiffOn` and
`iteratedDeriv 2` form used in this file; the converse direction is
`ContDiffOn.hasDerivAt_and_hasDerivAt_deriv`. -/
theorem contDiffOn_two_of_hasDerivAt {v : ℝ → 𝕜} (hI : IsOpen I) (hq : ContinuousOn q I)
    (hw : ∀ x ∈ I, HasDerivAt w (v x) x) (hv : ∀ x ∈ I, HasDerivAt v (q x * w x) x) :
    ContDiffOn ℝ 2 w I ∧ ∀ x ∈ I, iteratedDeriv 2 w x = q x * w x := by
  have hdw (x : ℝ) (hx : x ∈ I) : HasDerivAt (deriv w) (q x * w x) x :=
    (hv x hx).congr_of_eventuallyEq <|
      eventually_of_mem (hI.mem_nhds hx) fun t ht ↦ (hw t ht).deriv
  refine ⟨?_, fun x hx ↦ by rw [iteratedDeriv_succ, iteratedDeriv_one]; exact (hdw x hx).deriv⟩
  -- `contDiffOn_succ_iff_deriv_of_isOpen` is stated for orders of the form `n + 1`, so the orders
  -- `2` and `1` are first written as `1 + 1` and `0 + 1` to peel off one derivative at a time.
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen hI]
  refine ⟨fun x hx ↦ (hw x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen hI]
  refine ⟨fun x hx ↦ (hdw x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact (hq.mul fun x hx ↦ (hw x hx).continuousAt.continuousWithinAt).congr
    fun x hx ↦ (hdw x hx).deriv

variable (hI : IsOpen I) (hIc : I.OrdConnected) (hq : ContinuousOn q I)
include hI hIc hq

omit hIc in
/-- The hypotheses of the Carathéodory theorem on `I` for the system `(w, w')' = (w', q w)`. -/
private lemma secondOrderSystem_hyps :
    (∀ p : 𝕜 × 𝕜, LocallyIntegrableOn (fun t ↦ (p.2, q t * p.1)) I) ∧
    LocallyIntegrableOn (fun t ↦ ((‖q t‖₊ + 1 : ℝ≥0) : ℝ)) I ∧
    ∀ᵐ t ∂volume.restrict I, LipschitzWith (‖q t‖₊ + 1) (fun p : 𝕜 × 𝕜 ↦ (p.2, q t * p.1)) := by
  refine ⟨fun p ↦ (continuousOn_const.prodMk (hq.mul continuousOn_const)).locallyIntegrableOn
    hI.measurableSet, ?_, ae_of_all _ fun t ↦ lipschitzWith_secondOrderSystem (q t)⟩
  simp only [NNReal.coe_add, coe_nnNorm, NNReal.coe_one]
  exact (hq.norm.add continuousOn_const).locallyIntegrableOn hI.measurableSet

/-- A solution of `w'' = q w` on `I` gives a solution `(w, w')` of the integral equation of the
first-order system on `I`. -/
private lemma eq_picard_of_iteratedDeriv_eq_mul (hw : ContDiffOn ℝ 2 w I)
    (hwq : ∀ x ∈ I, iteratedDeriv 2 w x = q x * w x) {t₀ : ℝ} (ht₀ : t₀ ∈ I) :
    ContinuousOn (fun t ↦ (w t, deriv w t)) I ∧ ∀ t ∈ I, (w t, deriv w t) =
      ODE.picard (fun t p ↦ (p.2, q t * p.1)) t₀ (w t₀, deriv w t₀)
        (fun t ↦ (w t, deriv w t)) t := by
  have hd (x : ℝ) (hx : x ∈ I) :
      HasDerivAt (fun t ↦ (w t, deriv w t)) (deriv w x, q x * w x) x := by
    obtain ⟨h1, h2⟩ := hw.hasDerivAt_and_hasDerivAt_deriv hI hx
    exact h1.prodMk (hwq x hx ▸ h2)
  refine ⟨fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt, fun t ht ↦ ?_⟩
  have hsub : uIcc t₀ t ⊆ I := hIc.uIcc_subset ht₀ ht
  have hc : ContinuousOn (fun x ↦ (deriv w x, q x * w x)) I :=
    (hw.continuousOn_deriv_of_isOpen hI (by norm_num)).prodMk
      (hq.mul hw.continuousOn)
  rw [ODE.picard_apply, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ hd x (hsub hx)) ((hc.mono hsub).intervalIntegrable)]
  abel

/-- **Existence of solutions of `w'' = q w`.** If `q` is continuous on the open interval `I`, then
for every `t₀ ∈ I` and all `w₀, w₁` the equation `w'' = q w` has a solution, `C²` on `I`, with
`w(t₀) = w₀` and `w'(t₀) = w₁`. -/
theorem exists_contDiffOn_iteratedDeriv_eq_mul {t₀ : ℝ} (ht₀ : t₀ ∈ I) (w₀ w₁ : 𝕜) :
    ∃ w : ℝ → 𝕜, ContDiffOn ℝ 2 w I ∧ (∀ x ∈ I, iteratedDeriv 2 w x = q x * w x) ∧
      w t₀ = w₀ ∧ deriv w t₀ = w₁ := by
  obtain ⟨hF, hL, hLip⟩ := secondOrderSystem_hyps hI hq
  obtain ⟨X, hXc, hX⟩ :=
    exists_continuousOn_forall_mem_eq_picard_of_lipschitzWith hF hL hLip hIc ht₀ (w₀, w₁)
  set G : ℝ → 𝕜 × 𝕜 := fun t ↦ ((X t).2, q t * (X t).1)
  have hGc : ContinuousOn G I :=
    (continuous_snd.comp_continuousOn hXc).prodMk (hq.mul (continuous_fst.comp_continuousOn hXc))
  have hXd (x : ℝ) (hx : x ∈ I) : HasDerivAt X (G x) x := by
    have hi : HasDerivAt (fun t ↦ (w₀, w₁) + ∫ s in t₀..t, G s) (G x) x :=
      (intervalIntegral.integral_hasDerivAt_right
        ((hGc.mono (hIc.uIcc_subset ht₀ hx)).intervalIntegrable)
        (hGc.stronglyMeasurableAtFilter hI x hx) (hGc.continuousAt (hI.mem_nhds hx))).const_add _
    exact hi.congr_of_eventuallyEq <| eventually_of_mem (hI.mem_nhds hx) fun t ht ↦ hX t ht
  have hX1 (x : ℝ) (hx : x ∈ I) : HasDerivAt (fun t ↦ (X t).1) (X x).2 x :=
    (hasFDerivAt_fst (p := X x)).comp_hasDerivAt (f := X) x (hXd x hx)
  have hX2 (x : ℝ) (hx : x ∈ I) : HasDerivAt (fun t ↦ (X t).2) (q x * (X x).1) x :=
    (hasFDerivAt_snd (p := X x)).comp_hasDerivAt (f := X) x (hXd x hx)
  obtain ⟨hwc, hwq⟩ := contDiffOn_two_of_hasDerivAt hI hq hX1 hX2
  refine ⟨fun t ↦ (X t).1, hwc, hwq, by simp [hX t₀ ht₀], ?_⟩
  rw [(hX1 t₀ ht₀).deriv, hX t₀ ht₀]
  simp

/-- **Uniqueness of solutions of `w'' = q w`.** If `q` is continuous on the open interval `I`, then
two solutions of `w'' = q w`, `C²` on `I`, with the same value and derivative at a point `t₀ ∈ I`
agree on `I`. -/
theorem eqOn_of_iteratedDeriv_eq_mul (hu : ContDiffOn ℝ 2 u I)
    (huq : ∀ x ∈ I, iteratedDeriv 2 u x = q x * u x) (hw : ContDiffOn ℝ 2 w I)
    (hwq : ∀ x ∈ I, iteratedDeriv 2 w x = q x * w x) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (h₀ : u t₀ = w t₀) (h₁ : deriv u t₀ = deriv w t₀) : EqOn u w I := by
  obtain ⟨hF, hL, hLip⟩ := secondOrderSystem_hyps hI hq
  obtain ⟨huc, hup⟩ := eq_picard_of_iteratedDeriv_eq_mul hI hIc hq hu huq ht₀
  obtain ⟨hwc, hwp⟩ := eq_picard_of_iteratedDeriv_eq_mul hI hIc hq hw hwq ht₀
  rw [h₀, h₁] at hup
  intro t ht
  exact congrArg Prod.fst
    (eqOn_of_forall_mem_eq_picard_of_lipschitzWith hF hL hLip hIc ht₀ huc hwc hup hwp ht)

/-- **Solutions with vanishing Wronskian are proportional.** If `q` is continuous on the open
interval `I`, `u` and `w` solve `w'' = q w` on `I`, and their Wronskian `u w' - u' w` vanishes at
a point `t₀ ∈ I` with `u(t₀) ≠ 0`, then `w = (w(t₀) / u(t₀)) u` on `I`. -/
theorem eqOn_mul_of_wronskian_eq_zero (hu : ContDiffOn ℝ 2 u I)
    (huq : ∀ x ∈ I, iteratedDeriv 2 u x = q x * u x) (hw : ContDiffOn ℝ 2 w I)
    (hwq : ∀ x ∈ I, iteratedDeriv 2 w x = q x * w x) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hu₀ : u t₀ ≠ 0)
    (hW : u t₀ * deriv w t₀ - deriv u t₀ * w t₀ = 0) :
    EqOn w (fun x ↦ w t₀ / u t₀ * u x) I := by
  set c := w t₀ / u t₀
  have hcu : ContDiffOn ℝ 2 (fun x ↦ c * u x) I := contDiffOn_const.mul hu
  have hcuq (x : ℝ) (hx : x ∈ I) : iteratedDeriv 2 (fun x ↦ c * u x) x = q x * (c * u x) := by
    rw [iteratedDeriv_const_mul_field, huq x hx]
    ring
  refine eqOn_of_iteratedDeriv_eq_mul hI hIc hq hw hwq hcu hcuq ht₀
    (by simp only [c]; field_simp) ?_
  rw [deriv_const_mul_field]
  simp only [c]
  field_simp
  linear_combination hW

end TauCeti
