/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.Calculus.TaylorIntegral

/-!
# Concavity from second-order upper contacts

A continuous function admitting twice differentiable touching upper supports
with Hessian at most `K` becomes concave after subtraction of `K * ‖x‖² / 2`.
Only the Hessian at each contact point is bounded.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Lemma 7.15
through Corollary 7.19, with the concavity correction to the printed terminology.

Public formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

/-- A negative-second-derivative upper contact is incompatible with a local minimum. -/
theorem not_isLocalMin_of_strict_upper_contact {f B : ℝ → ℝ} {c : ℝ}
    (hcontact : B c = f c) (hupper : ∀ᶠ t in 𝓝 c, f t ≤ B t)
    (hcont : ContinuousAt B c) (hsecond : deriv (deriv B) c < 0) :
    ¬ IsLocalMin f c := by
  intro hmin
  have hBmin : IsLocalMin B c := by
    filter_upwards [hmin, hupper] with t ht htB
    exact hcontact.trans_le (ht.trans htB)
  have hBmax := isLocalMax_of_deriv_deriv_neg hsecond hBmin.deriv_eq_zero hcont
  have heq : B =ᶠ[𝓝 c] (fun _ ↦ B c) := by
    filter_upwards [hBmin, hBmax] with t ht₁ ht₂
    exact le_antisymm ht₂ ht₁
  have hzero : deriv (deriv B) c = 0 := by
    simpa only [deriv_const', deriv_const] using heq.deriv.deriv_eq
  linarith only [hsecond, hzero]

/-- Strictly concave upper contacts force the endpoint minimum bound on a compact interval. -/
theorem min_endpoints_le_of_strict_upper_contacts {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hcontacts : ∀ c ∈ Ioo a b, ∃ B : ℝ → ℝ,
      B c = f c ∧ (∀ᶠ t in 𝓝 c, f t ≤ B t) ∧
        ContinuousAt B c ∧ deriv (deriv B) c < 0)
    {x : ℝ} (hx : x ∈ Icc a b) : min (f a) (f b) ≤ f x := by
  by_contra! hbad
  obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) hf
  have hcx : f c ≤ f x := hmin hx
  have hca : c ≠ a := by
    intro heq
    subst c
    exact (not_lt_of_ge (hcx.trans' (min_le_left _ _))) hbad
  have hcb : c ≠ b := by
    intro heq
    subst c
    exact (not_lt_of_ge (hcx.trans' (min_le_right _ _))) hbad
  have hcint : c ∈ Ioo a b := ⟨lt_of_le_of_ne hc.1 hca.symm, lt_of_le_of_ne hc.2 hcb⟩
  obtain ⟨B, hcontact, hupper, hcont, hsecond⟩ := hcontacts c hcint
  exact not_isLocalMin_of_strict_upper_contact hcontact hupper hcont hsecond
    (hmin.isLocalMin (Icc_mem_nhds hcint.1 hcint.2))

/-- Subtracting an affine quadratic subtracts its exact second derivative. -/
theorem second_deriv_sub_quadratic {B : ℝ → ℝ} {c : ℝ}
    (hB : ContDiffAt ℝ 2 B c) (u v ε : ℝ) :
    deriv (deriv (fun t ↦ B t - (u + v * t + ε * t ^ 2))) c =
      deriv (deriv B) c - 2 * ε := by
  let P := fun t : ℝ ↦ u + v * t + ε * t ^ 2
  have hP (t : ℝ) : HasDerivAt P (v + 2 * ε * t) t := by
    dsimp only [P]
    have hd := ((hasDerivAt_const t u).add ((hasDerivAt_id t).const_mul v)).add
      ((hasDerivAt_pow 2 t).const_mul ε)
    apply hd.congr_deriv
    simp only [mul_one, zero_add, Nat.cast_ofNat]
    ring
  have hdP : deriv P = fun t ↦ v + 2 * ε * t := funext (fun t ↦ (hP t).deriv)
  have hddP : deriv (deriv P) c = 2 * ε := by
    rw [hdP]
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id c).const_mul (2 * ε)).const_add v).deriv
  have h := iteratedDeriv_sub hB (show ContDiffAt ℝ 2 P c by dsimp [P]; fun_prop)
  have h' : deriv (deriv (B - P)) c = deriv (deriv B) c - 2 * ε := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, hddP] using h
  exact h'

/-- Nonpositive second derivatives of local upper contacts force the chord inequality. -/
theorem chord_le_of_upper_contacts {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1))
    (hcontacts : ∀ c ∈ Ioo 0 1, ∃ B : ℝ → ℝ,
      B c = f c ∧ (∀ᶠ t in 𝓝 c, f t ≤ B t) ∧
        ContDiffAt ℝ 2 B c ∧ deriv (deriv B) c ≤ 0)
    {x : ℝ} (hx : x ∈ Icc 0 1) :
    (1 - x) * f 0 + x * f 1 ≤ f x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let P := fun t : ℝ ↦ f 0 + (f 1 - f 0 - ε) * t + ε * t ^ 2
  let h := fun t ↦ f t - P t
  have hcont : ContinuousOn h (Icc 0 1) :=
    hf.sub (show Continuous P by dsimp [P]; fun_prop).continuousOn
  have hstrict (c : ℝ) (hc : c ∈ Ioo 0 1) :
      ∃ B : ℝ → ℝ, B c = h c ∧ (∀ᶠ t in 𝓝 c, h t ≤ B t) ∧
        ContinuousAt B c ∧ deriv (deriv B) c < 0 := by
    obtain ⟨B, hBc, hupper, hB, hsecond⟩ := hcontacts c hc
    refine ⟨fun t ↦ B t - P t, ?_, ?_, ?_, ?_⟩
    · simp only [hBc, h]
    · exact hupper.mono (fun t ht ↦ sub_le_sub_right ht (P t))
    · exact hB.continuousAt.sub (by dsimp [P]; fun_prop)
    · rw [second_deriv_sub_quadratic hB]
      linarith only [hsecond, hε]
  have hbound := min_endpoints_le_of_strict_upper_contacts (by norm_num : (0 : ℝ) < 1)
    hcont hstrict hx
  have h0 : h 0 = 0 := by dsimp [h, P]; ring
  have h1 : h 1 = 0 := by dsimp [h, P]; ring
  rw [h0, h1, min_self] at hbound
  have hquadratic : x * (1 - x) ≤ 1 := by nlinarith [sq_nonneg x]
  have hεbound := mul_le_mul_of_nonneg_left hquadratic hε.le
  dsimp only [h, P] at hbound
  nlinarith only [hbound, hεbound]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Subtracting the Euclidean quadratic cancels the upper Hessian bound on every chord. -/
theorem second_deriv_sub_norm_sq_on_line {f : E → ℝ} (x v : E) {t : ℝ}
    (hf : ContDiffAt ℝ 2 f (x + t • v)) (K : ℝ) :
    deriv (deriv (fun s : ℝ ↦ f (x + s • v) - K * ‖x + s • v‖ ^ 2 / 2)) t =
      fderiv ℝ (fderiv ℝ f) (x + t • v) v v - K * ‖v‖ ^ 2 := by
  have hnorm (s : ℝ) : K * ‖x + s • v‖ ^ 2 / 2 =
      K * ‖x‖ ^ 2 / 2 + (K * inner ℝ x v) * s + (K * ‖v‖ ^ 2 / 2) * s ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  simp_rw [hnorm]
  have hline : ContDiffAt ℝ 2 (fun s : ℝ ↦ f (x + s • v)) t :=
    hf.comp t (by fun_prop)
  rw [second_deriv_sub_quadratic hline, hf.deriv_deriv_comp_add_smul]
  ring

/-- A uniform bound on the Hessians of upper contacts makes the corrected function concave. -/
theorem concaveOn_sub_norm_sq_of_upper_contacts {s : Set E} {f : E → ℝ} {K : ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hcontacts : ∀ x ∈ s, ∃ B : E → ℝ,
      B x = f x ∧ (∀ᶠ y in 𝓝 x, f y ≤ B y) ∧ ContDiffAt ℝ 2 B x ∧
        ∀ v : E, fderiv ℝ (fderiv ℝ B) x v v ≤ K * ‖v‖ ^ 2) :
    ConcaveOn ℝ s (fun x ↦ f x - K * ‖x‖ ^ 2 / 2) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  let L := fun t : ℝ ↦ x + t • (y - x)
  have hLform (t : ℝ) : L t = (1 - t) • x + t • y := by
    dsimp only [L]
    simp only [sub_smul, one_smul, smul_sub]
    abel
  have hL : Continuous L := by dsimp only [L]; fun_prop
  have hLmem : MapsTo L (Icc 0 1) s := by
    intro t ht
    rw [hLform]
    exact hs hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  let F := fun t ↦ f (L t) - K * ‖L t‖ ^ 2 / 2
  have hF : ContinuousOn F (Icc 0 1) :=
    (hf.comp hL.continuousOn hLmem).sub
      (show Continuous (fun t ↦ K * ‖L t‖ ^ 2 / 2) by fun_prop).continuousOn
  have hupper (c : ℝ) (hc : c ∈ Ioo 0 1) : ∃ B : ℝ → ℝ,
      B c = F c ∧ (∀ᶠ t in 𝓝 c, F t ≤ B t) ∧
        ContDiffAt ℝ 2 B c ∧ deriv (deriv B) c ≤ 0 := by
    obtain ⟨B, hBc, hupper, hB, hsecond⟩ := hcontacts (L c) (hLmem ⟨hc.1.le, hc.2.le⟩)
    refine ⟨fun t ↦ B (L t) - K * ‖L t‖ ^ 2 / 2, ?_, ?_, ?_, ?_⟩
    · simp only [hBc, F]
    · have hnear : ∀ᶠ t in 𝓝 c, f (L t) ≤ B (L t) := hL.continuousAt hupper
      exact hnear.mono (fun t ht ↦ sub_le_sub_right ht _)
    · exact (hB.comp c (by dsimp only [L]; fun_prop)).sub
        ((contDiffAt_const.mul ((show ContDiffAt ℝ 2 L c by
          dsimp only [L]; fun_prop).norm_sq ℝ)).div_const 2)
    · rw [second_deriv_sub_norm_sq_on_line x (y - x) hB K]
      exact sub_nonpos.mpr (hsecond (y - x))
  have hb1 : b ≤ 1 := by linarith
  have h := chord_le_of_upper_contacts hF hupper (x := b) ⟨hb, hb1⟩
  have h0 : L 0 = x := by simp [L]
  have h1 : L 1 = y := by simp [L]
  have hbform : L b = a • x + b • y := by
    rw [hLform, show 1 - b = a by linarith]
  simpa only [F, h0, h1, hbform, show 1 - b = a by linarith, smul_eq_mul] using h

end TauCeti
