/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.StationaryPhase.SmoothCutoff
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.LinearAlgebra.Complex.Determinant

/-! # Transport of a compactly supported amplitude through a holomorphic chart -/

public section

open MeasureTheory Metric Set
open scoped ContDiff

namespace TauCeti

universe u

/-- A normalized holomorphic chart transports amplitudes on a small ball with uniform derivative
bounds. At zero the transported amplitude has its original value. -/
theorem exists_bounded_transported_amplitude (n N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ),
      e.source = ball 0 ρ → ball 0 (ρ / 4) ⊆ e.target → e 0 = 0 →
      AnalyticOnNhd ℂ e.symm (ball 0 (ρ / 4)) →
      (∀ x ∈ ball 0 (ρ / 4), ‖e.symm x‖ ≤ ρ) →
      (∀ x ∈ ball 0 ρ, ‖e x‖ ≤ 3 / 2 * ‖x‖) →
      fderiv ℂ e.symm 0 = ContinuousLinearMap.id ℂ _ →
      ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
        (a : (Fin n → ℂ) → V) (S : ℝ), ContDiff ℝ N a →
        (∀ x ∉ closedBall 0 (ρ / 32), a x = 0) →
        (∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) →
        ∃ b : (Fin n → ℂ) → V, ContDiff ℝ N b ∧ b 0 = a 0 ∧
          tsupport b ⊆ closedBall 0 (ρ / 8) ∧
          (∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ C * S) ∧
          ∀ p q : (Fin n → ℂ) → ℂ, (∀ x ∈ ball 0 ρ, p x = q (e x)) →
            (∫ x, p x • a x) = ∫ x, q x • b x := by
  let E := Fin n → ℂ
  obtain ⟨A, -, hψ⟩ := exists_contDiff_extension_of_analyticOnNhd_ball (E := E) (F := E)
    (N + 1) (show ρ / 8 < ρ / 4 by linarith) ρ
  obtain ⟨χ, B, hB, hχ, hχs, hχ1, hχb⟩ := exists_bounded_smooth_cutoff (E := E) N
    (show ρ / 16 < ρ / 8 by linarith)
  let D := max 1 A
  have hD : 1 ≤ D := le_max_left ..
  have hdet : ContDiff ℝ N (fun L : E →L[ℝ] E ↦ L.det) := ContinuousLinearMap.contDiff_det
  obtain ⟨P, hP, hPb⟩ := hdet.contDiffOn.exists_nonneg_bound_iteratedFDeriv_of_isOpen
    isOpen_univ (isCompact_closedBall (0 : E →L[ℝ] E) D) (subset_univ _)
  let M : ℝ := N.factorial * D ^ N
  refine ⟨(2 ^ N * B) * (2 ^ N * (M * P)) * M, by positivity, ?_⟩
  intro e hsrc ht he0 he hei hen hinv V _ _ _ a S ha has hab
  have hS : 0 ≤ S := (norm_nonneg _).trans (hab 0 (Nat.zero_le _) 0)
  obtain ⟨ψ, hψn, hψε, hψb⟩ := hψ e.symm he hei
  let jaco (x : E) := (fderiv ℝ ψ x).det
  have hDψ : ContDiff ℝ N (fderiv ℝ ψ) := hψn.fderiv_right (by exact_mod_cast le_rfl)
  have hJ : ContDiff ℝ N jaco := hdet.comp hDψ
  have hψN : ContDiff ℝ N ψ := hψn.of_le (by exact_mod_cast Nat.le_succ N)
  have hcA : ContDiff ℝ N (a ∘ ψ) := ha.comp hψN
  have hbJ (i : ℕ) (hi : i ≤ N) (x : E) : ‖iteratedFDeriv ℝ i jaco x‖ ≤ M * P := by
    have hs : fderiv ℝ ψ x ∈ closedBall (0 : E →L[ℝ] E) D := by
      rw [mem_closedBall, dist_zero_right, ← norm_iteratedFDeriv_one (𝕜 := ℝ)]
      exact (hψb 1 (by omega) x).trans (le_max_right ..)
    calc
      _ ≤ i.factorial * P * D ^ i :=
        norm_iteratedFDeriv_comp_le hdet hDψ (by exact_mod_cast hi) x
          (fun k hk ↦ hPb k (by exact_mod_cast hk.trans hi) _ hs)
          (fun k hk hk' ↦ by
            rw [norm_iteratedFDeriv_fderiv]
            exact (hψb (k + 1) (Nat.succ_le_succ (hk'.trans hi)) x).trans
              ((le_max_right _ _).trans (le_self_pow₀ hD (Nat.ne_of_gt hk))))
      _ ≤ _ := by
        dsimp [M]
        rw [mul_right_comm]
        gcongr
  have hbA (i : ℕ) (hi : i ≤ N) (x : E) : ‖iteratedFDeriv ℝ i (a ∘ ψ) x‖ ≤ M * S := by
    calc
      _ ≤ i.factorial * S * D ^ i :=
        norm_iteratedFDeriv_comp_le ha hψN (by exact_mod_cast hi) x
          (fun k hk ↦ hab k (hk.trans hi) _)
          (fun k hk hk' ↦ (hψb k (by omega) x).trans
            ((le_max_right _ _).trans (le_self_pow₀ hD (Nat.ne_of_gt hk))))
      _ ≤ _ := by
        dsimp [M]
        rw [mul_right_comm]
        gcongr
  let d (x : E) := jaco x • a (ψ x)
  let b (x : E) := χ x • d x
  have hd : ContDiff ℝ N d := hJ.smul hcA
  have hχN : ContDiff ℝ N χ := hχ.of_le (by simp)
  let U := ball (0 : E) (ρ / 8)
  have hUt : U ⊆ e.target := (ball_subset_ball (by linarith)).trans ht
  have hψe (x : E) (hx : x ∈ U) : ψ x = e.symm x :=
    (hψε x (ball_subset_closedBall hx)).eq_of_nhds
  have hder (x : E) (hx : x ∈ U) :
      fderiv ℝ ψ x = (fderiv ℂ e.symm x).restrictScalars ℝ :=
    ((hψε x (ball_subset_closedBall hx)).fderiv_eq).trans
      ((he x (ball_subset_ball (by linarith) hx)).differentiableAt.fderiv_restrictScalars ℝ)
  have hJnonneg (x : E) (hx : x ∈ U) : 0 ≤ jaco x := by
    dsimp [jaco]
    rw [hder x hx]
    change 0 ≤ LinearMap.det ((fderiv ℂ e.symm x).toLinearMap.restrictScalars ℝ)
    rw [LinearMap.det_restrictScalars_eq_normSq]
    exact Complex.normSq_nonneg _
  have hu0 : 0 ∈ U := mem_ball_self (by positivity)
  have hχ0 : χ 0 = 1 := (hχ1 0 (mem_closedBall_self (by positivity))).eq_of_nhds
  have heinv₀ : e.symm 0 = 0 := by
    have hsrc0 : 0 ∈ e.source := by rw [hsrc]; exact mem_ball_self hρ
    simpa only [he0] using e.left_inv hsrc0
  have hb0 : b 0 = a 0 := by
    have hJ0 : jaco 0 = 1 := by
      dsimp [jaco]
      rw [hder 0 hu0, hinv]
      exact LinearMap.det_id
    simp [b, d, hχ0, hJ0, hψe 0 hu0, heinv₀]
  have hbS : tsupport b ⊆ tsupport χ := by
    apply closure_mono
    intro x hx
    exact fun hz ↦ hx (by simp [b, hz])
  refine ⟨b, hχN.smul hd, hb0, hbS.trans (hχs.trans ball_subset_closedBall), ?_, ?_⟩
  · intro i hi x
    have hdB := norm_iteratedFDeriv_smul_le_of_uniform_bounds isOpen_univ (mem_univ x)
      hJ.contDiffOn hcA.contDiffOn (fun k hk ↦ hbJ k hk x) (fun k hk ↦ hbA k hk x)
    have h := norm_iteratedFDeriv_smul_le_of_uniform_bounds isOpen_univ (mem_univ x)
      hχN.contDiffOn hd.contDiffOn (fun k hk ↦ hχb k hk x) hdB i hi
    exact h.trans_eq (by ring)
  · intro p q hpq
    have hsupport (x : E) (hx : x ∈ closedBall 0 (ρ / 32)) : x ∈ e.symm '' U := by
      have hxρ : x ∈ ball 0 ρ := closedBall_subset_ball (by linarith) hx
      have hex : e x ∈ closedBall 0 (ρ / 16) := by
        rw [mem_closedBall, dist_zero_right] at hx ⊢
        exact (hen x hxρ).trans (by linarith)
      refine ⟨e x, closedBall_subset_ball (by linarith) hex, e.left_inv ?_⟩
      rwa [hsrc]
    have hp : (∫ x in e.symm '' U, p x • a x) = ∫ x, p x • a x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ by rw [has x (fun h ↦ hx (hsupport x h)), smul_zero])
    have hq : (∫ x in U, q x • b x) = ∫ x, q x • b x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ by
          have hb : b x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hχs (hbS h)))
          rw [hb, smul_zero])
    rw [← hp, ← hq]
    have hU : MeasurableSet U := isOpen_ball.measurableSet
    have hfd (x : E) (hx : x ∈ U) :
        HasFDerivWithinAt (𝕜 := ℝ) e.symm
          ((fderiv ℂ e.symm x).restrictScalars ℝ) U x := by
      have h := (he x (ball_subset_ball (by linarith) hx)).differentiableAt.hasFDerivAt
      exact (HasFDerivAt.restrictScalars ℝ h).hasFDerivWithinAt
    rw [integral_image_eq_integral_abs_det_fderiv_smul volume hU hfd (e.symm.injOn.mono hUt)]
    apply setIntegral_congr_fun hU
    intro x hx
    have hxs : e.symm x ∈ ball 0 ρ := hsrc ▸ e.map_target (hUt hx)
    have hχa : χ x • a (e.symm x) = a (e.symm x) := by
      by_cases hmem : e.symm x ∈ closedBall 0 (ρ / 32)
      · have hh := hen (e.symm x) hxs
        rw [e.right_inv (hUt hx)] at hh
        have hxx : x ∈ closedBall 0 (ρ / 16) := by
          rw [mem_closedBall, dist_zero_right] at hmem ⊢
          linarith
        rw [(hχ1 x hxx).eq_of_nhds, one_smul]
      · simp [has _ hmem]
    simp only
    rw [hpq _ hxs, e.right_inv (hUt hx), ← hder x hx]
    change |jaco x| • (q x • a (e.symm x)) = q x • b x
    rw [abs_of_nonneg (hJnonneg x hx), smul_comm]
    congr 1
    dsimp [b, d]
    rw [hψe x hx, smul_comm (χ x), hχa]

end TauCeti
