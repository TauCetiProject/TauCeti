/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic

/-!
# Smooth concatenation of isotopies

Concatenate two smooth isotopies by traversing the first in the first quarter of
the interval and the second in the last quarter. Both motions are stationary on
an open neighbourhood of the joining time, so their concatenation is jointly smooth.
This works at finite regularity and at `C^∞`; no analytic concatenation is asserted.

The smoothing uses Mathlib's `Real.smoothTransition`, following the stationary-time
reparametrization in Hirsch, *Differential Topology*, Chapter 8, §8.1.
-/

public section

noncomputable section

namespace TauCeti.SmoothIsotopy

open Set Topology Filter
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω}
  {f₀ f₁ f₂ : C^n⟮I, M; J, N⟯}

private def firstTime (t : unitInterval) : unitInterval :=
  ⟨Real.smoothTransition (4 * t),
    Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private def secondTime (t : unitInterval) : unitInterval :=
  ⟨Real.smoothTransition (4 * t - 3),
    Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem contMDiff_firstTime (hn : n ≤ ∞) :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) n firstTime := by
  have h : ContDiff ℝ n (fun t : ℝ => 4 * t) := by fun_prop
  exact (h.contMDiff.comp (contMDiff_subtypeVal_Icc (x := 0) (y := 1))).smoothTransition hn

private theorem contMDiff_secondTime (hn : n ≤ ∞) :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) n secondTime := by
  have h : ContDiff ℝ n (fun t : ℝ => 4 * t - 3) := by fun_prop
  exact (h.contMDiff.comp (contMDiff_subtypeVal_Icc (x := 0) (y := 1))).smoothTransition hn

private theorem firstTime_eq_one {t : unitInterval} (ht : 1 / 4 ≤ (t : ℝ)) :
    firstTime t = 1 := by
  apply Subtype.ext
  exact Real.smoothTransition.one_of_one_le (by linarith)

private theorem secondTime_eq_zero {t : unitInterval} (ht : (t : ℝ) ≤ 3 / 4) :
    secondTime t = 0 := by
  apply Subtype.ext
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

private def concatMotion (F : SmoothIsotopy f₀ f₁) (G : SmoothIsotopy f₁ f₂)
    (p : unitInterval × M) : N :=
  if (p.1 : ℝ) ≤ 1 / 2 then F (firstTime p.1, p.2) else G (secondTime p.1, p.2)

private theorem contMDiff_concatMotion (F : SmoothIsotopy f₀ f₁)
    (G : SmoothIsotopy f₁ f₂) (hn : n ≤ ∞) :
    ContMDiff ((𝓡∂ 1).prod I) J n (concatMotion F G) := by
  classical
  have htime : Continuous (fun p : unitInterval × M => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  apply (F.contMDiff.comp
    (((contMDiff_firstTime hn).comp contMDiff_fst).prodMk contMDiff_snd)).piecewise
    (G.contMDiff.comp
      (((contMDiff_secondTime hn).comp contMDiff_fst).prodMk contMDiff_snd))
  intro p hp
  have hp' : (p.1 : ℝ) = 1 / 2 := frontier_le_subset_eq htime continuous_const hp
  have hneigh : {q : unitInterval × M | 1 / 4 < (q.1 : ℝ) ∧ (q.1 : ℝ) < 3 / 4} ∈ 𝓝 p :=
    (isOpen_Ioo.preimage htime).mem_nhds (by simp only [mem_preimage, mem_Ioo, hp']; norm_num)
  filter_upwards [hneigh] with q hq
  simp only [Function.comp_apply]
  rw [firstTime_eq_one hq.1.le, secondTime_eq_zero hq.2.le]
  exact (F.map_one_left q.2).trans (G.map_zero_left q.2).symm

/-- Concatenate smooth isotopies, making the motion stationary around the join.
Finite differentiability and `C^∞` are allowed. -/
def trans (F : SmoothIsotopy f₀ f₁) (G : SmoothIsotopy f₁ f₂) (hn : n ≤ ∞) :
    SmoothIsotopy f₀ f₂ where
  toContMDiffMap := ⟨concatMotion F G, contMDiff_concatMotion F G hn⟩
  map_zero_left x := by
    have htime : firstTime 0 = 0 := by
      apply Subtype.ext
      simp [firstTime, Real.smoothTransition.zero]
    dsimp [concatMotion]
    norm_num [htime]
  map_one_left x := by
    have htime : secondTime 1 = 1 := by
      apply Subtype.ext
      norm_num [secondTime, Real.smoothTransition.one]
    dsimp [concatMotion]
    norm_num [htime]
  isSmoothEmbedding t := by
    dsimp [concatMotion]
    split_ifs
    · exact F.isSmoothEmbedding _
    · exact G.isSmoothEmbedding _

/-- The concatenation traverses the first isotopy at smoothed speed in the first half,
and the second at smoothed speed in the second half. -/
@[simp]
theorem trans_apply (F : SmoothIsotopy f₀ f₁) (G : SmoothIsotopy f₁ f₂) (hn : n ≤ ∞)
    (p : unitInterval × M) :
    F.trans G hn p =
      if (p.1 : ℝ) ≤ 1 / 2 then
        F (⟨Real.smoothTransition (4 * p.1),
          Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, p.2)
      else G (⟨Real.smoothTransition (4 * p.1 - 3),
        Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, p.2) := (rfl)

/-- The concatenation is stationary at the common endpoint throughout the middle half. -/
theorem trans_apply_of_mem_Icc (F : SmoothIsotopy f₀ f₁) (G : SmoothIsotopy f₁ f₂)
    (hn : n ≤ ∞) {t : unitInterval} (ht : (t : ℝ) ∈ Icc (1 / 4) (3 / 4)) (x : M) :
    F.trans G hn (t, x) = f₁ x := by
  have hfirst : (⟨Real.smoothTransition (4 * t), Real.smoothTransition.nonneg _,
      Real.smoothTransition.le_one _⟩ : unitInterval) = 1 := firstTime_eq_one ht.1
  have hsecond : (⟨Real.smoothTransition (4 * t - 3), Real.smoothTransition.nonneg _,
      Real.smoothTransition.le_one _⟩ : unitInterval) = 0 := secondTime_eq_zero ht.2
  simp only [trans_apply, hfirst, hsecond, apply_one, apply_zero, ite_self]

end TauCeti.SmoothIsotopy

namespace TauCeti.SmoothIsotopic

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω}
  {f₀ f₁ f₂ : C^n⟮I, M; J, N⟯}

/-- Smooth isotopy is transitive at finite regularity and at `C^∞`. -/
theorem trans (h₀₁ : SmoothIsotopic f₀ f₁) (h₁₂ : SmoothIsotopic f₁ f₂) (hn : n ≤ ∞) :
    SmoothIsotopic f₀ f₂ := by
  obtain ⟨F⟩ := smoothIsotopic_def.mp h₀₁
  obtain ⟨G⟩ := smoothIsotopic_def.mp h₁₂
  exact smoothIsotopic_def.mpr ⟨F.trans G hn⟩

end TauCeti.SmoothIsotopic
