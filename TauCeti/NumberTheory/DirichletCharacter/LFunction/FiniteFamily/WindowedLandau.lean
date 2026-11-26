/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.Analysis.SpecialFunctions.Pow.Windows
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.FiniteFamily.RieszMellin
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
import TauCeti.Analysis.LaplaceTransform.Mellin
import TauCeti.Analysis.MellinTransform.WindowedLandau

/-!
# Windowed Landau for families of primitive Dirichlet characters

One-sided power bounds on arbitrarily distant scale windows exclude zeros of every
positive-weight member of a family. The bounds may hold pointwise or on weighted integrals
of the positive part of the real Riesz remainder. Inverse-pair averaging gives the Mellin
transform of the real remainder without requiring the support to be closed under inversion.

The criteria are those of Levent Alpöge's `Deduction.lemmaL` and
`Deduction.zeroFree_of_rpow_window` in the formalization of the Riemann hypothesis for
Dirichlet L-functions (<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Complex Filter MeasureTheory Set
open scoped Interval

namespace TauCeti

/-- The real-weighted sum of real remainders, in logarithmic coordinates, has the
inverse-averaged Laplace transform even for signed weights. -/
theorem hasLaplace_dirichletFamilyRieszRemainder_comp_exp
    (w : PrimitiveDirichletCharacter →₀ ℝ) {s : ℂ} (hs : 1 < s.re) :
    HasLaplace (fun u ↦ ((w.sum fun χ c ↦ c * (χ.rieszRemainder (Real.exp u)).re : ℝ) : ℂ)) s
      (dirichletFamilyRieszRemainderMellin w s) := by
  have h := hasLaplace_sum (u := w.support) fun χ _ ↦
    ((χ.hasLaplace_rieszRemainder_comp_exp hs).add
      (χ⁻¹.hasLaplace_rieszRemainder_comp_exp hs)).const_smul ((w χ : ℂ) / 2)
  rw [dirichletFamilyRieszRemainderMellin_apply]
  simpa only [Finsupp.sum, ofReal_sum, ofReal_mul, Complex.re_eq_add_conj,
    ← PrimitiveDirichletCharacter.rieszRemainder_inv, Pi.smul_apply, smul_eq_mul,
    Pi.add_apply, Function.comp_apply, mul_div_assoc, div_mul_eq_mul_div] using h

private theorem exists_re_rieszRemainder_le_rpow_two (χ : PrimitiveDirichletCharacter) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y ≥ 1, (χ.rieszRemainder y).re ≤ D * y ^ (2 : ℝ) := by
  let a (n : ℕ) := χ.character n * (ArithmeticFunction.vonMangoldt n : ℂ)
  let M := ∑' n : ℕ, ‖LSeries.term a ((2 : ℝ) : ℂ) n‖
  have hM : 0 ≤ M := tsum_nonneg fun _ ↦ norm_nonneg _
  have hs : LSeriesSummable a ((2 : ℝ) : ℂ) := by
    have ha : a = (fun n : ℕ ↦ χ.character n) *
        (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) := by
      funext n
      rw [Pi.mul_apply]
    rw [ha]
    have hs₂ : 1 < (((2 : ℝ) : ℂ)).re := by norm_num
    exact χ.character.LSeriesSummable_twist_vonMangoldt hs₂
  have hsum (y : ℝ) (hy : 1 ≤ y) : (rieszSum a y).re ≤ M * y ^ (2 : ℝ) := by
    rw [mul_comm M]
    exact (re_le_norm _).trans (norm_rieszSum_le (σ := 2) (by norm_num) (zero_le_one.trans hy) hs)
  have hy₂ {y : ℝ} (hy : 1 ≤ y) : y ≤ y ^ (2 : ℝ) :=
    Real.self_le_rpow_of_one_le hy (by norm_num)
  by_cases hχ : χ = 1
  · let D : ℝ := 1 + Real.eulerMascheroniConstant
    refine ⟨M + |D|, add_nonneg hM (abs_nonneg _), fun y hy ↦ ?_⟩
    have ha : rieszSum a y = rieszSum (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) y := by
      subst χ
      simp only [a, PrimitiveDirichletCharacter.character_one_apply, one_mul]
    have hlin : y * D ≤ |D| * y ^ (2 : ℝ) := calc
      y * D ≤ y * |D| := mul_le_mul_of_nonneg_left (le_abs_self _) (zero_le_one.trans hy)
      _ ≤ |D| * y ^ (2 : ℝ) := by
        rw [mul_comm y]
        exact mul_le_mul_of_nonneg_left (hy₂ hy) (abs_nonneg _)
    rw [hχ, PrimitiveDirichletCharacter.rieszRemainder_one, ← ha]
    simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, one_re, add_mul]
    have hlog : 0 ≤ y * Real.log y := mul_nonneg (zero_le_one.trans hy) (Real.log_nonneg hy)
    exact add_le_add (hsum y hy) ((sub_le_self _ hlog).trans hlin)
  · let d := logDeriv χ.character.LFunction 1
    refine ⟨M + ‖d‖, add_nonneg hM (norm_nonneg _), fun y hy ↦ ?_⟩
    rw [PrimitiveDirichletCharacter.rieszRemainder_of_ne_one hχ, add_re, add_mul]
    refine add_le_add (hsum y hy) ((re_le_norm ((y : ℂ) * d)).trans ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hy), mul_comm y]
    exact mul_le_mul_of_nonneg_left (hy₂ hy) (norm_nonneg _)

/-- **Windowed Landau for a positively weighted Dirichlet family.** If, for every `η > 0`,
there are arbitrarily far-out power windows on which the positive-part Mellin integral is
at most `Y ^ η`, no positive-weight member has a zero to the right of `θ`. -/
theorem zeroFreeRightOf_of_dirichletFamilyRiesz_meanWindows
    {w : PrimitiveDirichletCharacter →₀ ℝ} (hw : 0 ≤ w) {θ L : ℝ}
    (hθ : 0 ≤ θ) (hL : 1 < L)
    (hwin : ∀ η : ℝ, 0 < η → ∃ᶠ Y in atTop,
      (∫ y in Y..(Y ^ L), max (w.sum fun χ c ↦ c * (χ.rieszRemainder y).re) 0 *
        y ^ (-(θ + 1))) ≤ Y ^ η) :
    ∀ χ ∈ w.support, ZeroFreeRightOf θ χ.character.LFunction := by
  -- Bound the positive part by summing the individual upper bounds.
  choose D hD hbound using exists_re_rieszRemainder_le_rpow_two
  have hw' (χ : PrimitiveDirichletCharacter) : 0 ≤ w χ := by
    simpa using Finsupp.le_def.mp hw χ
  let B := ∑ χ ∈ w.support, w χ * D χ
  have hB (y : ℝ) (hy : 1 ≤ y) :
      max (w.sum fun χ c ↦ c * (χ.rieszRemainder y).re) 0 ≤ B * y ^ (2 : ℝ) := by
    apply max_le
    · dsimp only [B]
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun χ _ ↦ by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hbound χ y hy) (hw' χ)
    · exact mul_nonneg (Finset.sum_nonneg fun χ _ ↦ mul_nonneg (hw' χ) (hD χ))
        (Real.rpow_nonneg (zero_le_one.trans hy) _)
  -- Landau rules out poles of the family transform, and the pole criterion transfers this
  -- conclusion to each member.
  have hΦ := meromorphic_dirichletFamilyRieszRemainderMellin w
  have hno := meromorphicOrderAt_nonneg_of_mellin_window_of_simple_poles (A := 2) hL
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy ↦ hB y hy.le))
    (F := dirichletFamilyRieszRemainderMellin w) (θ := θ) hΦ.meromorphicOn
    (fun z hz ↦ by
      have h := (hasLaplace_comp_exp_iff
        (fun y ↦ ((w.sum fun χ c ↦ c * (χ.rieszRemainder y).re : ℝ) : ℂ)) z _ 0).mp
          (hasLaplace_dirichletFamilyRieszRemainder_comp_exp w
            ((by norm_num : (1 : ℝ) < 2).trans hz))
      simpa only [Real.exp_zero, smul_eq_mul] using h)
    (fun z hz hp ↦ dirichletFamilyRieszRemainderMellin_simplePole
      (ne_zero_of_re_pos (hθ.trans_lt hz)) hp)
    (fun β hβ ho ↦ by
      have hp : meromorphicOrderAt (dirichletFamilyRieszRemainderMellin w) β < 0 := by
        rw [ho]
        decide
      obtain ⟨c, hc, heq⟩ :=
        exists_pos_meromorphicTrailingCoeffAt_dirichletFamilyRieszRemainderMellin
          hw (hθ.trans_lt hβ) hp
      rwa [Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one ho, heq, ofReal_re])
    hwin
  intro χ hχ
  rw [zeroFreeRightOf_iff]
  intro z hz
  refine le_of_not_gt fun hzero ↦ (hno z hz).not_gt ?_
  exact (meromorphicOrderAt_dirichletFamilyRieszRemainderMellin_neg_iff hw
    (ne_zero_of_re_pos (hθ.trans_lt hz))).mpr ⟨χ, hχ, Or.inl hzero⟩

/-- Pointwise upper bounds on arbitrarily far-out power windows exclude zeros of all
positive-weight members of a Dirichlet family to the right of the bound's exponent. -/
theorem zeroFreeRightOf_of_dirichletFamilyRiesz_hasWindows
    {w : PrimitiveDirichletCharacter →₀ ℝ} (hw : 0 ≤ w) {θ L C : ℝ}
    (hθ : 0 ≤ θ) (hL : 1 < L)
    (hwin : HasWindows {y | w.sum (fun χ c ↦ c * (χ.rieszRemainder y).re) ≤ C * y ^ θ} L) :
    ∀ χ ∈ w.support, ZeroFreeRightOf θ χ.character.LFunction :=
  zeroFreeRightOf_of_dirichletFamilyRiesz_meanWindows hw hθ hL
    (fun _ hη ↦ hwin.frequently_integral_mul_rpow_le_rpow hη)

/-- If a positive-weight member has a zero to the right of `θ`, every sufficiently far-out
power window contains a point at which the family's real remainder exceeds `C * y ^ θ`. -/
theorem eventually_exists_lt_dirichletFamilyRiesz_on_window
    {w : PrimitiveDirichletCharacter →₀ ℝ} (hw : 0 ≤ w) {θ L : ℝ} (C : ℝ)
    (hθ : 0 ≤ θ) (hL : 1 < L) {χ : PrimitiveDirichletCharacter} (hχ : χ ∈ w.support)
    (hz : ¬ ZeroFreeRightOf θ χ.character.LFunction) :
    ∀ᶠ Y in atTop, ∃ y ∈ Icc Y (Y ^ L),
      C * y ^ θ < w.sum fun ψ c ↦ c * (ψ.rieszRemainder y).re := by
  have hn : ¬ HasWindows {y | w.sum (fun ψ c ↦ c * (ψ.rieszRemainder y).re) ≤ C * y ^ θ} L :=
    fun h ↦ hz (zeroFreeRightOf_of_dirichletFamilyRiesz_hasWindows hw hθ hL h χ hχ)
  rw [hasWindows_iff] at hn
  push Not at hn
  obtain ⟨Y₀, hY₀⟩ := hn
  filter_upwards [eventually_ge_atTop (max Y₀ 1)] with Y hY
  simpa only [mem_ofPred_eq, not_le] using Set.not_subset.mp (hY₀ Y hY)

end TauCeti
