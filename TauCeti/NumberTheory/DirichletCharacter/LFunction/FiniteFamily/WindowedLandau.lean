/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.Analysis.SpecialFunctions.Pow.Windows
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.FiniteFamily.RieszMellin
import TauCeti.Analysis.LaplaceTransform.Mellin
import TauCeti.Analysis.MellinTransform.WindowedLandau

/-!
# Windowed Landau for families of primitive Dirichlet characters

One-sided power bounds on arbitrarily distant scale windows exclude zeros of every
positive-weight member of a family. The bounds may hold pointwise or on weighted integrals
of the positive part of the real Riesz remainder.

The criteria are those of Levent Alpöge's `Deduction.lemmaL` and
`Deduction.zeroFree_of_rpow_window` in the formalization of the Riemann hypothesis for
Dirichlet L-functions (<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Complex Filter MeasureTheory Set
open scoped Interval

namespace TauCeti

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
  choose D hD hbound using PrimitiveDirichletCharacter.exists_re_rieszRemainder_le_rpow_two
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
