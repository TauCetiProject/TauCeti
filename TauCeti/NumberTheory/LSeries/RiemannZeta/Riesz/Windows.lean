/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.Analysis.SpecialFunctions.Pow.Windows
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
import TauCeti.Analysis.MellinTransform.WindowedLandau
import TauCeti.NumberTheory.LSeries.RiemannZeta.FirstRieszSum
import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis

/-!
# The Riemann hypothesis as a bound on Riesz remainders

The first Riesz remainder at conductor one is bounded above by `y ^ (1/2 + ε)` on
arbitrarily far-out power windows for every `ε > 0` exactly when the Riemann hypothesis
holds. The converse uses the windowed Landau argument of Levent Alpöge's
`Deduction.zeroFree_of_rpow_window` (<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Complex MeasureTheory Set

namespace TauCeti

/-- One-sided bounds `y ^ θ` for the conductor-one first Riesz remainder on arbitrarily far-out
windows of a fixed ratio `L > 1` rule out zeros of the Riemann zeta function right of `θ`. -/
theorem zeroFreeRightOf_riemannZeta_of_hasWindows_rieszRemainder_one {θ L : ℝ} (hθ : 0 < θ)
    (hL : 1 < L)
    (hwin : HasWindows {y | ((1 : PrimitiveDirichletCharacter).rieszRemainder y).re ≤ y ^ θ} L) :
    ZeroFreeRightOf θ riemannZeta := by
  let χ := (1 : PrimitiveDirichletCharacter)
  let F := rieszRemainderMellin χ.character.LFunction
  have hF : MeromorphicOn F {z | θ < z.re} := fun z _ ↦
    (meromorphicNFOn_rieszRemainderMellin χ.character.LFunction (mem_univ z)).meromorphicAt
  obtain ⟨B, hB⟩ := PrimitiveDirichletCharacter.exists_norm_rieszRemainder_one_le_rpow
    (zeroFreeRightOf_riemannZeta_iff.mpr fun _ h ↦ riemannZeta_ne_zero_of_one_lt_re h)
  have hG : ∀ᵐ y ∂volume.restrict (Ioi 1),
      max (χ.rieszRemainder y).re 0 ≤ B * y ^ (1 : ℝ) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun y hy ↦
      (max_le (re_le_norm _) (norm_nonneg _)).trans
        (by simpa only [χ, max_eq_left zero_le_one] using hB y hy.le)
  have hno := meromorphicOrderAt_nonneg_of_mellin_hasWindows_of_simple_poles (C := 1) hL hG hF
    (fun z hz ↦ by
      have hpow : -(z + 1) = -z - 1 := by ring
      simpa only [χ, PrimitiveDirichletCharacter.ofReal_re_rieszRemainder_one, hpow,
        mul_comm (_ ^ _)] using
        And.intro (χ.integrableOn_rieszRemainder_mul_cpow hz)
          (χ.integral_rieszRemainder_mul_cpow hz))
    (fun z hz hp ↦ (χ.character.rieszRemainderMellin_LFunction_simplePole
      (ne_zero_of_re_pos (hθ.trans hz))
      ((χ.character.meromorphicOrderAt_rieszRemainderMellin_LFunction_neg_iff
        (ne_zero_of_re_pos (hθ.trans hz))).mp hp)).1)
    (fun β hb hp ↦ by
      obtain ⟨c, hc, he⟩ :=
        χ.character.exists_pos_meromorphicTrailingCoeffAt_rieszRemainderMellin_LFunction
          (hθ.trans hb) (hp.trans_lt (by decide : (-1 : WithTop ℤ) < 0))
      rw [Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one hp, he, ofReal_re]
      exact hc)
    (by simpa only [one_mul] using hwin)
  refine zeroFreeRightOf_iff.mpr fun ρ hθρ ↦ ?_
  rw [← PrimitiveDirichletCharacter.LFunction_character_one]
  exact le_of_not_gt fun hpos ↦ (hno ρ hθρ).not_gt
    ((χ.character.meromorphicOrderAt_rieszRemainderMellin_LFunction_neg_iff
      (ne_zero_of_re_pos (hθ.trans hθρ))).mpr hpos)

/-- The Riemann hypothesis is equivalent to one-sided bounds for the conductor-one first Riesz
remainder on arbitrarily far-out windows. For each `ε > 0` the window ratio `L > 1` is fixed,
but it may depend on `ε`. -/
theorem riemannHypothesis_iff_forall_exists_windows :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ L > 1,
      HasWindows {y | ((1 : PrimitiveDirichletCharacter).rieszRemainder y).re ≤
        y ^ ((1 : ℝ) / 2 + ε)} L := by
  refine ⟨fun h ε hε ↦ ⟨2, by norm_num,
    PrimitiveDirichletCharacter.hasWindows_rieszRemainder_one_of_riemannHypothesis h hε 2⟩,
    fun h ↦ ?_⟩
  rw [riemannHypothesis_iff_zeroFreeRightOf, zeroFreeRightOf_iff_forall_gt]
  intro θ hθ
  obtain ⟨L, hL, hwin⟩ := h (θ - 1 / 2) (sub_pos.mpr hθ)
  rw [add_sub_cancel] at hwin
  exact zeroFreeRightOf_riemannZeta_of_hasWindows_rieszRemainder_one (by linarith) hL hwin

end TauCeti
