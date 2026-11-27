/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.Analysis.SpecialFunctions.Pow.Windows
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.GRH
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.CyclicFamily.Basic
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
import Mathlib.Data.Finsupp.Indicator
import TauCeti.NumberTheory.DirichletCharacter.LFunction.FiniteFamily.WindowedLandau
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ZeroFree
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ZeroReflection
import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz.ExplicitFormula
import TauCeti.NumberTheory.LSeries.RiemannZeta.FirstRieszSum

/-!
# The generalized Riemann hypothesis and cyclic Riesz windows

A finite set of primitive Dirichlet characters satisfies the Riemann hypothesis exactly when,
for every `ε > 0`, some positively weighted sum of its real Riesz remainders is at most
`y ^ (1 / 2 + ε)` on arbitrarily distant power windows. The weights and window ratio may vary
with `ε`. For the converse, the explicit formulas give a bound by a constant times `√y`, so
all weights can be taken to be `1` and every window ratio works.

Applying the criterion to the primitive characters inducing powers of a given character turns
cyclic window bounds into a criterion for GRH at every level, including imprimitive characters.
This direction is the window reduction in Levent Alpöge's [formalization][alpoege], notably
`UpperTheory.Comparison₂.formB` and `Formalism.HC.level_of_tiedWin`. It uses the windowed
Landau theorem `zeroFreeRightOf_of_dirichletFamilyRiesz_hasWindows`.

[alpoege]: https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005
-/

public section

open Filter

namespace TauCeti

/-- A weighted sum of real first Riesz remainders is bounded in norm by
`C * y ^ max σ (1 / 2)` on `y ≥ 1` if the L-functions of the nonzero-weight members
are zero-free right of `max σ (1 / 2)`. The weights need not be positive. -/
theorem exists_norm_sum_rieszRemainder_re_le_of_zeroFreeRightOf
    (S : Finset PrimitiveDirichletCharacter) (w : PrimitiveDirichletCharacter → ℝ) {σ : ℝ}
    (hσ : ∀ χ ∈ S, w χ ≠ 0 → ZeroFreeRightOf (max σ (1 / 2)) χ.character.LFunction) :
    ∃ C : ℝ, ∀ y ≥ 1,
      ‖∑ χ ∈ S, w χ * (χ.rieszRemainder y).re‖ ≤ C * y ^ max σ (1 / 2) := by
  have hterm (χ : PrimitiveDirichletCharacter) (hχ : χ ∈ S) (hwχ : w χ ≠ 0) :
      ∃ C : ℝ, ∀ y ≥ 1, ‖χ.rieszRemainder y‖ ≤ C * y ^ max σ (1 / 2) := by
    by_cases heq : χ = 1
    · subst χ
      have hz : ZeroFreeRightOf (max σ (1 / 2)) riemannZeta := by
        have hζ : (1 : PrimitiveDirichletCharacter).character.LFunction = riemannZeta := by
          rw [PrimitiveDirichletCharacter.character_one]
          exact DirichletCharacter.LFunction_modOne_eq
        rw [← hζ]
        exact hσ 1 hχ hwχ
      obtain ⟨C, hC⟩ := PrimitiveDirichletCharacter.exists_norm_rieszRemainder_one_le_rpow hz
      exact ⟨C, fun y hy ↦ by
        simpa only [max_eq_left (le_max_of_le_right (by norm_num : (0 : ℝ) ≤ 1 / 2))] using hC y hy⟩
    · obtain ⟨C, hC⟩ := χ.exists_norm_rieszRemainder_le_of_zeroFreeRightOf heq
      exact ⟨C, fun y hy ↦ by
        simpa only [max_eq_left (le_max_right σ (1 / 2))] using hC (hσ χ hχ hwχ) y hy⟩
  have hweighted (χ : PrimitiveDirichletCharacter) (hχ : χ ∈ S) :
      ∃ C : ℝ, ∀ y ≥ 1, ‖w χ * (χ.rieszRemainder y).re‖ ≤ C * y ^ max σ (1 / 2) := by
    by_cases h : w χ = 0
    · exact ⟨0, by simp [h]⟩
    obtain ⟨C, hC⟩ := hterm χ hχ h
    refine ⟨‖w χ‖ * C, fun y hy ↦ ?_⟩
    rw [norm_mul, Real.norm_eq_abs (χ.rieszRemainder y).re, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hC y hy)) (norm_nonneg _)
  choose C hC using hweighted
  refine ⟨∑ χ ∈ S.attach, C χ χ.property, fun y hy ↦ ?_⟩
  rw [← Finset.sum_attach S (fun χ ↦ w χ * (χ.rieszRemainder y).re), Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ ↦ hC χ χ.property y hy)

/-- Primitive characters in a finite set are all zero-free right of `1 / 2` if and only if,
for each `ε > 0`, some strictly positive weights give a one-sided Riesz window bound at
exponent `1 / 2 + ε`. Neither the weights nor the ratio must be uniform in `ε`. -/
theorem forall_exists_hasWindows_sum_rieszRemainder_iff (S : Finset PrimitiveDirichletCharacter) :
    (∀ ε : ℝ, 0 < ε → ∃ w : PrimitiveDirichletCharacter → ℝ, (∀ χ ∈ S, 0 < w χ) ∧
      ∃ L > 1, HasWindows {y | ∑ χ ∈ S, w χ * (χ.rieszRemainder y).re ≤ y ^ (1 / 2 + ε)} L) ↔
    ∀ χ ∈ S, ZeroFreeRightOf (1 / 2) χ.character.LFunction := by
  classical
  constructor
  · intro h χ hχ
    refine zeroFreeRightOf_iff_forall_gt.mpr fun σ hσ ↦ ?_
    obtain ⟨w, hw, L, hL, hwin⟩ := h (σ - 1 / 2) (sub_pos.mpr hσ)
    let v : PrimitiveDirichletCharacter →₀ ℝ := Finsupp.indicator S (fun κ _ ↦ w κ)
    have hv : 0 ≤ v := Finsupp.le_def.mpr fun κ ↦ by
      by_cases hk : κ ∈ S
      · simpa [v, Finsupp.indicator_apply, hk] using (hw κ hk).le
      · simp [v, Finsupp.indicator_apply, hk]
    have hmem : χ ∈ v.support := by
      simpa [v, Finsupp.mem_support_iff, Finsupp.indicator_apply, hχ] using (hw χ hχ).ne'
    have hexp : 1 / 2 + (σ - 1 / 2) = σ := by ring
    refine zeroFreeRightOf_of_dirichletFamilyRiesz_hasWindows (θ := σ) (C := 1) hv
      ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans hσ.le) hL (hwin.mono fun y hy ↦ ?_) χ hmem
    simp only [Set.mem_ofPred_eq, hexp] at hy
    dsimp only [Set.mem_ofPred_eq, v]
    rw [Finsupp.sum_indicator_index, one_mul]
    · exact hy
    · exact fun κ _ ↦ zero_mul (κ.rieszRemainder y).re
  · intro h ε hε
    obtain ⟨C, hC⟩ := exists_norm_sum_rieszRemainder_re_le_of_zeroFreeRightOf S (fun _ ↦ 1)
      (σ := 1 / 2) (fun χ hχ _ ↦ by simpa only [max_self] using h χ hχ)
    have hevent : ∀ᶠ y : ℝ in atTop,
        ∑ χ ∈ S, 1 * (χ.rieszRemainder y).re ≤ C * y ^ ((1 : ℝ) / 2) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      exact (Real.le_norm_self _).trans (by simpa only [max_self] using hC y hy)
    exact ⟨fun _ ↦ 1, fun _ _ ↦ one_pos, 2, one_lt_two,
      hasWindows_rpow_bound_of_eventually_le hevent (lt_add_of_pos_right _ hε) 2⟩

/-- GRH is equivalent to finding, for every primitive character and every `ε > 0`,
positive weights on its cyclic family and a power-window ratio greater than `1` for which
the weighted sum of real Riesz remainders is at most `y ^ (1 / 2 + ε)` on arbitrarily
far-out windows. The cyclic family uses the primitive inducing characters, not the
powers at the original level. -/
theorem grh_iff_forall_exists_hasWindows_cyclicFamily :
    GRH ↔ ∀ (ψ : PrimitiveDirichletCharacter) (ε : ℝ), 0 < ε →
      ∃ w : PrimitiveDirichletCharacter → ℝ, (∀ κ ∈ ψ.cyclicFamily, 0 < w κ) ∧
        ∃ L > 1, HasWindows
          {y | ∑ κ ∈ ψ.cyclicFamily, w κ * (κ.rieszRemainder y).re ≤ y ^ (1 / 2 + ε)} L := by
  simp_rw [grh_def, DirichletCharacter.dirichletGRH_def,
    ← DirichletCharacter.zeroFreeRightOf_one_half_LFunction_iff_forall_re_pos]
  rw [forall_zeroFreeRightOf_LFunction_iff_forall_mem_cyclicFamily (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact forall_congr' fun ψ ↦ (forall_exists_hasWindows_sum_rieszRemainder_iff ψ.cyclicFamily).symm

end TauCeti
