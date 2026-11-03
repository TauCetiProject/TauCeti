/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Independence
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.ConstantTerm
import TauCeti.NumberTheory.GCDMatrix
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-!
# Independence of the boundary values of corrected Eisenstein series

For each divisor `d > 1` of a nonzero level `N`, the corrected series
`E₂(z) - d E₂(dz)` has constant term `1 - gcd(c,d)²/d` at a cusp with denominator `c`.
These constant-term vectors are linearly independent. In particular, their span in
`M₂(Γ₀(N))` has zero intersection with the cusp forms, and every element of that span
is determined by its constant terms.

The result holds for every nonzero level, including levels with square factors. It supplies
directness of the corrected-series part of the weight-two cusp–Eisenstein decomposition;
spanning all admissible boundary data is a separate question.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Chapter 4.
* H. J. S. Smith, *On the value of a certain arithmetical determinant*, Proceedings of the
  London Mathematical Society, s1-7 (1875), 208–213.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup ModularForm CongruenceSubgroup
open scoped MatrixGroups ComplexOrder

namespace TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- Restricting a corrected series to `Γ₀(N)` preserves its constant term at every cusp. -/
@[simp↓ high]
theorem constantTermAt_correctedE2AtLevel (d : {d : ℕ // 1 < d ∧ d ∣ N})
    (γ : SL(2, ℤ)) :
    constantTermAt γ (correctedE2AtLevel N d) =
      1 - (Int.gcd (γ 1 0) d.val : ℂ) ^ 2 / d.val := by
  have : NeZero d.val := ⟨by omega⟩
  have hcoe : ⇑(correctedE2AtLevel N d) = ⇑(correctedE2 d.val) :=
    funext (correctedE2AtLevel_apply N d)
  simpa only [constantTermAt_eq_valueAtInfty, coe_translate, hcoe] using
    constantTermAt_correctedE2 d.val γ

/-- The boundary vectors of the corrected weight-two series at all nontrivial divisor
levels are linearly independent. -/
theorem linearIndependent_constantTerms_correctedE2AtLevel :
    LinearIndependent ℂ (fun d : {d : ℕ // 1 < d ∧ d ∣ N} ↦
      ModularForm.constantTerms (correctedE2AtLevel N d)) := by
  suffices h : LinearIndependent ℂ (constantTermsAtDivisors ∘ correctedE2AtLevel N) by
    apply LinearIndependent.of_comp (LinearMap.funLeft ℂ ℂ divisorCuspRep)
    convert h using 1
    funext d c
    simp only [Function.comp_apply, LinearMap.funLeft_apply, ModularForm.constantTerms_apply,
      constantTermsAtDivisors_apply]
  classical
  let v : N.divisors → N.divisors → ℂ :=
    fun d c ↦ (Nat.gcd c.val d.val : ℂ) ^ 2 / d.val
  have hv : LinearIndependent ℂ v := by
    have hG := Matrix.linearIndependent_cols_of_isUnit
      (Matrix.posDef_gcd_pow_divisors (𝕜 := ℂ) N (by omega : 0 < 2)).isUnit
    let u : N.divisors → ℂˣ := fun d ↦
      (Units.mk0 (d.val : ℂ) (Nat.cast_ne_zero.mpr
        (Nat.pos_of_mem_divisors d.property).ne'))⁻¹
    convert! hG.units_smul u using 1
    funext d c
    simp [v, u, Matrix.col_apply, Pi.smul_apply', Units.smul_def, div_eq_mul_inv, mul_comm]
  -- Differences from the divisor-one column are the negatives of the boundary vectors.
  let one : N.divisors := ⟨1, Nat.one_mem_divisors.mpr (NeZero.ne N)⟩
  have hd := (affineIndependent_iff_linearIndependent_vsub ℂ v one).mp
    (hv.affineIndependent ℂ)
  convert (hd.comp nontrivialDivisorEquiv nontrivialDivisorEquiv.injective).neg using 1
  funext d c
  dsimp only [Function.comp_def, Pi.neg_apply]
  rw [constantTermsAtDivisors_apply, constantTermAt_correctedE2AtLevel]
  simp [v, one, Int.gcd_natCast_natCast, sub_eq_add_neg, add_comm]

/-- The span of corrected weight-two Eisenstein series has no nonzero cusp form. -/
theorem disjoint_span_correctedE2AtLevel_cuspFormSubmodule :
    Disjoint (Submodule.span ℂ (Set.range (correctedE2AtLevel N)))
      (cuspFormSubmodule ((Gamma0 N).map (mapGL ℝ)) 2) := by
  rw [← ModularForm.ker_constantTerms, LinearMap.disjoint_ker]
  intro f hf hzero
  rw [← Finsupp.range_linearCombination] at hf
  obtain ⟨a, rfl⟩ := hf
  have ha : Finsupp.linearCombination ℂ
      (fun d ↦ ModularForm.constantTerms (correctedE2AtLevel N d)) a = 0 := by
    simpa only [LinearMap.comp_apply, Function.comp_def] using!
      (congrArg (fun F ↦ F a)
        (Finsupp.linearCombination_linear_comp ℂ ModularForm.constantTerms)).trans hzero
  have ha0 := (linearIndependent_iff_injective_finsuppLinearCombination.mp
    (linearIndependent_constantTerms_correctedE2AtLevel (N := N)))
    (ha.trans (map_zero _).symm)
  rw [ha0, map_zero]

/-- All cusp constant terms determine a form in the corrected weight-two Eisenstein span. -/
theorem constantTermsOnSpanCorrectedE2AtLevel_injective :
    Function.Injective fun f : Submodule.span ℂ (Set.range (correctedE2AtLevel N)) ↦
      ModularForm.constantTerms (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) 2) := by
  intro f g h
  apply Subtype.ext
  exact (ModularForm.constantTerms.injOn_of_disjoint_ker (Set.Subset.refl _)
    (by rw [ModularForm.ker_constantTerms]
        exact disjoint_span_correctedE2AtLevel_cuspFormSubmodule)) f.property g.property h

end TauCeti.EisensteinSeries
