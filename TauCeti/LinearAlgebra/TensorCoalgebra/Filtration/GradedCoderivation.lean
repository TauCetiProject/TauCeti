/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation

/-!
# Tensor-length bounds for graded coderivations

A Taylor map with zero unary component produces a coderivation which strictly shortens reduced
tensor words. Consequently its composite with any length-preserving endomorphism is locally
nilpotent. This is the finiteness input for applying homological perturbation to bar constructions:
the higher bar operations shorten words, while the tensor-trick homotopy preserves word length.

The length argument does not depend on the grading or the Koszul twist. It uses the formula for
the graded Taylor expansion and the conilpotence filtration of reduced tensor words.

Getzler--Jones, Sections 1--2, and Gugenheim--Lambe--Stasheff, *Perturbation theory in
differential homological algebra II*, supply the bar and transfer setting.
-/

public section

open scoped DirectSum TensorProduct

universe uR uM

namespace TauCeti.ReducedTensorWords

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

/-- A graded coderivation with no unary Taylor component lowers tensor length by at least one.
The twist parameter affects coefficients but not word length. -/
theorem gradedCoderiv_filtration_lowering (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ)
    (hF : F ∘ₗ ofLetter R M = 0) (n : ℕ) :
    Submodule.map (gradedCoderiv G F q) (filtration R M (n + 1)) ≤ filtration R M n := by
  rw [Submodule.map_le_iff_le_comap, filtration_le_iff]
  intro k hk
  rintro _ ⟨z, rfl⟩
  simp only [Submodule.mem_comap]
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a x =>
      rw [map_smul, map_smul, gradedCoderiv_of_tprod]
      apply Submodule.smul_mem
      refine Submodule.sum_mem _ fun p hp ↦ Submodule.sum_mem _ fun d hd ↦ ?_
      by_cases hd0 : d = 0
      · subst d
        rw [splice_zero_length]
        exact zero_mem _
      by_cases hd1 : d = 1
      · subst d
        have hp : p < k.1 := Finset.mem_range.mp hp
        have hFa : F (ofLetter R M (x ⟨p, hp⟩)) = 0 := by
          have h := LinearMap.congr_fun hF (x ⟨p, hp⟩)
          simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
        rw [subword_one R M x hp, hFa, splice_zero]
        exact zero_mem _
      by_cases hfit : p + d ≤ k.1
      · rw [splice_eq_of_tprod R _ _ (by omega) hfit (by omega)]
        refine of_mem_filtration R M (k := ⟨k.1 + 1 - d, by omega⟩) ?_ _
        -- Expose the length hidden by the positive-length subtype in `of_mem_filtration`.
        change k.1 + 1 - d ≤ n
        omega
      · rw [splice_eq_zero_of_block_lt_add R _ _ (by omega)]
        exact zero_mem _
  | add x y hx hy =>
      rw [map_add, map_add]
      exact add_mem hx hy

end TauCeti.ReducedTensorWords
