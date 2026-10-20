/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Filtration
public import TauCeti.LinearAlgebra.TensorCoalgebra.Brace
public import TauCeti.LinearAlgebra.TensorCoalgebra.GradedCoderivation

/-!
# Tensor-length bounds for graded coderivations

A Taylor map vanishing on the words of length at most `j` produces a coderivation which shortens
reduced tensor words by at least `j`. In particular a Taylor map with zero unary component produces
a coderivation which strictly shortens reduced tensor words, so its composite with any
length-preserving endomorphism is locally nilpotent. This is the finiteness input for applying
homological perturbation to bar constructions: the higher bar operations shorten words, while the
tensor-trick homotopy preserves word length. The general bound, and its consequence for braces,
controls which operations a gauge transformation of an `A∞` structure can change.

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

/-- A graded coderivation whose Taylor map vanishes on the words of length at most `j` lowers
tensor length by at least `j`: each of its summands collapses a block of more than `j` letters to
a single letter. The twist parameter affects coefficients but not word length. -/
theorem gradedCoderiv_filtration_add_le (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) {j : ℕ}
    (hF : ∀ z ∈ filtration R M j, F z = 0) (n : ℕ) :
    Submodule.map (gradedCoderiv G F q) (filtration R M (n + j)) ≤ filtration R M n := by
  rw [Submodule.map_le_iff_le_comap, filtration_le_iff]
  intro k hk
  rintro _ ⟨z, rfl⟩
  simp only [Submodule.mem_comap]
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a x =>
      rw [map_smul, map_smul, gradedCoderiv_of_tprod]
      apply Submodule.smul_mem
      refine Submodule.sum_mem _ fun p hp ↦ Submodule.sum_mem _ fun d hd ↦ ?_
      by_cases hdj : d ≤ j
      · rw [hF _ (subword_mem_filtration R M x p hdj), splice_zero]
        exact zero_mem _
      by_cases hfit : p + d ≤ k.1
      · rw [splice_eq_of_tprod R _ _ (by omega) hfit (by omega)]
        exact of_mem_filtration R M (k := ⟨k.1 + 1 - d, by omega⟩) (by dsimp only; omega) _
      · rw [splice_eq_zero_of_block_lt_add R _ _ (by omega)]
        exact zero_mem _
  | add x y hx hy =>
      rw [map_add, map_add]
      exact add_mem hx hy

/-- A graded coderivation with no unary Taylor component lowers tensor length by at least one.
The twist parameter affects coefficients but not word length. -/
theorem gradedCoderiv_filtration_lowering (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ)
    (hF : F ∘ₗ ofLetter R M = 0) (n : ℕ) :
    Submodule.map (gradedCoderiv G F q) (filtration R M (n + 1)) ≤ filtration R M n :=
  gradedCoderiv_filtration_add_le G F q (apply_eq_zero_of_mem_filtration_one R M hF) n

/-- A brace `F{g}` vanishes on the words of length at most `k + j` when `F` vanishes on the words
of length at most `k` and `g` on those of length at most `j`: the coderivation of `g` shortens
such a word to length at most `k`. -/
theorem brace_apply_eq_zero_of_mem_filtration {R : Type uR} {M : Type uM} [CommRing R]
    [AddCommGroup M] [Module R M] (G : InternalGrading R M) {F g : ReducedTensorWords R M →ₗ[R] M}
    (q : ℤ) {k j : ℕ} (hF : ∀ z ∈ filtration R M k, F z = 0)
    (hg : ∀ z ∈ filtration R M j, g z = 0) {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M (k + j)) : brace G F g q z = 0 := by
  rw [brace_def, LinearMap.comp_apply]
  exact hF _ (gradedCoderiv_filtration_add_le G g q hg k ⟨z, hz, rfl⟩)

end TauCeti.ReducedTensorWords
