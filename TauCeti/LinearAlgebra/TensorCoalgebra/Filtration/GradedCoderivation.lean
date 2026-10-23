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
the graded Taylor expansion and the conilpotence filtration of reduced tensor words. For a Taylor
map concentrated on the words of a single length `a`, the bound is exact: its coderivation sends
the words of length `j + a - 1` to words of length `j`, and the words of every other length to
words of other lengths (`TauCeti.ReducedTensorWords.lengthProj_comp_gradedCoderiv`).

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

/-- A graded coderivation does not increase tensor length. -/
theorem gradedCoderiv_mem_filtration (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) {n : ℕ} {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M n) : gradedCoderiv G F q z ∈ filtration R M n :=
  gradedCoderiv_filtration_add_le G F q (apply_eq_zero_of_mem_filtration_zero R M F) n
    ⟨z, hz, rfl⟩

/-- Graded coderivations whose Taylor maps agree on the words of length at most `n` agree on those
words: each summand of the graded Taylor expansion of such a word applies the Taylor map to a
block of it. -/
theorem gradedCoderiv_apply_eq_of_mem_filtration {R : Type uR} {M : Type uM} [CommRing R]
    [AddCommGroup M] [Module R M] (G : InternalGrading R M) {F F' : ReducedTensorWords R M →ₗ[R] M}
    (q : ℤ) {n : ℕ} (h : ∀ z ∈ filtration R M n, F z = F' z) {z : ReducedTensorWords R M}
    (hz : z ∈ filtration R M n) : gradedCoderiv G F q z = gradedCoderiv G F' q z := by
  have hz' := gradedCoderiv_filtration_add_le G (F - F') q
    (fun w hw ↦ by rw [LinearMap.sub_apply, h w hw, sub_self]) 0 ⟨z, by rwa [zero_add], rfl⟩
  rw [filtration_zero, Submodule.mem_bot] at hz'
  rw [← add_sub_cancel F' F, gradedCoderiv_add, LinearMap.add_apply, hz', add_zero]

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

/-- Projecting onto a fixed tensor length preserves total degree. -/
theorem isHomogeneous_lengthProj (G : InternalGrading R M) (n : {n : ℕ // 0 < n}) :
    LinearMap.IsHomogeneous (lengthProj R M n) (gradedPiece G) (gradedPiece G) 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  rw [add_zero]
  refine gradedPiece_induction (motive := fun w ↦ lengthProj R M n w ∈ gradedPiece G D) hz
    (fun k hk 𝒟 x hx hD ↦ ?_) (by rw [map_zero]; exact zero_mem _)
    (fun u v _ _ hu hv ↦ by rw [map_add]; exact add_mem hu hv)
    (fun c u _ hu ↦ by rw [map_smul]; exact Submodule.smul_mem _ c hu)
  by_cases h : (⟨k, hk⟩ : {n : ℕ // 0 < n}) = n
  · subst h
    rw [lengthProj_of_self, ← hD]
    exact mem_gradedPiece_of_tprod G hk x 𝒟 hx
  · rw [lengthProj_of_of_ne R M h]
    exact zero_mem _

/-- The graded Taylor expansion of a map `F` concentrated on the words of length `a` collapses a
block of exactly `a` letters to a single letter.  So its words of length `j` come from the words
of length `m = j + a - 1` alone. -/
theorem lengthProj_comp_gradedCoderiv (G : InternalGrading R M)
    {F : ReducedTensorWords R M →ₗ[R] M} (q : ℤ) {a : {a : ℕ // 0 < a}}
    (hF : F ∘ₗ lengthProj R M a = F) {j m : {j : ℕ // 0 < j}} (hm : m.1 + 1 = j.1 + a.1) :
    lengthProj R M j ∘ₗ gradedCoderiv G F q = gradedCoderiv G F q ∘ₗ lengthProj R M m := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨j, hj⟩ := j
  obtain ⟨m, hm0⟩ := m
  dsimp only at hm
  refine linearMap_ext R M fun ⟨k, hk⟩ x ↦ ?_
  -- The tuple `x` has length `↑⟨k, hk⟩`; record that it is `k` for `omega`.
  have hkk : ((⟨k, hk⟩ : {n : ℕ // 0 < n}) : ℕ) = k := rfl
  -- `F` vanishes on the blocks of every length other than `a`.
  have hsub (p d : ℕ) (hd : d ≠ a) : F (subword R x p d) = 0 := by
    rw [← hF, LinearMap.comp_apply]
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · rw [subword_length_zero, map_zero, map_zero]
    by_cases hpd : p + d ≤ k
    · rw [subword_eq_of_tprod R x hd0 hpd,
        lengthProj_of_of_ne R M fun h ↦ hd (congrArg Subtype.val h), map_zero]
    · rw [subword_eq_zero_of_lt_add R x (by omega), map_zero, map_zero]
  -- Each remaining summand collapses a block of `a` letters, leaving a word of length
  -- `k + 1 - a`.
  have hterm (p d : ℕ) :
      lengthProj R M ⟨j, hj⟩
          (splice R (G.twistedTuple q x 0 p) 0 k p d (F (subword R x p d))) =
        if k = m then
          splice R (G.twistedTuple q x 0 p) 0 k p d (F (subword R x p d))
        else 0 := by
    by_cases hd : d = a
    · subst hd
      by_cases hfit : p + d ≤ k
      · rw [splice_eq_of_tprod R _ _ ha hfit (by omega)]
        split_ifs with hkj
        · obtain rfl : j = k + 1 - d := by omega
          rw [lengthProj_of_self]
        · rw [lengthProj_of_of_ne]
          intro h
          have := Subtype.mk.inj h
          omega
      · rw [splice_eq_zero_of_block_lt_add R _ _ (by omega), map_zero, ite_self]
    · rw [hsub p d hd, splice_zero, map_zero, ite_self]
  simp only [LinearMap.comp_apply]
  rw [gradedCoderiv_of_tprod G F q hk x, map_sum]
  simp only [map_sum, hterm]
  by_cases hkj : k = m
  · subst hkj
    rw [lengthProj_of_self, gradedCoderiv_of_tprod G F q hk x]
    simp only [ite_true]
  · rw [lengthProj_of_of_ne R M fun h ↦ hkj (congrArg Subtype.val h), map_zero]
    simp only [hkj, ite_false, Finset.sum_const_zero]

end TauCeti.ReducedTensorWords
