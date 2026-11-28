/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.WellFoundedSet

/-!
# Normalised minimal-support kernel vectors over a valuation domain

Over a valuation domain `R`, every matrix `M : Matrix m d R` with a nonzero kernel vector admits a
kernel vector `a : d → R` with some coordinate `a ν = 1` that is fixed by every map `g : R → R`
satisfying `g 0 = 0`, `g 1 = 1` and `M *ᵥ (g ∘ a) = 0` (in particular, by every ring endomorphism
of `R` preserving the kernel relation `M *ᵥ (g ∘ a) = 0`). This is Artin's minimal-support
argument carried out over a valuation domain rather than a field.

## Main results

* `Matrix.exists_mulVec_eq_zero_and_forall_comp_eq`: for a matrix `M : Matrix m d R` over a
  valuation domain `R` with a nonzero kernel vector, there exist `a : d → R` and `ν : d` with
  `a ν = 1`, `M *ᵥ a = 0`, and `g ∘ a = a` for every `g : R → R` fixing `0` and `1` such that
  `M *ᵥ (g ∘ a) = 0`.
* `Matrix.exists_mulVec_eq_zero_and_forall_comp_eq_of_det_eq_zero`: specialisation to a square
  matrix `M : Matrix d d R` with `M.det = 0`.

## Proof idea

Choose a nonzero kernel vector `w` of minimal support. Because the principal ideals of a valuation
ring are totally ordered, some coordinate `t = w ν` divides every `w i`, giving `w = t • a` with
`t ≠ 0`, `a ν = 1`, and `M *ᵥ a = 0` (using that `R` is a domain). For any `g : R → R` with
`g 0 = 0`, `g 1 = 1` and `M *ᵥ (g ∘ a) = 0`, the difference `g ∘ a - a` lies in `ker M`, has
support contained in `Function.support w`, and vanishes at `ν`; minimality forces `g ∘ a = a`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/PadicHodge/Kisin/PeriodMatrixFrame.lean`
(`New.exists_mulVec_eq_zero_and_forall_comp_eq`), generalized from square singular matrices and ring
endomorphisms to arbitrary matrices with a nonzero kernel vector and maps fixing `0` and `1`.
-/

@[expose] public section

open Function Ideal Matrix

namespace Matrix

/-- Over a valuation domain `R`, if `M : Matrix m d R` has a nonzero kernel vector, then there
exist `a : d → R` and `ν : d` with `a ν = 1` and `M *ᵥ a = 0` such that every function `g : R → R`
with `g 0 = 0`, `g 1 = 1`, and `M *ᵥ (g ∘ a) = 0` satisfies `g ∘ a = a`. -/
theorem exists_mulVec_eq_zero_and_forall_comp_eq {m d R : Type*} [Fintype d] [CommRing R]
    [IsDomain R] [ValuationRing R] {M : Matrix m d R}
    (hw₀ : ∃ w : d → R, w ≠ 0 ∧ M *ᵥ w = 0) :
    ∃ (a : d → R) (ν : d), a ν = 1 ∧ M *ᵥ a = 0 ∧
      ∀ g : R → R, g 0 = 0 → g 1 = 1 → M *ᵥ (g ∘ a) = 0 → g ∘ a = a := by
  classical
  obtain ⟨w, ⟨hw, hMw⟩, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun v : d → R ↦ v ≠ 0 ∧ M *ᵥ v = 0) support hw₀
  have : Nonempty d := (Function.ne_iff.mp hw).nonempty
  obtain ⟨ν, hν⟩ : ∃ ν : d, ∀ i : d, w ν ∣ w i := by
    simpa [mem_span_singleton] using Finite.exists_max fun i ↦ (span {w i} : Ideal R)
  choose a ha using hν
  generalize ht : w ν = t at ha
  obtain rfl : w = t • a := funext ha
  have ht₀ : t ≠ 0 := left_ne_zero_of_smul hw
  have haν : a ν = 1 := by simpa [ht₀] using ht
  have hMa : M *ᵥ a = 0 := by simpa [ht₀, mulVec_smul] using hMw
  refine ⟨a, ν, haν, hMa, fun g hg0 hg1 hg ↦ by_contra fun hne ↦ ?_⟩
  have hker : M *ᵥ (g ∘ a - a) = 0 := by rw [mulVec_sub, hg, hMa, sub_zero]
  have hsub : support (g ∘ a - a) ⊆ support (t • a) := fun i hi ↦ by
    intro hta
    have hai : a i = 0 := by
      rcases mul_eq_zero.mp hta with h | h
      · exact (ht₀ h).elim
      · exact h
    exact hi (by simp [hai, hg0])
  have hν_mem : ν ∈ support (g ∘ a - a) :=
    hmin ⟨sub_ne_zero.mpr hne, hker⟩ hsub (by simp [haν, ht₀])
  simp [haν, hg1] at hν_mem

/-- Over a valuation domain `R`, a square matrix `M : Matrix d d R` with `M.det = 0` has a kernel
vector `a : d → R` with some coordinate `a ν = 1` such that every function `g : R → R` with
`g 0 = 0`, `g 1 = 1`, and `M *ᵥ (g ∘ a) = 0` satisfies `g ∘ a = a`. -/
theorem exists_mulVec_eq_zero_and_forall_comp_eq_of_det_eq_zero {d R : Type*} [Fintype d]
    [DecidableEq d] [CommRing R] [IsDomain R] [ValuationRing R] {M : Matrix d d R}
    (h_det : M.det = 0) :
    ∃ (a : d → R) (ν : d), a ν = 1 ∧ M *ᵥ a = 0 ∧
      ∀ g : R → R, g 0 = 0 → g 1 = 1 → M *ᵥ (g ∘ a) = 0 → g ∘ a = a :=
  exists_mulVec_eq_zero_and_forall_comp_eq (exists_mulVec_eq_zero_iff.mpr h_det)

end Matrix
