/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Grading finitely supported functions by assigned degrees

For an arbitrary assignment `g : I → ℤ`, `InternalGrading.finsupp A g` grades the free
`A`-module on `I` by placing its `i`-th basis vector in degree `g i`. A homogeneous element
has support in a single fibre of `g`. No finiteness or injectivity of `g` is required.

The internal direct sum gives every finitely supported function a unique finite homogeneous
decomposition, including when several basis vectors have the same degree. This construction
also applies after a linear change of coordinates, via `InternalGrading.map`.

The construction uses Mathlib's `Finsupp.supported` submodules and
`DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`.
-/

public section

namespace TauCeti.InternalGrading

variable (A : Type*) [Ring A] {I : Type*} (g : I → ℤ)

/-- The internal grading of the free module on `I` assigning its `i`-th basis vector
degree `g i`. The degree-`p` piece consists of functions supported in the fibre of `p`. -/
noncomputable def finsupp : InternalGrading A (I →₀ A) where
  piece p := Finsupp.supported A A {i | g i = p}
  isInternal := by
    classical
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · intro p
      dsimp only
      refine (Finsupp.disjoint_supported_supported (M := A) (R := A)
        (s := {i | g i = p}) (t := {i | g i ≠ p})
        (Set.disjoint_left.mpr fun _ hi hni => hni hi)).mono_right ?_
      refine iSup_le fun q => iSup_le fun hqp => Finsupp.supported_mono ?_
      intro i hi
      exact fun hip => hqp (hi.symm.trans hip)
    · rw [← Finsupp.supported_iUnion]
      have hcover : (⋃ p : ℤ, {i | g i = p}) = Set.univ := by
        ext i
        simp
      rw [hcover, Finsupp.supported_univ]

/-- The homogeneous piece is the supported submodule on the corresponding degree fibre. -/
theorem finsupp_piece (p : ℤ) :
    (finsupp A g).piece p = Finsupp.supported A A {i | g i = p} := (rfl)

variable {A g}

/-- A finitely supported function has degree `p` exactly when every nonzero coordinate
has assigned degree `p`. -/
@[simp]
theorem mem_finsupp_piece_iff {p : ℤ} {c : I →₀ A} :
    c ∈ (finsupp A g).piece p ↔ ∀ i, c i ≠ 0 → g i = p := by
  rw [finsupp_piece]
  simp [Finsupp.mem_supported, Set.subset_def]

/-- A single coordinate is homogeneous in its assigned degree, including a zero coefficient. -/
theorem single_mem_finsupp_piece (i : I) (a : A) :
    Finsupp.single i a ∈ (finsupp A g).piece (g i) := by
  rw [finsupp_piece]
  exact Finsupp.single_mem_supported A a rfl

/-- A single coordinate belongs to a homogeneous piece precisely when its coefficient
vanishes or its assigned degree is that of the piece. -/
theorem single_mem_finsupp_piece_iff (i : I) (a : A) (p : ℤ) :
    Finsupp.single i a ∈ (finsupp A g).piece p ↔ a = 0 ∨ g i = p := by
  classical
  rw [mem_finsupp_piece_iff]
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (h i (by simpa using ha))
  · rintro (rfl | hp) j hj
    · simp at hj
    · by_cases hji : j = i
      · simpa [hji] using hp
      · simp [hji] at hj

end TauCeti.InternalGrading
