/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Discriminant
import TauCeti.RingTheory.NormTrace.Pi

/-!
# Discriminants of finite products

In the product basis, the trace pairing is block diagonal, with one block for each
factor's trace pairing. The discriminant is therefore the product of the discriminants.
-/

public section

namespace Module.Basis

/-- The discriminant in the product basis is the product of the discriminants of the factors. -/
@[simp]
theorem discr_pi {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (b : ∀ i, Basis (κ i) R (A i)) :
    Algebra.discr R (Pi.basis b) = ∏ i, Algebra.discr R (b i) := by
  have (i : ι) : Module.Free R (A i) := Module.Free.of_basis (b i)
  have (i : ι) : Module.Finite R (A i) := Module.Finite.of_basis (b i)
  have h : Algebra.traceMatrix R (Pi.basis b) =
      Matrix.blockDiagonal' fun i ↦ Algebra.traceMatrix R (b i) := by
    ext ⟨i, j⟩ ⟨i', j'⟩
    simp only [Matrix.blockDiagonal'_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      Pi.basis_apply, TauCeti.Algebra.trace_pi, Pi.mul_apply]
    split_ifs with hij
    · subst i'
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
      · simp
      · intro k _ hk
        simp [Pi.single_eq_of_ne hk]
    · apply Finset.sum_eq_zero
      intro k _
      by_cases hk : k = i
      · subst k
        simp [Pi.single_eq_of_ne hij]
      · simp [Pi.single_eq_of_ne hk]
  simp only [Algebra.discr_def, h, Matrix.det_blockDiagonal']

end Module.Basis
