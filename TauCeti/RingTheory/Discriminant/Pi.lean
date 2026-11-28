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

namespace TauCeti.Algebra

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
  {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- The discriminant of families supported in individual factors is the product of their
discriminants. The families need not be bases. -/
@[simp]
theorem discr_pi [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (b : ∀ i, κ i → A i) :
    Algebra.discr R (fun j : Σ i, κ i ↦ Pi.single j.1 (b j.1 j.2)) =
      ∏ i, Algebra.discr R (b i) := by
  simp only [Algebra.discr_def, traceMatrix_pi, Matrix.det_blockDiagonal']

/-- The discriminant in the product basis is the product of the discriminants of the factors. -/
@[simp]
theorem discr_pi_basis (b : ∀ i, Module.Basis (κ i) R (A i)) :
    Algebra.discr R (Pi.basis b) = ∏ i, Algebra.discr R (b i) := by
  have (i : ι) : Module.Free R (A i) := Module.Free.of_basis (b i)
  have (i : ι) : Module.Finite R (A i) := Module.Finite.of_basis (b i)
  rw [funext (Pi.basis_apply b)]
  exact discr_pi (R := R) (fun i ↦ ⇑(b i))

end TauCeti.Algebra
