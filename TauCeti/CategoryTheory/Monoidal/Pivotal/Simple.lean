/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Spherical
public import TauCeti.CategoryTheory.Preadditive.Schur

/-!
# Traces of endomorphisms of simple objects

Let `C` be a pivotal category which is `k`-linear, for an algebraically closed field `k`, with
kernels. By Schur's lemma every endomorphism `f` of a simple object `X` with finite-dimensional
endomorphisms is the scalar `TauCeti.endAlgEquivOfSimple k X (End.of f)` times `𝟙 X`. Since the
traces are `k`-linear, the trace of `f` is that scalar times the dimension of `X`:

* `leftTrace f = endAlgEquivOfSimple k X (End.of f) • leftDim X`;
* `rightTrace f = endAlgEquivOfSimple k X (End.of f) • rightDim X`;
* `trace f = endAlgEquivOfSimple k X (End.of f) • quantumDim X` in a spherical category.

When the unit `𝟙_ C` is itself simple with finite-dimensional endomorphisms, applying
`endAlgEquivOfSimple k (𝟙_ C)` to these identities reads the traces as elements of `k`, by the
`simp` lemmas for `End.of` of `TauCeti.CategoryTheory.Linear.Endomorphism`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace TauCeti

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]
  [Preadditive C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C] [HasKernels C]
variable {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]

/-- The left trace of an endomorphism of a simple object is its scalar times the left dimension. -/
theorem leftTrace_eq_smul_leftDim (f : X ⟶ X) :
    leftTrace f = endAlgEquivOfSimple k X (End.of f) • leftDim X := by
  obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id k f
  simp

/-- The right trace of an endomorphism of a simple object is its scalar times the right
dimension. -/
theorem rightTrace_eq_smul_rightDim (f : X ⟶ X) :
    rightTrace f = endAlgEquivOfSimple k X (End.of f) • rightDim X := by
  obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id k f
  simp

/-- In a spherical category, the trace of an endomorphism of a simple object is its scalar times
the quantum dimension. -/
theorem trace_eq_smul_quantumDim [SphericalCategory C] (f : X ⟶ X) :
    trace f = endAlgEquivOfSimple k X (End.of f) • quantumDim X := by
  rw [trace_eq_leftTrace, leftTrace_eq_smul_leftDim k, quantumDim_eq_leftDim]

end TauCeti
