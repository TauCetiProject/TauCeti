/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.Algebra.Homology.GradedCochainComplex

/-!
# The cochain complex underlying a DG algebra

The internal direct-sum grading of a DG algebra gives a cochain complex of modules: its
term in degree `n` is the degree-`n` homogeneous submodule and its differential is the
restriction of the algebra differential. This connects DG algebras to Mathlib's complex
and homology API.

## References

* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uA uExtra

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A}

namespace IsDGAlgebra

/-- The cochain complex underlying a DG algebra, with degree-`n` term `ULift (𝒜 n)`.
The lift lets complexes of DG algebras in different carrier universes share a module category. -/
noncomputable abbrev toCochainComplex (h : IsDGAlgebra 𝒜 dA) :
    CochainComplex (ModuleCat.{max uA uExtra} R) ℤ :=
  gradedCochainComplexLift.{uR, uA, uExtra} 𝒜 dA
    (LinearMap.isHomogeneous_def.mpr fun _ _ ha ↦ h.map_mem ha)
    fun _ x ↦ h.sq_zero x

end IsDGAlgebra

end TauCeti
