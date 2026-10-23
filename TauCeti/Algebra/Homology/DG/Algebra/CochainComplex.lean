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

/-- The degree-`p` term of the cochain complex underlying a DG algebra. -/
theorem toCochainComplex_X (h : IsDGAlgebra 𝒜 dA) (p : ℤ) :
    h.toCochainComplex.{uR, uA, uExtra}.X p = ModuleCat.of R (ULift.{uExtra} (𝒜 p)) :=
  gradedCochainComplexLift_X p

/-- The differential of a DG algebra's underlying cochain complex is the lifted restriction
of its differential to homogeneous components. -/
theorem toCochainComplex_d (h : IsDGAlgebra 𝒜 dA) (p : ℤ) :
    h.toCochainComplex.{uR, uA, uExtra}.d p (p + 1) =
      eqToHom (h.toCochainComplex_X.{uR, uA, uExtra} p) ≫
        ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
          ((dA.restrict (p := 𝒜 p) (q := 𝒜 (p + 1))
            fun _ ha ↦ h.map_mem ha).comp ULift.moduleEquiv.toLinearMap)) ≫
        eqToHom (h.toCochainComplex_X.{uR, uA, uExtra} (p + 1)).symm := by
  simpa only [toCochainComplex, toCochainComplex_X] using
    gradedCochainComplexLift_d (hdeg := LinearMap.isHomogeneous_def.mpr
      fun _ _ ha ↦ h.map_mem ha) (hsq := fun _ y ↦ h.sq_zero y) p

/-- On a homogeneous element, the underlying cochain differential is the algebra differential. -/
theorem toCochainComplex_d_apply (h : IsDGAlgebra 𝒜 dA) (p : ℤ) (x : 𝒜 p) :
    (eqToHom (h.toCochainComplex_X.{uR, uA, uExtra} (p + 1))
      (h.toCochainComplex.{uR, uA, uExtra}.d p (p + 1)
        (eqToHom (h.toCochainComplex_X.{uR, uA, uExtra} p).symm
          (ULift.up x)))).down.val = dA x := by
  convert gradedCochainComplexLift_d_apply (hdeg := LinearMap.isHomogeneous_def.mpr
    fun _ _ ha ↦ h.map_mem ha) (hsq := fun _ y ↦ h.sq_zero y) p x using 1

end IsDGAlgebra

end TauCeti
