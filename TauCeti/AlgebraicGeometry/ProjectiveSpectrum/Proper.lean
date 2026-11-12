/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
public import TauCeti.RingTheory.GradedAlgebra.FiniteType

/-!
# Properness of the projective spectrum over its coefficient ring

Let `A` be an `ℕ`-graded `R`-algebra with grading `𝒜`. Mathlib proves that the projective spectrum
`Proj 𝒜` is separated over the spectrum of the degree-zero part `𝒜 0`, and proper over it when `A`
is of finite type over `𝒜 0` (`AlgebraicGeometry.Proj.toSpecZero`). This file transfers these
properties to the coefficient morphism `Proj 𝒜 ⟶ Spec R` (`AlgebraicGeometry.Proj.toSpecCoeff`),
which factors through `Spec (𝒜 0) ⟶ Spec R`:

* it is always separated;
* it is quasi-compact when `A` is of finite type over `𝒜 0`, and of finite type when `A` is of
  finite type over `R`;
* it is universally closed when moreover `𝒜 0` is integral over `R`, and proper when `A` is of
  finite type over `R` and `𝒜 0` is integral over `R`, for instance a finite `R`-module.

The hypothesis on the degree-zero part cannot be dropped: for `R[t][x]` with `t` in degree zero
and `x` in degree one, the projective spectrum is `Spec R[t]`, which is not universally closed over
`Spec R` when `R` is nonzero.

These statements are the affine-local input for properness of the relative `Proj` of a graded
quasi-coherent algebra over a scheme.

## Main results

* `AlgebraicGeometry.Proj.isSeparated_toSpecCoeff`
* `AlgebraicGeometry.Proj.quasiCompact_toSpecCoeff`
* `AlgebraicGeometry.Proj.locallyOfFiniteType_toSpecCoeff`
* `AlgebraicGeometry.Proj.universallyClosed_toSpecCoeff`
* `AlgebraicGeometry.Proj.isProper_toSpecCoeff`

## References

* [Stacks Project, Tag 01MC](https://stacks.math.columbia.edu/tag/01MC), separatedness of `Proj`
  over the degree-zero part.
* [Stacks Project, Tag 01MF](https://stacks.math.columbia.edu/tag/01MF), universal closedness of
  `Proj` over the degree-zero part for a graded ring of finite type over it.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Proj

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The projective spectrum of a graded algebra is separated over its coefficient ring. -/
instance isSeparated_toSpecCoeff : IsSeparated (toSpecCoeff 𝒜) := by
  rw [toSpecCoeff_def]
  infer_instance

/-- The projective spectrum of a graded algebra of finite type over its degree-zero part is
quasi-compact over the coefficient ring. -/
instance quasiCompact_toSpecCoeff [Algebra.FiniteType (𝒜 0) A] :
    QuasiCompact (toSpecCoeff 𝒜) := by
  rw [toSpecCoeff_def]
  infer_instance

/-- The projective spectrum of a graded algebra of finite type over `R` is locally of finite type
over `Spec R`. -/
instance locallyOfFiniteType_toSpecCoeff [Algebra.FiniteType R A] :
    LocallyOfFiniteType (toSpecCoeff 𝒜) := by
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  rw [toSpecCoeff_def]
  infer_instance

/-- The projective spectrum of a graded algebra of finite type over its degree-zero part is
universally closed over the coefficient ring when the degree-zero part is integral over it. -/
instance universallyClosed_toSpecCoeff [Algebra.FiniteType (𝒜 0) A]
    [Algebra.IsIntegral R (𝒜 0)] : UniversallyClosed (toSpecCoeff 𝒜) := by
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) := by
    rw [IsIntegralHom.SpecMap_iff]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  rw [toSpecCoeff_def]
  infer_instance

/-- **The projective spectrum is proper over the coefficient ring.** If the graded algebra is of
finite type over `R` and its degree-zero part is integral over `R`, for instance a finite
`R`-module, then `Proj 𝒜 ⟶ Spec R` is proper. -/
instance isProper_toSpecCoeff [Algebra.FiniteType R A] [Algebra.IsIntegral R (𝒜 0)] :
    IsProper (toSpecCoeff 𝒜) where

end AlgebraicGeometry.Proj
