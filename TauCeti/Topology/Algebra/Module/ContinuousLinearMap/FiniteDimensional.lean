/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Continuous endomorphisms of a finite-dimensional topological vector space

A continuous linear map on a finite-dimensional topological vector space is invertible once it is
invertible as a linear map. Neither a norm nor completeness of the scalars is needed. Hence the
spectrum of such a map over the scalar field `𝕜` is the spectrum of its underlying linear map,
which is the finite set of its eigenvalues. Consequently its spectrum over any field `S` of scalars
acting compatibly, for instance over `ℝ` for a map on a complex space, is finite.

Mathlib's `ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap` and
`ContinuousLinearMap.spectrum_eq` are the corresponding statements on a Banach space.

## Main results

* `ContinuousLinearMap.isUnit_of_isUnit_toLinearMap_of_finiteDimensional`: a continuous linear
  map invertible as a linear map is invertible as a continuous linear map.
* `ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap_of_finiteDimensional` and
  `ContinuousLinearMap.spectrum_eq_of_finiteDimensional`: the corresponding equivalence and the
  equality of the spectra of `T` and of its underlying linear map.
* `ContinuousLinearMap.finite_spectrum`: a continuous linear map has finite spectrum, also over
  subfields of the scalars such as `ℝ ⊆ ℂ`.
* `ContinuousLinearMap.isUnit_smul_one_sub`: `c • 1 - T` is invertible when `T` has no
  eigenvector of eigenvalue `c`.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousConstSMul 𝕜 V] [FiniteDimensional 𝕜 V]

/-- On a finite-dimensional topological vector space, a continuous linear map that is invertible
as a linear map is invertible as a continuous linear map. The scalar field need not be complete,
or even topologized. -/
theorem isUnit_of_isUnit_toLinearMap_of_finiteDimensional {u : V →L[𝕜] V}
    (hu : IsUnit (u : Module.End 𝕜 V)) : IsUnit u := by
  -- The continuous linear maps form a finite-dimensional algebra, hence an Artinian ring, in
  -- which an element that is not a zero divisor is a unit.
  have := IsArtinianRing.of_finite 𝕜 (V →L[𝕜] V)
  exact IsArtinianRing.isUnit_of_mem_nonZeroDivisors <| mem_nonZeroDivisors_of_injective
    (f := toLinearMapRingHom) (fun _ _ h ↦ coe_injective h) hu.mem_nonZeroDivisors

/-- On a finite-dimensional topological vector space, a continuous linear map is invertible if and
only if it is invertible as a linear map. -/
theorem isUnit_iff_isUnit_toLinearMap_of_finiteDimensional {u : V →L[𝕜] V} :
    IsUnit u ↔ IsUnit (u : Module.End 𝕜 V) :=
  ⟨IsUnit.map toLinearMapRingHom, isUnit_of_isUnit_toLinearMap_of_finiteDimensional⟩

/-- On a finite-dimensional topological vector space, the spectrum of a continuous linear map is
the spectrum of its underlying linear map. -/
theorem spectrum_eq_of_finiteDimensional {T : V →L[𝕜] V} :
    spectrum 𝕜 T = spectrum 𝕜 (T : Module.End 𝕜 V) := by
  ext μ
  rw [spectrum.mem_iff, spectrum.mem_iff, isUnit_iff_isUnit_toLinearMap_of_finiteDimensional]
  rfl

/-- A continuous linear map on a finite-dimensional topological vector space has finite spectrum
over any field `S` of scalars acting compatibly, for instance over `ℝ` for a map on a complex
space. -/
theorem finite_spectrum (S : Type*) [Field S] [Algebra S 𝕜] [Algebra S (V →L[𝕜] V)]
    [IsScalarTower S 𝕜 (V →L[𝕜] V)] (T : V →L[𝕜] V) : (spectrum S T).Finite := by
  rw [← spectrum.preimage_algebraMap 𝕜, spectrum_eq_of_finiteDimensional]
  exact (Module.End.finite_spectrum _).preimage (algebraMap S 𝕜).injective.injOn

/-- On a finite-dimensional topological vector space, `c • 1 - T` is invertible as soon as `T` has
no eigenvector of eigenvalue `c`. -/
theorem isUnit_smul_one_sub {T : V →L[𝕜] V} {c : 𝕜} (h : ∀ v, T v = c • v → v = 0) :
    IsUnit (c • 1 - T) := by
  refine isUnit_of_isUnit_toLinearMap_of_finiteDimensional
    ((LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot'.2 fun v hv ↦ h v ?_))
  have hv' : c • v - T v = 0 := by simpa using hv
  exact (sub_eq_zero.1 hv').symm

end ContinuousLinearMap
