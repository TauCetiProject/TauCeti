/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Cohomology
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Cohomology

/-!
# Cohomology of differential graded algebra morphisms as `A∞` morphisms

A differential graded algebra morphism `f : A ⟶ B` induces both a graded algebra homomorphism
`f.cohomologyMap` on DG cohomology (`TauCeti.DGAlgHom.cohomologyMap`) and, via the embedding of DG
algebras into `A∞` algebras (`TauCeti.NonUnitalDGAlgHom.toAInfinityStrictHom`), a strict `A∞`
morphism whose cohomology map determines `TauCeti.AInfinityHom.IsQuasiIso`.

This file compares the two notions of quasi-isomorphism: `f.cohomologyMap` is bijective if and only
if the associated `A∞` morphism is a quasi-isomorphism
(`TauCeti.DGAlgHom.bijective_cohomologyMap_iff_isQuasiIso`).

## Main results

* `TauCeti.DGAlgHom.bijective_cohomologyMap_iff_isQuasiIso`: a DG algebra morphism induces a
  bijection on DG cohomology algebras if and only if its associated `A∞` morphism is a
  quasi-isomorphism.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

namespace TauCeti.DGAlgHom

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B] {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

/-- A morphism of DG algebras induces a bijection on DG cohomology algebras if and only if its
associated strict `A∞` morphism is a quasi-isomorphism. -/
theorem bijective_cohomologyMap_iff_isQuasiIso (f : DGAlgHom hA hB) :
    Function.Bijective f.cohomologyMap ↔
      f.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsQuasiIso := by
  rw [f.bijective_cohomologyMap_iff_forall_cycles, AInfinityHom.isQuasiIso_iff_forall_cycles]
  have hlin (x : A) :
      f.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.linearPart x = f x := by
    simp
  have hcycA (x : A) :
      x ∈ hA.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.cycles ↔ x ∈ hA.cycles := by
    simp [AInfinityAlgebra.mem_cycles, IsDGAlgebra.mem_cycles]
  have hcycB (y : B) :
      y ∈ hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.cycles ↔ y ∈ hB.cycles := by
    simp [AInfinityAlgebra.mem_cycles, IsDGAlgebra.mem_cycles]
  have hbdA (x : A) :
      x ∈ hA.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.boundaries ↔ x ∈ LinearMap.range dA := by
    simp [AInfinityAlgebra.mem_boundaries, LinearMap.mem_range]
  have hbdB (y : B) :
      y ∈ hB.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.boundaries ↔ y ∈ LinearMap.range dB := by
    simp [AInfinityAlgebra.mem_boundaries, LinearMap.mem_range]
  simp only [hlin, hcycA, hcycB, hbdA, hbdB]

end TauCeti.DGAlgHom
