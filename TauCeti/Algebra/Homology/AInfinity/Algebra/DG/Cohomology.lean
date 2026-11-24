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

This file proves `TauCeti.DGAlgHom.bijective_cohomologyMap_iff_isQuasiIso`: a DG algebra morphism
induces a bijection on DG cohomology algebras if and only if its associated strict `A∞` morphism is
a quasi-isomorphism.

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
  simp [AInfinityAlgebra.mem_cycles, IsDGAlgebra.mem_cycles, AInfinityAlgebra.mem_boundaries,
    LinearMap.mem_range]

end TauCeti.DGAlgHom
