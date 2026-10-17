/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Continuity
public import Mathlib.RingTheory.Finiteness.Defs

import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.StrictMorphism

/-!
# Finite injective maps into affinoid algebras

A finite injective algebra homomorphism from a noetherian ultrametric Banach algebra into
an affinoid algebra with a complete compatible ultrametric algebra norm is a closed topological
embedding. In particular this applies when the source is affinoid. Continuity follows from the
algebraic hypotheses, and the chosen complete algebra norms need not agree on the image.

The finite-module topology identifies the source with its image topologically, and
noetherianity makes that image closed. This allows finite algebraic inclusions to be used as
closed inclusions with any compatible complete algebra norms.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§3.7.2 and 6.1.3.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open Topology

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
    [CompleteSpace A] [IsNoetherianRing A]
    {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B]
    [CompleteSpace B]

/-- A finite injective algebra homomorphism from a noetherian ultrametric Banach algebra into
a completely normed affinoid algebra is a closed topological embedding. No continuity
hypothesis or normalisation of either algebra norm is required. -/
theorem isClosedEmbedding_of_finite_injective (hB : IsAffinoidAlgebra K B)
    (f : A →ₐ[K] B) (hfin : f.Finite) (hinj : Function.Injective f) :
    IsClosedEmbedding f := by
  let : Algebra A B := f.toRingHom.toAlgebra
  have : Module.Finite A B := hfin
  have : ContinuousSMul A B := continuousSMul_of_algebraMap A B (hB.continuous_algHom f)
  let : Huber.IsTateRing A := Huber.IsTateRing.of_normedAlgebra K A
  exact ⟨isEmbedding_iff_isStrictMap_injective.mpr
    ⟨(Algebra.linearMap A B).isStrictMap_of_module_finite, hinj⟩,
    Huber.isClosed_of_isNoetherian (LinearMap.range (Algebra.linearMap A B))⟩

end TauCeti.IsAffinoidAlgebra
