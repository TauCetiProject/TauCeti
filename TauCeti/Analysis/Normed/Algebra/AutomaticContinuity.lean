/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic

import TauCeti.RingTheory.Huber.ClosedSubmodule
import TauCeti.RingTheory.Huber.Normed
import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Automatic continuity into finite-dimensional algebras

An algebra homomorphism from a noetherian nonarchimedean Banach algebra into a
finite-dimensional topological algebra is continuous. The source kernel is closed, so its
quotient is a Hausdorff finite-dimensional vector space. This permits continuity to be tested
on finite-dimensional quotients without assuming continuity of the original homomorphism.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§3.7.2 and 3.7.5.
-/

public section

namespace TauCeti

/-- An algebra homomorphism from a noetherian ultrametric Banach algebra into a
finite-dimensional topological algebra is automatically continuous. The target need not
carry a norm, be complete, or be Hausdorff. -/
theorem continuous_algHom_of_finiteDimensional
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
    [CompleteSpace A] [IsNoetherianRing A]
    {B : Type*} [Ring B] [Algebra K B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [ContinuousSMul K B] [Module.Finite K B]
    (f : A →ₐ[K] B) : Continuous f := by
  let : Huber.IsTateRing A := Huber.IsTateRing.of_normedAlgebra K A
  let I := RingHom.ker f
  have : IsClosed (I : Set A) := Huber.isClosed_of_isNoetherian I
  have : Module.Finite K (A ⧸ I) :=
    Module.Finite.equiv (Ideal.quotientKerEquivRange f).symm.toLinearEquiv
  let g : A ⧸ I →ₐ[K] B := Ideal.kerLiftAlg f
  have hg : Continuous g := g.toLinearMap.continuous_of_finiteDimensional
  exact (hg.comp continuous_quot_mk).congr fun x ↦ Ideal.kerLiftAlg_mk f x

end TauCeti
