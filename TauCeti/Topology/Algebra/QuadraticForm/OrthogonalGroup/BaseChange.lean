/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.Topology.Algebra.Module.BaseChange

/-!
# Continuous scalar extension for orthogonal point groups

Let `K → L` be a continuous homomorphism of commutative rings carrying topologies, with `2`
invertible in `K`. Extending scalars from a quadratic space over `K` to `L` induces continuous
homomorphisms on its orthogonal group, and, for finite free modules, on its special orthogonal
group. The topology on each group is the subtype topology from the forward-and-inverse topology
on linear automorphisms.

These maps are the topological form of the localization maps used to compare rational orthogonal
point groups with local point groups.

## Main results

* `TauCeti.QuadraticMap.continuous_orthogonalGroupBaseChange`: scalar extension on orthogonal
  groups is continuous.
* `TauCeti.QuadraticMap.continuous_specialOrthogonalGroupBaseChange`: scalar extension on special
  orthogonal groups is continuous.
-/

public section

namespace TauCeti

namespace QuadraticMap

universe u v w

variable {K : Type u} {L : Type v} {V : Type w}
  [CommRing K] [CommRing L] [Algebra K L]
  [TopologicalSpace K] [TopologicalSpace L]
  [AddCommGroup V] [Module K V] [ContinuousMul (Module.End K V)]
  [Invertible (2 : K)]

/-- Extension of scalars is continuous on orthogonal groups when the scalar homomorphism is
continuous. -/
@[fun_prop]
theorem continuous_orthogonalGroupBaseChange (hKL : Continuous (algebraMap K L))
    (Q : _root_.QuadraticForm K V) :
    Continuous (orthogonalGroupBaseChange (A := L) Q) := by
  apply continuous_induced_rng.mpr
  exact ((LinearEquiv.continuous_baseChange (V := V) hKL).comp
    continuous_subtype_val).congr fun g => (coe_orthogonalGroupBaseChange (A := L) Q g).symm

/-- Extension of scalars is continuous on special orthogonal groups when the scalar homomorphism
is continuous. -/
@[fun_prop]
theorem continuous_specialOrthogonalGroupBaseChange [Module.Free K V] [Module.Finite K V]
    (hKL : Continuous (algebraMap K L))
    (Q : _root_.QuadraticForm K V) :
    Continuous (specialOrthogonalGroupBaseChange (A := L) Q) := by
  apply continuous_induced_rng.mpr
  exact ((LinearEquiv.continuous_baseChange (V := V) hKL).comp
    continuous_subtype_val).congr fun g =>
      (coe_specialOrthogonalGroupBaseChange (A := L) Q g).symm

end QuadraticMap

end TauCeti
