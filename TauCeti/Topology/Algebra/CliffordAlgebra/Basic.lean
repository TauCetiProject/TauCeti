/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Star

/-!
# Topology on Clifford algebras

This file gives a Clifford algebra its module topology. Over a topological ring this makes the
Clifford algebra a topological additive group, and multiplication is continuous when the Clifford
algebra is a finite module. The topology is Hausdorff when the base ring is Hausdorff and the
Clifford algebra is free. Clifford reverse, involution, and star are continuous without these
additional assumptions.

The topology is intrinsic: it depends only on the module structure of the Clifford algebra and does
not use a basis, Pin or Spin groups, or their actions. A basis appears only in the proof that the
topology is Hausdorff.

## Main results

* `CliffordAlgebra.instTopologicalSpaceCliffordAlgebra` installs the module topology.
* `CliffordAlgebra.instIsTopologicalAddGroupCliffordAlgebra` makes addition continuous.
* `QuadraticMap.Isometry.continuous_cliffordAlgebraMap` proves continuity of maps induced by
  quadratic isometries.
* `CliffordAlgebra.instIsTopologicalRingCliffordAlgebra` makes multiplication continuous.
* `CliffordAlgebra.instT2SpaceCliffordAlgebra` proves the topology is Hausdorff.
* `CliffordAlgebra.continuous_reverse` and `CliffordAlgebra.continuous_involute` prove continuity
  of the two canonical Clifford involutions.
* `CliffordAlgebra.instContinuousStarCliffordAlgebra` packages continuity of Clifford star.
-/

public section


namespace CliffordAlgebra

open TauCeti

noncomputable section

universe u v


variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {V : Type v} [AddCommGroup V] [Module R V]

/-- The canonical topology on a Clifford algebra is its module topology. -/
instance instTopologicalSpaceCliffordAlgebra (Q : QuadraticForm R V) :
    TopologicalSpace (CliffordAlgebra Q) :=
  moduleTopology R _

/-- The Clifford-algebra map induced by an isometry of quadratic spaces is continuous for the
canonical module topologies. -/
@[fun_prop]
theorem _root_.QuadraticMap.Isometry.continuous_cliffordAlgebraMap
    {W : Type*} [AddCommGroup W] [Module R W]
    {Q : QuadraticForm R V} {P : QuadraticForm R W} (f : Q →qᵢ P) :
    Continuous (CliffordAlgebra.map f) := by
  let _ : ContinuousAdd (CliffordAlgebra P) := IsModuleTopology.toContinuousAdd R _
  exact IsModuleTopology.continuous_of_linearMap (CliffordAlgebra.map f).toLinearMap

/-- Clifford reversal is continuous for the module topology. -/
@[fun_prop]
theorem continuous_reverse (Q : QuadraticForm R V) :
    Continuous (reverse (Q := Q) : CliffordAlgebra Q → CliffordAlgebra Q) := by
  let _ : ContinuousAdd (CliffordAlgebra Q) := IsModuleTopology.toContinuousAdd R _
  exact IsModuleTopology.continuous_of_linearMap (reverse (Q := Q))

/-- The Clifford grade involution is continuous for the module topology. -/
@[fun_prop]
theorem continuous_involute (Q : QuadraticForm R V) :
    Continuous (involute (Q := Q) : CliffordAlgebra Q → CliffordAlgebra Q) := by
  let _ : ContinuousAdd (CliffordAlgebra Q) := IsModuleTopology.toContinuousAdd R _
  exact IsModuleTopology.continuous_of_linearMap (involute (Q := Q)).toLinearMap

/-- Clifford star is continuous for the module topology. -/
instance instContinuousStarCliffordAlgebra (Q : QuadraticForm R V) :
    ContinuousStar (CliffordAlgebra Q) where
  continuous_star := by
    convert (continuous_reverse Q).comp (continuous_involute Q) using 1
    funext x
    exact star_def x

variable [IsTopologicalRing R]

/-- A Clifford algebra is a topological additive group for its module topology. -/
instance instIsTopologicalAddGroupCliffordAlgebra (Q : QuadraticForm R V) :
    IsTopologicalAddGroup (CliffordAlgebra Q) :=
  IsModuleTopology.isTopologicalAddGroup R _

/-- The module topology on a free Clifford algebra over a Hausdorff ring is Hausdorff. -/
instance instT2SpaceCliffordAlgebra [T2Space R] (Q : QuadraticForm R V)
    [Module.Free R (CliffordAlgebra Q)] :
    T2Space (CliffordAlgebra Q) := by
  let b := Module.Free.chooseBasis R (CliffordAlgebra Q)
  let f : CliffordAlgebra Q → (Module.Free.ChooseBasisIndex R (CliffordAlgebra Q) → R) :=
    fun x i => b.repr x i
  exact T2Space.of_injective_continuous (f := f)
    (by
      intro x y h
      apply b.repr.injective
      ext i
      exact congrFun h i)
    (continuous_pi fun i => IsModuleTopology.continuous_of_linearMap (b.coord i))

/-- A Clifford algebra that is finite as a module is a topological ring for its module topology. -/
instance instIsTopologicalRingCliffordAlgebra (Q : QuadraticForm R V)
    [Module.Finite R (CliffordAlgebra Q)] :
    IsTopologicalRing (CliffordAlgebra Q) :=
  IsModuleTopology.isTopologicalRing R _

end

end CliffordAlgebra
