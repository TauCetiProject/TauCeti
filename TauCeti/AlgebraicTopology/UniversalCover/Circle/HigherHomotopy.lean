/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Instances.ZMultiples
public import TauCeti.Topology.Homotopy.HomotopyGroup.Covering
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
public import TauCeti.Topology.Homotopy.HomotopyGroup.TopologicalVectorSpace

/-!
# Higher homotopy groups of the circle

The real line covers every real additive circle `AddCircle p`. This file combines that
covering with the invariance of higher homotopy groups under covering maps to show that all
homotopy groups of a circle in dimensions at least two are trivial. The complex unit circle
`Circle` is homeomorphic to `AddCircle (2 * π)`, so its higher homotopy groups vanish as
well.

The only calculation needed in the total space is elementary: any two generalized loops in a
real topological vector space are homotopic relative to the cube boundary, so all homotopy
groups of such a space are subsingletons
(`HomotopyGroup.subsingleton_of_topologicalVectorSpace`). Applying the covering-map
isomorphism for `ℝ → AddCircle p` gives the circle calculation.

This proves Stage 4, item 11 of the Tau Ceti universal-covers roadmap
(`TauCetiRoadmap/UniversalCovers/README.md`): `π_n(S¹) = 0` for `n ≥ 2`.

## Main declarations

* `AddCircle.subsingleton_homotopyGroup`: `π_N(AddCircle p)` is trivial when `N` has at least two
  elements; instance resolution specializes it to `π_(n + 2)`.
* `AddCircle.homotopyGroup_eq_one`, `AddCircle.homotopyGroupPi_eq_one`: the corresponding
  equalities.
* `Circle.subsingleton_homotopyGroup`, `Circle.homotopyGroup_eq_one` and
  `Circle.homotopyGroupPi_eq_one`: the same statements for the complex unit circle.

The covering map is Junyan Xu's `AddCircle.isCoveringMap_coe` in
`Mathlib.Topology.Covering.AddCircle`.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace AddCircle

variable {N : Type*} [Nontrivial N] (p : ℝ) (x : AddCircle p)

/-- Every higher homotopy group of a real circle is trivial. The index type `N` being
nontrivial expresses that the dimension is at least two. -/
instance subsingleton_homotopyGroup : Subsingleton (HomotopyGroup N (AddCircle p) x) := by
  classical
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact (IsCoveringMap.homotopyGroupMulEquiv (N := N)
    (AddCircle.isCoveringMap_coe p) x).toEquiv.subsingleton_congr.mp inferInstance

/-- Every higher homotopy class of a real circle is the identity. -/
theorem homotopyGroup_eq_one [DecidableEq N] (a : HomotopyGroup N (AddCircle p) x) : a = 1 :=
  Subsingleton.elim _ _

/-- Every element of `π_(n + 2)` of a real circle is the identity. -/
theorem homotopyGroupPi_eq_one (n : ℕ) (a : π_ (n + 2) (AddCircle p) x) : a = 1 :=
  homotopyGroup_eq_one p x a

end AddCircle

namespace Circle

variable {N : Type*} [Nontrivial N] (z : Circle)

/-- Every higher homotopy group of the complex unit circle is trivial. It is transported from
`AddCircle (2 * π)` along `AddCircle.homeomorphCircle`. -/
instance subsingleton_homotopyGroup : Subsingleton (HomotopyGroup N Circle z) :=
  (HomotopyGroup.homeomorphEquivOfEq (N := N)
      (AddCircle.homeomorphCircle (T := 2 * Real.pi) Real.two_pi_pos.ne')
      ((AddCircle.homeomorphCircle (T := 2 * Real.pi)
        Real.two_pi_pos.ne').apply_symm_apply z)).subsingleton_congr.mp inferInstance

/-- Every higher homotopy class of the complex unit circle is the identity. -/
theorem homotopyGroup_eq_one [DecidableEq N] (a : HomotopyGroup N Circle z) : a = 1 :=
  Subsingleton.elim _ _

/-- Every element of `π_(n + 2)` of the complex unit circle is the identity. -/
theorem homotopyGroupPi_eq_one (n : ℕ) (a : π_ (n + 2) Circle z) : a = 1 :=
  homotopyGroup_eq_one z a

end Circle
