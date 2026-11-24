/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Continuity of change of scalars on general linear groups

A continuous ring homomorphism `f : A →+* B` induces a continuous group homomorphism
`Matrix.GeneralLinearGroup.continuousMap f hf : GL ι A →ₜ* GL ι B` acting entrywise via
`Matrix.GeneralLinearGroup.map f`.

## Main definitions

* `Matrix.GeneralLinearGroup.continuousMap`: continuous homomorphism `GL ι A →ₜ* GL ι B` induced
  by a continuous ring homomorphism `f : A →+* B`.

## Main results

* `Matrix.GeneralLinearGroup.continuousMap_apply`: evaluating `continuousMap f hf` agrees with
  `Matrix.GeneralLinearGroup.map f`.
* `Matrix.GeneralLinearGroup.toMonoidHom_continuousMap`: the underlying `MonoidHom` of
  `continuousMap f hf` is `Matrix.GeneralLinearGroup.map f`.
-/

public section

namespace Matrix.GeneralLinearGroup

/-- **Continuous `GL` map induced by a continuous ring homomorphism.** -/
def continuousMap {A B ι : Type*} [CommRing A] [TopologicalSpace A]
    [CommRing B] [TopologicalSpace B] [Fintype ι] [DecidableEq ι]
    (f : A →+* B) (hf : Continuous f) : GL ι A →ₜ* GL ι B where
  toMonoidHom := Matrix.GeneralLinearGroup.map f
  continuous_toFun := hf.generalLinearGroup_map

/-- Applying `Matrix.GeneralLinearGroup.continuousMap f hf` agrees with
`Matrix.GeneralLinearGroup.map f`. -/
@[simp]
theorem continuousMap_apply {A B ι : Type*} [CommRing A] [TopologicalSpace A]
    [CommRing B] [TopologicalSpace B] [Fintype ι] [DecidableEq ι]
    (f : A →+* B) (hf : Continuous f) (g : GL ι A) :
    continuousMap f hf g = Matrix.GeneralLinearGroup.map f g :=
  (rfl)

/-- The underlying `MonoidHom` of `Matrix.GeneralLinearGroup.continuousMap f hf` is
`Matrix.GeneralLinearGroup.map f`. -/
@[simp]
theorem toMonoidHom_continuousMap {A B ι : Type*} [CommRing A] [TopologicalSpace A]
    [CommRing B] [TopologicalSpace B] [Fintype ι] [DecidableEq ι]
    (f : A →+* B) (hf : Continuous f) :
    (continuousMap (ι := ι) f hf : GL ι A →* GL ι B) = Matrix.GeneralLinearGroup.map f :=
  (rfl)

end Matrix.GeneralLinearGroup
