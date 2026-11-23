/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Canonical maps on topological cylinders

This file defines the canonical continuous maps associated with a topological cylinder `X × I`:

* `TauCeti.cylinderZero X`: the projection `(x, t) ↦ (x, 0)` onto the bottom of the cylinder.
* `TauCeti.cylinderSetIncl s`: the inclusion `s × I → X × I` of the cylinder over a subset
  `s ⊆ X`.
* `TauCeti.cylinderSlice X t`: the time-`t` slice embedding `x ↦ (x, t)` into `X × I`.

`TauCeti.cylinderZero` and `TauCeti.cylinderSetIncl` are exposed so dependent pullback fibres
reduce definitionally, while all three maps are accompanied by evaluation,
`ContinuousMap`-equality, and composition lemmas.
-/

public section

open scoped unitInterval

namespace TauCeti

/-- Projection `(x, t) ↦ (x, 0)` of a cylinder onto its time-zero slice. -/
@[expose] def cylinderZero (X : Type*) [TopologicalSpace X] : C(X × I, X × I) :=
  ContinuousMap.fst.prodMk (ContinuousMap.const (X × I) (0 : I))

theorem cylinderZero_eq (X : Type*) [TopologicalSpace X] :
    cylinderZero X = ContinuousMap.fst.prodMk (ContinuousMap.const (X × I) (0 : I)) :=
  (rfl)

theorem coe_cylinderZero (X : Type*) [TopologicalSpace X] :
    (cylinderZero X : X × I → X × I) = fun q ↦ (q.1, 0) :=
  (rfl)

@[simp]
theorem cylinderZero_apply {X : Type*} [TopologicalSpace X] (q : X × I) :
    cylinderZero X q = (q.1, 0) :=
  (rfl)

/-- Inclusion `s × I → X × I` of the cylinder over a subset `s ⊆ X`. -/
@[expose] def cylinderSetIncl {X : Type*} [TopologicalSpace X] (s : Set X) : C(s × I, X × I) :=
  ((ContinuousMap.id X).restrict s).prodMap (ContinuousMap.id I)

theorem cylinderSetIncl_eq {X : Type*} [TopologicalSpace X] (s : Set X) :
    cylinderSetIncl s = ((ContinuousMap.id X).restrict s).prodMap (ContinuousMap.id I) :=
  (rfl)

theorem coe_cylinderSetIncl {X : Type*} [TopologicalSpace X] (s : Set X) :
    (cylinderSetIncl s : s × I → X × I) = fun q ↦ (q.1.val, q.2) :=
  (rfl)

@[simp]
theorem cylinderSetIncl_apply {X : Type*} [TopologicalSpace X] (s : Set X) (q : s × I) :
    cylinderSetIncl s q = (q.1.val, q.2) :=
  (rfl)

/-- Time-`t` slice embedding `x ↦ (x, t)` into the cylinder `X × I`. -/
def cylinderSlice (X : Type*) [TopologicalSpace X] (t : I) : C(X, X × I) :=
  (ContinuousMap.id X).prodMk (ContinuousMap.const X t)

theorem cylinderSlice_eq (X : Type*) [TopologicalSpace X] (t : I) :
    cylinderSlice X t = (ContinuousMap.id X).prodMk (ContinuousMap.const X t) :=
  (rfl)

theorem coe_cylinderSlice (X : Type*) [TopologicalSpace X] (t : I) :
    (cylinderSlice X t : X → X × I) = fun x ↦ (x, t) :=
  (rfl)

@[simp]
theorem cylinderSlice_apply {X : Type*} [TopologicalSpace X] (t : I) (x : X) :
    cylinderSlice X t x = (x, t) :=
  (rfl)

@[simp]
theorem fst_comp_cylinderSlice (X : Type*) [TopologicalSpace X] (t : I) :
    ContinuousMap.fst.comp (cylinderSlice X t) = .id X := by
  ext x
  simp

@[simp]
theorem cylinderSlice_zero_comp_fst (X : Type*) [TopologicalSpace X] :
    (cylinderSlice X 0).comp ContinuousMap.fst = cylinderZero X :=
  ContinuousMap.ext fun q ↦ by simp

@[simp]
theorem cylinderZero_comp_cylinderSlice (X : Type*) [TopologicalSpace X] (t : I) :
    (cylinderZero X).comp (cylinderSlice X t) = cylinderSlice X 0 :=
  ContinuousMap.ext fun x ↦ by simp

@[simp]
theorem cylinderZero_comp_cylinderZero (X : Type*) [TopologicalSpace X] :
    (cylinderZero X).comp (cylinderZero X) = cylinderZero X :=
  ContinuousMap.ext fun q ↦ by simp

@[simp]
theorem cylinderZero_comp_cylinderSetIncl {X : Type*} [TopologicalSpace X] (s : Set X) :
    (cylinderZero X).comp (cylinderSetIncl s) = (cylinderSetIncl s).comp (cylinderZero s) :=
  ContinuousMap.ext fun q ↦ by simp

@[simp]
theorem cylinderSetIncl_comp_cylinderSlice {X : Type*} [TopologicalSpace X] (s : Set X) (t : I) :
    (cylinderSetIncl s).comp (cylinderSlice s t) =
      (cylinderSlice X t).comp ((ContinuousMap.id X).restrict s) :=
  ContinuousMap.ext fun _ ↦ rfl

end TauCeti
