/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.Basic
import TauCeti.Topology.Algebra.Module.ComplexSmulI

/-!
# Complex-differentiable maps are `J`-holomorphic

A complex normed space `V` carries the almost complex structure `v ↦ i v`
(`TauCeti.AlmostComplexStructure.ofComplexModule`). A map between complex normed spaces that is
complex differentiable at a point has a complex-linear derivative there, so it is
constant-structure `J`-holomorphic for these structures
(`DifferentiableAt.isConstStructureJHolomorphicAt_ofComplexModule`), and likewise within a set
(`DifferentiableWithinAt.isConstStructureJHolomorphicWithinAt_ofComplexModule`,
`DifferentiableOn.isConstStructureJHolomorphicOn_ofComplexModule`). This supplies holomorphic
reparametrizations of discs, such as affine maps of `ℂ`, as `J`-holomorphic maps.

Conversely, a real-linear map commuting with multiplication by `i` is the real restriction of a
complex-linear map (`ContinuousLinearMap.complexOfMapISmul`), so for these structures
constant-structure `J`-holomorphicity is complex differentiability
(`TauCeti.isConstStructureJHolomorphicAt_ofComplexModule_iff`,
`TauCeti.isConstStructureJHolomorphicWithinAt_ofComplexModule_iff`,
`TauCeti.isConstStructureJHolomorphicOn_ofComplexModule_iff`). This turns `J`-holomorphic
functions on discs into holomorphic functions, to which complex analysis applies.
-/

public section

open TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {f : V → W} {s : Set V} {x : V}

/-- The real restriction of a complex-linear map is complex linear for the structures `v ↦ i v`. -/
theorem ContinuousLinearMap.isComplexLinearMap_ofComplexModule_restrictScalars (L : V →L[ℂ] W) :
    IsComplexLinearMap (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) (L.restrictScalars ℝ).toLinearMap :=
  (isComplexLinearMap_iff_apply _ _ _).2 fun v ↦ by
    simp [AlmostComplexStructure.ofComplexModule_apply]

/-- A map that is complex differentiable at `x` is constant-structure `J`-holomorphic there for the
structures `v ↦ i v`. -/
theorem DifferentiableAt.isConstStructureJHolomorphicAt_ofComplexModule
    (hf : DifferentiableAt ℂ f x) :
    IsConstStructureJHolomorphicAt (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) f x :=
  isConstStructureJHolomorphicAt_of_hasFDerivAt (hf.hasFDerivAt.restrictScalars ℝ)
    (fderiv ℂ f x).isComplexLinearMap_ofComplexModule_restrictScalars

/-- A map that is complex differentiable within `s` at `x` is constant-structure `J`-holomorphic
within `s` there for the structures `v ↦ i v`. -/
theorem DifferentiableWithinAt.isConstStructureJHolomorphicWithinAt_ofComplexModule
    (hf : DifferentiableWithinAt ℂ f s x) :
    IsConstStructureJHolomorphicWithinAt (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) f s x :=
  isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt
    (hf.hasFDerivWithinAt.restrictScalars ℝ)
    (fderivWithin ℂ f s x).isComplexLinearMap_ofComplexModule_restrictScalars

/-- A map that is complex differentiable on `s` is constant-structure `J`-holomorphic on `s` for the
structures `v ↦ i v`. -/
theorem DifferentiableOn.isConstStructureJHolomorphicOn_ofComplexModule
    (hf : DifferentiableOn ℂ f s) :
    IsConstStructureJHolomorphicOn (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) f s :=
  isConstStructureJHolomorphicOn_of_forall fun x hx ↦
    (hf x hx).isConstStructureJHolomorphicWithinAt_ofComplexModule

namespace TauCeti

/-- For the structures `v ↦ i v`, a map is constant-structure `J`-holomorphic at `x` exactly when it
is complex differentiable at `x`. -/
theorem isConstStructureJHolomorphicAt_ofComplexModule_iff :
    IsConstStructureJHolomorphicAt (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) f x ↔ DifferentiableAt ℂ f x := by
  refine ⟨fun hf ↦ ?_, DifferentiableAt.isConstStructureJHolomorphicAt_ofComplexModule⟩
  obtain ⟨L, hL, hlin⟩ := (isConstStructureJHolomorphicAt_iff _ _ f x).1 hf
  have hI : ∀ v, L (Complex.I • v) = Complex.I • L v := by
    simpa [AlmostComplexStructure.ofComplexModule_apply] using
      (isComplexLinearMap_iff_apply _ _ _).1 hlin
  exact (hasFDerivAt_of_restrictScalars ℝ hL
    (L.restrictScalars_complexOfMapISmul hI)).differentiableAt

/-- For the structures `v ↦ i v`, a map is constant-structure `J`-holomorphic within `s` at `x`
exactly when it is complex differentiable within `s` at `x`. -/
theorem isConstStructureJHolomorphicWithinAt_ofComplexModule_iff :
    IsConstStructureJHolomorphicWithinAt (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) f s x ↔ DifferentiableWithinAt ℂ f s x := by
  refine ⟨fun hf ↦ ?_,
    DifferentiableWithinAt.isConstStructureJHolomorphicWithinAt_ofComplexModule⟩
  obtain ⟨L, hL, hlin⟩ := (isConstStructureJHolomorphicWithinAt_iff _ _ f s x).1 hf
  have hI : ∀ v, L (Complex.I • v) = Complex.I • L v := by
    simpa [AlmostComplexStructure.ofComplexModule_apply] using
      (isComplexLinearMap_iff_apply _ _ _).1 hlin
  exact (hL.of_restrictScalars ℝ (L.restrictScalars_complexOfMapISmul hI)).differentiableWithinAt

/-- For the structures `v ↦ i v`, a map is constant-structure `J`-holomorphic on `s` exactly when it
is complex differentiable on `s`. -/
theorem isConstStructureJHolomorphicOn_ofComplexModule_iff :
    IsConstStructureJHolomorphicOn (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) f s ↔ DifferentiableOn ℂ f s :=
  ⟨fun hf x hx ↦ isConstStructureJHolomorphicWithinAt_ofComplexModule_iff.1
      ((isConstStructureJHolomorphicWithinAt_iff _ _ f s x).2
        ((isConstStructureJHolomorphicOn_iff _ _ f s).1 hf x hx)),
    DifferentiableOn.isConstStructureJHolomorphicOn_ofComplexModule⟩

end TauCeti
