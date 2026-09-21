/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
import TauCeti.RingTheory.IntegralClosure.MvPolynomial
import TauCeti.RingTheory.IntegralClosure.Transfer

/-!
# The intermediate ring is module-finite over the target coordinate ring

`φ.intermediateRing` is a finite `W₂.CoordinateRing`-module, with no normality or separability
hypothesis. This is the finiteness that the relative ideal norm — and through it `pushClass` and
the induced map on points — needs, including for Frobenius.

The target coordinate ring is finite over `F[X]`, and `W₁.FunctionField` is finite over the
fraction field of `F[X]`: first through `W₂.FunctionField`, then through the finite extension an
isogeny induces. Since `φ.intermediateRing` is the integral closure of `W₂.CoordinateRing`, it is
also the integral closure of `F[X]`. The separability-free normalization theorem
`TauCeti.IsIntegralClosure.finite_polynomial` makes it finite over `F[X]`, hence over the target
coordinate ring.

## Main results

* `TauCeti.Isogeny.moduleFinite_intermediateRing`: `φ.intermediateRing` is module-finite over
  `W₂.CoordinateRing` for every isogeny.

## Design

The result is stated for arbitrary algebra structures whose structure maps are the pullback,
matching `Isogeny.degree_eq_finrank`, rather than for one fixed choice: registering such a
structure globally would be a diamond, since different isogenies induce different ones. A consumer
produces the `W₂.CoordinateRing`-structure on the intermediate ring from the bundled
`φ.pullbackToIntermediateRing` — `letI := φ.pullbackToIntermediateRing.toAlgebra` — which is why
`IntermediateRing/Basic.lean` corestricts the pullback rather than registering an instance.

That `letI` supplies the `Algebra` but not the `IsScalarTower` this theorem also takes, so it is
not by itself the whole setup. `Isogeny.isScalarTower_intermediateRing` supplies the tower from the
same corestriction, and the two together are what a caller needs.

## Provenance

The conclusion follows D. K. Angdinata's `Isogeny.lean`, Apache-2.0, supplied by the author on
2026-09-07, declaration `intermediateRingFinite`. That proof chooses a separating coordinate on
the source. The proof here instead uses the target's fixed coordinate line and the general
separability-free finite-normalization theorem, so it needs no coordinate case split.
-/

public section

open Polynomial

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The intermediate ring is module-finite over the target coordinate ring.** No normality or
separability hypothesis is needed, so this includes inseparable isogenies such as Frobenius. -/
theorem moduleFinite_intermediateRing (φ : Isogeny W₁ W₂)
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    Module.Finite W₂.CoordinateRing φ.intermediateRing := by
  -- Override the source-coordinate action of `F[X]` by the target-coordinate action. The
  -- explicit `SMul` bindings keep the algebra and module structures definitionally aligned.
  let polyFunctionFieldAlgebra : Algebra F[X] W₁.FunctionField :=
    Algebra.restrictScalars F[X] W₂.CoordinateRing W₁.FunctionField
  let _ : SMul F[X] W₁.FunctionField := polyFunctionFieldAlgebra.toSMul
  let _ : Algebra F[X] W₁.FunctionField := polyFunctionFieldAlgebra
  have : IsScalarTower F[X] W₂.CoordinateRing W₁.FunctionField :=
    .of_algebraMap_eq fun _ ↦ rfl
  let polyIntermediateRingAlgebra : Algebra F[X] φ.intermediateRing :=
    Algebra.restrictScalars F[X] W₂.CoordinateRing φ.intermediateRing
  let _ : SMul F[X] φ.intermediateRing := polyIntermediateRingAlgebra.toSMul
  let _ : Algebra F[X] φ.intermediateRing := polyIntermediateRingAlgebra
  have : IsScalarTower F[X] W₂.CoordinateRing φ.intermediateRing :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower F[X] φ.intermediateRing W₁.FunctionField :=
    .of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply F[X] W₂.CoordinateRing W₁.FunctionField,
        IsScalarTower.algebraMap_apply F[X] W₂.CoordinateRing φ.intermediateRing,
        IsScalarTower.algebraMap_apply W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
  let fractionFunctionFieldAlgebra : Algebra (FractionRing F[X]) W₁.FunctionField :=
    Algebra.restrictScalars (FractionRing F[X]) W₂.FunctionField W₁.FunctionField
  let _ : SMul (FractionRing F[X]) W₁.FunctionField :=
    fractionFunctionFieldAlgebra.toSMul
  let _ : Algebra (FractionRing F[X]) W₁.FunctionField := fractionFunctionFieldAlgebra
  have : IsScalarTower (FractionRing F[X]) W₂.FunctionField W₁.FunctionField :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower F[X] (FractionRing F[X]) W₁.FunctionField :=
    .of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply F[X] W₂.CoordinateRing W₁.FunctionField,
        IsScalarTower.algebraMap_apply W₂.CoordinateRing W₂.FunctionField W₁.FunctionField,
        ← IsScalarTower.algebraMap_apply F[X] W₂.CoordinateRing W₂.FunctionField,
        IsScalarTower.algebraMap_apply F[X] (FractionRing F[X]) W₂.FunctionField,
        IsScalarTower.algebraMap_apply (FractionRing F[X]) W₂.FunctionField W₁.FunctionField]
  have : FiniteDimensional W₂.FunctionField W₁.FunctionField :=
    φ.finiteDimensional_functionField (φ.algebraMap_functionField_eq_fieldPullback h)
  have : FiniteDimensional (FractionRing F[X]) W₁.FunctionField :=
    FiniteDimensional.trans (FractionRing F[X]) W₂.FunctionField W₁.FunctionField
  have : IsIntegralClosure φ.intermediateRing W₂.CoordinateRing W₁.FunctionField :=
    φ.isIntegralClosure_intermediateRing h
  have : IsIntegralClosure φ.intermediateRing F[X] W₁.FunctionField :=
    TauCeti.IsIntegralClosure.tower_bot (A := W₂.CoordinateRing)
  have : Module.Finite F[X] φ.intermediateRing :=
    TauCeti.IsIntegralClosure.finite_polynomial F (FractionRing F[X]) W₁.FunctionField
      φ.intermediateRing
  exact Module.Finite.of_restrictScalars_finite F[X] W₂.CoordinateRing φ.intermediateRing

end Isogeny

end TauCeti
