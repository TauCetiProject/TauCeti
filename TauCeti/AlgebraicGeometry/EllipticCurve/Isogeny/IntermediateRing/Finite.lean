/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.IntegralClosure.FinitePolynomialModel
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing

/-!
# The intermediate ring is module-finite over the target coordinate ring

`φ.intermediateRing` is a finite `W₂.CoordinateRing`-module. This is the finiteness that the
relative ideal norm — and through it `pushClass` and the induced map on points — needs.

Two routes reach it, with incomparable hypotheses.

* A **Dedekind source coordinate ring** needs no separability at all, Frobenius included.
  `W₁.CoordinateRing` is of finite type over `F` and its fraction field is exactly
  `W₁.FunctionField`, so being Dedekind makes it its own fraction model, and every one of its
  elements is integral over `W₂.CoordinateRing` because an isogeny maps infinity to infinity;
  `IsIntegralClosure.finite_of_fraction_model` then applies. An elliptic source curve is the
  case of interest, and supplies the Dedekind hypothesis.
* A **separable function-field extension** over an integrally closed `W₂.CoordinateRing` reaches
  it through Mathlib's `IsIntegralClosure.finite` directly. That asks nothing of `W₁` beyond the
  isogeny, so it still serves sources whose coordinate ring is not Dedekind.

Why the two routes differ in this hypothesis is worth stating, since it is exactly Frobenius that
fails to be separable and Frobenius is the case `pushClass` needs. `IsIntegralClosure.finite`
carries `[Algebra.IsSeparable K L]` because it argues through the trace pairing, whose form is
nondegenerate only in the separable case. The fraction-model route instead adjoins the finitely
many generators of `W₁.CoordinateRing` and uses that an overring of a Dedekind domain inside its
own fraction field is integrally closed; no trace form is built, so separability never arises.

## Main results

* `TauCeti.Isogeny.moduleFinite_intermediateRing_of_isDedekindDomain`: `φ.intermediateRing` is
  module-finite over `W₂.CoordinateRing` for a Dedekind source coordinate ring, with no
  separability hypothesis, and `TauCeti.Isogeny.moduleFinite_intermediateRing_of_isElliptic` for
  an elliptic source curve.
* `TauCeti.Isogeny.moduleFinite_intermediateRing`: the same conclusion for an integrally closed
  `W₂.CoordinateRing` and separable function-field extension.

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

The statement and the proof route — `IsIntegralClosure.finite` against a normal base — are those of
`module_finite` in AINTLIB's `HasseWeil/Curves/RamificationFinite.lean`
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `dev/hasse-weil @ 513e83879e2f`); that file's header
reads `Authors: Chris Birkbeck`, credited here rather than in the copyright header, following this
repository's convention for adapted material and matching `IntermediateRing/Basic.lean`. The source
*assumes* the integral-closure property that `isIntegralClosure_intermediateRing` proves, and
assumes the finite-dimensionality that `Isogeny.finiteDimensional_functionField` derives.

The separability-free route follows D. K. Angdinata's `Isogeny.lean`, Apache-2.0, supplied by the
author on 2026-09-07, whose `intermediateRingFinite` is the same conclusion reached by feeding an
isogeny's `mapsInfinity` into what is here
`IsIntegralClosure.finite_of_polynomial_model`. The route taken here differs, and is shorter: that
source keeps the curves general and therefore needs a *polynomial* model on a coordinate line,
which forces a case split on whether `W₁.polynomial`'s derivative vanishes — the `x`-coordinate
when it does not, and a `y`-coordinate fallback in the degenerate characteristic-two case, each
with its own separability lemma. Assuming `[W₁.IsElliptic]` instead makes `W₁.CoordinateRing`
itself a Dedekind domain whose fraction field is already `W₁.FunctionField`, so
`IsIntegralClosure.finite_of_fraction_model` applies with no model, no case split and no
separability lemma at all.
-/

public section

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **The intermediate ring is module-finite over the target coordinate ring**, for an isogeny
whose function-field extension is separable.

Integral closedness of `W₂.CoordinateRing` is what the proof spends, so it is assumed directly
rather than through `[W₂.IsElliptic]`, matching the sibling `id_intermediateRing`; for an elliptic
curve it is discharged by `WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing`.

Separability is what the Mathlib route needs, not what the result needs — see the module
docstring. -/
theorem moduleFinite_intermediateRing (φ : Isogeny W₁ W₂)
    [IsIntegrallyClosed W₂.CoordinateRing]
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.FunctionField W₁.FunctionField]
    [IsScalarTower W₂.CoordinateRing W₂.FunctionField W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    [Algebra.IsSeparable W₂.FunctionField W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    Module.Finite W₂.CoordinateRing φ.intermediateRing := by
  -- the integral-closure property is not assumed: it is what `intermediateRing` is
  have := φ.isIntegralClosure_intermediateRing h
  have := φ.finiteDimensional_functionField (φ.algebraMap_functionField_eq_fieldPullback h)
  exact IsIntegralClosure.finite W₂.CoordinateRing W₂.FunctionField W₁.FunctionField
    φ.intermediateRing

/-- **The intermediate ring is module-finite over the target coordinate ring, with no separability
hypothesis**, so this covers Frobenius. `W₁.CoordinateRing` is of finite type over `F` with
`W₁.FunctionField` as its fraction field, so being a Dedekind domain makes it its own fraction
model, and `φ.mapsInfinity` makes each of its elements integral over `W₂.CoordinateRing`.

Unlike the sibling `moduleFinite_intermediateRing`, integral closedness of `W₂.CoordinateRing` is
not needed either: the fraction-model route never asks the base to be normal. -/
theorem moduleFinite_intermediateRing_of_isDedekindDomain (φ : Isogeny W₁ W₂)
    [IsDedekindDomain W₁.CoordinateRing]
    [inst : Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    Module.Finite W₂.CoordinateRing φ.intermediateRing := by
  -- the caller's structure and the pullback-induced one agree on the structure map, so they are
  -- the same instance; substituting is what lets `algebraMap_mem_intermediateRing`, which is
  -- stated for the pullback-induced structure, apply on the nose
  have halg : inst = φ.pullback.toRingHom.toAlgebra := Algebra.algebra_ext _ _ h
  subst halg
  let _ := φ.pullback.toRingHom.toAlgebra
  have := φ.isIntegralClosure_intermediateRing h
  exact IsIntegralClosure.finite_of_fraction_model (F := F) (A := W₁.CoordinateRing)
    (K := W₁.FunctionField)
    fun x ↦ (φ.mem_intermediateRing_iff _).1 (φ.algebraMap_mem_intermediateRing x)

/-- `moduleFinite_intermediateRing_of_isDedekindDomain` for an elliptic source curve, whose
coordinate ring is a Dedekind domain. -/
theorem moduleFinite_intermediateRing_of_isElliptic (φ : Isogeny W₁ W₂) [W₁.IsElliptic]
    [Algebra W₂.CoordinateRing W₁.FunctionField]
    [Algebra W₂.CoordinateRing φ.intermediateRing]
    [IsScalarTower W₂.CoordinateRing φ.intermediateRing W₁.FunctionField]
    (h : ∀ x, algebraMap W₂.CoordinateRing W₁.FunctionField x = φ.pullback x) :
    Module.Finite W₂.CoordinateRing φ.intermediateRing := by
  have : IsDedekindDomain W₁.CoordinateRing :=
    WeierstrassCurve.Affine.isDedekindDomain_coordinateRing W₁
  exact φ.moduleFinite_intermediateRing_of_isDedekindDomain h

end Isogeny

end TauCeti
