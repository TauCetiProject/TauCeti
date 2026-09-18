/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Valuation extensions from valuative relations

Mathlib has two compatible notions of one valuation extending another. `ValuativeExtension A B`
states the relation intrinsically, without choosing value groups, while
`Valuation.HasExtension vA vB` states that the pullback of `vB` is equivalent to `vA`.

This file supplies the canonical bridge for the valuations attached to valuative relations. It
allows Mathlib's valuation-extension API, including its algebra maps between valuation rings and
residue fields, to be used directly from a `ValuativeExtension` hypothesis.

## Main result

* `ValuativeExtension.valuationHasExtension`: the canonical valuation on `B` extends the
  canonical valuation on `A`.
-/

public section

open ValuativeRel

namespace ValuativeExtension

variable {A B : Type*} [CommRing A] [Ring B] [ValuativeRel A] [ValuativeRel B]
  [Algebra A B] [ValuativeExtension A B]

/-- A compatible extension of valuative relations makes the canonical valuation on the larger
ring an extension, in Mathlib's valuation-level sense, of the canonical valuation on the base.
-/
instance valuationHasExtension :
    Valuation.HasExtension (valuation A) (valuation B) where
  val_isEquiv_comap :=
    (ValuativeRel.isEquiv ((valuation B).comap (algebraMap A B)) (valuation A)).symm

end ValuativeExtension
