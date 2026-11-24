/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Henselian
public import TauCeti.RingTheory.Valuation.ValuativeRel.ModelField

/-!
# Nonarchimedean local fields are model fields

A nonarchimedean local field `K` is a `TauCeti.ModelField`: Mathlib supplies the nontrivial
discrete valuative relation of rank at most one and the finiteness (hence perfectness) of the
residue field, and `TauCeti.henselianLocalRing_integer` the Henselian property of `𝒪[K]`.

## Main results

* `TauCeti.IsNonarchimedeanLocalField.modelField`: every nonarchimedean local field is a model
  field.
-/

public section

namespace TauCeti.IsNonarchimedeanLocalField

/-- Every nonarchimedean local field is a model field. -/
instance modelField (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [_root_.IsNonarchimedeanLocalField K] : ModelField K where
  henselianLocalRing := henselianLocalRing_integer K
  perfectField := inferInstance

end TauCeti.IsNonarchimedeanLocalField
