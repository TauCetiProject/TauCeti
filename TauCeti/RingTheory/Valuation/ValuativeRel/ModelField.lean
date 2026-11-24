/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Henselian
public import TauCeti.RingTheory.Valuation.ValuativeRel.ValueGroup

/-!
# Model fields: henselian discretely valued fields with perfect residue field

A field `K` with a valuative relation is a *model field* (`TauCeti.ModelField K`) if its valuation
is nontrivial, discrete and of rank at most one, its valuation ring `𝒪[K]` is a Henselian local
ring, and its residue field `𝓀[K]` is perfect. This is the base of Bruhat and Tits' theory of
integral models of reductive groups.

## Main definitions and results

* `TauCeti.ModelField`: the class of model fields.
* `TauCeti.ModelField.isDiscreteValuationRing`: the valuation ring of a model field is a discrete
  valuation ring.
* `TauCeti.ModelField.not_of_not_isNontrivial`: a field whose valuative relation is trivial is not a
  model field.
-/

public section

open ValuativeRel

namespace TauCeti

/-- A *model field* is a field `K` with a nontrivial discrete valuative relation of rank at most
one, whose valuation ring `𝒪[K]` is a Henselian local ring and whose residue field `𝓀[K]` is
perfect. Nonarchimedean local fields are model fields. -/
class ModelField (K : Type*) [Field K] [ValuativeRel K] : Prop extends
    IsDiscrete K, IsNontrivial K, IsRankLeOne K where
  /-- The valuation ring of a model field is a Henselian local ring. -/
  henselianLocalRing : HenselianLocalRing 𝒪[K]
  /-- The residue field of a model field is perfect. -/
  perfectField : PerfectField 𝓀[K]

namespace ModelField

attribute [instance] henselianLocalRing perfectField

variable (K : Type*) [Field K] [ValuativeRel K]

/-- The valuation ring of a model field is a discrete valuation ring. -/
theorem isDiscreteValuationRing [ModelField K] : IsDiscreteValuationRing 𝒪[K] :=
  inferInstance

/-- A field whose valuative relation is trivial is not a model field. -/
theorem not_of_not_isNontrivial (h : ¬ IsNontrivial K) : ¬ ModelField K :=
  fun hK ↦ h hK.toIsNontrivial

end ModelField

end TauCeti
