/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.DiscreteValuativeRel
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Model fields: henselian discretely valued fields with perfect residue field

A field `K` with a valuative relation is a *model field* (`TauCeti.ModelField K`) if its valuation
is nontrivial, discrete and of rank at most one, its valuation ring `𝒪[K]` is a Henselian local
ring, and its residue field `𝓀[K]` is perfect. This is the base of Bruhat and Tits' theory of
integral models of reductive groups, and the context of every discrete valuation ring statement in
the layer on smooth models of the ReductiveGroupsPartII roadmap.

`ValuativeRel.IsDiscrete` alone does not make the value group `ℤ`: a lexicographically ordered
`ℤ × ℤ` also has a largest element below `1`. Together with `ValuativeRel.IsNontrivial` and
`ValuativeRel.IsRankLeOne`, the value group with zero is `ℤᵐ⁰`, and `𝒪[K]` is a discrete valuation
ring.

## Main definitions and results

* `TauCeti.ModelField`: the class of model fields.
* `ValuativeRel.isDiscreteValuationRing_integer`: the valuation ring of a nontrivial discrete
  valuative relation of rank at most one on a field is a discrete valuation ring.
* `TauCeti.ModelField.isDiscreteValuationRing`: the valuation ring of a model field is a discrete
  valuation ring.
* `TauCeti.ModelField.not_of_isNontrivial`: a field whose valuative relation is trivial is not a
  model field.
-/

public section

open ValuativeRel

namespace ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K]

/-- The valuation ring of a nontrivial discrete valuative relation of rank at most one on a field
is a discrete valuation ring: its value group with zero is `ℤᵐ⁰`, by
`ValuativeRel.ValueGroupWithZero.nonempty_orderMonoidIso_withZeroMulInt_iff`. -/
theorem isDiscreteValuationRing_integer [IsDiscrete K] [IsNontrivial K] [IsRankLeOne K] :
    IsDiscreteValuationRing 𝒪[K] := by
  have hM : MulArchimedean (ValueGroupWithZero K) := isRankLeOne_iff_mulArchimedean.mp ‹_›
  obtain ⟨e⟩ := ValueGroupWithZero.nonempty_orderMonoidIso_withZeroMulInt_iff.mpr
    ⟨‹_›, ‹_›, hM⟩
  have : IsCyclic (ValueGroupWithZero K)ˣ :=
    (Units.mapEquiv e.toMulEquiv).isCyclic.mpr inferInstance
  have : (valuation K).IsNontrivial := (isNontrivial_iff_isNontrivial (valuation K)).mp ‹_›
  exact inferInstanceAs (IsDiscreteValuationRing (valuation K).valuationSubring)

end ValuativeRel

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
instance isDiscreteValuationRing [ModelField K] : IsDiscreteValuationRing 𝒪[K] :=
  isDiscreteValuationRing_integer K

/-- A field whose valuative relation is trivial is not a model field. -/
theorem not_of_isNontrivial (h : ¬ IsNontrivial K) : ¬ ModelField K :=
  fun hK ↦ h hK.toIsNontrivial

end ModelField

end TauCeti
