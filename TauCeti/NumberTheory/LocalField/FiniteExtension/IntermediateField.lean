/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic

/-!
# Local-field structures on finite intermediate fields

A finite intermediate field of an extension of a nonarchimedean local field need not inherit a
topology or a valuative relation from its ambient field. This file packages the spectral-norm
construction for such an intermediate field directly. The resulting named normed-field,
valuative-relation, and topology structures can be installed locally without placing any
structure on the ambient field and without introducing global instance diamonds.

The three accompanying theorems give the closed construction chain needed by consumers: the
new valuative relation extends the one on the base, the new topology is valuative, and together
they make the intermediate field a nonarchimedean local field.

## Main definitions

* `TauCeti.finiteIntermediateFieldNormedField`: the spectral-norm structure on a finite
  intermediate field.
* `TauCeti.finiteIntermediateFieldValuativeRel`: its valuative relation.
* `TauCeti.finiteIntermediateFieldTopology`: its topology.

## Main results

* `TauCeti.finiteIntermediateField_valuativeExtension`: the valuation extends the base
  valuation.
* `TauCeti.finiteIntermediateField_isValuativeTopology`: the topology is induced by the
  valuation.
* `TauCeti.finiteIntermediateField_isNonarchimedeanLocalField`: the intermediate field is a
  nonarchimedean local field.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §6.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §2.
-/

public section
noncomputable section

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (Ω : Type*) [Field Ω] [Algebra K Ω]

/-- The spectral-norm structure on a finite intermediate field `M/K`, constructed without
requiring a norm, topology, or valuative relation on the ambient field. -/
@[implicit_reducible]
def finiteIntermediateFieldNormedField (M : IntermediateField K Ω) [Module.Finite K M] :
    NormedField M :=
  finiteExtensionNormedField K M

/-- The valuative relation defined by the spectral norm on a finite intermediate field `M/K`.
It is a named structure so consumers can install it locally without creating instance diamonds. -/
@[implicit_reducible]
def finiteIntermediateFieldValuativeRel (M : IntermediateField K Ω) [Module.Finite K M] :
    ValuativeRel M :=
  finiteExtensionValuativeRel K M

/-- The topology defined by the spectral norm on a finite intermediate field `M/K`. -/
@[implicit_reducible]
def finiteIntermediateFieldTopology (M : IntermediateField K Ω) [Module.Finite K M] :
    TopologicalSpace M :=
  finiteExtensionNormedFieldTopology K M

/-- The valuative relation constructed on a finite intermediate field extends the valuative
relation of the base field. -/
theorem finiteIntermediateField_valuativeExtension
    (M : IntermediateField K Ω) [Module.Finite K M] :
    letI := finiteIntermediateFieldValuativeRel K Ω M
    ValuativeExtension K M :=
  finiteExtension_valuativeExtension K M

/-- The spectral-norm topology and valuative relation constructed on a finite intermediate field
are compatible. -/
theorem finiteIntermediateField_isValuativeTopology
    (M : IntermediateField K Ω) [Module.Finite K M] :
    @IsValuativeTopology M _ (finiteIntermediateFieldValuativeRel K Ω M)
      (finiteIntermediateFieldTopology K Ω M) :=
  finiteExtension_isValuativeTopology K M

/-- A finite intermediate field, equipped with its spectral-norm topology and valuative relation,
is a nonarchimedean local field. -/
theorem finiteIntermediateField_isNonarchimedeanLocalField
    (M : IntermediateField K Ω) [Module.Finite K M] :
    @IsNonarchimedeanLocalField M _ (finiteIntermediateFieldValuativeRel K Ω M)
      (finiteIntermediateFieldTopology K Ω M) :=
  finiteExtension_isNonarchimedeanLocalField K M

end TauCeti
