/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.ResidueField
public import TauCeti.RingTheory.Valuation.ValuativeRel.ModelField

/-!
# `Breve E` is a model field

Let `E` be a nonarchimedean local field and `Breve E` the completion of its maximal unramified
extension. The valuation of `Breve E` is discrete of rank at most one, by instance search through
`UniformSpace.Completion.isDiscrete` and `UniformSpace.Completion.isRankLeOne` applied to the
unramified extension; it is nontrivial, its valuation ring is Henselian, and its residue field is
algebraically closed, hence perfect. So `Breve E` is a `TauCeti.ModelField`, the base field of
Bruhat and Tits' theory of integral models, although it is not a local field: its residue field is
infinite.

## Main results

* `TauCeti.MaxUnramifiedCompletion.breveModelField`: `Breve E` is a model field.
-/

public section

open ValuativeRel

namespace TauCeti.MaxUnramifiedCompletion

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- **`Breve E` is a model field**: its valuation is nontrivial, discrete and of rank at most one,
its valuation ring is Henselian, and its residue field is algebraically closed, hence perfect. -/
instance breveModelField : ModelField (Breve E) where
  henselianLocalRing := breveHenselianLocalRing E
  perfectField := inferInstance

end TauCeti.MaxUnramifiedCompletion
