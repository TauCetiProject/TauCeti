/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.WildInertia

/-!
# Composita of tame Galois extensions

The compositum of two finite Galois extensions of a nonarchimedean local field is tamely
ramified exactly when both factors are tamely ramified. This gives closure under composita
of the finite Galois subextensions of the maximal tame extension.

The criterion `TauCeti.le_maximalTameExtension_iff` identifies tameness with containment in
the canonical maximal tame extension. The compositum criterion below uses that identification
rather than constructing a second tame extension or choosing radical generators. All three
finite fields may carry any compatible local-field structures; no structure is imposed on
the algebraic closure.

## Main result

* `TauCeti.isTamelyRamified_sup_iff`: tameness of a finite Galois compositum is equivalent to
  tameness of its two factors.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (L M : IntermediateField K (AlgebraicClosure K))
  [Module.Finite K L] [Module.Finite K M] [IsGalois K L] [IsGalois K M]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]
  [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [ValuativeExtension K M]
  [ValuativeRel ↥(L ⊔ M)] [TopologicalSpace ↥(L ⊔ M)]
  [IsNonarchimedeanLocalField ↥(L ⊔ M)] [ValuativeExtension K ↥(L ⊔ M)]

/-- The compositum of two finite Galois subextensions of the algebraic closure of a
nonarchimedean local field is tamely ramified exactly when both factors are tamely ramified.
The valuation and topology on each finite field may be any compatible local-field structures. -/
theorem isTamelyRamified_sup_iff :
    IsTamelyRamified K ↥(L ⊔ M) ↔ IsTamelyRamified K L ∧ IsTamelyRamified K M := by
  rw [← le_maximalTameExtension_iff (L ⊔ M), sup_le_iff,
    le_maximalTameExtension_iff L, le_maximalTameExtension_iff M]

end TauCeti
