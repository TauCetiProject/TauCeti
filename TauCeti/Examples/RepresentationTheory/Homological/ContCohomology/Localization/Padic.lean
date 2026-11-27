/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.Homological.ContCohomology.Localization.Padic

/-!
# Checks: rationalisation of lattice cohomology

Checks that the hypotheses of `TauCeti.ContinuousCohomology.rationalisationEquiv` are met by the
inclusion `ℤ_p → ℚ_p` with the trivial action of a compact group `G`, so that
`ℚ_p ⊗[ℤ_p] Hⁿ(G, ℤ_p) ≃ Hⁿ(G, ℚ_p)` in every degree.
-/

open CategoryTheory TauCeti.ContinuousCohomology
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (G : Type) [Group G]

/-- The inclusion `ℤ_p → ℚ_p` of trivial representations of a compact group satisfies the
hypotheses of `rationalisationEquiv`: its scalar extension `ℚ_p ⊗ ℤ_p → ℚ_p` is bijective. -/
noncomputable example [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (n : ℕ) :
    ℚ_[p] ⊗[ℤ_[p]] continuousCohomology n (TopRep.of (ContRepresentation.trivial ℤ_[p] G ℤ_[p]))
      ≃ₗ[ℤ_[p]] continuousCohomology n (TopRep.of (ContRepresentation.trivial ℤ_[p] G ℚ_[p])) :=
  rationalisationEquiv
    (ι := (TopRep.ofHom
      { toLinearMap := Algebra.linearMap ℤ_[p] ℚ_[p]
        cont := continuous_subtypeVal
        isIntertwining' _ := rfl } :
      TopRep.of (ContRepresentation.trivial ℤ_[p] G ℤ_[p]) ⟶
        TopRep.of (ContRepresentation.trivial ℤ_[p] G ℚ_[p])))
    (by
      convert (IsBaseChange.linearMap ℤ_[p] ℚ_[p]).equiv.bijective
      ext x
      rfl) n
