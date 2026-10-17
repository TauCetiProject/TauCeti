/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Huber.Completion.Noetherian

/-!
# Examples of completions of adic rings

The integers with the `(p)`-adic topology and its additive uniformity form a noetherian adic
ring; their uniform completion is complete for the extended ideal `(p)` and is noetherian. The
zero ideal gives the discrete topology, whose completion is complete for the zero ideal.
-/

open UniformSpace

-- `ℤ` with the `(p)`-adic topology: the completion is complete for `(p)` and noetherian.
example (p : ℤ) :
    letI := (Ideal.span {p}).adicTopology
    letI := IsTopologicalAddGroup.rightUniformSpace ℤ
    haveI := isUniformAddGroup_of_addCommGroup (G := ℤ)
    IsAdicComplete ((Ideal.span {p}).map (Completion.coeRingHom : ℤ →+* Completion ℤ))
        (Completion ℤ) ∧ IsNoetherianRing (Completion ℤ) := by
  let := (Ideal.span {p}).adicTopology
  let := IsTopologicalAddGroup.rightUniformSpace ℤ
  have := isUniformAddGroup_of_addCommGroup (G := ℤ)
  have hI : IsAdic (Ideal.span {p}) := rfl
  exact ⟨TauCeti.Huber.isAdicComplete_completion_of_isAdic hI (Submodule.fg_span_singleton p),
    TauCeti.Huber.isNoetherianRing_completion_of_isAdic hI⟩

-- The zero ideal: the completion of a discretely topologized ring is complete for the zero ideal.
example (R : Type*) [CommRing R] :
    letI := (⊥ : Ideal R).adicTopology
    letI := IsTopologicalAddGroup.rightUniformSpace R
    haveI := isUniformAddGroup_of_addCommGroup (G := R)
    IsAdicComplete ((⊥ : Ideal R).map (Completion.coeRingHom : R →+* Completion R))
      (Completion R) := by
  let := (⊥ : Ideal R).adicTopology
  let := IsTopologicalAddGroup.rightUniformSpace R
  have := isUniformAddGroup_of_addCommGroup (G := R)
  exact TauCeti.Huber.isAdicComplete_completion_of_isAdic rfl Submodule.fg_bot
