/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Huber.Completion.Noetherian

/-!
# Examples: adic completeness and noetherianity of completions

The completion of a ring with the `I`-adic topology, `I` finitely generated, is complete for the
extended ideal. These examples apply this at the zero ideal (discrete topology), at the unit ideal
(indiscrete topology, whose Hausdorff completion is the zero ring), at the ideal `(p)` of `ℤ` with
its `(p)`-adic topology and additive uniformity, and at the ideal `(X)` of `ℤ[X]` with its
`X`-adic topology; in the last two cases the completion is moreover Noetherian.

## References

* [The Stacks Project][stacks], Lemma 10.96.3 (tag
  [05GG](https://stacks.math.columbia.edu/tag/05GG)).
-/

open UniformSpace

section Generic

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

-- The zero ideal: the topology is discrete and the completion is complete for the zero ideal.
example (h : IsAdic (⊥ : Ideal R)) :
    IsAdicComplete ((⊥ : Ideal R).map (Completion.coeRingHom : R →+* Completion R))
      (Completion R) :=
  h.isAdicComplete_map_coeRingHom Submodule.fg_bot

-- The unit ideal: the topology is indiscrete and the completion is complete for the unit ideal.
example (h : IsAdic (⊤ : Ideal R)) :
    IsAdicComplete ((⊤ : Ideal R).map (Completion.coeRingHom : R →+* Completion R))
      (Completion R) :=
  h.isAdicComplete_map_coeRingHom ⟨{1}, by simp⟩

end Generic

section Integers

-- `ℤ` with the `(p)`-adic topology and its additive uniformity: the completion is complete for the
-- extended ideal `(p)` and Noetherian.
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
  exact ⟨hI.isAdicComplete_map_coeRingHom (Submodule.fg_span_singleton p),
    hI.isNoetherianRing_completion⟩

end Integers

section Polynomial

open Polynomial

-- `ℤ[X]` with its `(X)`-adic topology: the completion is complete for the extended ideal `(X)`.
example :
    letI : WithIdeal ℤ[X] := ⟨Ideal.span {X}⟩
    IsAdicComplete ((Ideal.span {X}).map (Completion.coeRingHom : ℤ[X] →+* Completion ℤ[X]))
      (Completion ℤ[X]) :=
  letI : WithIdeal ℤ[X] := ⟨Ideal.span {X}⟩
  IsAdic.isAdicComplete_map_coeRingHom (by rfl) (Submodule.fg_span_singleton X)

-- `ℤ[X]` with its `(X)`-adic topology: the completion, that is `ℤ⟦X⟧`, is Noetherian.
example :
    letI : WithIdeal ℤ[X] := ⟨Ideal.span {X}⟩
    IsNoetherianRing (Completion ℤ[X]) :=
  letI : WithIdeal ℤ[X] := ⟨Ideal.span {X}⟩
  IsAdic.isNoetherianRing_completion (I := Ideal.span {X}) (by rfl)

end Polynomial
