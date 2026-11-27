/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.Induction.Classification
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.OneDimensional

import TauCeti.Topology.Algebra.Group.Units

/-!
# The irreducible continuous representations of `W_ℝ`

This file assembles the classification of the irreducible finite-dimensional continuous complex
representations of the Weil group `W_ℝ = ℂˣ ⊔ jℂˣ`: such a representation is either a character
through the norm, `character s ε`, acting on a line, or it is isomorphic to the two-dimensional
induction `induceRepresentation (complexUnitsCharacter s k)` of a character
`z ↦ |z| ^ s * (z / |z|) ^ k` of `W_ℂ = ℂˣ` with `k ≠ 0`. Conversely each of these is
irreducible.

The two-dimensional half is `WeilGroupReal.exists_equiv_induceRepresentation`, which needs no
continuity. For a continuous `ρ`, the character `χ` it produces is continuous: in the basis of
`induceRepresentation χ`, the value `χ z` is a coordinate of `ρ z` applied to a fixed vector
(`WeilGroupReal.continuous_of_equiv_induceRepresentation`). Hence `χ` is
`complexUnitsCharacter s k`, and `χ ∘ conj ≠ χ` becomes `k ≠ 0`, because precomposing with complex
conjugation replaces `k` by `-k`. Interchanging the two exponents of the character does not change
the induction (`WeilGroupReal.nonempty_equiv_induceRepresentation_comp_star`), so the inductions of
`complexUnitsCharacter s k` and `complexUnitsCharacter s (-k)` are isomorphic.

## Main results

* `TauCeti.ClassFieldTheory.WeilGroupReal.continuous_of_equiv_induceRepresentation`: a continuous
  finite-dimensional representation isomorphic to the induction of `χ` forces `χ` continuous.
* `WeilGroupReal.isIrreducible_induceRepresentation_complexUnitsCharacter_iff`: the induction of
  `complexUnitsCharacter s k` is irreducible if and only if `k ≠ 0`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.exists_equiv_induceRepresentation_complexUnitsCharacter`:
  an irreducible two-dimensional continuous representation of `W_ℝ` is isomorphic to the induction
  of `complexUnitsCharacter s k` for some `s` and some `k ≠ 0`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.irreducibleClassification`: the classification of the
  irreducible finite-dimensional continuous representations of `W_ℝ`.

## References

* A. W. Knapp, *Local Langlands correspondence: the archimedean case*, in *Motives*,
  Proc. Sympos. Pure Math. 55, Part 2 (1994), §3, pp.401–403.
-/

public section

open Module Representation

namespace TauCeti.ClassFieldTheory

namespace WeilGroupReal

/-- **Irreducibility of the induction of `z ↦ |z| ^ s * (z / |z|) ^ k`.** The induction of
`complexUnitsCharacter s k` from `W_ℂ` to `W_ℝ` is irreducible if and only if `k ≠ 0`. -/
theorem isIrreducible_induceRepresentation_complexUnitsCharacter_iff (s : ℂ) (k : ℤ) :
    (induceRepresentation (complexUnitsCharacter s k : WeilGroupComplex →* ℂˣ)).IsIrreducible ↔
      k ≠ 0 := by
  rw [isIrreducible_induceRepresentation_iff, complexUnitsCharacter_comp_starMulAut_ne_iff]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [IsModuleTopology ℂ V]

/-- **Continuity of the inducing character.** If a continuous representation
of `W_ℝ` is isomorphic to the induction of a character `χ` of `W_ℂ`, then `χ` is continuous. -/
theorem continuous_of_equiv_induceRepresentation
    (ρ : ContinuousRep WeilGroupReal ℂ V) {χ : WeilGroupComplex →* ℂˣ}
    (e : ρ.toRepresentation.Equiv (induceRepresentation χ)) : Continuous χ := by
  have he : Continuous (e.toLinearMap : V → Fin 2 → ℂ) :=
    IsModuleTopology.continuous_of_linearMap _
  have hval (z : WeilGroupComplex) :
      (χ z : ℂ) = e (ρ (includeComplex z) (e.symm (Pi.single 0 1))) 0 := by
    have h := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap
      (includeComplex z) (e.symm (Pi.single 0 1))
    rw [Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.apply_symm_apply,
      ContinuousRep.coe_toRepresentation] at h
    rw [h, induceRepresentation_includeComplex]
    simp
  have hc : Continuous fun z : WeilGroupComplex ↦ (χ z : ℂ) := by
    simp_rw [hval]
    exact (continuous_apply 0).comp
      (he.comp ((ρ.continuous_orbit _).comp continuous_includeComplex))
  exact (MonoidHom.continuous_iff_continuous_val χ).2 hc

/-- **The two-dimensional irreducible continuous representations of `W_ℝ`.** An irreducible
two-dimensional continuous representation of `W_ℝ` is isomorphic to the induction of a character
`z ↦ |z| ^ s * (z / |z|) ^ k` of `W_ℂ` with `k ≠ 0`. -/
theorem exists_equiv_induceRepresentation_complexUnitsCharacter
    (ρ : ContinuousRep WeilGroupReal ℂ V) (hρ : ρ.toRepresentation.IsIrreducible)
    (h2 : finrank ℂ V = 2) :
    ∃ (s : ℂ) (k : ℤ), k ≠ 0 ∧ Nonempty (ρ.toRepresentation.Equiv
      (induceRepresentation (complexUnitsCharacter s k : WeilGroupComplex →* ℂˣ))) := by
  have : FiniteDimensional ℂ V := .of_finrank_pos (by omega)
  obtain ⟨χ, hχ, ⟨e⟩⟩ := exists_equiv_induceRepresentation ρ.toRepresentation hρ h2
  obtain ⟨s, k, hsk⟩ :=
    exists_eq_complexUnitsCharacter ⟨χ, continuous_of_equiv_induceRepresentation ρ e⟩
  have hχ' : χ = (complexUnitsCharacter s k : WeilGroupComplex →* ℂˣ) :=
    congrArg ContinuousMonoidHom.toMonoidHom hsk
  subst hχ'
  exact ⟨s, k, (complexUnitsCharacter_comp_starMulAut_ne_iff s k).1 hχ, ⟨e⟩⟩

/-- **Classification of the irreducible continuous representations of `W_ℝ`.** A continuous
finite-dimensional complex representation of `W_ℝ` is irreducible if and only if either it is a
line on which `W_ℝ` acts by a character through the norm `character s ε`, or it is isomorphic to
the two-dimensional induction of a character `z ↦ |z| ^ s * (z / |z|) ^ k` of `W_ℂ` with
`k ≠ 0`. -/
theorem irreducibleClassification [FiniteDimensional ℂ V] (ρ : ContinuousRep WeilGroupReal ℂ V) :
    ρ.toRepresentation.IsIrreducible ↔
      (finrank ℂ V = 1 ∧ ∃ (s : ℂ) (ε : ZMod 2), ∀ w v, ρ w v = (character s ε w : ℂ) • v) ∨
        ∃ (s : ℂ) (k : ℤ), k ≠ 0 ∧ Nonempty (ρ.toRepresentation.Equiv
          (induceRepresentation (complexUnitsCharacter s k : WeilGroupComplex →* ℂˣ))) := by
  constructor
  · intro hρ
    have hpos := hρ.finrank_pos
    have hle := finrank_le_two_of_isIrreducible ρ.toRepresentation hρ
    by_cases h1 : finrank ℂ V = 1
    · exact .inl ⟨h1, exists_eq_character_smul ρ h1⟩
    · exact .inr (exists_equiv_induceRepresentation_complexUnitsCharacter ρ hρ (by omega))
  · rintro (⟨h1, -⟩ | ⟨s, k, hk, ⟨e⟩⟩)
    · exact isIrreducible_of_finrank_eq_one _ h1
    · exact e.symm.isIrreducible
        ((isIrreducible_induceRepresentation_complexUnitsCharacter_iff s k).2 hk)

end WeilGroupReal

end TauCeti.ClassFieldTheory
