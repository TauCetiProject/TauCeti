/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.ConjugateSubgroups
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Character

/-!
# The character of a quadratic field extension

A quadratic extension `L/K`, together with an embedding `σ : L →ₐ[K] Kˢ`, cuts out an
index-two open subgroup of `G_K`. Its index-two character gives a class
`χ_{L/K} ∈ H¹(G_K, 𝔽₂)`. Although the subgroup is initially described using `σ`, quadratic
fixing subgroups are normal and therefore independent of the embedding, so the resulting class is
attached to the extension alone.

This is the field-extension form of
`OpenSubgroup.indexTwoCharacterClass`. It is the character used by the index-two exact
sequence and by the norm-of-restriction formula for the Evens norm.

## Main definitions and results

* `TauCeti.galoisCharacter`: the class `χ_{L/K} ∈ H¹(G_K, 𝔽₂)`.
* `TauCeti.galoisCharacter_embedding_independent`: the class does not depend on the embedding of
  `L` into `Kˢ`.

## Reference

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I,
  §§5–6.
-/

public section

noncomputable section

namespace TauCeti

universe u v

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K) [FiniteDimensional K L]

/-- **The quadratic character `χ_{L/K}`.** It is the class in `H¹(G_K, 𝔽₂)` of the
index-two character whose kernel is the subgroup fixing the embedded copy `σ(L)`. -/
def galoisCharacter (hL : Module.finrank K L = 2) :
    continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup K)) :=
  (galoisSubgroup K L σ).indexTwoCharacterClass
    ((galoisSubgroup_index K L σ).trans hL)

/-- The quadratic character is the index-two character class of the Galois subgroup cut out by
the chosen embedding. -/
theorem galoisCharacter_def (hL : Module.finrank K L = 2) :
    galoisCharacter K L σ hL =
      (galoisSubgroup K L σ).indexTwoCharacterClass
        ((galoisSubgroup_index K L σ).trans hL) :=
  (rfl)

/-- **The quadratic character is independent of the embedding** `L →ₐ[K] Kˢ`. -/
theorem galoisCharacter_embedding_independent
    (τ : L →ₐ[K] SeparableClosure K) (hL : Module.finrank K L = 2) :
    galoisCharacter K L σ hL = galoisCharacter K L τ hL := by
  rw [galoisCharacter_def, galoisCharacter_def]
  exact OpenSubgroup.indexTwoCharacterClass_congr
    (galoisSubgroup_eq_of_finrank_eq_two K L σ τ hL) _ _

end TauCeti
