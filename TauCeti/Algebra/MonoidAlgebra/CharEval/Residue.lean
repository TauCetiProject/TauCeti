/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.Algebra.MonoidAlgebra.CharEval.Basic

/-!
# Congruences of character evaluations modulo the maximal ideal

Let `O` be a commutative local ring with residue field `κ` and `G` a commutative group. Two
characters `ψ₁, ψ₂ : G →* Oˣ` whose values at every group element are congruent modulo the maximal
ideal of `O` induce identical `O[G] →ₐ[O] κ` homomorphisms
(`TauCeti.ofId_comp_charEval_eq_of_residue_eq`) and identical evaluations modulo `𝔪_O`
(`TauCeti.residue_charEval_eq_of_residue_eq`).

## Main results

* `TauCeti.ofId_comp_charEval_eq_of_residue_eq` and
  `TauCeti.residue_charEval_eq_of_residue_eq`: characters agreeing modulo `𝔪_O` induce equal
  evaluations on `O[G]` modulo `𝔪_O`.
-/

public section

namespace TauCeti

section ResidueEq

variable {O G : Type*} [CommRing O] [IsLocalRing O] [CommGroup G]

/-- Two characters whose values at every element of `G` agree modulo the maximal ideal of `O`
induce identical `O`-algebra homomorphisms `O[G] →ₐ[O] ResidueField O`. -/
theorem ofId_comp_charEval_eq_of_residue_eq {ψ₁ ψ₂ : G →* Oˣ}
    (h : ∀ g : G, IsLocalRing.residue O (ψ₁ g) = IsLocalRing.residue O (ψ₂ g)) :
    (Algebra.ofId O (IsLocalRing.ResidueField O)).comp ψ₁.charEval =
      (Algebra.ofId O (IsLocalRing.ResidueField O)).comp ψ₂.charEval := by
  apply MonoidAlgebra.algHom_ext
  · intro g
    simpa [IsLocalRing.ResidueField.algebraMap_eq] using h g
  · apply AlgHom.ext; intro a; simp

/-- Two characters whose values at every element of `G` agree modulo the maximal ideal of `O`
induce identical evaluations on `O[G]` modulo the maximal ideal of `O`. -/
theorem residue_charEval_eq_of_residue_eq {ψ₁ ψ₂ : G →* Oˣ}
    (h : ∀ g : G, IsLocalRing.residue O (ψ₁ g) = IsLocalRing.residue O (ψ₂ g))
    (x : MonoidAlgebra O G) :
    IsLocalRing.residue O (ψ₁.charEval x) = IsLocalRing.residue O (ψ₂.charEval x) := by
  simpa [IsLocalRing.ResidueField.algebraMap_eq] using
    DFunLike.congr_fun (ofId_comp_charEval_eq_of_residue_eq h) x

end ResidueEq

end TauCeti
