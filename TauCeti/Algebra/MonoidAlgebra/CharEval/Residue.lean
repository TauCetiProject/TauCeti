/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.Algebra.MonoidAlgebra.CharEval.Basic
import TauCeti.Algebra.CharP.LocalRing

/-!
# Congruences of character evaluations modulo the maximal ideal

Let `O` be a commutative local ring with residue field `κ` and `G` a commutative group. Two
characters `ψ₁, ψ₂ : G →* Oˣ` whose values at every group element are congruent modulo the maximal
ideal of `O` induce identical `O[G] → κ` homomorphisms
(`TauCeti.residue_charEval_eq_of_residue_eq`). When `κ` has exponential characteristic `p`, this
residue congruence holds whenever `ψ₁(g)` and `ψ₂(g)` have equal `p^k`-th powers for some `k`
(`TauCeti.residue_charEval_eq_of_pow_eq`), by `IsLocalRing.residue_eq_of_pow_eq`.

## Main results

* `TauCeti.residue_charEval_eq_of_residue_eq`: characters agreeing modulo `𝔪_O` induce equal
  evaluations on `O[G]` modulo `𝔪_O`.
* `TauCeti.residue_charEval_eq_of_pow_eq`: characters with equal `p^k`-th powers induce equal
  evaluations on `O[G]` modulo `𝔪_O`.
-/

public section

namespace TauCeti

section ResidueEq

variable {O G : Type*} [CommRing O] [IsLocalRing O] [CommGroup G]

/-- Two characters whose values at every element of `G` agree modulo the maximal ideal of `O`
induce identical evaluations on `O[G]` modulo the maximal ideal of `O`. -/
theorem residue_charEval_eq_of_residue_eq {ψ₁ ψ₂ : G →* Oˣ}
    (h : ∀ g : G, IsLocalRing.residue O (ψ₁ g) = IsLocalRing.residue O (ψ₂ g))
    (x : MonoidAlgebra O G) :
    IsLocalRing.residue O (ψ₁.charEval x) = IsLocalRing.residue O (ψ₂.charEval x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single g a => simp [h g]

end ResidueEq

section ExpChar

variable {O G : Type*} [CommRing O] [IsLocalRing O] [CommGroup G]
variable (p : ℕ) [ExpChar (IsLocalRing.ResidueField O) p]

/-- Two characters whose values at every element of `G` have equal `p^k`-th powers for some `k`
induce identical evaluations modulo the maximal ideal of `O`. -/
theorem residue_charEval_eq_of_pow_eq {ψ₁ ψ₂ : G →* Oˣ}
    (h : ∀ g : G, ∃ k : ℕ, ψ₁ g ^ p ^ k = ψ₂ g ^ p ^ k) (x : MonoidAlgebra O G) :
    IsLocalRing.residue O (ψ₁.charEval x) = IsLocalRing.residue O (ψ₂.charEval x) :=
  residue_charEval_eq_of_residue_eq
    (fun g ↦ let ⟨_, hk⟩ := h g
      IsLocalRing.residue_eq_of_pow_eq p (by simpa using congrArg Units.val hk))
    x

end ExpChar

end TauCeti
