/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The dimension of a finite product of lines and zero spaces

Over a ring `R` with the strong rank condition (for instance a division ring), let
`M : J → Type*` be a finite family of free `R`-modules, each of which is either a line
(dimension `1`) or zero. Then `Π j, M j` is finite (`TauCeti.finite_pi_of_finrank_eq_one`) and
has dimension the number of lines (`TauCeti.finrank_pi_eq_card_of_finrank_eq_one`). This is the
form in which Krull–Schmidt multiplicities show up as dimensions over residue division rings.
-/

public section

open Module (finrank)

namespace TauCeti

variable {R : Type*} [Semiring R] [StrongRankCondition R] {J : Type*} [Finite J]
  (M : J → Type*) [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)] [∀ j, Module.Free R (M j)]
  (p : J → Prop)

omit [Finite J] in
/-- A free line or a zero space is a finite module. -/
private theorem finite_of_finrank_eq_one (h₁ : ∀ j, p j → finrank R (M j) = 1)
    (h₀ : ∀ j, ¬p j → Subsingleton (M j)) (j : J) : Module.Finite R (M j) := by
  by_cases h : p j
  · exact Module.finite_of_finrank_eq_succ (h₁ j h)
  · have := h₀ j h
    infer_instance

/-- **A finite product of lines and zero spaces** is a finite module. -/
theorem finite_pi_of_finrank_eq_one (h₁ : ∀ j, p j → finrank R (M j) = 1)
    (h₀ : ∀ j, ¬p j → Subsingleton (M j)) : Module.Finite R (Π j, M j) :=
  have := finite_of_finrank_eq_one M p h₁ h₀
  inferInstance

/-- **A finite product of lines and zero spaces** has dimension the number of lines. -/
theorem finrank_pi_eq_card_of_finrank_eq_one (h₁ : ∀ j, p j → finrank R (M j) = 1)
    (h₀ : ∀ j, ¬p j → Subsingleton (M j)) :
    finrank R (Π j, M j) = Nat.card {j // p j} := by
  classical
  have := Fintype.ofFinite J
  have := finite_of_finrank_eq_one M p h₁ h₀
  have hdim (j : J) : finrank R (M j) = if p j then 1 else 0 := by
    split_ifs with h
    · exact h₁ j h
    · have := h₀ j h
      exact Module.finrank_zero_of_subsingleton
  rw [Module.finrank_pi_fintype]
  simp [hdim, Nat.card_eq_fintype_card, Fintype.card_subtype]

end TauCeti
