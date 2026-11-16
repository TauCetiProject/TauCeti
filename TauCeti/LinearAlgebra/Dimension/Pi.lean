/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The dimension of a finite product of lines and zero spaces

Over a division ring `D`, let `M : J → Type*` be a finite family of `D`-modules, each of which
is either a line (dimension `1`) or zero. Then `Π j, M j` has dimension the number of lines
(`TauCeti.finrank_pi_eq_card_of_finrank_eq_one`). This is the form in which Krull–Schmidt
multiplicities show up as dimensions over residue division rings.
-/

public section

open Module (finrank)

namespace TauCeti

/-- **A finite product of lines and zero spaces** over a division ring has dimension the number of
lines. -/
theorem finrank_pi_eq_card_of_finrank_eq_one {D : Type*} [DivisionRing D] {J : Type*}
    [Finite J] (M : J → Type*) [∀ j, AddCommGroup (M j)] [∀ j, Module D (M j)] (p : J → Prop)
    (h₁ : ∀ j, p j → finrank D (M j) = 1) (h₀ : ∀ j, ¬p j → Subsingleton (M j)) :
    finrank D (Π j, M j) = Nat.card {j // p j} := by
  classical
  have := Fintype.ofFinite J
  have (j : J) : Module.Finite D (M j) := by
    by_cases h : p j
    · exact Module.finite_of_finrank_eq_succ (h₁ j h)
    · have := h₀ j h
      infer_instance
  have hdim (j : J) : finrank D (M j) = if p j then 1 else 0 := by
    split_ifs with h
    · exact h₁ j h
    · have := h₀ j h
      exact Module.finrank_zero_of_subsingleton
  rw [Module.finrank_pi_fintype]
  simp [hdim, Nat.card_eq_fintype_card, Fintype.card_subtype]

end TauCeti
