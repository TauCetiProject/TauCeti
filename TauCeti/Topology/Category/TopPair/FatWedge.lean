/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopPair

/-!
# The fat wedge of a power of a pointed space

For a pointed space `(X, x₀)`, the **fat wedge** of `Xⁿ` is the set of words of length `n` some
letter of which is the basepoint (`TauCeti.fatWedge`). The quotient of `Xⁿ` by the fat wedge is the
`n`-fold smash power of `(X, x₀)`, formed as the pointed quotient of the pair `(Xⁿ, fat wedge)`
(`TauCeti.fatWedgePair`).

## Main definitions

* `TauCeti.fatWedge`: the words of length `n` with a letter equal to the basepoint.
* `TauCeti.fatWedgePair`: the pair `(Xⁿ, fat wedge)`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.C.
-/

public section

universe u

namespace TauCeti

variable {X : Type u} {x₀ : X}

variable (X x₀) in
/-- The **fat wedge** of `Xⁿ`: the words of length `n` some letter of which is the basepoint. The
quotient of `Xⁿ` by the fat wedge is the `n`-fold smash power of `(X, x₀)`. -/
def fatWedge (n : ℕ) : Set (Fin n → X) :=
  {v | ∃ i, v i = x₀}

@[simp]
theorem mem_fatWedge_iff {n : ℕ} {v : Fin n → X} : v ∈ fatWedge X x₀ n ↔ ∃ i, v i = x₀ :=
  Iff.rfl

theorem notMem_fatWedge_iff {n : ℕ} {v : Fin n → X} : v ∉ fatWedge X x₀ n ↔ ∀ i, v i ≠ x₀ := by
  simp

variable [TopologicalSpace X]

variable (X x₀) in
/-- The pair `(Xⁿ, fat wedge)`. Its pointed quotient is the `n`-fold smash power of `(X, x₀)`. -/
abbrev fatWedgePair (n : ℕ) : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (Fin n → X)) (fatWedge X x₀ n)

instance (n : ℕ) : Nonempty (fatWedgePair X x₀ (n + 1)).snd :=
  ⟨⟨fun _ => x₀, 0, rfl⟩⟩

end TauCeti
