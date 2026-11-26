/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Order.Setoid.Basic
import Mathlib.Algebra.Group.Basic

/-!
# Conjugacy of multiplicative homomorphisms

Two multiplicative homomorphisms `φ, ψ : G →* H` into a group `H` are conjugate when they differ by
an inner automorphism of `H`, that is, when there is `c : H` with `c * φ a * c⁻¹ = ψ a` for all
`a : G`. In algebraic topology, when `Y` is path connected and aspherical, free homotopy classes of
maps `X → Y` from a path-connected CW complex correspond to equivalence classes under this setoid on
`π₁(X, x₀) →* π₁(Y, y₀)`.

## Main definitions

* `TauCeti.monoidHomConjSetoid`: the equivalence relation on `G →* H` identifying homomorphisms
  conjugate by an element of `H`, with `TauCeti.monoidHomConjSetoid_iff`.
-/

public section

namespace TauCeti

/-- **Conjugacy of multiplicative homomorphisms** by inner automorphisms of the target group: two
homomorphisms `φ, ψ : G →* H` are related when there exists `c : H` with `c * φ a * c⁻¹ = ψ a`
for every `a : G`. -/
def monoidHomConjSetoid (G H : Type*) [MulOne G] [Group H] : Setoid (G →* H) where
  r φ ψ := ∃ c : H, ∀ a : G, c * φ a * c⁻¹ = ψ a
  iseqv :=
    { refl := fun φ ↦ ⟨1, fun a ↦ by simp⟩
      symm := fun ⟨c, hc⟩ ↦ ⟨c⁻¹, fun a ↦ by
        have h := congrArg (fun x ↦ c⁻¹ * x * c) (hc a).symm
        simpa [mul_assoc] using h⟩
      trans := fun ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ ↦ ⟨c₂ * c₁, fun a ↦ by
        simp [mul_assoc, ← hc₁ a, ← hc₂ a]⟩ }

/-- Two homomorphisms are related by `TauCeti.monoidHomConjSetoid` exactly when they differ by
pointwise conjugation with a single element of the target group. -/
theorem monoidHomConjSetoid_iff {G H : Type*} [MulOne G] [Group H] {φ ψ : G →* H} :
    monoidHomConjSetoid G H φ ψ ↔ ∃ c : H, ∀ a : G, c * φ a * c⁻¹ = ψ a :=
  Iff.rfl

end TauCeti
