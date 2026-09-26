/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.ZModTwist

/-!
# The prescription property of a character

Let `G` be a topological group and `χ : G →ₜ* ℤ_pˣ` a continuous character, with twisted
coefficient modules `I(χ)/pⁱ = TauCeti.ZModTwist χ i`, on which `G` acts by `g • x = χ(g) x`. The
equivariant reductions `I(χ)/pⁱ → I(χ)/pʲ` for `j ≤ i` induce maps on continuous cohomology.

A character has the **prescription property** when every reduction
`H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)` is surjective: every continuous crossed homomorphism to
`I(χ)/p` lifts, modulo principal ones, to a continuous crossed homomorphism to `I(χ)/pⁱ`. This is
Labute's condition on the orientation of a Demushkin group: such a group has exactly one continuous
character with the prescription property, its canonical character (Labute, Thm 4). Here the
property is defined, against the explicit model of continuous cohomology; it holds for every
continuous character of a free pro-`p` group
(`TauCeti.freeProP.hasPrescriptionProperty`, in
`TauCeti.Topology.Algebra.Group.Profinite.Free.Prescription`). `I(χ)/p` is `ZModTwist χ 1`, the
module at `i = 1`, with carrier `ZMod (p ^ 1)`.

## Main definitions

* `TauCeti.HasPrescriptionProperty`: surjectivity of every `H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2
  and Theorem 4.
-/

public section

namespace TauCeti

universe u

open ContCohomology

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]

/-- **The prescription property** of a continuous character `χ : G →ₜ* ℤ_pˣ` (Labute's condition
on the orientation of a Demushkin group): every reduction `H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)`, for
`i ≥ 1`, is surjective. In cocycle terms, every continuous crossed homomorphism `G → I(χ)/p` is,
modulo principal ones, the reduction of a continuous crossed homomorphism `G → I(χ)/pⁱ`. -/
def HasPrescriptionProperty (χ : G →ₜ* ℤ_[p]ˣ) : Prop :=
  ∀ (i : ℕ) (hi : 1 ≤ i),
    Function.Surjective
      (explicitCoeff1 G (ZModTwist χ i) (ZModTwist.reduce χ hi) continuous_of_discreteTopology)

/-- The defining property of `HasPrescriptionProperty`, available to modules that only see the
declaration and not its body. -/
theorem hasPrescriptionProperty_iff (χ : G →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty χ ↔ ∀ (i : ℕ) (hi : 1 ≤ i),
      Function.Surjective
        (explicitCoeff1 G (ZModTwist χ i) (ZModTwist.reduce χ hi)
          continuous_of_discreteTopology) :=
  Iff.rfl

end TauCeti
