/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Character
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.NeTwo
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CupSquare

/-!
# Marked normal forms of Demushkin groups

The normal form of a Demushkin group records more than its abstract isomorphism type: the
isomorphism can be chosen so that the canonical character takes Labute's prescribed values on the
marked generators. This file begins the marked classification with the `q ≠ 2` family. In that
case the relator is

`x₁ ^ q (x₁, x₂) (x₃, x₄) ⋯ (xₙ₋₁, xₙ)`,

the canonical character takes the value `(1 - q)⁻¹` on `x₂`, and it is trivial on the other
generators. The equation is stated without choosing an inverse, as
`χ(x₂) * (1 - q) = 1` in `ℤ_p`.

## Main result

* `TauCeti.isDemushkin_marked_of_q_ne_two`: the marked classification of a Demushkin group whose
  `q`-invariant is not `2`.

## References

* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106--132,
  Theorems 3 and 4.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **The marked classification at `q ≠ 2`.** A Demushkin group with `q`-invariant different
from `2` is isomorphic to the standard one-relator presentation on its generator rank. Under this
isomorphism the canonical character takes the value `(1 - q)⁻¹` on the second marked generator
and is trivial on every other marked generator. -/
theorem isDemushkin_marked_of_q_ne_two (hG : IsDemushkin p G) (hq : demushkinQ hG ≠ 2)
    (hn : 2 ≤ demushkinRank hG) :
    ∃ e : G ≃ₜ* presentedProP p (Fin (demushkinRank hG))
        {demushkinWordNeTwo (demushkinQ hG) (demushkinRank hG)
          (freeProPGen p (demushkinRank hG))},
      ((demushkinCharacter hG
          (e.symm (presentedProPGen p (demushkinRank hG) _ 1)) : ℤ_[p])
          * (1 - (demushkinQ hG : ℤ_[p])) = 1) ∧
        ∀ i : ℕ, i ≠ 1 → i < demushkinRank hG →
          demushkinCharacter hG
            (e.symm (presentedProPGen p (demushkinRank hG) _ i)) = 1 := by
  obtain ⟨e⟩ := hG.exists_continuousMulEquiv_presentedProP_demushkinWordNeTwo_of_demushkinQ_ne_two
    hq
  refine ⟨e, ?_⟩
  have heven : Even (demushkinRank hG) := by
    by_cases hp : p = 2
    · subst p
      exact hG.even_demushkinRank_of_demushkinQ_ne_two hq
    · exact hG.even_demushkinRank_of_ne_two hp
  obtain ⟨hvalue, htrivial⟩ :=
    demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordNeTwo hG
      hG.prime_dvd_demushkinQ heven (by omega) e
  exact ⟨hvalue, fun i hi _ ↦ htrivial i hi⟩

end TauCeti
