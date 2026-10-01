/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Character
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.NeTwo
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Odd.Image
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CupSquare

/-!
# Marked normal forms of Demushkin groups

The normal form of a Demushkin group records more than its abstract isomorphism type: the
isomorphism can be chosen so that the canonical character takes Labute's prescribed values on the
marked generators. This file states the marked classification for the `q ≠ 2` family and for the
dyadic family of odd rank.

For `q ≠ 2` the relator is

`x₁ ^ q (x₁, x₂) (x₃, x₄) ⋯ (xₙ₋₁, xₙ)`,

the canonical character takes the value `(1 - q)⁻¹` on `x₂`, and it is trivial on the other
generators. The equation is stated without choosing an inverse, as
`χ(x₂) * (1 - q) = 1` in `ℤ_p`.

For odd rank `n`, where `p = 2` and `q = 2`, the relator is

`x₁² x₂^{2^f} (x₂, x₃) (x₄, x₅) ⋯ (xₙ₋₁, xₙ)`, `2 ≤ f < ∞`, or `x₁² (x₂, x₃) ⋯ (xₙ₋₁, xₙ)`, `f = ∞`,

the canonical character takes the value `-1` on `x₁`, the value `(1 - 2^f)⁻¹` on `x₃` at a finite
level, and is trivial on the other generators. The level `f` is an invariant of the group, the
level of the image `{±1} × U^(f)` of its canonical character, with `f = ∞` the image `{±1}`; the
statements take the image as a hypothesis, which is what pins `f`, and the finite-level statement
assumes `n ≥ 3`, since at rank one the marking clause on the third generator would read
`1 - 2^f = 1` (`TauCeti.not_marked_of_demushkinRank_le`). The standard dyadic group `D₀` is the
case `n = 3`, `f = 2`.

## Main results

* `TauCeti.isDemushkin_marked_of_q_ne_two`: the marked classification of a Demushkin group whose
  `q`-invariant is not `2`.
* `TauCeti.isDemushkin_marked_of_q_two_odd`, `TauCeti.isDemushkin_marked_of_q_two_odd_top`: the
  marked classification of a Demushkin group of odd rank, at a finite level and at level `f = ∞`.

## References

* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106--132,
  Theorems 3 and 4.
-/

public section

namespace TauCeti

open Subgroup

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **The marked classification at `q ≠ 2`.** A Demushkin group with `q`-invariant different
from `2` is isomorphic to the standard one-relator presentation on its generator rank. Under this
isomorphism the canonical character takes the value `(1 - q)⁻¹` on the second marked generator
and is trivial on every other marked generator. -/
theorem isDemushkin_marked_of_q_ne_two (hG : IsDemushkin p G) (hq : demushkinQ hG ≠ 2) :
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
  have hn : 1 < demushkinRank hG := by
    obtain ⟨k, hk⟩ := heven
    have := hG.demushkinRank_pos
    omega
  obtain ⟨hvalue, htrivial⟩ :=
    demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordNeTwo hG
      hG.prime_dvd_demushkinQ heven hn e
  exact ⟨hvalue, fun i hi _ ↦ htrivial i hi⟩

/-- **The marked classification at `q = 2` with `n` odd, finite level.** A Demushkin group at
`p = 2` of odd rank `n ≥ 3` whose canonical character has image `{±1} × U^(f)`, with `f ≥ 2`, is
isomorphic to `⟨x₁, …, xₙ ∣ x₁² x₂^{2^f} (x₂, x₃) ⋯ (xₙ₋₁, xₙ)⟩`. Under this isomorphism the
canonical character takes the value `-1` on the first marked generator, the value `(1 - 2^f)⁻¹` on
the third, and is trivial on every other marked generator. -/
theorem isDemushkin_marked_of_q_two_odd (hG : IsDemushkin 2 G) (hodd : Odd (demushkinRank hG))
    (hn : 3 ≤ demushkinRank hG) {f : ℕ} (hf : 2 ≤ f)
    (hrange : (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f) :
    ∃ e : G ≃ₜ* presentedProP 2 (Fin (demushkinRank hG))
        {demushkinWordTwoOdd f (demushkinRank hG) (freeProPGen 2 (demushkinRank hG))},
      demushkinCharacter hG (e.symm (presentedProPGen 2 (demushkinRank hG) _ 0)) = -1 ∧
        ((demushkinCharacter hG (e.symm (presentedProPGen 2 (demushkinRank hG) _ 2)) : ℤ_[2])
          * (1 - 2 ^ f) = 1) ∧
        ∀ i : ℕ, i ≠ 0 → i ≠ 2 → i < demushkinRank hG →
          demushkinCharacter hG (e.symm (presentedProPGen 2 (demushkinRank hG) _ i)) = 1 := by
  obtain ⟨e⟩ :=
    hG.nonempty_continuousMulEquiv_presentedProP_demushkinWordTwoOdd_of_range_eq hodd hn hf hrange
  obtain ⟨hfirst, hthird, htrivial⟩ :=
    demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordTwoOdd hG (by omega) hodd (by omega) e
  exact ⟨e, hfirst, hthird, fun i hi hi' _ ↦ htrivial i hi hi'⟩

/-- **The marked classification at `q = 2` with `n` odd, level `f = ∞`.** A Demushkin group at
`p = 2` of odd rank `n` whose canonical character has image `{±1}` is isomorphic to
`⟨x₁, …, xₙ ∣ x₁² (x₂, x₃) ⋯ (xₙ₋₁, xₙ)⟩`. Under this isomorphism the canonical character takes
the value `-1` on the first marked generator and is trivial on every other marked generator. At
rank one this is `ℤ/2 = ⟨x₁ ∣ x₁²⟩` with `χ(x₁) = -1`. -/
theorem isDemushkin_marked_of_q_two_odd_top (hG : IsDemushkin 2 G) (hodd : Odd (demushkinRank hG))
    (hrange : (demushkinCharacter hG).toMonoidHom.range = zpowers (-1 : ℤ_[2]ˣ)) :
    ∃ e : G ≃ₜ* presentedProP 2 (Fin (demushkinRank hG))
        {demushkinWordTwoOddTop (demushkinRank hG) (freeProPGen 2 (demushkinRank hG))},
      demushkinCharacter hG (e.symm (presentedProPGen 2 (demushkinRank hG) _ 0)) = -1 ∧
        ∀ i : ℕ, i ≠ 0 → i < demushkinRank hG →
          demushkinCharacter hG (e.symm (presentedProPGen 2 (demushkinRank hG) _ i)) = 1 := by
  obtain ⟨e⟩ :=
    hG.nonempty_continuousMulEquiv_presentedProP_demushkinWordTwoOddTop_of_range_eq hodd hrange
  obtain ⟨hfirst, htrivial⟩ :=
    demushkinCharacter_apply_equiv_symm_of_equiv_demushkinWordTwoOddTop hG hodd e
  exact ⟨e, hfirst, fun i hi _ ↦ htrivial i hi⟩

end TauCeti
