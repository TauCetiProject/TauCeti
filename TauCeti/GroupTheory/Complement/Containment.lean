/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.Local
public import TauCeti.GroupTheory.PGroup.Coset

/-!
# Complements containing a prescribed prime-power subgroup

If a normal subgroup `N` has a complement and `p` does not divide `|N|`, every `p`-subgroup
is contained in some complement of `N`. The complement is obtained by conjugating the given
one, using the fixed-point theorem for the action on its cosets. No commutativity of `N`,
solvability, or finiteness of the ambient group is needed.

In a semidirect product, this allows a complement to be chosen to contain the acting group;
its intersection with the normal factor is then an invariant complement.

## References

* B. Sambale, *On the converse of Gaschütz' complement theorem*, arXiv:2303.00254,
  Section 1, for the invariant-complement application.
-/

public section

namespace Subgroup.IsComplement'

variable {G : Type*} [Group G] {N D A : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]

/-- If `p` does not divide the order of a complemented normal subgroup, any `p`-subgroup
is contained in a complement. -/
theorem exists_isComplement'_and_le_of_not_dvd_card (h : N.IsComplement' D)
    (hA : IsPGroup p A) (hN : ¬ p ∣ Nat.card N) :
    ∃ D' : Subgroup G, N.IsComplement' D' ∧ A ≤ D' := by
  obtain ⟨g, hg⟩ := hA.exists_le_map_conj_of_not_dvd_index D
    (by simpa only [h.index_eq_card] using hN)
  have hm := (isLocalComplement_top_iff.mpr h).map
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  have hc : N.IsComplement' (D.map (MulAut.conj g).toMonoidHom) := by
    apply isLocalComplement_top_iff.mp
    have hn : N.map (MulAut.conj g).toMonoidHom = N := Normal.map_conj_eq N g
    have ht := map_top_of_surjective (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective
    simpa only [hn, ht] using hm
  exact ⟨_, hc, hg⟩

end Subgroup.IsComplement'
