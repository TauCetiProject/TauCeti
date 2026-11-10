/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.CrossedProjection
public import TauCeti.GroupTheory.Transfer.Crossed

/-!
# Gaschütz's splitting theorem

Let `N` be an abelian normal subgroup of a group `G` and `H` a subgroup containing `N` whose
index is prime to `|N|`. **Gaschütz's theorem** says that if `N` has a complement in `H`, then it
has a complement in `G`. Unlike the Schur–Zassenhaus theorem
(`Subgroup.exists_right_complement'_of_coprime`), no coprimality of `|N|` and `[G : N]` is
assumed, so the theorem detects complements of `N` from a subgroup such as a Sylow subgroup.

The proof follows Gaschütz. The projection along the local complement is a crossed map on `H`
which is the identity on `N`. Its crossed transfer to `G`, raised to an inverse of `[G : H]`
modulo `|N|`, is a crossed map on `G` which is still the identity on `N`
(`TauCeti.exists_isMulCocycle₁_eq_of_coprime_index`), and the zero locus of such a map is a
complement of `N` (`Subgroup.exists_complement_iff_crossedProjection`).

The theorem fails for non-abelian `N`: in the central product of `SL(2, 3)` and a cyclic group
of order `4`, the quaternion group `Q₈` has a complement in a Sylow `2`-subgroup, of index `3`,
but none in the whole group (Sambale, Section 1).

This file is unrelated to `TauCeti.GroupTheory.Gaschutz`, which lifts generating sets along
surjections of finite groups.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107, Satz 1.
* B. Sambale, *On the converse of Gaschütz' complement theorem*, arXiv:2303.00254, Theorem 1.
-/

public section

open scoped IsMulCommutative

namespace Subgroup

variable {G : Type*} [Group G] {N K H : Subgroup G} [N.Normal] [IsMulCommutative N]

attribute [local instance] conjugationAction

/-- **Gaschütz's splitting theorem.** Let `N` be an abelian normal subgroup of `G` with a local
complement `K` in a subgroup `H`, and let `[G : H]` be prime to `|N|`. Then `N` has a complement
in `G`.

No finiteness of `G` is assumed. With the conventions of `Subgroup.index` and `Nat.card`, the
coprimality forces `N = ⊥` when `[G : H]` is infinite, and `H = ⊤` when `N` is infinite. -/
theorem IsLocalComplement.exists_isComplement'_of_coprime_index (h : N.IsLocalComplement K H)
    (hcop : Nat.Coprime H.index (Nat.card N)) : ∃ D : Subgroup G, N.IsComplement' D := by
  rcases eq_or_ne H.index 0 with hH | hH
  · rw [hH, Nat.coprime_zero_left, card_eq_one] at hcop
    subst hcop
    exact ⟨⊤, isComplement'_bot_top⟩
  have : H.FiniteIndex := ⟨hH⟩
  -- On `N` the left projection is the identity, hence equivariant for conjugation by `G`.
  have hequiv (g : G) (x y : H) (hx : (x : G) ∈ N) (hy : (y : G) = g * x * g⁻¹) :
      g • h.leftProjection x = h.leftProjection y := by
    obtain ⟨x, hxH⟩ := x
    obtain ⟨y, hyH⟩ := y
    dsimp only at hx hy
    subst hy
    have hx' : h.leftProjection ⟨x, hxH⟩ = ⟨x, hx⟩ := h.leftProjection_left ⟨x, hx⟩
    have hy' : h.leftProjection ⟨_, hyH⟩ = ⟨_, ‹N.Normal›.conj_mem x hx g⟩ :=
      h.leftProjection_left ⟨_, ‹N.Normal›.conj_mem x hx g⟩
    rw [hx', hy']
    exact Subtype.ext (coe_conjugationAction_smul N g _)
  obtain ⟨d, hd, hdN⟩ := TauCeti.exists_isMulCocycle₁_eq_of_coprime_index hcop h.left_le
    h.isMulCocycle₁_leftProjection hequiv
  refine N.exists_complement_iff_crossedProjection.mpr ⟨d, hd, fun n => ?_⟩
  rw [hdN n n.property]
  exact h.leftProjection_left n

end Subgroup
