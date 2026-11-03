/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Uniqueness
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.OpenSubgroup

/-!
# Open subgroups of Demushkin groups, up to isomorphism

An open subgroup `U` of an infinite Demushkin group `G` is again a Demushkin group, of rank
`n(U) = 2 + [G : U] (n(G) - 2)` and with canonical character the restriction `χ|_U` of the
canonical character `χ` of `G`, so that `Im(χ|_U) = χ(U)`
(`TauCeti/Topology/Algebra/Group/Profinite/Demushkin/OpenSubgroup.lean`). Since a Demushkin group
is determined up to topological isomorphism by its rank and the image of its canonical character
(`TauCeti.IsDemushkin.nonempty_continuousMulEquiv_iff`), these two invariants identify `U` up to
isomorphism: the isomorphism type of `U` depends only on `n(G)`, the index `[G : U]` and the
subgroup `χ(U)` of `ℤ_pˣ`. This is the classification content of Serre's open-subgroup theorem
(Serre's exposé, §9.2), read through Labute's classification.

In rank two the rank formula gives `n(U) = 2` for every `U`, so an open subgroup is isomorphic to
`G` exactly when `χ(U) = χ(G)`; this happens for proper subgroups, for instance every open subgroup
of `ℤ_p × ℤ_p`, where `χ` is trivial, is isomorphic to `ℤ_p × ℤ_p`. In rank at least three, the rank
strictly grows on passing to a proper open subgroup, so `G` is isomorphic to none of its proper open
subgroups.

## Main results

* `TauCeti.IsDemushkin.nonempty_continuousMulEquiv_openSubgroup_iff`: an open subgroup `U` of an
  infinite Demushkin group `G` is topologically isomorphic to a Demushkin group `H` if and only if
  `n(H) = 2 + [G : U] (n(G) - 2)` and `Im χ_H = χ_G(U)`.
* `TauCeti.IsDemushkin.nonempty_continuousMulEquiv_openSubgroup_openSubgroup_iff`: open subgroups
  `U ≤ G` and `V ≤ H` of infinite Demushkin groups are topologically isomorphic if and only if
  `[G : U] (n(G) - 2) = [H : V] (n(H) - 2)` and `χ_G(U) = χ_H(V)`.
* `TauCeti.IsDemushkin.nonempty_continuousMulEquiv_openSubgroup_self_iff`: an open subgroup `U` of
  an infinite Demushkin group `G` is topologically isomorphic to `G` if and only if `U = G`, or
  `n(G) = 2` and `χ(U) = χ(G)`.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.2.
* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132.
-/

public section

namespace TauCeti

namespace IsDemushkin

universe u v

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Infinite G]
  (hG : IsDemushkin p G) (U : OpenSubgroup G)
  {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TotallyDisconnectedSpace H]

include hG

/-- **The isomorphism type of an open subgroup of a Demushkin group**: an open subgroup `U` of an
infinite Demushkin group `G` is topologically isomorphic to a Demushkin group `H` if and only if
`H` has rank `2 + [G : U] (n(G) - 2)` and the canonical character of `H` has image `χ(U)`, where
`χ` is the canonical character of `G`. -/
theorem nonempty_continuousMulEquiv_openSubgroup_iff (hH : IsDemushkin p H) :
    Nonempty (U.toSubgroup ≃ₜ* H) ↔
      demushkinRank hH = 2 + U.toSubgroup.index * (demushkinRank hG - 2) ∧
        (demushkinCharacter hH).toMonoidHom.range =
          U.toSubgroup.map (demushkinCharacter hG).toMonoidHom := by
  rw [(hG.openSubgroup U).nonempty_continuousMulEquiv_iff hH, hG.demushkinRank_openSubgroup U,
    hG.range_demushkinCharacter_openSubgroup U]
  exact and_congr eq_comm eq_comm

/-- **Open subgroups of Demushkin groups up to isomorphism**: open subgroups `U ≤ G` and `V ≤ H`
of infinite Demushkin groups are topologically isomorphic if and only if
`[G : U] (n(G) - 2) = [H : V] (n(H) - 2)` and `χ_G(U) = χ_H(V)`, where `χ_G` and `χ_H` are the
canonical characters. In particular two open subgroups of `G` of the same index with the same
image under `χ_G` are isomorphic. The subtractions are not truncated, since an infinite Demushkin
group has rank at least `2`. -/
theorem nonempty_continuousMulEquiv_openSubgroup_openSubgroup_iff [Infinite H]
    (hH : IsDemushkin p H) (V : OpenSubgroup H) :
    Nonempty (U.toSubgroup ≃ₜ* V.toSubgroup) ↔
      U.toSubgroup.index * (demushkinRank hG - 2) = V.toSubgroup.index * (demushkinRank hH - 2) ∧
        U.toSubgroup.map (demushkinCharacter hG).toMonoidHom =
          V.toSubgroup.map (demushkinCharacter hH).toMonoidHom := by
  rw [hG.nonempty_continuousMulEquiv_openSubgroup_iff U (hH.openSubgroup V),
    hH.demushkinRank_openSubgroup V, hH.range_demushkinCharacter_openSubgroup V,
    Nat.add_left_cancel_iff]
  exact and_congr eq_comm eq_comm

/-- **When an open subgroup of a Demushkin group is isomorphic to the group**: an open subgroup
`U` of an infinite Demushkin group `G` is topologically isomorphic to `G` if and only if `U = G`,
or `G` has rank `2` and `χ(U) = χ(G)` for the canonical character `χ` of `G`. In particular an
infinite Demushkin group of rank at least `3` is isomorphic to none of its proper open
subgroups. -/
theorem nonempty_continuousMulEquiv_openSubgroup_self_iff :
    Nonempty (U.toSubgroup ≃ₜ* G) ↔
      U = ⊤ ∨ demushkinRank hG = 2 ∧
        U.toSubgroup.map (demushkinCharacter hG).toMonoidHom =
          (demushkinCharacter hG).toMonoidHom.range := by
  rw [hG.nonempty_continuousMulEquiv_openSubgroup_iff U hG]
  have h2 := hG.two_le_demushkinRank_of_infinite
  constructor
  · rintro ⟨hn, hr⟩
    -- `n(G) - 2 = [G : U] (n(G) - 2)`, so `[G : U] = 1` or `n(G) = 2`
    have hm : (U.toSubgroup.index - 1) * (demushkinRank hG - 2) = 0 := by
      rw [Nat.sub_one_mul]
      omega
    rcases mul_eq_zero.1 hm with hi | hm
    · have hU : U.toSubgroup.index = 1 := by
        have := U.toSubgroup.index_ne_zero_of_finite
        omega
      exact Or.inl (OpenSubgroup.toSubgroup_injective (Subgroup.index_eq_one.1 hU))
    · exact Or.inr ⟨by omega, hr.symm⟩
  · rintro (rfl | ⟨hn, hr⟩)
    · simp only [OpenSubgroup.toSubgroup_top, Subgroup.index_top, one_mul,
        ← MonoidHom.range_eq_map, and_true]
      omega
    · exact ⟨by simp [hn], hr.symm⟩

end IsDemushkin

end TauCeti
