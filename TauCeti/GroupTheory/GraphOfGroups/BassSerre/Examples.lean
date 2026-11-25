/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Star
public import TauCeti.GroupTheory.GraphOfGroups.Cyclic
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Index

/-!
# Concrete Bass–Serre trees

Calculations of vertex degrees, star and adjacent-vertex cardinalities, and quotients of
`GraphOfGroups.bassSerreTree` on concrete graphs of groups:

* **Baumslag–Solitar groups (`baumslagSolitar`)**: every vertex of
  `bassSerreTree (baumslagSolitar m n hm hn) default` has degree `|m| + |n|` (`3` for `BS(1, 2)`).
* **Free product `ℤ ∗ ℤ` (`freeProductInt`)**: outgoing stars and adjacent-vertex sets have
  cardinality `ℵ₀` at every vertex.
* **Disconnected graphs (`SerreGraph.noEdge Bool`)**: `X(𝔸, false)` and its `π₁`-quotient each have
  `1` vertex while the ambient graph has `2`, witnessing recovery of `Γ.component a`.

## Main definitions

* `TauCeti.GraphOfGroups.freeProductInt`: the segment of groups for `ℤ ∗ ℤ`.

## Main results

* `TauCeti.GraphOfGroups.card_src_eq_bassSerreTree_baumslagSolitar`,
  `TauCeti.GraphOfGroups.card_src_eq_bassSerreTree_baumslagSolitar_one_two`: vertex degrees in
  Baumslag–Solitar Bass–Serre trees.
* `TauCeti.GraphOfGroups.mk_star_freeProductInt`,
  `TauCeti.GraphOfGroups.mk_adjacent_freeProductInt`: star and adjacent-vertex cardinalities in
  `ℤ ∗ ℤ`.
* `TauCeti.GraphOfGroups.card_bassSerreTree_noEdge_bool_V`,
  `TauCeti.GraphOfGroups.card_quotient_bassSerreTree_noEdge_bool_V`,
  `TauCeti.GraphOfGroups.isEmpty_quotient_bassSerreTree_iso_noEdge_bool`: disconnected example.

## References

* J.-P. Serre, *Trees*, Chapter I, §4.1 and §5.3.
-/

public section

namespace TauCeti.GraphOfGroups

/-! ### Baumslag–Solitar groups -/

section BaumslagSolitar

/-- Every vertex of the Bass–Serre tree of the Baumslag–Solitar group `BS(m, n)` has degree
`|m| + |n|`. -/
theorem card_src_eq_bassSerreTree_baumslagSolitar (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (x : (bassSerreTree (baumslagSolitar m n hm hn) default).V) :
    Nat.card {d : (bassSerreTree (baumslagSolitar m n hm hn) default).E //
        (bassSerreTree (baumslagSolitar m n hm hn) default).src d = x} =
      m.natAbs + n.natAbs := by
  have : Finite (Multiplicative ℤ ⧸ (zpowGroupHom (α := Multiplicative ℤ) m).range) :=
    Subgroup.index_ne_zero_iff_finite.1 (by simp [hm])
  have : Finite (Multiplicative ℤ ⧸ (zpowGroupHom (α := Multiplicative ℤ) n).range) :=
    Subgroup.index_ne_zero_iff_finite.1 (by simp [hn])
  exact (card_src_eq_bassSerreTree_loop
    (zpowGroupHom (α := Multiplicative ℤ) m) (zpowGroupHom (α := Multiplicative ℤ) n)
    (zpow_left_injective hm) (zpow_left_injective hn) x).trans (by simp)

/-- Every vertex of the Bass–Serre tree of `BS(1, 2)` has degree `3`. -/
theorem card_src_eq_bassSerreTree_baumslagSolitar_one_two
    (x : (bassSerreTree (baumslagSolitar 1 2 one_ne_zero (by decide)) default).V) :
    Nat.card {d : (bassSerreTree (baumslagSolitar 1 2 one_ne_zero (by decide)) default).E //
        (bassSerreTree (baumslagSolitar 1 2 one_ne_zero (by decide)) default).src d = x} = 3 :=
  card_src_eq_bassSerreTree_baumslagSolitar 1 2 one_ne_zero (by decide) x

end BaumslagSolitar

/-! ### Free product `ℤ ∗ ℤ` -/

section FreeProductInt

/-- The segment of groups for the free product `ℤ ∗ ℤ`, amalgamating two copies of
`Multiplicative ℤ` over the trivial group `PUnit`. -/
abbrev freeProductInt : GraphOfGroups.{0, 0, 0, 0} SerreGraph.segment :=
  segment (1 : PUnit →* Multiplicative ℤ) (1 : PUnit →* Multiplicative ℤ)
    (Function.injective_of_subsingleton _) (Function.injective_of_subsingleton _)

/-- In the Bass–Serre tree of `ℤ ∗ ℤ`, the outgoing star of every vertex has cardinality `ℵ₀`. -/
theorem mk_star_freeProductInt (v₀ : SerreGraph.segment.V)
    (x : (bassSerreTree freeProductInt v₀).V) :
    Cardinal.mk {d : (bassSerreTree freeProductInt v₀).E //
        (bassSerreTree freeProductInt v₀).src d = x} = Cardinal.aleph0 := by
  induction x using bassSerreVertex_induction_on with | @h v p
  rw [← Cardinal.mk_int]
  cases v
  · exact Cardinal.mk_congr ((segmentFreeStarEquivFalse (1 : PUnit →* Multiplicative ℤ)
      (1 : PUnit →* Multiplicative ℤ) _ _ p).symm.trans Multiplicative.toAdd)
  · exact Cardinal.mk_congr ((segmentFreeStarEquivTrue (1 : PUnit →* Multiplicative ℤ)
      (1 : PUnit →* Multiplicative ℤ) _ _ p).symm.trans Multiplicative.toAdd)

/-- In the Bass–Serre tree of `ℤ ∗ ℤ`, the set of adjacent vertices of every vertex has cardinality
`ℵ₀`. -/
theorem mk_adjacent_freeProductInt (v₀ : SerreGraph.segment.V)
    (x : (bassSerreTree freeProductInt v₀).V) :
    Cardinal.mk {y : (bassSerreTree freeProductInt v₀).V // Nonempty (x ⟶ y)} =
      Cardinal.aleph0 :=
  (Cardinal.mk_congr
    ((bassSerreTree freeProductInt v₀).isAcyclic.starEquivAdjacent x).symm).trans
    (mk_star_freeProductInt v₀ x)

end FreeProductInt

/-! ### Disconnected underlying graph: two isolated vertices -/

section Disconnected

/-- On `SerreGraph.noEdge Bool`, the Bass–Serre tree at `false` has `1` vertex. -/
theorem card_bassSerreTree_noEdge_bool_V :
    Nat.card (bassSerreTree (trivial (SerreGraph.noEdge.{0, 0} Bool)) false).V = 1 :=
  Nat.card_unique

/-- On `SerreGraph.noEdge Bool`, the `π₁`-quotient of the Bass–Serre tree at `false` has `1`
vertex. -/
theorem card_quotient_bassSerreTree_noEdge_bool_V :
    Nat.card (bassSerreTree (trivial (SerreGraph.noEdge.{0, 0} Bool)) false).quotient.V = 1 :=
  Nat.card_unique

/-- On the disconnected graph `SerreGraph.noEdge Bool`, the quotient of the Bass–Serre tree by `π₁`
is not isomorphic to `SerreGraph.noEdge Bool`: it recovers only the connected component of the base
vertex. -/
theorem isEmpty_quotient_bassSerreTree_iso_noEdge_bool :
    IsEmpty ((bassSerreTree (trivial (SerreGraph.noEdge.{0, 0} Bool)) false).quotient.Iso
      (SerreGraph.noEdge.{0, 0} Bool)) :=
  ⟨fun φ ↦ by
    have h := Nat.card_congr φ.equivV
    rw [card_quotient_bassSerreTree_noEdge_bool_V] at h
    have h2 : Nat.card (SerreGraph.noEdge.{0, 0} Bool).V = 2 := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.card_bool
    omega⟩

end Disconnected

end TauCeti.GraphOfGroups
