/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Discrimination
public import TauCeti.GroupTheory.LimitGroup.MRDiagram.Centralizer

/-!
# Makanin–Razborov diagrams with limit vertex groups

In the canonical diagrams of the homomorphisms from a finitely generated group to a free group
`F`, the group at every vertex other than the root is a limit group: a finitely generated fully
residually free group. In the version with coefficients the vertex groups receive `F`, and fully
residually free means discriminated by `F` through homomorphisms fixing the coefficients.

This file states the condition for a diagram over an arbitrary group `A` of coefficients and an
arbitrary target `L` receiving `A`. Finite generation is that of the vertex group itself, not
finite generation over the coefficients. A group which is finitely generated and discriminated by
`A` over `A` retracts onto `A`, so with target `A` over a group of coefficients which is not
finitely generated no diagram has limit groups.

## Main definitions

* `TauCeti.LimitGroup.MRDiagram.HasLimitGroups`: every vertex group is finitely generated and
  discriminated by the target through homomorphisms fixing the coefficients.
* `TauCeti.LimitGroup.MRDiagram.HasLimitQuotients`: this holds at every vertex other than the
  root, of whose group nothing is asked.

## Main results

* `TauCeti.LimitGroup.MRDiagram.hasLimitGroups_iff`: a diagram has limit groups exactly when its
  root group is finitely generated and discriminated by the target and the diagram has limit
  quotients.
* `TauCeti.LimitGroup.MRDiagram.hasLimitGroups_centralizerOfModular_iff`: the three-vertex
  diagram of the extension `G(u, ℤ)` of the centralizer of `u` has limit groups exactly when `G`
  is finitely generated and the target discriminates `G(u, ℤ)` over `G`, whatever its modular
  group.
* `TauCeti.LimitGroup.MRDiagram.hasLimitGroups_centralizer_of_ne_one`: with target `G`, the
  twist diagram of `G(u, ℤ)` has limit groups for every `u ≠ 1` over a finitely generated CSA
  group with the big powers property, such as a free group of finite rank.

## References

* O. Kharlampovich, A. Myasnikov, *Effective JSJ decompositions*, in: Groups, Languages,
  Algorithms, Contemp. Math. 378 (2005), §11.1 (canonical hom-diagrams, condition 1).
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5 (extensions of centralizers are discriminated by the base group).
-/

public section

namespace TauCeti.LimitGroup

open GroupAlgGeom

universe u v w

namespace MRDiagram

variable {A : Type v} [Group A] {H : Type u} [Group H] {ι : A →* H}
  {L : Type w} [Group L] (ιL : A →* L)

/-! ### Limit vertex groups -/

/-- Every vertex group of the diagram is finitely generated and discriminated by the target
through homomorphisms fixing the coefficients. -/
def HasLimitGroups : ∀ {H : Type u} [Group H] {ι : A →* H}, MRDiagram ι → Prop
  | H, _, ι, leaf _ => Group.FG H ∧ IsDiscriminatedBy ι ιL
  | H, _, ι, node _ _ _ child =>
    Group.FG H ∧ IsDiscriminatedBy ι ιL ∧ ∀ i, HasLimitGroups (child i)

/-- Every vertex group below the root is finitely generated and discriminated by the target
through homomorphisms fixing the coefficients; nothing is asked of the root group. -/
def HasLimitQuotients : MRDiagram ι → Prop
  | leaf _ => True
  | node _ _ _ child => ∀ i, (child i).HasLimitGroups ιL

variable {ιL}

@[simp]
theorem hasLimitGroups_leaf {free : IsFreeGGroup ι} :
    (leaf free).HasLimitGroups ιL ↔ Group.FG H ∧ IsDiscriminatedBy ι ιL :=
  Iff.rfl

@[simp]
theorem hasLimitGroups_node {M : Subgroup (MulAut H)}
    {hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)} {n : ℕ} {K : Fin n → Type u}
    [∀ i, Group (K i)] {κ : ∀ i, A →* K i} {π : ∀ i, GHom ι (κ i)}
    {child : ∀ i, MRDiagram (κ i)} :
    (node M hM π child).HasLimitGroups ιL ↔
      Group.FG H ∧ IsDiscriminatedBy ι ιL ∧ ∀ i, (child i).HasLimitGroups ιL :=
  Iff.rfl

@[simp]
theorem hasLimitQuotients_leaf (free : IsFreeGGroup ι) : (leaf free).HasLimitQuotients ιL :=
  trivial

@[simp]
theorem hasLimitQuotients_node {M : Subgroup (MulAut H)}
    {hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)} {n : ℕ} {K : Fin n → Type u}
    [∀ i, Group (K i)] {κ : ∀ i, A →* K i} {π : ∀ i, GHom ι (κ i)}
    {child : ∀ i, MRDiagram (κ i)} :
    (node M hM π child).HasLimitQuotients ιL ↔ ∀ i, (child i).HasLimitGroups ιL :=
  Iff.rfl

/-- All vertex groups of a diagram are limit groups exactly when its root group is one and its
vertex groups below the root are. -/
theorem hasLimitGroups_iff {D : MRDiagram ι} :
    D.HasLimitGroups ιL ↔ Group.FG H ∧ IsDiscriminatedBy ι ιL ∧ D.HasLimitQuotients ιL := by
  cases D with
  | leaf _ => simp
  | node M hM π child => exact hasLimitGroups_node

/-- If all vertex groups of a diagram are limit groups, then so are those below the root. -/
theorem HasLimitGroups.hasLimitQuotients {D : MRDiagram ι} (h : D.HasLimitGroups ιL) :
    D.HasLimitQuotients ιL :=
  (hasLimitGroups_iff.1 h).2.2

/-! ### Diagrams with one edge at the root, and the diagram without branches -/

section edge

variable {K : Type u} [Group K] {κ : A →* K} {M : Subgroup (MulAut H)}
  {hM : M ≤ fixingSubgroup (MulAut H) (Set.range ι)} {π : GHom ι κ} {D : MRDiagram κ}

@[simp]
theorem hasLimitGroups_edge :
    (edge M hM π D).HasLimitGroups ιL ↔
      Group.FG H ∧ IsDiscriminatedBy ι ιL ∧ D.HasLimitGroups ιL := by
  simp [edge_def]

@[simp]
theorem hasLimitQuotients_edge : (edge M hM π D).HasLimitQuotients ιL ↔ D.HasLimitGroups ιL := by
  simp [edge_def]

end edge

/-- The diagram without branches has limit quotients: it has no vertex below its root. -/
@[simp]
theorem hasLimitQuotients_empty : (MRDiagram.empty ι).HasLimitQuotients ιL := by
  simp [empty_def]

/-- The diagram without branches has limit groups exactly when its root group is finitely
generated and discriminated by the target. -/
@[simp]
theorem hasLimitGroups_empty :
    (MRDiagram.empty ι).HasLimitGroups ιL ↔ Group.FG H ∧ IsDiscriminatedBy ι ιL := by
  simp [hasLimitGroups_iff]

/-- The one-edge diagram of a free `A`-group has limit quotients exactly when its root group is
finitely generated and discriminated by the target: the vertex below the root carries the root
group again. -/
@[simp]
theorem hasLimitQuotients_freeRoot {free : IsFreeGGroup ι} :
    (freeRoot free).HasLimitQuotients ιL ↔ Group.FG H ∧ IsDiscriminatedBy ι ιL := by
  rw [freeRoot_def, hasLimitQuotients_edge, hasLimitGroups_leaf]

/-! ### The twist diagram of an extension of a centralizer -/

section centralizer

open CentralizerExt

variable {G : Type u} [Group G] {u : G} {ιG : G →* L}

/-- The three-vertex diagram of the extension `G(u, ℤ)` of a centralizer has limit groups exactly
when `G` is finitely generated and the target discriminates `G(u, ℤ)` over `G`: its vertex groups
are `G(u, ℤ)`, twice, and `G`. -/
@[simp]
theorem hasLimitGroups_centralizerOfModular_iff {M : Subgroup (MulAut (CentralizerExt u 1))}
    {hM : M ≤ fixingSubgroup (MulAut (CentralizerExt u 1))
      (Set.range (of : G →* CentralizerExt u 1))} :
    (centralizerOfModular u M hM).HasLimitGroups ιG ↔
      Group.FG G ∧ IsDiscriminatedBy (of : G →* CentralizerExt u 1) ιG := by
  rw [centralizerOfModular_def, hasLimitGroups_edge, hasLimitGroups_edge, hasLimitGroups_leaf]
  constructor
  · rintro ⟨-, h, -, -, hG, -⟩
    exact ⟨hG, h⟩
  · rintro ⟨hG, h⟩
    exact ⟨inferInstance, h, inferInstance, h, hG, h.of_injective ⟨of, fun _ => rfl⟩ of_injective⟩

/-- The twist diagram of `G(u, ℤ)`, whose modular group is generated by the Dehn twist, has limit
groups exactly when `G` is finitely generated and the target discriminates `G(u, ℤ)` over `G`. -/
@[simp]
theorem hasLimitGroups_centralizer_iff :
    (centralizer u).HasLimitGroups ιG ↔
      Group.FG G ∧ IsDiscriminatedBy (of : G →* CentralizerExt u 1) ιG := by
  rw [centralizer_def, hasLimitGroups_centralizerOfModular_iff]

/-- Over a finitely generated CSA group `G` with the big powers property, such as a free group of
finite rank, the vertex groups of the twist diagram of `G(u, ℤ)` are finitely generated and
discriminated by `G` over `G`, for every `u ≠ 1`. -/
theorem hasLimitGroups_centralizer_of_ne_one [Group.FG G] (hBP : Group.IsBP G)
    (hCSA : Group.IsCSA G) (hu : u ≠ 1) : (centralizer u).HasLimitGroups (.id G) :=
  hasLimitGroups_centralizer_iff.2 ⟨‹_›, CentralizerExt.isDiscriminatedBy hBP hCSA hu⟩

end centralizer

end MRDiagram

end TauCeti.LimitGroup
