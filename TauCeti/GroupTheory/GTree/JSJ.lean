/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Line

/-!
# Universally elliptic trees and JSJ trees

Fix a group `G`, a family `𝒜` of subgroups (the allowed edge stabilizers) and a family `ℋ` of
subgroups (required to be elliptic). An `(𝒜, ℋ)`-tree is a minimal `G`-tree relative to `𝒜` and
`ℋ`: `T.IsMinimal` and `T.IsRelative 𝒜 ℋ`. Following Guirardel and Levitt:

* a subgroup is *universally elliptic* when it is elliptic in every `(𝒜, ℋ)`-tree, and a tree is
  universally elliptic when its dart stabilizers are;
* a *JSJ tree* is a universally elliptic `(𝒜, ℋ)`-tree dominating every universally elliptic
  `(𝒜, ℋ)`-tree;
* a vertex is *rigid* when its stabilizer is universally elliptic and *flexible* otherwise.

JSJ trees are not unique, but any two of them dominate each other: by
`GTree.IsJSJ.isJSJ_iff_sameDeformationSpace`, the JSJ trees are exactly the universally elliptic
`(𝒜, ℋ)`-trees in the deformation space of any one of them, the *JSJ deformation space*, and by
`GTree.IsJSJ.isEllipticSubgroup_iff` they all have the same elliptic subgroups.

An `(𝒜, ℋ)`-tree all of whose vertices are rigid is a JSJ tree
(`GTree.IsJSJ.of_forall_isRigidVertex`), and its elliptic subgroups are exactly the universally
elliptic subgroups. In particular an `(𝒜, ℋ)`-tree with trivial vertex stabilizers is a JSJ tree
(`GTree.IsJSJ.of_forall_stabilizer_eq_bot`); when there is one, the trivial subgroup is the only
universally elliptic subgroup and the JSJ trees are exactly the minimal trees with trivial vertex
stabilizers, which are then automatically `(𝒜, ℋ)`-trees, so for a nontrivial group no tree with
one vertex is a JSJ tree. For
instance, when `𝒜` contains the trivial subgroup and every member of `ℋ` is trivial, a minimal
free action of a free group on a tree is a JSJ tree. For the infinite cyclic group, under the
same two hypotheses on `𝒜` and `ℋ`, the line is a JSJ tree and the one-vertex tree is not, and
its vertex is flexible (all in `GTree.{0, 0}`).

A tree with one vertex is a JSJ tree exactly when `G` fixes a vertex of every universally
elliptic `(𝒜, ℋ)`-tree, and its vertex is rigid exactly when `G` is universally elliptic. When a
tree with one vertex is a JSJ tree, the JSJ trees are exactly the trees with one vertex; this is
the case for the trivial group, whatever `𝒜` and `ℋ`.

## Rigid vertices

The terminology is that of Guirardel and Levitt: rigidity is universal ellipticity of the vertex
stabilizer. Kharlampovich and Myasnikov instead call a vertex group of a JSJ decomposition rigid
when it is neither quadratically hanging nor abelian; the two notions are different in general.

## Universes

Universal ellipticity quantifies over all `(𝒜, ℋ)`-trees, so the universes `u` and `v` of the
vertex and dart types of those trees have to be fixed: they are universe parameters of
`GTree.IsUniversallyEllipticSubgroup`, and `GTree.IsUniversallyElliptic`, `GTree.IsRigidVertex` and
`GTree.IsJSJ` test a tree in `GTree.{u, v} G` against the trees of the same universes. No
comparison between different choices of `u` and `v` is proved here. Mathematically, a minimal
`G`-tree is the convex hull of the orbit of any of its vertices, so it has at most
`max (#G) ℵ₀` vertices and darts, and the notions are expected not to depend on `u` and `v` once
both are at least the universe of `G`; taking both equal to that universe is the canonical choice.

## Main declarations

* `TauCeti.GTree.IsUniversallyEllipticSubgroup`, `TauCeti.GTree.IsUniversallyElliptic`:
  universally elliptic subgroups and trees.
* `TauCeti.GTree.IsRigidVertex`, `TauCeti.GTree.IsFlexibleVertex`: rigid and flexible vertices.
* `TauCeti.GTree.IsJSJ`: JSJ trees.
* `TauCeti.GTree.IsJSJ.sameDeformationSpace`, `TauCeti.GTree.IsJSJ.isJSJ_iff_sameDeformationSpace`,
  `TauCeti.GTree.IsJSJ.isJSJ_iff_forall_isEllipticSubgroup`: the JSJ trees form one deformation
  space of universally elliptic trees.
* `TauCeti.GTree.IsJSJ.of_forall_isRigidVertex`, `TauCeti.GTree.IsJSJ.of_forall_stabilizer_eq_bot`:
  minimal relative trees with universally elliptic, in particular trivial, vertex stabilizers are
  JSJ trees.
* `TauCeti.GTree.isUniversallyEllipticSubgroup_iff_isEllipticSubgroup`,
  `TauCeti.GTree.isUniversallyEllipticSubgroup_iff_eq_bot`,
  `TauCeti.GTree.IsJSJ.isJSJ_iff_forall_stabilizer_eq_bot`: the universally elliptic subgroups and
  the JSJ trees in the presence of a minimal relative tree with rigid, or trivial, vertex
  stabilizers.
* `TauCeti.GTree.isJSJ_iff_of_subsingleton`, `TauCeti.GTree.IsJSJ.isJSJ_iff_subsingleton`: trees
  with one vertex as JSJ trees.
* `TauCeti.GTree.isJSJ_iff_subsingleton`: the JSJ trees of the trivial group.
* `TauCeti.GTree.line_isJSJ`, `TauCeti.GTree.not_point_isJSJ_int`: over a family containing the
  trivial subgroup, relative to a family of trivial subgroups, the line is a JSJ tree of the
  infinite cyclic group and the one-vertex tree is not.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017),
  Introduction, §2.2 Definition 2.7, §2.3 Definitions 2.12 and 2.14, §3 Lemma 3.1 and §3.1.
* O. Kharlampovich and A. Myasnikov, *Effective JSJ decompositions*, Contemp. Math. 378 (2005),
  §2, for the other use of the word rigid.
-/

public section

universe u v w

namespace TauCeti

namespace GTree

open _root_.MulAction

variable {G : Type w} [Group G] {𝒜 𝒜' ℋ ℋ' : Set (Subgroup G)} {H K : Subgroup G}

/-! ### Universally elliptic subgroups -/

/-- A subgroup is universally elliptic, over `𝒜` relative to `ℋ`, when it is elliptic in every
minimal `G`-tree relative to `𝒜` and `ℋ`. The trees range over `GTree.{u, v} G`. -/
def IsUniversallyEllipticSubgroup (𝒜 ℋ : Set (Subgroup G)) (H : Subgroup G) : Prop :=
  ∀ T : GTree.{u, v} G, T.IsMinimal → T.IsRelative 𝒜 ℋ → T.IsEllipticSubgroup H

theorem isUniversallyEllipticSubgroup_iff :
    IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ H ↔
      ∀ T : GTree.{u, v} G, T.IsMinimal → T.IsRelative 𝒜 ℋ → T.IsEllipticSubgroup H := Iff.rfl

/-- A universally elliptic subgroup is elliptic in every minimal relative tree. -/
theorem IsUniversallyEllipticSubgroup.isEllipticSubgroup
    (hH : IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ H) {T : GTree.{u, v} G} (hm : T.IsMinimal)
    (hr : T.IsRelative 𝒜 ℋ) : T.IsEllipticSubgroup H :=
  hH T hm hr

/-- Subgroups of universally elliptic subgroups are universally elliptic. -/
theorem IsUniversallyEllipticSubgroup.mono (hH : IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ H)
    (hKH : K ≤ H) : IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ K :=
  fun T hm hr => (hH T hm hr).mono hKH

/-- Universal ellipticity is antitone in the family of edge stabilizers and monotone in the family
of subgroups required to be elliptic: fewer trees have to be tested. -/
theorem IsUniversallyEllipticSubgroup.of_subset
    (hH : IsUniversallyEllipticSubgroup.{u, v} 𝒜' ℋ' H) (h𝒜 : 𝒜 ⊆ 𝒜') (hℋ : ℋ' ⊆ ℋ) :
    IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ H :=
  fun T hm hr => hH T hm (hr.mono h𝒜 hℋ)

variable (𝒜 ℋ) in
/-- The trivial subgroup is universally elliptic. -/
@[simp] theorem isUniversallyEllipticSubgroup_bot :
    IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (⊥ : Subgroup G) :=
  fun T _ _ => T.isEllipticSubgroup_bot

variable (𝒜) in
/-- The subgroups required to be elliptic are universally elliptic. -/
theorem isUniversallyEllipticSubgroup_of_mem (hH : H ∈ ℋ) :
    IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ H :=
  fun _ _ hr => hr.isEllipticSubgroup hH

/-- Conjugates of a universally elliptic subgroup are universally elliptic. -/
theorem IsUniversallyEllipticSubgroup.map_conj
    (hH : IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ H) (g : G) :
    IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (H.map (MulAut.conj g : G →* G)) :=
  fun T hm hr => (hH T hm hr).map_conj g

/-- A subgroup is universally elliptic exactly when its conjugates are. -/
@[simp] theorem isUniversallyEllipticSubgroup_map_conj_iff {g : G} :
    IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (H.map (MulAut.conj g : G →* G)) ↔
      IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ H := by
  simp only [isUniversallyEllipticSubgroup_iff, isEllipticSubgroup_map_conj_iff]

/-! ### Universally elliptic trees -/

section Tree

variable (T : GTree.{u, v} G) {T' : GTree.{u, v} G}

/-- A `G`-tree is universally elliptic, over `𝒜` relative to `ℋ`, when its dart stabilizers are
universally elliptic: they are elliptic in every minimal `G`-tree relative to `𝒜` and `ℋ` whose
vertex and dart types lie in the same universes as those of `T`. -/
def IsUniversallyElliptic (𝒜 ℋ : Set (Subgroup G)) : Prop :=
  ∀ e : T.E, IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (stabilizer G e)

variable {T}

theorem isUniversallyElliptic_iff :
    T.IsUniversallyElliptic 𝒜 ℋ ↔
      ∀ e : T.E, IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (stabilizer G e) := Iff.rfl

/-- The dart stabilizers of a universally elliptic tree are universally elliptic. -/
theorem IsUniversallyElliptic.isUniversallyEllipticSubgroup_stabilizer
    (hT : T.IsUniversallyElliptic 𝒜 ℋ) (e : T.E) :
    IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (stabilizer G e) :=
  hT e

/-- A tree is universally elliptic exactly when it is elliptic with respect to every minimal
relative tree: its dart stabilizers are elliptic in each of them. -/
theorem isUniversallyElliptic_iff_forall_isEllipticSubgroup :
    T.IsUniversallyElliptic 𝒜 ℋ ↔ ∀ T' : GTree.{u, v} G, T'.IsMinimal → T'.IsRelative 𝒜 ℋ →
      ∀ e : T.E, T'.IsEllipticSubgroup (stabilizer G e) :=
  ⟨fun h T' hm hr e => h e T' hm hr, fun h e T' hm hr => h T' hm hr e⟩

/-- The dart stabilizers of a universally elliptic tree are elliptic in every minimal relative
tree. -/
theorem IsUniversallyElliptic.isEllipticSubgroup_stabilizer (hT : T.IsUniversallyElliptic 𝒜 ℋ)
    (hm : T'.IsMinimal) (hr : T'.IsRelative 𝒜 ℋ) (e : T.E) :
    T'.IsEllipticSubgroup (stabilizer G e) :=
  hT e T' hm hr

/-- Universal ellipticity of a tree is antitone in the family of edge stabilizers and monotone in
the family of subgroups required to be elliptic. -/
theorem IsUniversallyElliptic.of_subset (hT : T.IsUniversallyElliptic 𝒜' ℋ') (h𝒜 : 𝒜 ⊆ 𝒜')
    (hℋ : ℋ' ⊆ ℋ) : T.IsUniversallyElliptic 𝒜 ℋ :=
  fun e => (hT e).of_subset h𝒜 hℋ

variable (T) in
/-- A `G`-tree with at most one vertex is universally elliptic. -/
theorem isUniversallyElliptic_of_subsingleton [Subsingleton T.V] (𝒜 ℋ : Set (Subgroup G)) :
    T.IsUniversallyElliptic 𝒜 ℋ :=
  fun e => (T.isEmpty_dart_of_subsingleton.false e).elim

/-- A tree relative to `𝒜` and `ℋ` is universally elliptic exactly when it is relative to the
family of universally elliptic members of `𝒜`. -/
theorem IsRelative.isUniversallyElliptic_iff (hr : T.IsRelative 𝒜 ℋ) :
    T.IsUniversallyElliptic 𝒜 ℋ ↔
      T.IsRelative {A ∈ 𝒜 | IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ A} ℋ :=
  ⟨fun h => isRelative_iff.mpr
      ⟨fun e => ⟨hr.stabilizer_mem e, h e⟩, fun _ hH => hr.isEllipticSubgroup hH⟩,
    fun h e => (h.stabilizer_mem e).2⟩

/-! ### Rigid and flexible vertices -/

variable (T) in
/-- A vertex of a `G`-tree is rigid, over `𝒜` relative to `ℋ`, when its stabilizer is universally
elliptic. The notion is meant for the vertices of a JSJ tree. -/
def IsRigidVertex (𝒜 ℋ : Set (Subgroup G)) (x : T.V) : Prop :=
  IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (stabilizer G x)

variable (T) in
/-- A vertex of a `G`-tree is flexible, over `𝒜` relative to `ℋ`, when it is not rigid: its
stabilizer fails to be elliptic in some minimal `G`-tree relative to `𝒜` and `ℋ`. The notion is
meant for the vertices of a JSJ tree. -/
def IsFlexibleVertex (𝒜 ℋ : Set (Subgroup G)) (x : T.V) : Prop :=
  ¬T.IsRigidVertex 𝒜 ℋ x

variable {x : T.V}

theorem isRigidVertex_iff :
    T.IsRigidVertex 𝒜 ℋ x ↔ IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (stabilizer G x) := Iff.rfl

theorem isFlexibleVertex_iff : T.IsFlexibleVertex 𝒜 ℋ x ↔ ¬T.IsRigidVertex 𝒜 ℋ x := Iff.rfl

@[simp] theorem not_isFlexibleVertex_iff : ¬T.IsFlexibleVertex 𝒜 ℋ x ↔ T.IsRigidVertex 𝒜 ℋ x :=
  not_not

/-- A vertex is flexible exactly when its stabilizer is not elliptic in some minimal relative
tree. -/
theorem isFlexibleVertex_iff_exists :
    T.IsFlexibleVertex 𝒜 ℋ x ↔ ∃ T' : GTree.{u, v} G, T'.IsMinimal ∧ T'.IsRelative 𝒜 ℋ ∧
      ¬T'.IsEllipticSubgroup (stabilizer G x) := by
  simp only [isFlexibleVertex_iff, isRigidVertex_iff, isUniversallyEllipticSubgroup_iff,
    not_forall, exists_prop]

/-- The stabilizer of a rigid vertex is universally elliptic. -/
theorem IsRigidVertex.isUniversallyEllipticSubgroup_stabilizer (hx : T.IsRigidVertex 𝒜 ℋ x) :
    IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (stabilizer G x) :=
  hx

/-- The stabilizer of a rigid vertex is elliptic in every minimal relative tree. -/
theorem IsRigidVertex.isEllipticSubgroup_stabilizer (hx : T.IsRigidVertex 𝒜 ℋ x)
    (hm : T'.IsMinimal) (hr : T'.IsRelative 𝒜 ℋ) : T'.IsEllipticSubgroup (stabilizer G x) :=
  hx T' hm hr

/-- Rigidity is antitone in the family of edge stabilizers and monotone in the family of
subgroups required to be elliptic. -/
theorem IsRigidVertex.of_subset (hx : T.IsRigidVertex 𝒜' ℋ' x) (h𝒜 : 𝒜 ⊆ 𝒜') (hℋ : ℋ' ⊆ ℋ) :
    T.IsRigidVertex 𝒜 ℋ x :=
  hx.isUniversallyEllipticSubgroup_stabilizer.of_subset h𝒜 hℋ

/-- Flexibility is monotone in the family of edge stabilizers and antitone in the family of
subgroups required to be elliptic. -/
theorem IsFlexibleVertex.of_subset (hx : T.IsFlexibleVertex 𝒜 ℋ x) (h𝒜 : 𝒜 ⊆ 𝒜')
    (hℋ : ℋ' ⊆ ℋ) : T.IsFlexibleVertex 𝒜' ℋ' x :=
  fun h => hx (h.of_subset h𝒜 hℋ)

/-- Rigidity is constant on orbits of vertices. -/
@[simp] theorem isRigidVertex_smul_iff {g : G} :
    T.IsRigidVertex 𝒜 ℋ (g • x) ↔ T.IsRigidVertex 𝒜 ℋ x := by
  rw [isRigidVertex_iff, stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    isUniversallyEllipticSubgroup_map_conj_iff, isRigidVertex_iff]

/-- Flexibility is constant on orbits of vertices. -/
@[simp] theorem isFlexibleVertex_smul_iff {g : G} :
    T.IsFlexibleVertex 𝒜 ℋ (g • x) ↔ T.IsFlexibleVertex 𝒜 ℋ x :=
  not_congr isRigidVertex_smul_iff

variable (𝒜 ℋ) in
/-- A vertex with trivial stabilizer is rigid. -/
theorem isRigidVertex_of_stabilizer_eq_bot (hx : stabilizer G x = ⊥) : T.IsRigidVertex 𝒜 ℋ x :=
  isRigidVertex_iff.mpr (hx ▸ isUniversallyEllipticSubgroup_bot 𝒜 ℋ)

/-- A tree all of whose vertices are rigid is universally elliptic. -/
theorem isUniversallyElliptic_of_forall_isRigidVertex (h : ∀ x : T.V, T.IsRigidVertex 𝒜 ℋ x) :
    T.IsUniversallyElliptic 𝒜 ℋ :=
  fun e => (h (T.src e)).mono (T.stabilizer_dart_le_stabilizer_src e)

/-- A tree all of whose vertices are rigid dominates every minimal relative tree. -/
theorem dominates_of_forall_isRigidVertex (h : ∀ x : T.V, T.IsRigidVertex 𝒜 ℋ x)
    (hm : T'.IsMinimal) (hr : T'.IsRelative 𝒜 ℋ) : T.Dominates T' :=
  dominates_iff.mpr fun x => (h x).isEllipticSubgroup_stabilizer hm hr

/-! ### JSJ trees -/

variable (T) in
/-- A JSJ tree of `G` over `𝒜` relative to `ℋ`: a minimal `G`-tree relative to `𝒜` and `ℋ` that
is universally elliptic and dominates every universally elliptic minimal `G`-tree relative to `𝒜`
and `ℋ`. The trees it is compared with lie in the same universes as `T`. -/
structure IsJSJ (𝒜 ℋ : Set (Subgroup G)) : Prop where
  /-- A JSJ tree is minimal. -/
  isMinimal : T.IsMinimal
  /-- A JSJ tree has dart stabilizers in `𝒜`, and the members of `ℋ` are elliptic in it. -/
  isRelative : T.IsRelative 𝒜 ℋ
  /-- A JSJ tree is universally elliptic. -/
  isUniversallyElliptic : T.IsUniversallyElliptic 𝒜 ℋ
  /-- A JSJ tree dominates every universally elliptic minimal relative tree. -/
  dominates ⦃T' : GTree.{u, v} G⦄ : T'.IsMinimal → T'.IsRelative 𝒜 ℋ →
    T'.IsUniversallyElliptic 𝒜 ℋ → T.Dominates T'

theorem isJSJ_iff :
    T.IsJSJ 𝒜 ℋ ↔ T.IsMinimal ∧ T.IsRelative 𝒜 ℋ ∧ T.IsUniversallyElliptic 𝒜 ℋ ∧
      ∀ T' : GTree.{u, v} G, T'.IsMinimal → T'.IsRelative 𝒜 ℋ →
        T'.IsUniversallyElliptic 𝒜 ℋ → T.Dominates T' :=
  ⟨fun h => ⟨h.isMinimal, h.isRelative, h.isUniversallyElliptic, h.dominates⟩,
    fun ⟨hm, hr, hu, hd⟩ => ⟨hm, hr, hu, hd⟩⟩

/-- Any two JSJ trees lie in the same deformation space. -/
theorem IsJSJ.sameDeformationSpace (hT : T.IsJSJ 𝒜 ℋ) (hT' : T'.IsJSJ 𝒜 ℋ) :
    T.SameDeformationSpace T' :=
  sameDeformationSpace_iff.mpr
    ⟨hT.dominates hT'.isMinimal hT'.isRelative hT'.isUniversallyElliptic,
      hT'.dominates hT.isMinimal hT.isRelative hT.isUniversallyElliptic⟩

/-- Any two JSJ trees have the same elliptic subgroups. -/
theorem IsJSJ.isEllipticSubgroup_iff (hT : T.IsJSJ 𝒜 ℋ) (hT' : T'.IsJSJ 𝒜 ℋ) :
    T.IsEllipticSubgroup H ↔ T'.IsEllipticSubgroup H :=
  (hT.sameDeformationSpace hT').isEllipticSubgroup_iff

/-- A universally elliptic minimal relative tree dominating a JSJ tree is a JSJ tree. -/
theorem IsJSJ.of_dominates (hT : T.IsJSJ 𝒜 ℋ) (hm : T'.IsMinimal) (hr : T'.IsRelative 𝒜 ℋ)
    (hu : T'.IsUniversallyElliptic 𝒜 ℋ) (h : T'.Dominates T) : T'.IsJSJ 𝒜 ℋ :=
  ⟨hm, hr, hu, fun _ hm'' hr'' hu'' => h.trans (hT.dominates hm'' hr'' hu'')⟩

/-- The JSJ trees are the universally elliptic minimal relative trees in the deformation space of
any one of them. -/
theorem IsJSJ.isJSJ_iff_sameDeformationSpace (hT : T.IsJSJ 𝒜 ℋ) :
    T'.IsJSJ 𝒜 ℋ ↔ T'.IsMinimal ∧ T'.IsRelative 𝒜 ℋ ∧ T'.IsUniversallyElliptic 𝒜 ℋ ∧
      T.SameDeformationSpace T' :=
  ⟨fun h => ⟨h.isMinimal, h.isRelative, h.isUniversallyElliptic, hT.sameDeformationSpace h⟩,
    fun ⟨hm, hr, hu, h⟩ => hT.of_dominates hm hr hu (sameDeformationSpace_iff.mp h).2⟩

/-- The JSJ trees are the universally elliptic minimal relative trees with the same elliptic
subgroups as any one of them. -/
theorem IsJSJ.isJSJ_iff_forall_isEllipticSubgroup (hT : T.IsJSJ 𝒜 ℋ) :
    T'.IsJSJ 𝒜 ℋ ↔ T'.IsMinimal ∧ T'.IsRelative 𝒜 ℋ ∧ T'.IsUniversallyElliptic 𝒜 ℋ ∧
      ∀ H : Subgroup G, T.IsEllipticSubgroup H ↔ T'.IsEllipticSubgroup H := by
  rw [hT.isJSJ_iff_sameDeformationSpace, sameDeformationSpace_iff_forall_isEllipticSubgroup]

/-- A minimal relative tree all of whose vertices are rigid is a JSJ tree. -/
theorem IsJSJ.of_forall_isRigidVertex (hm : T.IsMinimal) (hr : T.IsRelative 𝒜 ℋ)
    (h : ∀ x : T.V, T.IsRigidVertex 𝒜 ℋ x) : T.IsJSJ 𝒜 ℋ :=
  ⟨hm, hr, isUniversallyElliptic_of_forall_isRigidVertex h,
    fun _ hm' hr' _ => dominates_of_forall_isRigidVertex h hm' hr'⟩

/-- A minimal relative tree with trivial vertex stabilizers is a JSJ tree. -/
theorem IsJSJ.of_forall_stabilizer_eq_bot (hm : T.IsMinimal) (hr : T.IsRelative 𝒜 ℋ)
    (h : ∀ x : T.V, stabilizer G x = ⊥) : T.IsJSJ 𝒜 ℋ :=
  .of_forall_isRigidVertex hm hr fun x => isRigidVertex_of_stabilizer_eq_bot 𝒜 ℋ (h x)

/-- In a minimal relative tree all of whose vertices are rigid, the universally elliptic
subgroups are exactly the elliptic subgroups. -/
theorem isUniversallyEllipticSubgroup_iff_isEllipticSubgroup (hm : T.IsMinimal)
    (hr : T.IsRelative 𝒜 ℋ) (h : ∀ x : T.V, T.IsRigidVertex 𝒜 ℋ x) :
    IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ H ↔ T.IsEllipticSubgroup H :=
  ⟨fun hH => hH T hm hr, fun hH => (isEllipticSubgroup_iff.mp hH).elim fun x hx =>
    (h x).isUniversallyEllipticSubgroup_stabilizer.mono hx⟩

/-- If some minimal relative tree has trivial vertex stabilizers, the trivial subgroup is the
only universally elliptic subgroup. -/
theorem isUniversallyEllipticSubgroup_iff_eq_bot (hm : T.IsMinimal) (hr : T.IsRelative 𝒜 ℋ)
    (h : ∀ x : T.V, stabilizer G x = ⊥) :
    IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ H ↔ H = ⊥ := by
  rw [isUniversallyEllipticSubgroup_iff_isEllipticSubgroup hm hr
    fun x => isRigidVertex_of_stabilizer_eq_bot 𝒜 ℋ (h x), isEllipticSubgroup_iff_eq_bot h]

/-- If some JSJ tree has trivial vertex stabilizers, the JSJ trees are exactly the minimal trees
with trivial vertex stabilizers. -/
theorem IsJSJ.isJSJ_iff_forall_stabilizer_eq_bot (hT : T.IsJSJ 𝒜 ℋ)
    (h : ∀ x : T.V, stabilizer G x = ⊥) :
    T'.IsJSJ 𝒜 ℋ ↔ T'.IsMinimal ∧ ∀ x : T'.V, stabilizer G x = ⊥ := by
  refine ⟨fun hT' => ⟨hT'.isMinimal, fun x => (isEllipticSubgroup_iff_eq_bot h).mp
    ((hT'.isEllipticSubgroup_iff hT).mp (T'.isEllipticSubgroup_stabilizer x))⟩,
    fun ⟨hm, h'⟩ => .of_forall_stabilizer_eq_bot hm ?_ h'⟩
  rcases isEmpty_or_nonempty T.E with _ | ⟨⟨e⟩⟩
  · -- `T` has one vertex, so `G` is trivial and the minimal tree `T'` has one vertex too.
    have := T.subsingleton_of_isEmpty_dart
    have := hm.subsingleton ((isEllipticSubgroup_iff_eq_bot h').mpr
      ((stabilizer_eq_top_of_subsingleton _).symm.trans (h (Classical.arbitrary T.V))))
    exact T'.isRelative_of_subsingleton 𝒜 ℋ
  · -- The stabilizer of a dart of `T` is trivial and lies in `𝒜`; the members of `ℋ` are elliptic
    -- in `T`, hence trivial.
    exact isRelative_of_forall_stabilizer_eq_bot
      ((isEllipticSubgroup_iff_eq_bot h).mp (T.isEllipticSubgroup_stabilizer_dart e) ▸
        hT.isRelative.stabilizer_mem e)
      (fun _ hH => (isEllipticSubgroup_iff_eq_bot h).mp (hT.isRelative.isEllipticSubgroup hH)) h'

/-! ### Trees with one vertex -/

/-- A vertex of a `G`-tree with one vertex is rigid exactly when `G` is universally elliptic. -/
theorem isRigidVertex_iff_of_subsingleton [Subsingleton T.V] :
    T.IsRigidVertex 𝒜 ℋ x ↔ IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (⊤ : Subgroup G) := by
  rw [isRigidVertex_iff, stabilizer_eq_top_of_subsingleton]

/-- A vertex of a `G`-tree with one vertex is flexible exactly when `G` is not universally
elliptic. -/
theorem isFlexibleVertex_iff_of_subsingleton [Subsingleton T.V] :
    T.IsFlexibleVertex 𝒜 ℋ x ↔ ¬IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (⊤ : Subgroup G) :=
  not_congr isRigidVertex_iff_of_subsingleton

/-- A `G`-tree with one vertex is a JSJ tree exactly when `G` fixes a vertex of every universally
elliptic minimal relative tree. -/
theorem isJSJ_iff_of_subsingleton [Subsingleton T.V] :
    T.IsJSJ 𝒜 ℋ ↔ ∀ T' : GTree.{u, v} G, T'.IsMinimal → T'.IsRelative 𝒜 ℋ →
      T'.IsUniversallyElliptic 𝒜 ℋ → T'.IsEllipticSubgroup ⊤ :=
  ⟨fun h _ hm hr hu => dominates_iff_of_subsingleton.mp (h.dominates hm hr hu),
    fun h => ⟨isMinimal_of_subsingleton, T.isRelative_of_subsingleton 𝒜 ℋ,
      T.isUniversallyElliptic_of_subsingleton 𝒜 ℋ,
      fun T' hm hr hu => dominates_iff_of_subsingleton.mpr (h T' hm hr hu)⟩⟩

/-- A `G`-tree with one vertex is a JSJ tree when `G` is universally elliptic. -/
theorem isJSJ_of_subsingleton [Subsingleton T.V]
    (h : IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (⊤ : Subgroup G)) : T.IsJSJ 𝒜 ℋ :=
  isJSJ_iff_of_subsingleton.mpr fun T' hm hr _ => h T' hm hr

/-- If a `G`-tree with one vertex is a JSJ tree, the JSJ trees are exactly the trees with one
vertex. -/
theorem IsJSJ.isJSJ_iff_subsingleton [Subsingleton T.V] (hT : T.IsJSJ 𝒜 ℋ) :
    T'.IsJSJ 𝒜 ℋ ↔ Subsingleton T'.V :=
  ⟨fun h => h.isMinimal.subsingleton
      ((hT.isEllipticSubgroup_iff h).mp (T.isEllipticSubgroup_of_subsingleton ⊤)),
    fun _ => hT.of_dominates isMinimal_of_subsingleton (T'.isRelative_of_subsingleton 𝒜 ℋ)
      (T'.isUniversallyElliptic_of_subsingleton 𝒜 ℋ) (T'.dominates_of_subsingleton)⟩

/-- If some JSJ tree of a nontrivial group has trivial vertex stabilizers, no tree with one
vertex is a JSJ tree. -/
theorem IsJSJ.not_isJSJ_of_subsingleton [Nontrivial G] [Subsingleton T'.V] (hT : T.IsJSJ 𝒜 ℋ)
    (h : ∀ x : T.V, stabilizer G x = ⊥) : ¬T'.IsJSJ 𝒜 ℋ := fun hT' => by
  have hx := ((hT.isJSJ_iff_forall_stabilizer_eq_bot h).mp hT').2 (Classical.arbitrary T'.V)
  rw [stabilizer_eq_top_of_subsingleton] at hx
  exact top_ne_bot hx

end Tree

/-! ### The one-vertex tree -/

/-- The one-vertex tree is universally elliptic. -/
@[simp] theorem point_isUniversallyElliptic : (point.{u, v} G).IsUniversallyElliptic 𝒜 ℋ :=
  isUniversallyElliptic_of_subsingleton _ 𝒜 ℋ

/-- The vertex of the one-vertex tree is rigid exactly when `G` is universally elliptic. -/
@[simp] theorem point_isRigidVertex_iff {x : (point.{u, v} G).V} :
    (point.{u, v} G).IsRigidVertex 𝒜 ℋ x ↔
      IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (⊤ : Subgroup G) :=
  isRigidVertex_iff_of_subsingleton

/-- The vertex of the one-vertex tree is flexible exactly when `G` is not universally
elliptic. -/
@[simp] theorem point_isFlexibleVertex_iff {x : (point.{u, v} G).V} :
    (point.{u, v} G).IsFlexibleVertex 𝒜 ℋ x ↔
      ¬IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (⊤ : Subgroup G) :=
  isFlexibleVertex_iff_of_subsingleton

/-- The one-vertex tree is a JSJ tree exactly when `G` fixes a vertex of every universally
elliptic minimal relative tree. -/
theorem point_isJSJ_iff :
    (point.{u, v} G).IsJSJ 𝒜 ℋ ↔ ∀ T : GTree.{u, v} G, T.IsMinimal → T.IsRelative 𝒜 ℋ →
      T.IsUniversallyElliptic 𝒜 ℋ → T.IsEllipticSubgroup ⊤ :=
  isJSJ_iff_of_subsingleton

/-- The one-vertex tree is a JSJ tree when `G` is universally elliptic. -/
theorem point_isJSJ (h : IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ (⊤ : Subgroup G)) :
    (point.{u, v} G).IsJSJ 𝒜 ℋ :=
  isJSJ_of_subsingleton h

/-! ### The trivial group -/

variable (𝒜 ℋ) in
/-- Every subgroup of the trivial group is universally elliptic. -/
theorem isUniversallyEllipticSubgroup_of_subsingleton [Subsingleton G] (H : Subgroup G) :
    IsUniversallyEllipticSubgroup.{u, v} 𝒜 ℋ H :=
  Subsingleton.elim ⊥ H ▸ isUniversallyEllipticSubgroup_bot 𝒜 ℋ

/-- The JSJ trees of the trivial group are the trees with one vertex. -/
theorem isJSJ_iff_subsingleton [Subsingleton G] {T : GTree.{u, v} G} :
    T.IsJSJ 𝒜 ℋ ↔ Subsingleton T.V :=
  (point_isJSJ (isUniversallyEllipticSubgroup_of_subsingleton 𝒜 ℋ ⊤)).isJSJ_iff_subsingleton

/-! ### The infinite cyclic group -/

/-- The line is a JSJ tree of the infinite cyclic group, over any family containing the trivial
subgroup and relative to at most the trivial subgroup. -/
theorem line_isJSJ {𝒜 ℋ : Set (Subgroup (Multiplicative ℤ))} (h𝒜 : ⊥ ∈ 𝒜) (hℋ : ℋ ⊆ {⊥}) :
    line.IsJSJ 𝒜 ℋ :=
  .of_forall_stabilizer_eq_bot line_isMinimal (line_isRelative h𝒜 hℋ) line_stabilizer_vertex

/-- The trivial subgroup is the only universally elliptic subgroup of the infinite cyclic group,
over a family containing the trivial subgroup and relative to at most the trivial subgroup: the
integers act freely on the line. -/
theorem isUniversallyEllipticSubgroup_iff_eq_bot_int {𝒜 ℋ : Set (Subgroup (Multiplicative ℤ))}
    (h𝒜 : ⊥ ∈ 𝒜) (hℋ : ℋ ⊆ {⊥}) {H : Subgroup (Multiplicative ℤ)} :
    IsUniversallyEllipticSubgroup.{0, 0} 𝒜 ℋ H ↔ H = ⊥ :=
  isUniversallyEllipticSubgroup_iff_eq_bot line_isMinimal (line_isRelative h𝒜 hℋ)
    line_stabilizer_vertex

/-- The infinite cyclic group is not universally elliptic over a family containing the trivial
subgroup, relative to at most the trivial subgroup. -/
theorem not_isUniversallyEllipticSubgroup_top_int {𝒜 ℋ : Set (Subgroup (Multiplicative ℤ))}
    (h𝒜 : ⊥ ∈ 𝒜) (hℋ : ℋ ⊆ {⊥}) :
    ¬IsUniversallyEllipticSubgroup.{0, 0} 𝒜 ℋ (⊤ : Subgroup (Multiplicative ℤ)) :=
  fun h => top_ne_bot ((isUniversallyEllipticSubgroup_iff_eq_bot_int h𝒜 hℋ).mp h)

/-- The one-vertex tree is not a JSJ tree of the infinite cyclic group, over a family containing
the trivial subgroup and relative to at most the trivial subgroup. -/
theorem not_point_isJSJ_int {𝒜 ℋ : Set (Subgroup (Multiplicative ℤ))} (h𝒜 : ⊥ ∈ 𝒜)
    (hℋ : ℋ ⊆ {⊥}) : ¬(point.{0, 0} (Multiplicative ℤ)).IsJSJ 𝒜 ℋ :=
  (line_isJSJ h𝒜 hℋ).not_isJSJ_of_subsingleton line_stabilizer_vertex

/-- The vertex of the one-vertex tree of the infinite cyclic group is flexible, over a family
containing the trivial subgroup and relative to at most the trivial subgroup. -/
theorem point_isFlexibleVertex_int {𝒜 ℋ : Set (Subgroup (Multiplicative ℤ))} (h𝒜 : ⊥ ∈ 𝒜)
    (hℋ : ℋ ⊆ {⊥}) (x : (point.{0, 0} (Multiplicative ℤ)).V) :
    (point.{0, 0} (Multiplicative ℤ)).IsFlexibleVertex 𝒜 ℋ x :=
  point_isFlexibleVertex_iff.mpr (not_isUniversallyEllipticSubgroup_top_int h𝒜 hℋ)

end GTree

end TauCeti
