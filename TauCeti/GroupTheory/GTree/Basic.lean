/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Aut
public import TauCeti.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Group actions on trees

A `G`-tree is a Serre tree with an action of `G` by graph automorphisms without inversions: no
element maps a dart to its reverse. This file sets up the vocabulary of Bass–Serre theory for
such actions.

* An element is *elliptic* when it fixes a vertex and *hyperbolic* otherwise; a subgroup is
  elliptic when it fixes a vertex. The vertices fixed by an element or a subgroup form a convex
  set, and an element is elliptic exactly when its translation length
  `ℓ(g) = min_v d(v, g v)` vanishes. Translation length is invariant under conjugation and
  inversion.
* A `G`-tree is *minimal* when no nonempty convex `G`-invariant proper set of vertices exists,
  and it is *relative* to families `𝒜` and `ℋ` of subgroups when its dart stabilizers lie in `𝒜`
  and every member of `ℋ` is elliptic.
* A `G`-tree `T` *dominates* `T'` when there is a `G`-equivariant map from the vertices of `T`
  to those of `T'`. Since the targets are trees, such a map extends to an equivariant continuous
  map of geometric realizations sending each edge to a geodesic segment, and an element fixing a
  point of an edge fixes the edge because there are no inversions. By `GTree.dominates_iff`,
  `T` dominates `T'` exactly when every vertex stabilizer of `T` is elliptic in `T'`. Two
  `G`-trees lie in the same deformation space when each dominates the other.

The one-vertex `G`-tree is minimal, every subgroup is elliptic in it, and it is dominated by
every `G`-tree. The line, a `G`-tree for the infinite cyclic group, is in
`TauCeti.GroupTheory.GTree.Line`. The automorphism of the segment exchanging its
vertices inverts its edge (`TauCeti.SerreGraph.segmentSwap_smul`); more generally, no element of
a `G`-tree exchanges the endpoints of a dart.

## Main declarations

* `TauCeti.GTree`: a Serre tree with an action of `G` without inversions.
* `TauCeti.GTree.IsElliptic`, `TauCeti.GTree.IsHyperbolic`,
  `TauCeti.GTree.IsEllipticSubgroup`: elliptic and hyperbolic elements, elliptic subgroups.
* `TauCeti.GTree.translationLength`: the translation length of an element.
* `TauCeti.GTree.IsMinimal`, `TauCeti.GTree.IsRelative`: minimal and relative trees.
* `TauCeti.GTree.Dominates`, `TauCeti.GTree.SameDeformationSpace`: domination and deformation
  spaces, with `TauCeti.GTree.dominates_iff`.
* `TauCeti.GTree.point`: the one-vertex tree.

## References

* J.-P. Serre, *Trees*, Chapter I, §3.1 and §6.
* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.1,
  Definition 2.1 and §2.2.
-/

public section

universe u v u' v' u'' v'' w

namespace TauCeti

open SerreGraph _root_.MulAction

/-- A `G`-tree: a Serre tree with an action of `G` by graph automorphisms without inversions. -/
structure GTree (G : Type w) [Group G] extends SerreGraph.{u, v} where
  /-- The underlying graph is a tree. -/
  isTree : toSerreGraph.IsTree
  /-- The action, as a homomorphism to the automorphism group of the tree. -/
  action : G →* toSerreGraph.Aut
  /-- No element maps a dart to its reverse. -/
  action_smul_ne_rev : ∀ (g : G) (e : E), (action g).equivE e ≠ rev e

namespace GTree

variable {G : Type w} [Group G] (T : GTree.{u, v} G)

/-- `G` acts on the vertices of a `G`-tree. -/
instance : MulAction G T.V := MulAction.compHom T.V T.action

/-- `G` acts on the darts of a `G`-tree. -/
instance : MulAction G T.E := MulAction.compHom T.E T.action

theorem smul_vertex_def (g : G) (v : T.V) : g • v = T.action g • v := (rfl)

theorem smul_dart_def (g : G) (e : T.E) : g • e = T.action g • e := (rfl)

@[simp] theorem src_smul (g : G) (e : T.E) : T.src (g • e) = g • T.src e :=
  Aut.src_smul (T.action g) e

@[simp] theorem rev_smul (g : G) (e : T.E) : T.rev (g • e) = g • T.rev e :=
  Aut.rev_smul (T.action g) e

@[simp] theorem tgt_smul (g : G) (e : T.E) : T.tgt (g • e) = g • T.tgt e :=
  Aut.tgt_smul (T.action g) e

/-- The action has no inversions. -/
theorem smul_ne_rev (g : G) (e : T.E) : g • e ≠ T.rev e :=
  T.action_smul_ne_rev g e

/-- The action preserves distances. -/
@[simp] theorem dist_smul (g : G) (a b : T.V) : T.dist (g • a) (g • b) = T.dist a b :=
  Aut.dist_smul (T.action g) a b

/-- Any two vertices of a `G`-tree are joined by a path. -/
theorem nonempty_path (a b : T.V) : Nonempty (T.Path a b) :=
  (preconnected_iff _).mp ((connected_iff _).mp (IsTree.connected _ T.isTree)).2 a b

instance : Nonempty T.V := ((connected_iff _).mp (IsTree.connected _ T.isTree)).1

/-- No element exchanges the endpoints of a dart. -/
theorem smul_tgt_ne_src_of_smul_src_eq_tgt {g : G} {e : T.E} (h : g • T.src e = T.tgt e) :
    g • T.tgt e ≠ T.src e := by
  intro h'
  let x : Quiver.Hom (T.tgt e) (T.src e) := ⟨g • e, by rw [src_smul, h], by rw [tgt_smul, h']⟩
  let y : Quiver.Hom (T.tgt e) (T.src e) := ⟨T.rev e, T.src_rev e, T.tgt_rev e⟩
  have hxy := congrArg (Path.darts T.toSerreGraph)
    ((IsTree.isAcyclic _ T.isTree).eq_of_isReduced (Path.isReduced_toPath _ x)
      (Path.isReduced_toPath _ y))
  simp only [Path.darts_toPath, List.cons.injEq, and_true, x, y] at hxy
  exact T.smul_ne_rev g e hxy

/-! ### Elliptic and hyperbolic elements -/

/-- An element is elliptic when it fixes a vertex. -/
def IsElliptic (g : G) : Prop :=
  ∃ v : T.V, g • v = v

/-- An element is hyperbolic when it fixes no vertex. -/
def IsHyperbolic (g : G) : Prop :=
  ¬T.IsElliptic g

/-- A subgroup is elliptic when it fixes a vertex. -/
def IsEllipticSubgroup (H : Subgroup G) : Prop :=
  ∃ v : T.V, H ≤ stabilizer G v

variable {T}

theorem isElliptic_iff {g : G} : T.IsElliptic g ↔ ∃ v : T.V, g • v = v := Iff.rfl

theorem isHyperbolic_iff {g : G} : T.IsHyperbolic g ↔ ∀ v : T.V, g • v ≠ v := not_exists

theorem not_isHyperbolic_iff {g : G} : ¬T.IsHyperbolic g ↔ T.IsElliptic g := not_not

theorem isEllipticSubgroup_iff {H : Subgroup G} :
    T.IsEllipticSubgroup H ↔ ∃ v : T.V, H ≤ stabilizer G v := Iff.rfl

/-- A subgroup is elliptic exactly when some vertex is fixed by each of its elements. -/
theorem isEllipticSubgroup_iff_forall {H : Subgroup G} :
    T.IsEllipticSubgroup H ↔ ∃ v : T.V, ∀ h ∈ H, h • v = v := by
  simp only [isEllipticSubgroup_iff, IsConcreteLE.le_iff, mem_stabilizer_iff]

variable (T) in
@[simp] theorem isElliptic_one : T.IsElliptic 1 :=
  ⟨Classical.arbitrary T.V, one_smul G _⟩

@[simp] theorem isElliptic_inv_iff {g : G} : T.IsElliptic g⁻¹ ↔ T.IsElliptic g :=
  exists_congr fun v => by rw [inv_smul_eq_iff, eq_comm]

/-- Conjugate elements are elliptic together. -/
@[simp] theorem isElliptic_conj_iff {g h : G} : T.IsElliptic (h * g * h⁻¹) ↔ T.IsElliptic g := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨h⁻¹ • v, ?_⟩
    calc g • h⁻¹ • v = h⁻¹ • (h * g * h⁻¹) • v := by simp only [mul_smul, inv_smul_smul]
      _ = h⁻¹ • v := by rw [hv]
  · rintro ⟨v, hv⟩
    exact ⟨h • v, by rw [mul_smul, mul_smul, inv_smul_smul, hv]⟩

@[simp] theorem isHyperbolic_inv_iff {g : G} : T.IsHyperbolic g⁻¹ ↔ T.IsHyperbolic g :=
  not_congr isElliptic_inv_iff

@[simp] theorem isHyperbolic_conj_iff {g h : G} :
    T.IsHyperbolic (h * g * h⁻¹) ↔ T.IsHyperbolic g :=
  not_congr isElliptic_conj_iff

/-- A hyperbolic element is not the identity. -/
theorem IsHyperbolic.ne_one {g : G} (hg : T.IsHyperbolic g) : g ≠ 1 := by
  rintro rfl
  exact hg (isElliptic_one T)

/-- The cyclic subgroup of an element is elliptic exactly when the element is. -/
@[simp] theorem isEllipticSubgroup_zpowers_iff {g : G} :
    T.IsEllipticSubgroup (Subgroup.zpowers g) ↔ T.IsElliptic g := by
  simp only [isEllipticSubgroup_iff, Subgroup.zpowers_le, mem_stabilizer_iff, isElliptic_iff]

/-- The powers of an elliptic element are elliptic. -/
theorem IsElliptic.zpow {g : G} (hg : T.IsElliptic g) (n : ℤ) : T.IsElliptic (g ^ n) := by
  obtain ⟨v, hv⟩ := isEllipticSubgroup_zpowers_iff.mpr hg
  exact ⟨v, hv (Subgroup.zpow_mem_zpowers g n)⟩

/-- Elements of an elliptic subgroup are elliptic. -/
theorem IsEllipticSubgroup.isElliptic {H : Subgroup G} (hH : T.IsEllipticSubgroup H) {g : G}
    (hg : g ∈ H) : T.IsElliptic g := by
  obtain ⟨v, hv⟩ := hH
  exact ⟨v, hv hg⟩

/-- Subgroups of elliptic subgroups are elliptic. -/
theorem IsEllipticSubgroup.mono {H K : Subgroup G} (hH : T.IsEllipticSubgroup H) (hKH : K ≤ H) :
    T.IsEllipticSubgroup K := by
  obtain ⟨v, hv⟩ := hH
  exact ⟨v, hKH.trans hv⟩

variable (T) in
@[simp] theorem isEllipticSubgroup_bot : T.IsEllipticSubgroup ⊥ :=
  ⟨Classical.arbitrary T.V, bot_le⟩

variable (T) in
/-- Vertex stabilizers are elliptic. -/
theorem isEllipticSubgroup_stabilizer (v : T.V) : T.IsEllipticSubgroup (stabilizer G v) :=
  ⟨v, le_rfl⟩

/-- Conjugates of an elliptic subgroup are elliptic. -/
theorem IsEllipticSubgroup.map_conj {H : Subgroup G} (hH : T.IsEllipticSubgroup H) (g : G) :
    T.IsEllipticSubgroup (H.map (MulAut.conj g : G →* G)) := by
  obtain ⟨v, hv⟩ := hH
  refine ⟨g • v, ?_⟩
  rw [stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe]
  exact Subgroup.map_mono hv

/-- A subgroup is elliptic exactly when its conjugates are. -/
@[simp] theorem isEllipticSubgroup_map_conj_iff {H : Subgroup G} {g : G} :
    T.IsEllipticSubgroup (H.map (MulAut.conj g : G →* G)) ↔ T.IsEllipticSubgroup H := by
  refine ⟨fun h => (h.map_conj g⁻¹).mono fun x hx => ?_, fun h => h.map_conj g⟩
  refine Subgroup.mem_map.mpr ⟨MulAut.conj g x, Subgroup.mem_map_of_mem _ hx, ?_⟩
  simp [mul_assoc]

/-! ### Fixed vertices -/

variable (T) in
/-- The vertices fixed by an element form a convex set. -/
theorem isConvex_fixedBy (g : G) : T.IsConvex (fixedBy T.V g) :=
  Aut.isConvex_fixedBy (IsTree.isAcyclic _ T.isTree) (T.action g)

variable (T) in
/-- The vertices fixed by a subgroup form a convex set. -/
theorem isConvex_fixedPoints (H : Subgroup G) : T.IsConvex (fixedPoints H T.V) := by
  rw [fixed_eq_iInter_fixedBy]
  exact isConvex_iInter fun h => T.isConvex_fixedBy h

/-- A subgroup is elliptic exactly when it fixes some vertex. -/
theorem isEllipticSubgroup_iff_nonempty_fixedPoints {H : Subgroup G} :
    T.IsEllipticSubgroup H ↔ (fixedPoints H T.V).Nonempty := by
  simp only [isEllipticSubgroup_iff_forall, Set.Nonempty, mem_fixedPoints, Subtype.forall,
    Subgroup.mk_smul]

/-! ### Translation length -/

variable (T) in
/-- The translation length `ℓ(g) = min_v d(v, g v)` of an element. -/
noncomputable def translationLength (g : G) : ℕ :=
  ⨅ v : T.V, T.dist v (g • v)

theorem translationLength_le (g : G) (v : T.V) : T.translationLength g ≤ T.dist v (g • v) :=
  ciInf_le (OrderBot.bddBelow _) v

/-- Some vertex is moved exactly by the translation length. -/
theorem exists_dist_eq_translationLength (g : G) :
    ∃ v : T.V, T.dist v (g • v) = T.translationLength g :=
  Nat.sInf_mem (Set.range_nonempty fun v : T.V => T.dist v (g • v))

/-- An element has translation length zero exactly when it is elliptic. -/
theorem translationLength_eq_zero_iff {g : G} : T.translationLength g = 0 ↔ T.IsElliptic g := by
  refine ⟨fun h => ?_, fun ⟨v, hv⟩ => Nat.le_zero.mp ?_⟩
  · obtain ⟨v, hv⟩ := exists_dist_eq_translationLength (T := T) g
    exact ⟨v, ((dist_eq_zero_iff (T.nonempty_path _ _)).mp (hv.trans h)).symm⟩
  · simpa only [hv, dist_self] using translationLength_le g v

/-- An element has positive translation length exactly when it is hyperbolic. -/
theorem translationLength_pos_iff {g : G} : 0 < T.translationLength g ↔ T.IsHyperbolic g := by
  rw [Nat.pos_iff_ne_zero, Ne, translationLength_eq_zero_iff, IsHyperbolic]

variable (T) in
@[simp] theorem translationLength_one : T.translationLength 1 = 0 :=
  translationLength_eq_zero_iff.mpr (isElliptic_one T)

/-- An element and its inverse have the same translation length. -/
@[simp] theorem translationLength_inv (g : G) :
    T.translationLength g⁻¹ = T.translationLength g := by
  unfold translationLength
  congr 1
  ext v
  rw [← T.dist_smul g, smul_inv_smul, dist_comm]

/-- Translation length is invariant under conjugation. -/
@[simp] theorem translationLength_conj (g h : G) :
    T.translationLength (h * g * h⁻¹) = T.translationLength g := by
  unfold translationLength
  exact ((MulAction.surjective h).iInf_congr (h • ·) fun v => by
    simp only [mul_smul, inv_smul_smul, dist_smul]).symm

/-! ### Minimal and relative trees -/

variable (T) in
/-- A `G`-tree is minimal when it has no proper invariant subtree: every nonempty convex set of
vertices invariant under `G` contains every vertex. -/
def IsMinimal : Prop :=
  ∀ S : Set T.V, S.Nonempty → T.IsConvex S → (∀ g : G, ∀ v ∈ S, g • v ∈ S) → S = Set.univ

theorem isMinimal_iff : T.IsMinimal ↔
    ∀ S : Set T.V, S.Nonempty → T.IsConvex S → (∀ g : G, ∀ v ∈ S, g • v ∈ S) →
      S = Set.univ := Iff.rfl

/-- A `G`-tree with at most one vertex is minimal. -/
theorem isMinimal_of_subsingleton [Subsingleton T.V] : T.IsMinimal :=
  fun _ hS _ _ => hS.eq_univ

/-- A minimal `G`-tree on which `G` fixes a vertex is a single vertex. -/
theorem IsMinimal.subsingleton (hT : T.IsMinimal) (h : T.IsEllipticSubgroup ⊤) :
    Subsingleton T.V := by
  obtain ⟨v, hv⟩ := isEllipticSubgroup_iff_forall.mp h
  have hS := hT {v} (Set.singleton_nonempty v)
    ((IsTree.isAcyclic _ T.isTree).isConvex_singleton v) fun g w hw => by
      rw [Set.mem_singleton_iff] at hw ⊢
      rw [hw, hv g (Subgroup.mem_top g)]
  exact Set.subsingleton_univ_iff.mp (hS ▸ Set.subsingleton_singleton)

variable (T) in
/-- A `G`-tree is relative to families `𝒜` and `ℋ` of subgroups when the stabilizer of every
dart lies in `𝒜` and every subgroup in `ℋ` is elliptic. -/
def IsRelative (𝒜 ℋ : Set (Subgroup G)) : Prop :=
  (∀ e : T.E, stabilizer G e ∈ 𝒜) ∧ ∀ H ∈ ℋ, T.IsEllipticSubgroup H

theorem isRelative_iff {𝒜 ℋ : Set (Subgroup G)} : T.IsRelative 𝒜 ℋ ↔
    (∀ e : T.E, stabilizer G e ∈ 𝒜) ∧ ∀ H ∈ ℋ, T.IsEllipticSubgroup H := Iff.rfl

theorem IsRelative.stabilizer_mem {𝒜 ℋ : Set (Subgroup G)} (h : T.IsRelative 𝒜 ℋ) (e : T.E) :
    stabilizer G e ∈ 𝒜 :=
  h.1 e

theorem IsRelative.isEllipticSubgroup {𝒜 ℋ : Set (Subgroup G)} (h : T.IsRelative 𝒜 ℋ)
    {H : Subgroup G} (hH : H ∈ ℋ) : T.IsEllipticSubgroup H :=
  h.2 H hH

/-- Relativity is monotone: larger edge families and smaller elliptic families. -/
theorem IsRelative.mono {𝒜 𝒜' ℋ ℋ' : Set (Subgroup G)} (h : T.IsRelative 𝒜 ℋ) (h𝒜 : 𝒜 ⊆ 𝒜')
    (hℋ : ℋ' ⊆ ℋ) : T.IsRelative 𝒜' ℋ' :=
  ⟨fun e => h𝒜 (h.1 e), fun H hH => h.2 H (hℋ hH)⟩

/-! ### Domination and deformation spaces -/

variable (T) in
/-- A `G`-tree `T` dominates `T'` when there is a `G`-equivariant map from the vertices of `T`
to the vertices of `T'`. -/
def Dominates (T' : GTree.{u', v'} G) : Prop :=
  Nonempty (T.V →[G] T'.V)

variable {T' : GTree.{u', v'} G} {T'' : GTree.{u'', v''} G}

theorem dominates_iff_nonempty : T.Dominates T' ↔ Nonempty (T.V →[G] T'.V) := Iff.rfl

variable (T) in
/-- Every `G`-tree dominates itself. -/
theorem Dominates.refl : T.Dominates T :=
  ⟨MulActionHom.id G⟩

/-- Domination is transitive. -/
theorem Dominates.trans (h : T.Dominates T') (h' : T'.Dominates T'') : T.Dominates T'' :=
  ⟨h'.some.comp h.some⟩

/-- A subgroup elliptic in a tree is elliptic in every tree it dominates. -/
theorem Dominates.isEllipticSubgroup (h : T.Dominates T') {H : Subgroup G}
    (hH : T.IsEllipticSubgroup H) : T'.IsEllipticSubgroup H := by
  obtain ⟨f⟩ := h
  obtain ⟨v, hv⟩ := isEllipticSubgroup_iff_forall.mp hH
  exact isEllipticSubgroup_iff_forall.mpr ⟨f v, fun g hg => by rw [← map_smul f, hv g hg]⟩

/-- An element elliptic in a tree is elliptic in every tree it dominates. -/
theorem Dominates.isElliptic (h : T.Dominates T') {g : G} (hg : T.IsElliptic g) :
    T'.IsElliptic g :=
  isEllipticSubgroup_zpowers_iff.mp (h.isEllipticSubgroup (isEllipticSubgroup_zpowers_iff.mpr hg))

/-- `T` dominates `T'` exactly when every vertex stabilizer of `T` is elliptic in `T'`. -/
theorem dominates_iff : T.Dominates T' ↔ ∀ v : T.V, T'.IsEllipticSubgroup (stabilizer G v) :=
  MulAction.nonempty_mulActionHom_iff

variable (T T') in
/-- Two `G`-trees lie in the same deformation space when each dominates the other. -/
def SameDeformationSpace : Prop :=
  T.Dominates T' ∧ T'.Dominates T

theorem sameDeformationSpace_iff :
    T.SameDeformationSpace T' ↔ T.Dominates T' ∧ T'.Dominates T := Iff.rfl

variable (T) in
theorem SameDeformationSpace.refl : T.SameDeformationSpace T :=
  ⟨.refl T, .refl T⟩

theorem SameDeformationSpace.symm (h : T.SameDeformationSpace T') : T'.SameDeformationSpace T :=
  ⟨h.2, h.1⟩

theorem SameDeformationSpace.trans (h : T.SameDeformationSpace T')
    (h' : T'.SameDeformationSpace T'') : T.SameDeformationSpace T'' :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- Trees in the same deformation space have the same elliptic subgroups. -/
theorem SameDeformationSpace.isEllipticSubgroup_iff (h : T.SameDeformationSpace T')
    {H : Subgroup G} : T.IsEllipticSubgroup H ↔ T'.IsEllipticSubgroup H :=
  ⟨h.1.isEllipticSubgroup, h.2.isEllipticSubgroup⟩

/-! ### The one-vertex tree -/

variable (G) in
/-- The one-vertex `G`-tree, with the trivial action. -/
def point : GTree.{u, v} G where
  toSerreGraph := SerreGraph.point
  isTree := single_vertex_isTree
  action := 1
  action_smul_ne_rev _ e := e.elim

instance : Subsingleton (point.{u, v} G).V :=
  inferInstanceAs (Subsingleton PUnit)

/-- Every subgroup is elliptic in the one-vertex tree. -/
@[simp] theorem point_isEllipticSubgroup (H : Subgroup G) :
    (point.{u, v} G).IsEllipticSubgroup H :=
  ⟨Classical.arbitrary _, fun _ _ => Subsingleton.elim _ _⟩

/-- Every element is elliptic in the one-vertex tree. -/
@[simp] theorem point_isElliptic (g : G) : (point.{u, v} G).IsElliptic g :=
  isEllipticSubgroup_zpowers_iff.mp (point_isEllipticSubgroup _)

variable (G) in
theorem point_isMinimal : (point.{u, v} G).IsMinimal :=
  isMinimal_of_subsingleton

variable (G) in
/-- The one-vertex tree is relative to all families of subgroups. -/
theorem point_isRelative (𝒜 ℋ : Set (Subgroup G)) : (point.{u, v} G).IsRelative 𝒜 ℋ :=
  ⟨fun e => e.elim, fun H _ => point_isEllipticSubgroup H⟩

variable (T) in
/-- Every `G`-tree dominates the one-vertex tree. -/
theorem dominates_point : T.Dominates (point.{u', v'} G) :=
  dominates_iff.mpr fun _ => point_isEllipticSubgroup _

/-- The one-vertex tree dominates exactly the `G`-trees in which `G` is elliptic. -/
theorem point_dominates_iff : (point.{u', v'} G).Dominates T ↔ T.IsEllipticSubgroup ⊤ := by
  rw [dominates_iff]
  refine ⟨fun h => ?_, fun h _ => h.mono le_top⟩
  have hstab : stabilizer G (Classical.arbitrary (point.{u', v'} G).V) = ⊤ :=
    eq_top_iff.mpr fun _ _ => mem_stabilizer_iff.mpr (Subsingleton.elim _ _)
  exact hstab ▸ h _

end GTree

end TauCeti
