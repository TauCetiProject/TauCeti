/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Quotient
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

* The quotient graph `T / G` of a `G`-tree (`GTree.quotient`) has the orbits of vertices and
  of darts as its vertices and darts; it is connected, and the projection `GTree.quotientMap`
  onto it is surjective with the orbits as fibres.
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

A `G`-tree has at most one vertex exactly when it has no darts. Such a tree is minimal and
relative to all families of subgroups, every subgroup is elliptic in it, and it is dominated by
every `G`-tree; it dominates exactly the `G`-trees in which `G` fixes a vertex. The one-vertex
`G`-tree is such a tree. In a `G`-tree with trivial vertex stabilizers only the trivial subgroup
is elliptic, so such a tree is relative to every family containing the trivial subgroup and every
family of trivial subgroups. The line, a `G`-tree for the infinite cyclic group, is in
`TauCeti.GroupTheory.GTree.Line`, and the axis of a hyperbolic element is in
`TauCeti.GroupTheory.GTree.Axis`. The automorphism of the segment exchanging its vertices inverts
its edge (`TauCeti.SerreGraph.segmentSwap_smul`); more generally, no element of a `G`-tree
exchanges the endpoints of a dart.

## Main declarations

* `TauCeti.GTree`: a Serre tree with an action of `G` without inversions.
* `TauCeti.GTree.quotient`, `TauCeti.GTree.quotientMap`: the quotient graph and the projection
  onto it.
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
  T.isTree.nonempty_path a b

/-! ### The quotient graph -/

section Quotient

/-- The quotient graph `T / G` of a `G`-tree. -/
abbrev quotient : SerreGraph.{u, v} :=
  T.toSerreGraph.quotient T.action T.smul_ne_rev

/-- The projection of a `G`-tree to its quotient graph. -/
abbrev quotientMap : T.toSerreGraph.Hom T.quotient :=
  T.toSerreGraph.quotientMap T.action T.smul_ne_rev

/-- Every vertex of the quotient graph is the image of a vertex of the tree. -/
theorem quotientMap_mapV_surjective : Function.Surjective T.quotientMap.mapV :=
  SerreGraph.quotientMap_mapV_surjective _ _ _

/-- Every dart of the quotient graph is the image of a dart of the tree. -/
theorem quotientMap_mapE_surjective : Function.Surjective T.quotientMap.mapE :=
  SerreGraph.quotientMap_mapE_surjective _ _ _

/-- The quotient graph of a `G`-tree is connected. -/
theorem quotient_connected : T.quotient.Connected :=
  SerreGraph.quotient_connected T.isTree.connected

variable {T}

/-- Two vertices of a `G`-tree have the same image in the quotient graph exactly when they are in
the same orbit. -/
theorem quotientMap_mapV_eq_iff {a b : T.V} :
    T.quotientMap.mapV a = T.quotientMap.mapV b ↔ ∃ g : G, g • a = b :=
  SerreGraph.quotientMap_mapV_eq_iff

/-- Two darts of a `G`-tree have the same image in the quotient graph exactly when they are in
the same orbit. -/
theorem quotientMap_mapE_eq_iff {e f : T.E} :
    T.quotientMap.mapE e = T.quotientMap.mapE f ↔ ∃ g : G, g • e = f :=
  SerreGraph.quotientMap_mapE_eq_iff

/-- A vertex of a `G`-tree and its translates have the same image in the quotient graph. -/
@[simp] theorem quotientMap_mapV_smul (g : G) (a : T.V) :
    T.quotientMap.mapV (g • a) = T.quotientMap.mapV a :=
  SerreGraph.quotientMap_mapV_smul g a

/-- A dart of a `G`-tree and its translates have the same image in the quotient graph. -/
@[simp] theorem quotientMap_mapE_smul (g : G) (e : T.E) :
    T.quotientMap.mapE (g • e) = T.quotientMap.mapE e :=
  SerreGraph.quotientMap_mapE_smul g e

end Quotient

section Translate

variable {T}

/-- The translate of a path by an element of the group: the path through the translates of its
darts. -/
def smulPath (g : G) {a b : T.V} (p : T.Path a b) : T.Path (g • a) (g • b) :=
  (T.action g).smulPath p

/-- The translate of a path by `g` is its translate by the automorphism by which `g` acts. -/
theorem smulPath_def (g : G) {a b : T.V} (p : T.Path a b) :
    smulPath g p = (T.action g).smulPath p := (rfl)

/-- The translate of the empty path is empty. -/
@[simp] theorem smulPath_nil (g : G) (a : T.V) :
    smulPath g (Quiver.Path.nil : T.Path a a) = Quiver.Path.nil :=
  Aut.smulPath_nil (T.action g) a

/-- The translate of a path extended by a dart is the translate extended by the translated
dart. -/
@[simp] theorem smulPath_cons (g : G) {a b c : T.V} (p : T.Path a b) (e : Quiver.Hom b c) :
    smulPath g (p.cons e) =
      (smulPath g p).cons ⟨g • e.1, by rw [src_smul, e.2.1], by rw [tgt_smul, e.2.2]⟩ :=
  Aut.smulPath_cons (T.action g) p e

/-- The translate of a one-dart path is the one-dart path through the translated dart. -/
@[simp] theorem smulPath_toPath (g : G) {a b : T.V} (e : Quiver.Hom a b) :
    smulPath g e.toPath =
      Quiver.Hom.toPath (⟨g • e.1, by rw [src_smul, e.2.1], by rw [tgt_smul, e.2.2]⟩ :
        Quiver.Hom (g • a) (g • b)) :=
  Aut.smulPath_toPath (T.action g) e

/-- The translate of a concatenation is the concatenation of the translates. -/
@[simp] theorem smulPath_comp (g : G) {a b c : T.V} (p : T.Path a b) (q : T.Path b c) :
    smulPath g (p.comp q) = (smulPath g p).comp (smulPath g q) :=
  Aut.smulPath_comp (T.action g) p q

/-- The translate of a reversed path is the reverse of the translate. -/
@[simp] theorem smulPath_reverse (g : G) {a b : T.V} (p : T.Path a b) :
    smulPath g p.reverse = (smulPath g p).reverse :=
  Aut.smulPath_reverse (T.action g) p

/-- The translate of a path passes through the translates of its vertices. -/
@[simp] theorem vertices_smulPath (g : G) {a b : T.V} (p : T.Path a b) :
    (smulPath g p).vertices = p.vertices.map (g • ·) :=
  Aut.vertices_smulPath (T.action g) p

/-- The identity translates every path to itself. -/
theorem one_smulPath {a b : T.V} (p : T.Path a b) :
    smulPath (1 : G) p = p.cast (one_smul G a).symm (one_smul G b).symm := by
  rw [Quiver.Path.eq_cast_iff_heq]
  exact (congr_arg_heq (fun φ : T.Aut => φ.smulPath p) (map_one T.action)).trans
    (heq_of_eq (Aut.one_smulPath p))

/-- Translating by a product is translating by each factor in turn. -/
theorem mul_smulPath (g h : G) {a b : T.V} (p : T.Path a b) :
    smulPath (g * h) p = (smulPath g (smulPath h p)).cast (mul_smul g h a).symm
      (mul_smul g h b).symm := by
  rw [Quiver.Path.eq_cast_iff_heq]
  exact (congr_arg_heq (fun φ : T.Aut => φ.smulPath p) (map_mul T.action g h)).trans
    (heq_of_eq (Aut.mul_smulPath _ _ p))

/-- The translate of a path traverses the translates of its darts. -/
@[simp] theorem darts_smulPath (g : G) {a b : T.V} (p : T.Path a b) :
    Path.darts T.toSerreGraph (smulPath g p) = (Path.darts T.toSerreGraph p).map (g • ·) :=
  Aut.darts_smulPath (T.action g) p

/-- The translate of a path is reduced exactly when the path is. -/
@[simp] theorem isReduced_smulPath (g : G) {a b : T.V} (p : T.Path a b) :
    Path.IsReduced T.toSerreGraph (smulPath g p) ↔ Path.IsReduced T.toSerreGraph p :=
  Aut.isReduced_smulPath (T.action g) p

/-- The translate of a path has the same length as the path. -/
@[simp] theorem length_smulPath (g : G) {a b : T.V} (p : T.Path a b) :
    (smulPath g p).length = p.length :=
  Aut.length_smulPath (T.action g) p

end Translate

/-- The `n`-th power of an element moves a vertex by at most `n` times as much as the element. -/
theorem dist_pow_smul_le (g : G) (v : T.V) (n : ℕ) :
    T.dist v (g ^ n • v) ≤ n * T.dist v (g • v) := by
  rw [smul_vertex_def, smul_vertex_def, map_pow]
  exact Aut.dist_pow_smul_le (T.action g) (T.nonempty_path _ _) n

/-- The `n`-th power of an element moves a vertex by at most `|n|` times as much as the
element. -/
theorem dist_zpow_smul_le (g : G) (v : T.V) (n : ℤ) :
    T.dist v (g ^ n • v) ≤ n.natAbs * T.dist v (g • v) := by
  rw [smul_vertex_def, smul_vertex_def, map_zpow]
  exact Aut.dist_zpow_smul_le (T.action g) (T.nonempty_path _ _) n

/-- A vertex `v` is moved by at most the displacement of another vertex `a` plus twice the
distance between them. -/
theorem dist_smul_le_dist_smul_add_two_mul_dist (g : G) (a v : T.V) :
    T.dist v (g • v) ≤ T.dist a (g • a) + 2 * T.dist v a := by
  have h₁ := dist_triangle (T.nonempty_path v a) (T.nonempty_path a (g • v))
  have h₂ := dist_triangle (T.nonempty_path a (g • a)) (T.nonempty_path (g • a) (g • v))
  rw [dist_smul, dist_comm a v] at h₂
  omega

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

/-- The integer powers of an elliptic element are elliptic. -/
theorem IsElliptic.zpow {g : G} (hg : T.IsElliptic g) (n : ℤ) : T.IsElliptic (g ^ n) := by
  obtain ⟨v, hv⟩ := isEllipticSubgroup_zpowers_iff.mpr hg
  exact ⟨v, hv (Subgroup.zpow_mem_zpowers g n)⟩

/-- The natural powers of an elliptic element are elliptic. -/
theorem IsElliptic.pow {g : G} (hg : T.IsElliptic g) (n : ℕ) : T.IsElliptic (g ^ n) := by
  simpa only [zpow_natCast] using hg.zpow n

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

variable (T) in
/-- The stabilizer of a dart fixes its source. -/
theorem stabilizer_dart_le_stabilizer_src (e : T.E) :
    stabilizer G e ≤ stabilizer G (T.src e) := fun g hg => by
  rw [mem_stabilizer_iff] at hg ⊢
  rw [← src_smul, hg]

variable (T) in
/-- The stabilizer of a dart fixes its target. -/
theorem stabilizer_dart_le_stabilizer_tgt (e : T.E) :
    stabilizer G e ≤ stabilizer G (T.tgt e) := fun g hg => by
  rw [mem_stabilizer_iff] at hg ⊢
  rw [← tgt_smul, hg]

/-- A dart and its reverse have the same stabilizer. -/
@[simp] theorem stabilizer_rev (e : T.E) : stabilizer G (T.rev e) = stabilizer G e := by
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, ← rev_smul, T.rev_injective.eq_iff]

variable (T) in
/-- Dart stabilizers are elliptic. -/
theorem isEllipticSubgroup_stabilizer_dart (e : T.E) : T.IsEllipticSubgroup (stabilizer G e) :=
  ⟨T.src e, T.stabilizer_dart_le_stabilizer_src e⟩

/-- If the vertex stabilizers of a `G`-tree are trivial, only the trivial subgroup is elliptic. -/
theorem isEllipticSubgroup_iff_eq_bot (h : ∀ v : T.V, stabilizer G v = ⊥) {H : Subgroup G} :
    T.IsEllipticSubgroup H ↔ H = ⊥ := by
  simp only [isEllipticSubgroup_iff, h, le_bot_iff, exists_const]

/-- In a `G`-tree with at most one vertex, `G` fixes the vertex. -/
@[simp] theorem stabilizer_eq_top_of_subsingleton [Subsingleton T.V] (v : T.V) :
    stabilizer G v = ⊤ :=
  eq_top_iff.mpr fun _ _ => mem_stabilizer_iff.mpr (Subsingleton.elim _ _)

variable (T) in
/-- Every subgroup is elliptic in a `G`-tree with at most one vertex. -/
theorem isEllipticSubgroup_of_subsingleton [Subsingleton T.V] (H : Subgroup G) :
    T.IsEllipticSubgroup H :=
  ⟨Classical.arbitrary T.V, le_top.trans_eq (stabilizer_eq_top_of_subsingleton _).symm⟩

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

variable (T) in
/-- A `G`-tree with at most one vertex has no darts. -/
theorem isEmpty_dart_of_subsingleton [Subsingleton T.V] : IsEmpty T.E :=
  (IsTree.isAcyclic _ T.isTree).isEmpty_dart_of_subsingleton

variable (T) in
/-- A `G`-tree without darts has at most one vertex. -/
theorem subsingleton_of_isEmpty_dart [IsEmpty T.E] : Subsingleton T.V :=
  ⟨fun a b => (T.nonempty_path a b).elim (eq_of_path_of_forall_src_eq_tgt _ isEmptyElim)⟩

variable (T) in
/-- A `G`-tree with at most one vertex is relative to all families of subgroups. -/
theorem isRelative_of_subsingleton [Subsingleton T.V] (𝒜 ℋ : Set (Subgroup G)) :
    T.IsRelative 𝒜 ℋ :=
  ⟨fun e => (T.isEmpty_dart_of_subsingleton.false e).elim,
    fun H _ => T.isEllipticSubgroup_of_subsingleton H⟩

/-- A `G`-tree with trivial vertex stabilizers is relative to any family of subgroups containing
the trivial subgroup and any family of trivial subgroups. -/
theorem isRelative_of_forall_stabilizer_eq_bot {𝒜 ℋ : Set (Subgroup G)} (h𝒜 : ⊥ ∈ 𝒜)
    (hℋ : ℋ ⊆ {⊥}) (h : ∀ v : T.V, stabilizer G v = ⊥) : T.IsRelative 𝒜 ℋ :=
  ⟨fun e => (isEllipticSubgroup_iff_eq_bot h).mp (T.isEllipticSubgroup_stabilizer_dart e) ▸ h𝒜,
    fun _ hH => (isEllipticSubgroup_iff_eq_bot h).mpr (hℋ hH)⟩

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

/-- `T` dominates `T'` exactly when every subgroup elliptic in `T` is elliptic in `T'`. -/
theorem dominates_iff_forall_isEllipticSubgroup :
    T.Dominates T' ↔ ∀ H : Subgroup G, T.IsEllipticSubgroup H → T'.IsEllipticSubgroup H :=
  ⟨fun h _ hH => h.isEllipticSubgroup hH,
    fun h => dominates_iff.mpr fun v => h _ (T.isEllipticSubgroup_stabilizer v)⟩

variable (T) in
/-- Every `G`-tree dominates a `G`-tree with at most one vertex. -/
theorem dominates_of_subsingleton [Subsingleton T'.V] : T.Dominates T' :=
  dominates_iff.mpr fun _ => T'.isEllipticSubgroup_of_subsingleton _

/-- A `G`-tree with at most one vertex dominates exactly the `G`-trees in which `G` is
elliptic. -/
theorem dominates_iff_of_subsingleton [Subsingleton T.V] :
    T.Dominates T' ↔ T'.IsEllipticSubgroup ⊤ := by
  rw [dominates_iff]
  exact ⟨fun h => stabilizer_eq_top_of_subsingleton (Classical.arbitrary T.V) ▸ h _,
    fun h _ => h.mono le_top⟩

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

/-- Two `G`-trees lie in the same deformation space exactly when they have the same elliptic
subgroups. -/
theorem sameDeformationSpace_iff_forall_isEllipticSubgroup :
    T.SameDeformationSpace T' ↔
      ∀ H : Subgroup G, T.IsEllipticSubgroup H ↔ T'.IsEllipticSubgroup H := by
  simp only [sameDeformationSpace_iff, dominates_iff_forall_isEllipticSubgroup, iff_def,
    forall_and]

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
  isEllipticSubgroup_of_subsingleton _ H

/-- Every element is elliptic in the one-vertex tree. -/
@[simp] theorem point_isElliptic (g : G) : (point.{u, v} G).IsElliptic g :=
  isEllipticSubgroup_zpowers_iff.mp (point_isEllipticSubgroup _)

variable (G) in
theorem point_isMinimal : (point.{u, v} G).IsMinimal :=
  isMinimal_of_subsingleton

variable (G) in
/-- The one-vertex tree is relative to all families of subgroups. -/
theorem point_isRelative (𝒜 ℋ : Set (Subgroup G)) : (point.{u, v} G).IsRelative 𝒜 ℋ :=
  isRelative_of_subsingleton _ 𝒜 ℋ

variable (T) in
/-- Every `G`-tree dominates the one-vertex tree. -/
theorem dominates_point : T.Dominates (point.{u', v'} G) :=
  T.dominates_of_subsingleton

/-- The one-vertex tree dominates exactly the `G`-trees in which `G` is elliptic. -/
theorem point_dominates_iff : (point.{u', v'} G).Dominates T ↔ T.IsEllipticSubgroup ⊤ :=
  dominates_iff_of_subsingleton

end GTree

end TauCeti
