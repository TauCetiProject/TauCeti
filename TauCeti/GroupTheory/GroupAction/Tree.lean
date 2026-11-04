/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Tree
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Group actions on trees

A `G`-tree is a Serre tree with an action of `G` by graph automorphisms *without inversions*: no
element maps a dart to its reverse. These are the actions studied in Bass–Serre theory, where the
quotient of a `G`-tree carries a graph of groups whose fundamental group is `G`.

An element of `G` is *elliptic* when it fixes a vertex and *hyperbolic* otherwise, and a subgroup
is elliptic when it fixes a vertex. Elements of `G` act by isometries of the path metric of the
tree, so the *translation length* `ℓ(g) = min_x d(x, g • x)` is a conjugacy invariant, and it
vanishes exactly on the elliptic elements.

Because a tree has at most one dart between two given vertices, an element fixes a dart exactly
when it fixes both endpoints, and it fixes every dart of the geodesic between two vertices it
fixes. In particular, an action without inversions never swaps the two endpoints of a dart: for a
dart of the segment, swapping its endpoints would invert it.

A `G`-tree `T` *dominates* `T'` when there is a `G`-equivariant map from the vertices of `T` to
those of `T'`; this is the combinatorial form of an equivariant map of geometric trees, which may
collapse edges or stretch them over edge paths. Domination holds exactly when every vertex
stabilizer of `T` is elliptic in `T'`. Two trees lie in the same *deformation space* when each
dominates the other. Every `G`-tree dominates the one-vertex tree, on which every subgroup is
elliptic; conversely the one-vertex tree dominates `T` exactly when `G` fixes a vertex of `T`.

## Main definitions

* `TauCeti.GTree G`: a Serre tree with an action of `G` without inversions.
* `TauCeti.GTree.IsElliptic`, `TauCeti.GTree.IsHyperbolic`: elements that fix a vertex, and those
  that do not.
* `TauCeti.GTree.IsEllipticSubgroup`: subgroups that fix a vertex.
* `TauCeti.GTree.translationLength`: the translation length `ℓ(g)`.
* `TauCeti.GTree.Dominates`, `TauCeti.GTree.SameDeformationSpace`: domination and the deformation
  space relation.
* `TauCeti.GTree.point`: the one-vertex `G`-tree.

## Main results

* `TauCeti.GTree.translationLength_eq_zero_iff`: `ℓ(g) = 0` if and only if `g` is elliptic.
* `TauCeti.GTree.translationLength_eq_of_isConj`: translation length is a conjugacy invariant.
* `TauCeti.GTree.stabilizer_dart`: the stabilizer of a dart is the intersection of the stabilizers
  of its endpoints.
* `TauCeti.GTree.smul_eq_self_of_mem_darts_geodesic`: an element fixing two vertices fixes the
  geodesic between them.
* `TauCeti.GTree.not_smul_src_eq_tgt_and_smul_tgt_eq_src`: no element swaps the endpoints of a dart.
* `TauCeti.GTree.dominates_iff`: `T` dominates `T'` if and only if every vertex stabilizer of `T`
  is elliptic in `T'`.

## References

* J.-P. Serre, *Trees*, Chapter I, §§3.1 and 6.1–6.4.
* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.1 and §2.2.
-/

public section

universe u v w x

namespace TauCeti

open MulAction

/-- A `G`-tree: a Serre tree with an action of `G` by graph automorphisms without inversions. -/
structure GTree (G : Type*) [Group G] where
  /-- The underlying Serre graph. -/
  graph : SerreGraph.{u, v}
  /-- The underlying graph is a tree. -/
  isTree : graph.IsTree
  /-- The action on the vertices. -/
  [mulActionV : MulAction G graph.V]
  /-- The action on the darts. -/
  [mulActionE : MulAction G graph.E]
  /-- The action preserves the source of a dart. -/
  src_smul : ∀ (g : G) (e : graph.E), graph.src (g • e) = g • graph.src e
  /-- The action commutes with reversal. -/
  rev_smul : ∀ (g : G) (e : graph.E), graph.rev (g • e) = g • graph.rev e
  /-- The action has no inversions: no element maps a dart to its reverse. -/
  smul_ne_rev : ∀ (g : G) (e : graph.E), g • e ≠ graph.rev e

namespace GTree

attribute [instance] mulActionV mulActionE

attribute [simp] src_smul rev_smul

variable {G : Type*} [Group G] (T : GTree.{u, v} G)

instance : Nonempty T.graph.V := (T.graph.connected_iff.mp T.isTree.connected).1

/-- The action preserves the target of a dart. -/
@[simp] theorem tgt_smul (g : G) (e : T.graph.E) : T.graph.tgt (g • e) = g • T.graph.tgt e := by
  rw [SerreGraph.tgt_def, T.rev_smul, T.src_smul, SerreGraph.tgt_def]

/-- The graph automorphism by which an element acts. -/
def smulHom (g : G) : T.graph.Hom T.graph where
  mapV x := g • x
  mapE e := g • e
  map_src e := T.src_smul g e
  map_rev e := (T.rev_smul g e).symm

@[simp] theorem smulHom_mapV (g : G) (x : T.graph.V) : (T.smulHom g).mapV x = g • x := (rfl)

@[simp] theorem smulHom_mapE (g : G) (e : T.graph.E) : (T.smulHom g).mapE e = g • e := (rfl)

/-- Every element of `G` acts by an isometry of the tree. -/
@[simp] theorem dist_smul (g : G) (x y : T.graph.V) :
    T.isTree.dist (g • x) (g • y) = T.isTree.dist x y :=
  T.isTree.dist_map T.isTree (T.smulHom g) (MulAction.injective g) x y

/-! ### Fixed points -/

/-- An element fixes a dart exactly when it fixes both of its endpoints. -/
theorem smul_eq_self_iff (g : G) (e : T.graph.E) :
    g • e = e ↔ g • T.graph.src e = T.graph.src e ∧ g • T.graph.tgt e = T.graph.tgt e := by
  refine ⟨fun h => ?_, fun ⟨hs, ht⟩ => ?_⟩
  · rw [← T.src_smul, ← T.tgt_smul, h]
    exact ⟨rfl, rfl⟩
  · exact T.isTree.isAcyclic.eq_of_src_eq_of_tgt_eq (by rw [T.src_smul, hs])
      (by rw [T.tgt_smul, ht])

/-- The stabilizer of a dart is the intersection of the stabilizers of its endpoints. -/
theorem stabilizer_dart (e : T.graph.E) :
    stabilizer G e = stabilizer G (T.graph.src e) ⊓ stabilizer G (T.graph.tgt e) := by
  ext g
  simp only [mem_stabilizer_iff, Subgroup.mem_inf, T.smul_eq_self_iff]

/-- An element fixing two vertices fixes every dart of the geodesic between them. -/
theorem smul_eq_self_of_mem_darts_geodesic {g : G} {a b : T.graph.V} (ha : g • a = a)
    (hb : g • b = b) {e : T.graph.E}
    (he : e ∈ SerreGraph.Path.darts T.graph (T.isTree.geodesic a b)) : g • e = e := by
  have hmap := T.isTree.darts_geodesic_map T.isTree (T.smulHom g) (MulAction.injective g) a b
  rw [smulHom_mapV, smulHom_mapV, ha, hb] at hmap
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
  have hie := List.map_eq_iff.mp hmap.symm i
  rw [hi, Option.map_some, Option.some_inj] at hie
  exact (smulHom_mapE T g e).symm.trans hie.symm

/-- An action without inversions never swaps the two endpoints of a dart. -/
theorem not_smul_src_eq_tgt_and_smul_tgt_eq_src (g : G) (e : T.graph.E) :
    ¬(g • T.graph.src e = T.graph.tgt e ∧ g • T.graph.tgt e = T.graph.src e) := by
  rintro ⟨hs, ht⟩
  refine T.smul_ne_rev g e (T.isTree.isAcyclic.eq_of_src_eq_of_tgt_eq ?_ ?_)
  · rw [T.src_smul, hs, SerreGraph.src_rev]
  · rw [T.tgt_smul, ht, SerreGraph.tgt_rev]

/-! ### Elliptic and hyperbolic elements -/

/-- An element is elliptic when it fixes a vertex. -/
def IsElliptic (g : G) : Prop := ∃ x : T.graph.V, g • x = x

/-- An element is hyperbolic when it is not elliptic, that is, when it fixes no vertex. -/
def IsHyperbolic (g : G) : Prop := ¬T.IsElliptic g

/-- A subgroup is elliptic when it fixes a vertex. -/
def IsEllipticSubgroup (H : Subgroup G) : Prop := ∃ x : T.graph.V, H ≤ stabilizer G x

variable {T}

theorem isElliptic_iff {g : G} : T.IsElliptic g ↔ ∃ x : T.graph.V, g • x = x := Iff.rfl

theorem isHyperbolic_iff {g : G} : T.IsHyperbolic g ↔ ∀ x : T.graph.V, g • x ≠ x := by
  simp [IsHyperbolic, IsElliptic]

theorem not_isHyperbolic_iff {g : G} : ¬T.IsHyperbolic g ↔ T.IsElliptic g :=
  not_not

theorem isEllipticSubgroup_iff {H : Subgroup G} :
    T.IsEllipticSubgroup H ↔ ∃ x : T.graph.V, H ≤ stabilizer G x := Iff.rfl

@[simp] theorem isElliptic_one : T.IsElliptic 1 :=
  ⟨Classical.arbitrary _, one_smul G _⟩

@[simp] theorem isElliptic_inv {g : G} : T.IsElliptic g⁻¹ ↔ T.IsElliptic g := by
  simp only [isElliptic_iff, inv_smul_eq_iff]
  exact exists_congr fun _ => eq_comm

/-- Vertex stabilizers are elliptic. -/
theorem isEllipticSubgroup_stabilizer (x : T.graph.V) : T.IsEllipticSubgroup (stabilizer G x) :=
  ⟨x, le_rfl⟩

theorem IsEllipticSubgroup.mono {H K : Subgroup G} (hK : T.IsEllipticSubgroup K) (hHK : H ≤ K) :
    T.IsEllipticSubgroup H :=
  let ⟨x, hx⟩ := hK
  ⟨x, hHK.trans hx⟩

/-- Every element of an elliptic subgroup is elliptic. -/
theorem IsEllipticSubgroup.isElliptic {H : Subgroup G} (hH : T.IsEllipticSubgroup H) {g : G}
    (hg : g ∈ H) : T.IsElliptic g :=
  let ⟨x, hx⟩ := hH
  ⟨x, hx hg⟩

/-- An element is elliptic exactly when the cyclic subgroup it generates is elliptic. -/
@[simp] theorem isEllipticSubgroup_zpowers_iff {g : G} :
    T.IsEllipticSubgroup (Subgroup.zpowers g) ↔ T.IsElliptic g := by
  simp only [isEllipticSubgroup_iff, Subgroup.zpowers_le, mem_stabilizer_iff, isElliptic_iff]

/-- Ellipticity is invariant under conjugation. -/
theorem IsElliptic.conj {g : G} (hg : T.IsElliptic g) (c : G) : T.IsElliptic (c * g * c⁻¹) := by
  obtain ⟨x, hx⟩ := hg
  exact ⟨c • x, by rw [mul_smul, mul_smul, inv_smul_smul, hx]⟩

/-! ### Translation length -/

variable (T) in
/-- The translation length `ℓ(g)` of an element: the least distance by which it moves a vertex. -/
noncomputable def translationLength (g : G) : ℕ := ⨅ x : T.graph.V, T.isTree.dist x (g • x)

theorem translationLength_le (g : G) (x : T.graph.V) :
    T.translationLength g ≤ T.isTree.dist x (g • x) :=
  ciInf_le (OrderBot.bddBelow _) x

theorem le_translationLength_iff {g : G} {n : ℕ} :
    n ≤ T.translationLength g ↔ ∀ x : T.graph.V, n ≤ T.isTree.dist x (g • x) :=
  le_ciInf_iff (OrderBot.bddBelow _)

/-- The translation length is attained at some vertex. -/
theorem exists_dist_eq_translationLength (g : G) :
    ∃ x : T.graph.V, T.isTree.dist x (g • x) = T.translationLength g :=
  ciInf_mem _

/-- An element has translation length zero exactly when it is elliptic. -/
@[simp] theorem translationLength_eq_zero_iff {g : G} :
    T.translationLength g = 0 ↔ T.IsElliptic g := by
  refine ⟨fun h => ?_, fun ⟨x, hx⟩ => ?_⟩
  · obtain ⟨x, hx⟩ := exists_dist_eq_translationLength (T := T) g
    exact ⟨x, ((T.isTree.dist_eq_zero_iff).mp (hx.trans h)).symm⟩
  · exact Nat.le_zero.mp ((translationLength_le g x).trans_eq (by rw [hx, T.isTree.dist_self]))

/-- An element has positive translation length exactly when it is hyperbolic. -/
theorem translationLength_pos_iff {g : G} : 0 < T.translationLength g ↔ T.IsHyperbolic g := by
  rw [Nat.pos_iff_ne_zero, ne_eq, translationLength_eq_zero_iff, IsHyperbolic]

@[simp] theorem translationLength_one : T.translationLength 1 = 0 :=
  translationLength_eq_zero_iff.mpr isElliptic_one

private theorem translationLength_conj_le (c g : G) :
    T.translationLength (c * g * c⁻¹) ≤ T.translationLength g :=
  le_translationLength_iff.mpr fun x => (translationLength_le _ (c • x)).trans_eq <| by
    rw [mul_smul, mul_smul, inv_smul_smul, dist_smul]

/-- Translation length is invariant under conjugation. -/
@[simp] theorem translationLength_conj (c g : G) :
    T.translationLength (c * g * c⁻¹) = T.translationLength g := by
  refine le_antisymm (translationLength_conj_le c g) ?_
  have h := translationLength_conj_le (T := T) c⁻¹ (c * g * c⁻¹)
  rwa [inv_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] at h

/-- Conjugate elements have the same translation length. -/
theorem translationLength_eq_of_isConj {g g' : G} (h : IsConj g g') :
    T.translationLength g = T.translationLength g' := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact (translationLength_conj c g).symm

private theorem translationLength_inv_le (g : G) :
    T.translationLength g⁻¹ ≤ T.translationLength g :=
  le_translationLength_iff.mpr fun x => (translationLength_le _ (g • x)).trans_eq <| by
    rw [inv_smul_smul, T.isTree.dist_comm]

@[simp] theorem translationLength_inv (g : G) : T.translationLength g⁻¹ = T.translationLength g :=
  le_antisymm (translationLength_inv_le g) (by simpa using translationLength_inv_le (T := T) g⁻¹)

/-! ### Domination and deformation spaces -/

variable (T) in
/-- A `G`-tree `T` dominates `T'` when there is a `G`-equivariant map from the vertices of `T` to
those of `T'`. -/
def Dominates (T' : GTree.{w, x} G) : Prop := Nonempty (T.graph.V →[G] T'.graph.V)

variable (T) in
/-- Two `G`-trees lie in the same deformation space when each dominates the other. -/
def SameDeformationSpace (T' : GTree.{w, x} G) : Prop := T.Dominates T' ∧ T'.Dominates T

/-- A `G`-tree `T` dominates `T'` exactly when every vertex stabilizer of `T` is elliptic in `T'`.
-/
theorem dominates_iff {T' : GTree.{w, x} G} :
    T.Dominates T' ↔ ∀ x : T.graph.V, T'.IsEllipticSubgroup (stabilizer G x) := by
  refine ⟨fun ⟨f⟩ x => ⟨f x, fun g hg => ?_⟩, fun hS => ?_⟩
  · rw [mem_stabilizer_iff] at hg ⊢
    rw [← f.map_smul, hg]
  · choose y hy using hS
    -- `r x` is a chosen representative of the orbit of `x`, and `c x • r x = x`.
    let r : T.graph.V → T.graph.V := fun x =>
      (Quotient.mk'' x : Quotient (orbitRel G T.graph.V)).out
    have hr : ∀ x, ∃ c : G, c • r x = x := fun x => by
      obtain ⟨c, hc⟩ := orbitRel_apply.mp (Quotient.mk_out' (s₁ := orbitRel G T.graph.V) x)
      exact ⟨c⁻¹, by rw [inv_smul_eq_iff]; exact hc.symm⟩
    choose c hc using hr
    have hrs : ∀ (g : G) x, r (g • x) = r x := fun g x =>
      congrArg Quotient.out (Quotient.sound (orbitRel_apply.mpr (mem_orbit x g)))
    refine ⟨⟨fun x => c x • y (r x), fun g x => ?_⟩⟩
    have hgx : c (g • x) • r x = g • x := by simpa only [hrs] using hc (g • x)
    have hk : (c x)⁻¹ * g⁻¹ * c (g • x) ∈ stabilizer G (r x) := by
      rw [mem_stabilizer_iff, mul_smul, mul_smul, hgx, inv_smul_smul, inv_smul_eq_iff, hc]
    have hky := mem_stabilizer_iff.mp (hy (r x) hk)
    rw [mul_smul, mul_smul, inv_smul_eq_iff, inv_smul_eq_iff] at hky
    simp only [id, hrs, hky, smul_smul]

theorem Dominates.refl : T.Dominates T := ⟨MulActionHom.id G⟩

theorem Dominates.trans {T' : GTree.{w, x} G} {T'' : GTree G} (h : T.Dominates T')
    (h' : T'.Dominates T'') : T.Dominates T'' :=
  let ⟨f⟩ := h
  let ⟨f'⟩ := h'
  ⟨f'.comp f⟩

/-- Ellipticity of a subgroup passes along domination. -/
theorem IsEllipticSubgroup.of_dominates {T' : GTree.{w, x} G} (h : T.Dominates T')
    {H : Subgroup G} (hH : T.IsEllipticSubgroup H) : T'.IsEllipticSubgroup H :=
  let ⟨x, hx⟩ := hH
  (dominates_iff.mp h x).mono hx

theorem SameDeformationSpace.refl : T.SameDeformationSpace T :=
  ⟨Dominates.refl, Dominates.refl⟩

theorem SameDeformationSpace.symm {T' : GTree.{w, x} G} (h : T.SameDeformationSpace T') :
    T'.SameDeformationSpace T :=
  ⟨h.2, h.1⟩

theorem SameDeformationSpace.trans {T' : GTree.{w, x} G} {T'' : GTree G}
    (h : T.SameDeformationSpace T') (h' : T'.SameDeformationSpace T'') :
    T.SameDeformationSpace T'' :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

variable (G) in
/-- Lying in the same deformation space is an equivalence relation. -/
theorem sameDeformationSpace_equivalence :
    Equivalence (SameDeformationSpace : GTree.{u, v} G → GTree.{u, v} G → Prop) :=
  ⟨fun _ => .refl, .symm, .trans⟩

/-! ### The one-vertex tree -/

variable (G) in
/-- The one-vertex `G`-tree, with the trivial action. -/
def point : GTree.{u, v} G where
  graph := SerreGraph.point
  isTree := SerreGraph.single_vertex_isTree
  mulActionV := { smul _ x := x, one_smul _ := rfl, mul_smul _ _ _ := rfl }
  mulActionE := { smul _ e := e, one_smul _ := rfl, mul_smul _ _ _ := rfl }
  src_smul _ e := e.elim
  rev_smul _ e := e.elim
  smul_ne_rev _ e := e.elim

instance : Subsingleton (point.{u, v} G).graph.V := inferInstanceAs (Subsingleton PUnit)

/-- Every subgroup is elliptic in the one-vertex tree. -/
theorem point_isEllipticSubgroup (H : Subgroup G) : (point.{u, v} G).IsEllipticSubgroup H :=
  ⟨Classical.arbitrary _, fun _ _ => Subsingleton.elim _ _⟩

/-- Every `G`-tree dominates the one-vertex tree. -/
theorem dominates_point : T.Dominates (point.{w, x} G) :=
  dominates_iff.mpr fun _ => point_isEllipticSubgroup _

/-- The one-vertex tree dominates `T` exactly when `G` fixes a vertex of `T`. -/
theorem point_dominates_iff : (point.{w, x} G).Dominates T ↔ T.IsEllipticSubgroup ⊤ := by
  rw [dominates_iff]
  refine ⟨fun h => h (Classical.arbitrary _) |>.mono fun g _ => ?_, fun h _ => h.mono le_top⟩
  exact mem_stabilizer_iff.mpr (Subsingleton.elim _ _)

end GTree

end TauCeti
