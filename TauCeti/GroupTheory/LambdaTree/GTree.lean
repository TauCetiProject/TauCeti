/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Axis
public import TauCeti.GroupTheory.GTree.Cayley
public import TauCeti.GroupTheory.LambdaTree.Chiswell
public import TauCeti.GroupTheory.LambdaTree.SerreGraph
public import TauCeti.GroupTheory.LyndonLength.FreeGroup

/-!
# Simplicial `G`-trees and isometric actions on `ℤ`-trees

A `G`-tree (`TauCeti.GTree`) is a simplicial Serre tree equipped with an action of `G` by graph
automorphisms without edge inversions. Equipped with its integer-valued path metric, the vertex set
of a `G`-tree is a `ℤ`-tree on which `G` acts by isometries without metric inversions
(`TauCeti.GTree.isTree_pathMetric`, `TauCeti.GTree.isIsometricAction_pathMetric`,
`TauCeti.GTree.not_lambdaMetric_isInversion`), and the two notions of elliptic and hyperbolic
elements agree.

Conversely, an isometric action of `G` on a `ℤ`-tree `(X, d)` induces an action of `G` by graph
automorphisms on the unit-distance Serre graph `d.toSerreGraph`
(`TauCeti.LambdaMetric.IsIsometricAction.toSerreGraphAut`). An element `g : G` inverts a dart of
`d.toSerreGraph` if and only if it is a metric inversion on `X`, meaning `g` fixes no point while
`g ^ 2` does (`TauCeti.LambdaMetric.IsTree.exists_toSerreGraph_dart_rev_iff`): if `g ^ 2` fixes `x`
and `g` fixes no point, `g` reverses the geodesic `[x, g • x]`, which therefore has odd length
`2 k + 1` and middle dart exchanged with its reverse by `g`. Consequently an isometric `ℤ`-tree
action without metric inversions yields a `G`-tree (`TauCeti.LambdaMetric.IsTree.toGTree`) whose
path metric recovers `d` along `TauCeti.LambdaMetric.IsTree.toGTreeVertexEquiv`.

Combined with Chiswell's construction (`TauCeti.LyndonLength.exists_isFree_iff`), a group `G`
admits a free `ℤ`-valued Lyndon length function if and only if it acts freely (without inversions)
on a simplicial `G`-tree (`TauCeti.LyndonLength.exists_isFree_int_iff`). For the free group
`FreeGroup α`, the based length function of the Cayley `G`-tree at the identity vertex
`TauCeti.GTree.cayleyBaseVertex` is word length `TauCeti.LyndonLength.freeGroupNorm`, and
Chiswell's equivariant embedding identifies the Chiswell `ℤ`-tree of `freeGroupNorm` with the
Cayley tree (`TauCeti.GTree.basedLength_cayley_one`,
`TauCeti.GTree.bijective_chiswellEmbed_cayley`).

## Main definitions

* `TauCeti.GTree.pathMetric`: the `ℤ`-valued path metric on the vertices of a `G`-tree.
* `TauCeti.GTree.cayleyBaseVertex`: the identity vertex of the Cayley `G`-tree `GTree.cayley α`.
* `TauCeti.LambdaMetric.IsIsometricAction.toSerreGraphAut`: the action on `d.toSerreGraph` induced
  by an isometric action on `(X, d)`.
* `TauCeti.LambdaMetric.IsTree.toGTree`: the `G`-tree attached to an inversion-free isometric
  action on a `ℤ`-tree, with vertex coordinate `TauCeti.LambdaMetric.IsTree.toGTreeVertexEquiv`.
* `TauCeti.LyndonLength.IsFree.chiswellGTree`: the Chiswell `G`-tree of a free `ℤ`-valued Lyndon
  length function, with base vertex `TauCeti.LyndonLength.IsFree.chiswellGTreeBase`.

## Main results

* `TauCeti.GTree.not_lambdaMetric_isInversion`, `TauCeti.GTree.lambdaMetric_isHyperbolic_iff`:
  a `G`-tree has no metric inversions, and metric hyperbolicity agrees with `GTree.IsHyperbolic`.
* `TauCeti.GTree.basedLength_cayley_one`, `TauCeti.GTree.bijective_chiswellEmbed_cayley`:
  the based length function of `GTree.cayley α` at `1` is `freeGroupNorm α`, and Chiswell's
  embedding onto `GTree.cayley α` is bijective.
* `TauCeti.LambdaMetric.IsTree.exists_toSerreGraph_dart_rev_iff`: `g` inverts a dart of
  `d.toSerreGraph` if and only if `g` is a metric inversion on `(X, d)`.
* `TauCeti.LyndonLength.exists_isFree_int_iff`,
  `TauCeti.LyndonLength.exists_isFree_int_iff_stabilizer_eq_bot`: `G` has a free `ℤ`-valued Lyndon
  length function if and only if `G` acts freely on a simplicial `G`-tree.

## References

* I. Chiswell, *Introduction to Λ-trees*, World Scientific, 2001, §§2.1 and 3.1.
* R. C. Lyndon, *Length functions in groups*, Math. Scand. 12 (1963), 209–234.
* J.-P. Serre, *Trees*, Chapter I, §§2–3 and §6.
-/

public section

universe u v w

namespace TauCeti

/-! ### From a `G`-tree to an inversion-free `ℤ`-tree action -/

namespace GTree

variable {G : Type w} [Group G] (T : GTree.{u, v} G)

/-- The underlying graph of a `G`-tree is preconnected. -/
theorem preconnected : T.Preconnected :=
  (T.connected_iff.1 (SerreGraph.IsTree.connected _ T.isTree)).2

/-- The integer-valued path metric on the vertices of a `G`-tree. -/
noncomputable def pathMetric : LambdaMetric ℤ T.V :=
  T.preconnected.pathMetric

@[simp]
theorem pathMetric_apply (a b : T.V) : T.pathMetric a b = T.dist a b :=
  T.preconnected.pathMetric_apply a b

/-- The vertex set of a `G`-tree, with its path metric, is a `ℤ`-tree. -/
theorem isTree_pathMetric : T.pathMetric.IsTree :=
  T.isTree.isTree_pathMetric

/-- A group `G` acts by isometries for the path metric of any `G`-tree. -/
theorem isIsometricAction_pathMetric : T.pathMetric.IsIsometricAction G :=
  T.pathMetric.isIsometricAction_iff.2 fun g a b => by simp

@[simp]
theorem lambdaMetric_isElliptic_iff {g : G} :
    LambdaMetric.IsElliptic T.V g ↔ T.IsElliptic g :=
  LambdaMetric.isElliptic_iff.trans T.isElliptic_iff.symm

/-- An action on a `G`-tree has no metric inversions: if `g ^ 2` fixes a vertex, so does `g`. -/
theorem not_lambdaMetric_isInversion (g : G) : ¬LambdaMetric.IsInversion T.V g := by
  intro h
  obtain ⟨hne, hsq⟩ := LambdaMetric.isInversion_iff.1 h
  rw [T.lambdaMetric_isElliptic_iff] at hne hsq
  exact hne ((T.isElliptic_pow_iff (n := 2)).1 hsq |>.resolve_right (by decide))

@[simp]
theorem lambdaMetric_isHyperbolic_iff {g : G} :
    LambdaMetric.IsHyperbolic T.V g ↔ T.IsHyperbolic g := by
  have hT : ¬T.IsElliptic g ↔ T.IsHyperbolic g := not_iff_comm.1 T.not_isHyperbolic_iff
  refine LambdaMetric.isHyperbolic_iff.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact hT.1 (T.lambdaMetric_isElliptic_iff.not.1 h.1)
  · have hne : ¬LambdaMetric.IsElliptic T.V g := T.lambdaMetric_isElliptic_iff.not.2 (hT.2 h)
    exact ⟨hne, fun hsq =>
      T.not_lambdaMetric_isInversion g (LambdaMetric.isInversion_iff.2 ⟨hne, hsq⟩)⟩

/-- Metric freeness of the vertex action of a `G`-tree means that every nontrivial element is
hyperbolic. -/
theorem lambdaMetric_isFreeAction_iff :
    LambdaMetric.IsFreeAction G T.V ↔ ∀ g : G, g ≠ 1 → T.IsHyperbolic g :=
  LambdaMetric.isFreeAction_iff.trans (forall₂_congr fun _ _ => T.lambdaMetric_isHyperbolic_iff)

/-- Metric freeness of the vertex action of a `G`-tree is equivalent to triviality of all vertex
stabilizers. -/
theorem lambdaMetric_isFreeAction_iff_stabilizer_eq_bot :
    LambdaMetric.IsFreeAction G T.V ↔ ∀ v : T.V, MulAction.stabilizer G v = ⊥ := by
  rw [T.lambdaMetric_isFreeAction_iff]
  simp only [T.isHyperbolic_iff, Subgroup.eq_bot_iff_forall, MulAction.mem_stabilizer_iff]
  exact ⟨fun h v g hg => Classical.not_not.1 fun hne => h g hne v hg,
    fun h g hne v hgv => hne (h v g hgv)⟩

/-! ### Compatibility with the Cayley tree of a free group -/

/-- The identity vertex `1` of the Cayley `G`-tree of `FreeGroup α`. -/
def cayleyBaseVertex (α : Type u) : (cayley α).V :=
  SerreGraph.cayleyVertexEquiv.symm 1

@[simp]
theorem cayleyVertexEquiv_cayleyBaseVertex (α : Type u) :
    SerreGraph.cayleyVertexEquiv (cayleyBaseVertex α) = 1 :=
  Equiv.apply_symm_apply _ 1

/-- The based length function of the Cayley `G`-tree of `FreeGroup α` at the identity vertex is
word length `LyndonLength.freeGroupNorm α`. -/
@[simp]
theorem basedLength_cayley_one {α : Type u} [DecidableEq α] :
    (cayley α).isTree_pathMetric.basedLength (cayley α).isIsometricAction_pathMetric
      (cayleyBaseVertex α) = LyndonLength.freeGroupNorm α := by
  ext g
  rw [LambdaMetric.IsTree.basedLength_apply, (cayley α).pathMetric_apply,
    LyndonLength.freeGroupNorm_apply, Nat.cast_inj]
  have hd := SerreGraph.cayley_dist (cayleyBaseVertex α) (g • cayleyBaseVertex α)
  rw [cayleyVertexEquiv_cayleyBaseVertex, cayleyVertexEquiv_cayley_smul,
    cayleyVertexEquiv_cayleyBaseVertex, inv_one, one_mul, mul_one] at hd
  exact hd

/-- Chiswell's equivariant isometric embedding maps the Chiswell `ℤ`-tree of
`LyndonLength.freeGroupNorm α` bijectively onto the vertex set of the Cayley tree `cayley α`. -/
theorem bijective_chiswellEmbed_cayley {α : Type u} [DecidableEq α] :
    Function.Bijective
      (LyndonLength.chiswellEmbed (cayley α).isTree_pathMetric
        (cayley α).isIsometricAction_pathMetric (cayleyBaseVertex α)
        basedLength_cayley_one) := by
  refine ⟨LyndonLength.chiswellEmbed_injective _ _ _ _, fun v => ?_⟩
  rw [← Set.mem_range, LyndonLength.range_chiswellEmbed]
  refine Set.mem_iUnion.2 ⟨SerreGraph.cayleyVertexEquiv v, ?_⟩
  have hv : SerreGraph.cayleyVertexEquiv v • cayleyBaseVertex α = v :=
    SerreGraph.cayleyVertexEquiv.injective (by simp)
  rw [hv]
  exact (cayley α).isTree_pathMetric.right_mem_segment _ v

end GTree

/-! ### From an inversion-free `ℤ`-tree action to a `G`-tree -/

namespace LambdaMetric

open Set

section ToSerreGraphAut

variable {G : Type w} {X : Type u} [Group G] [MulAction G X] {d : LambdaMetric ℤ X}

private def smulUnitDistEquiv (hG : d.IsIsometricAction G) (g : G) :
    { p : X × X // d p.1 p.2 = 1 } ≃ { p : X × X // d p.1 p.2 = 1 } where
  toFun p := ⟨(g • p.1.1, g • p.1.2), by rw [hG.dist_smul_smul, p.2]⟩
  invFun p := ⟨(g⁻¹ • p.1.1, g⁻¹ • p.1.2), by rw [hG.dist_smul_smul, p.2]⟩
  left_inv p := Subtype.ext (Prod.ext (inv_smul_smul g p.1.1) (inv_smul_smul g p.1.2))
  right_inv p := Subtype.ext (Prod.ext (smul_inv_smul g p.1.1) (smul_inv_smul g p.1.2))

/-- The automorphism of `d.toSerreGraph` induced by an element `g : G` of an isometric action. -/
def IsIsometricAction.toSerreGraphIso (hG : d.IsIsometricAction G) (g : G) :
    d.toSerreGraph.Aut where
  equivV := d.toSerreGraphVertexEquiv.trans
    ((MulAction.toPerm g).trans d.toSerreGraphVertexEquiv.symm)
  equivE := d.toSerreGraphDartEquiv.trans
    ((smulUnitDistEquiv hG g).trans d.toSerreGraphDartEquiv.symm)
  map_src e := d.toSerreGraphVertexEquiv.injective (by simp [smulUnitDistEquiv])
  map_rev e := d.toSerreGraphDartEquiv.injective (Subtype.ext (by simp [smulUnitDistEquiv]))

/-- An isometric action of `G` on a `ℤ`-metric space `(X, d)` induces a group action by graph
automorphisms on the unit-distance Serre graph `d.toSerreGraph`. -/
def IsIsometricAction.toSerreGraphAut (hG : d.IsIsometricAction G) :
    G →* d.toSerreGraph.Aut where
  toFun := hG.toSerreGraphIso
  map_one' := SerreGraph.Iso.ext
    (fun v => d.toSerreGraphVertexEquiv.injective (by simp [IsIsometricAction.toSerreGraphIso]))
    (fun e => d.toSerreGraphDartEquiv.injective <| Subtype.ext <| by
      simp [IsIsometricAction.toSerreGraphIso, smulUnitDistEquiv])
  map_mul' g h := SerreGraph.Iso.ext
    (fun v => d.toSerreGraphVertexEquiv.injective <| by
      simp [IsIsometricAction.toSerreGraphIso, mul_smul])
    (fun e => d.toSerreGraphDartEquiv.injective <| Subtype.ext <| by
      simp [IsIsometricAction.toSerreGraphIso, smulUnitDistEquiv, mul_smul])

@[simp]
theorem IsIsometricAction.toSerreGraphVertexEquiv_smul (hG : d.IsIsometricAction G) (g : G)
    (v : d.toSerreGraph.V) :
    d.toSerreGraphVertexEquiv (hG.toSerreGraphAut g • v) = g • d.toSerreGraphVertexEquiv v := by
  simp [SerreGraph.Aut.smul_vertex_def, IsIsometricAction.toSerreGraphAut,
    IsIsometricAction.toSerreGraphIso]

@[simp]
theorem IsIsometricAction.toSerreGraphDartEquiv_smul (hG : d.IsIsometricAction G) (g : G)
    (e : d.toSerreGraph.E) :
    (d.toSerreGraphDartEquiv (hG.toSerreGraphAut g • e)).1 =
      (g • (d.toSerreGraphDartEquiv e).1.1, g • (d.toSerreGraphDartEquiv e).1.2) := by
  simp [SerreGraph.Aut.smul_dart_def, IsIsometricAction.toSerreGraphAut,
    IsIsometricAction.toSerreGraphIso, smulUnitDistEquiv]

/-- In a `ℤ`-tree `(X, d)` with an isometric action of `G`, an element `g` reverses a dart of
`d.toSerreGraph` if and only if `g` is a metric inversion on `X`. -/
theorem IsTree.exists_toSerreGraph_dart_rev_iff (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (g : G) :
    (∃ e : d.toSerreGraph.E, hG.toSerreGraphAut g • e = d.toSerreGraph.rev e) ↔
      IsInversion X g := by
  rw [isInversion_iff, isElliptic_iff, isElliptic_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨e, hrev⟩
    have hval := congrArg (fun f => (d.toSerreGraphDartEquiv f).1) hrev
    rw [hG.toSerreGraphDartEquiv_smul, toSerreGraphDartEquiv_rev] at hval
    rcases heq : d.toSerreGraphDartEquiv e with ⟨⟨u, v⟩, huv⟩
    rw [heq] at hval
    have hgu : g • u = v := congrArg Prod.fst hval
    have hgv : g • v = u := congrArg Prod.snd hval
    refine ⟨fun ⟨z, hz⟩ => ?_, ⟨u, by rw [pow_two, mul_smul, hgu, hgv]⟩⟩
    have hzv : d z v = d z u := by rw [← hz, ← hgu, hG.dist_smul_smul, hz]
    obtain ⟨k, hk⟩ := hd.even_dist_add_dist_sub_dist z u v
    rw [hzv, huv] at hk
    omega
  · rintro ⟨hne, x, hx⟩
    obtain ⟨f, hf0, hfD, hf, hσ⟩ := d.isSegment_iff.1 (hd.isSegment_segment x (g • x))
    set D := d x (g • x)
    have hDpos : 0 < D := d.pos_iff.2 fun h => hne ⟨x, h.symm⟩
    have hrev (t : ℤ) (ht : t ∈ Icc 0 D) : g • f t = f (D - t) :=
      hd.smul_apply_of_sq_smul_eq hG hx hf0 hfD hf hσ ht
    -- If `D` were even, `f (D / 2)` would be fixed by `g`; hence `D = 2 * k + 1` is odd.
    set k := D / 2
    have hodd : D = 2 * k + 1 := by
      rcases Int.even_or_odd' D with ⟨m, hm | hm⟩
      · exfalso
        have hm0 : m ∈ Icc 0 D := ⟨by omega, by omega⟩
        have hDm : D - m = m := by omega
        have hfix := hrev m hm0
        rw [hDm] at hfix
        exact hne ⟨f m, hfix⟩
      · omega
    have hk : k ∈ Icc 0 D := ⟨by omega, by omega⟩
    have hk1 : k + 1 ∈ Icc 0 D := ⟨by omega, by omega⟩
    have huv : d (f k) (f (k + 1)) = 1 := by
      rw [hf.dist_eq hk hk1, sub_add_cancel_left, abs_neg, abs_one]
    let e : d.toSerreGraph.E := d.toSerreGraphDartEquiv.symm ⟨(f k, f (k + 1)), huv⟩
    have hDk : D - k = k + 1 := by omega
    have hDk1 : D - (k + 1) = k := by omega
    refine ⟨e, d.toSerreGraphDartEquiv.injective (Subtype.ext ?_)⟩
    rw [hG.toSerreGraphDartEquiv_smul, toSerreGraphDartEquiv_rev]
    simp only [e, Equiv.apply_symm_apply]
    exact Prod.ext ((hrev k hk).trans (congrArg f hDk))
      ((hrev (k + 1) hk1).trans (congrArg f hDk1))

/-- An inversion-free isometric action of `G` on a `ℤ`-tree `(X, d)` defines a simplicial `G`-tree
with vertex set `X` and unit-distance darts. The body is exposed so that `toGTreeVertexEquiv`
compiles under the `module` code generator; use `toGTreeVertexEquiv` to access vertices. -/
@[expose] def IsTree.toGTree (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) : GTree.{u, u} G where
  toSerreGraph := d.toSerreGraph
  isTree := hd.isTree_toSerreGraph
  action := hG.toSerreGraphAut
  action_smul_ne_rev g e he :=
    hinv g ((hd.exists_toSerreGraph_dart_rev_iff hG g).1 ⟨e, by rwa [SerreGraph.Aut.smul_dart_def]⟩)

/-- The vertices of `hd.toGTree hG hinv` are identified with `X`. -/
def IsTree.toGTreeVertexEquiv (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) : (hd.toGTree hG hinv).V ≃ X :=
  d.toSerreGraphVertexEquiv

@[simp]
theorem IsTree.toGTreeVertexEquiv_smul (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) (g : G) (v : (hd.toGTree hG hinv).V) :
    hd.toGTreeVertexEquiv hG hinv (g • v) = g • hd.toGTreeVertexEquiv hG hinv v :=
  hG.toSerreGraphVertexEquiv_smul g v

@[simp]
theorem IsTree.toGTree_isElliptic_iff (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) {g : G} :
    (hd.toGTree hG hinv).IsElliptic g ↔ IsElliptic X g := by
  rw [GTree.isElliptic_iff, isElliptic_iff]
  refine (hd.toGTreeVertexEquiv hG hinv).exists_congr fun v => ?_
  rw [← (hd.toGTreeVertexEquiv hG hinv).injective.eq_iff, hd.toGTreeVertexEquiv_smul]

@[simp]
theorem IsTree.toGTree_isHyperbolic_iff (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) {g : G} :
    (hd.toGTree hG hinv).IsHyperbolic g ↔ IsHyperbolic X g := by
  rw [← (hd.toGTree hG hinv).lambdaMetric_isHyperbolic_iff, isHyperbolic_iff, isHyperbolic_iff,
    (hd.toGTree hG hinv).lambdaMetric_isElliptic_iff,
    (hd.toGTree hG hinv).lambdaMetric_isElliptic_iff,
    hd.toGTree_isElliptic_iff, hd.toGTree_isElliptic_iff]

@[simp]
theorem IsTree.pathMetric_toGTree (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) (u v : (hd.toGTree hG hinv).V) :
    (hd.toGTree hG hinv).pathMetric u v =
      d (hd.toGTreeVertexEquiv hG hinv u) (hd.toGTreeVertexEquiv hG hinv v) := by
  rw [GTree.pathMetric_apply]
  exact hd.isGeodesic.toSerreGraph_dist u v

@[simp]
theorem IsTree.basedLength_toGTree (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) (x : X) :
    (hd.toGTree hG hinv).isTree_pathMetric.basedLength
      (hd.toGTree hG hinv).isIsometricAction_pathMetric
      ((hd.toGTreeVertexEquiv hG hinv).symm x) = hd.basedLength hG x := by
  ext g
  rw [IsTree.basedLength_apply, IsTree.basedLength_apply, hd.pathMetric_toGTree,
    hd.toGTreeVertexEquiv_smul, Equiv.apply_symm_apply]

end ToSerreGraphAut

end LambdaMetric

/-! ### Free `ℤ`-valued length functions and free `G`-tree actions -/

namespace LyndonLength

/-- The Chiswell `G`-tree attached to a free `ℤ`-valued Lyndon length function on `G`. The body is
exposed so that `chiswellGTreeBase` compiles under the `module` code generator. -/
@[expose] def IsFree.chiswellGTree {G : Type u} [Group G] {l : LyndonLength G ℤ}
    (hl : l.IsFree) : GTree.{u, u} G :=
  (l.isTree_chiswellMetric hl.exists_coe_eq_gromovProduct).toGTree
    l.isIsometricAction_chiswell
    ((l.isFreeAction_chiswell_iff hl.exists_coe_eq_gromovProduct).2 hl).not_isInversion

/-- The base vertex of `hl.chiswellGTree` corresponding to `l.chiswellBase`. -/
def IsFree.chiswellGTreeBase {G : Type u} [Group G] {l : LyndonLength G ℤ}
    (hl : l.IsFree) : hl.chiswellGTree.V :=
  ((l.isTree_chiswellMetric hl.exists_coe_eq_gromovProduct).toGTreeVertexEquiv
    l.isIsometricAction_chiswell
    ((l.isFreeAction_chiswell_iff hl.exists_coe_eq_gromovProduct).2 hl).not_isInversion).symm
    l.chiswellBase

/-- Every nontrivial element of `G` acts hyperbolically on `hl.chiswellGTree`. -/
theorem IsFree.isHyperbolic_chiswellGTree {G : Type u} [Group G] {l : LyndonLength G ℤ}
    (hl : l.IsFree) {g : G} (hg : g ≠ 1) : hl.chiswellGTree.IsHyperbolic g := by
  rw [IsFree.chiswellGTree, LambdaMetric.IsTree.toGTree_isHyperbolic_iff]
  exact LambdaMetric.isFreeAction_iff.1
    ((l.isFreeAction_chiswell_iff hl.exists_coe_eq_gromovProduct).2 hl) g hg

/-- The based length function of `hl.chiswellGTree` at `hl.chiswellGTreeBase` recovers `l`. -/
@[simp]
theorem IsFree.basedLength_chiswellGTree {G : Type u} [Group G] {l : LyndonLength G ℤ}
    (hl : l.IsFree) :
    hl.chiswellGTree.isTree_pathMetric.basedLength hl.chiswellGTree.isIsometricAction_pathMetric
      hl.chiswellGTreeBase = l :=
  ((l.isTree_chiswellMetric hl.exists_coe_eq_gromovProduct).basedLength_toGTree
    l.isIsometricAction_chiswell
    ((l.isFreeAction_chiswell_iff hl.exists_coe_eq_gromovProduct).2 hl).not_isInversion
    l.chiswellBase).trans (l.basedLength_chiswellBase hl.exists_coe_eq_gromovProduct)

/-- A group `G` admits a free `ℤ`-valued Lyndon length function if and only if it acts on a
simplicial `G`-tree in which every nontrivial element is hyperbolic. -/
theorem exists_isFree_int_iff (G : Type u) [Group G] :
    (∃ l : LyndonLength G ℤ, l.IsFree) ↔
      ∃ T : GTree.{u, u} G, ∀ g : G, g ≠ 1 → T.IsHyperbolic g := by
  refine ⟨fun ⟨l, hl⟩ => ⟨hl.chiswellGTree, fun g hg => hl.isHyperbolic_chiswellGTree hg⟩, ?_⟩
  rintro ⟨T, hT⟩
  obtain ⟨v⟩ := (T.connected_iff.1 (SerreGraph.IsTree.connected _ T.isTree)).1
  exact ⟨T.isTree_pathMetric.basedLength T.isIsometricAction_pathMetric v,
    (T.isTree_pathMetric.isFree_basedLength_iff T.isIsometricAction_pathMetric v).2
      (T.lambdaMetric_isFreeAction_iff.2 hT)⟩

/-- A group `G` admits a free `ℤ`-valued Lyndon length function if and only if it acts freely
(with trivial vertex stabilizers and without edge inversions) on a simplicial `G`-tree. -/
theorem exists_isFree_int_iff_stabilizer_eq_bot (G : Type u) [Group G] :
    (∃ l : LyndonLength G ℤ, l.IsFree) ↔
      ∃ T : GTree.{u, u} G, ∀ v : T.V, MulAction.stabilizer G v = ⊥ := by
  rw [exists_isFree_int_iff]
  refine exists_congr fun T => ?_
  rw [← T.lambdaMetric_isFreeAction_iff, T.lambdaMetric_isFreeAction_iff_stabilizer_eq_bot]

end LyndonLength

end TauCeti
