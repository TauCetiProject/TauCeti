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
`g ^ 2` does (`TauCeti.LambdaMetric.IsTree.exists_toSerreGraphAut_smul_eq_rev_iff`): if `g ^ 2`
fixes `x` and `g` fixes no point, `g` reverses the geodesic `[x, g • x]`, which therefore has odd
length `2 k + 1` and middle dart exchanged with its reverse by `g`. Consequently an isometric
`ℤ`-tree action without metric inversions yields a `G`-tree (`TauCeti.LambdaMetric.IsTree.toGTree`)
whose path metric recovers `d` along `TauCeti.LambdaMetric.IsTree.toGTreeVertexEquiv`.

Combined with Chiswell's construction (`TauCeti.LyndonLength.exists_isFree_iff`), a group `G`
admits a free `ℤ`-valued Lyndon length function if and only if it acts freely (without inversions)
on a simplicial `G`-tree (`TauCeti.LyndonLength.exists_isFree_int_iff`). For the free group
`FreeGroup α`, the based length function of the Cayley `G`-tree at the identity vertex
`TauCeti.GTree.cayleyBaseVertex` is word length `TauCeti.LyndonLength.freeGroupNorm`, and
Chiswell's equivariant embedding identifies the Chiswell `ℤ`-tree of `freeGroupNorm` with the
Cayley tree (`TauCeti.GTree.basedLength_cayleyBaseVertex`,
`TauCeti.GTree.chiswellEmbed_cayley_bijective`).

## Main definitions

* `TauCeti.GTree.pathMetric`: the `ℤ`-valued path metric on the vertices of a `G`-tree.
* `TauCeti.LambdaMetric.IsIsometricAction.toSerreGraphAut`: the action on `d.toSerreGraph` induced
  by an isometric action on `(X, d)`.
* `TauCeti.LambdaMetric.IsTree.toGTree`: the `G`-tree attached to an inversion-free isometric
  action on a `ℤ`-tree, with vertex and dart coordinates
  `TauCeti.LambdaMetric.IsTree.toGTreeVertexEquiv` and
  `TauCeti.LambdaMetric.IsTree.toGTreeDartEquiv`.
* `TauCeti.LyndonLength.IsFree.chiswellGTree`: the Chiswell `G`-tree of a free `ℤ`-valued Lyndon
  length function, with coordinates `TauCeti.LyndonLength.IsFree.chiswellGTreeVertexEquiv` and
  `TauCeti.LyndonLength.IsFree.chiswellGTreeDartEquiv`, and root vertex
  `TauCeti.LyndonLength.IsFree.chiswellGTreeRoot`.

## Main results

* `TauCeti.GTree.not_lambdaMetric_isInversion`, `TauCeti.GTree.lambdaMetric_isHyperbolic_iff`:
  a `G`-tree has no metric inversions, and metric hyperbolicity agrees with `GTree.IsHyperbolic`.
* `TauCeti.GTree.basedLength_cayleyBaseVertex`, `TauCeti.GTree.chiswellEmbed_cayley_bijective`:
  the based length function of `GTree.cayley α` at `1` is `freeGroupNorm α`, and Chiswell's
  embedding onto `GTree.cayley α` is bijective.
* `TauCeti.LambdaMetric.IsTree.exists_toSerreGraphAut_smul_eq_rev_iff`: `g` inverts a dart of
  `d.toSerreGraph` if and only if `g` is a metric inversion on `(X, d)`.
* `TauCeti.LyndonLength.IsFree.chiswellGTree_isHyperbolic_iff`,
  `TauCeti.LyndonLength.IsFree.chiswellGTree_isElliptic_iff`: on `hl.chiswellGTree`, nontrivial
  elements are hyperbolic and only `1` is elliptic.
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

/-- Metric hyperbolicity on `T.V` agrees with `GTree.IsHyperbolic`, since a `G`-tree has no
inversions. -/
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

/-- The based length function of the Cayley `G`-tree of `FreeGroup α` at the identity vertex is
word length `LyndonLength.freeGroupNorm α`. -/
@[simp]
theorem basedLength_cayleyBaseVertex {α : Type u} [DecidableEq α] :
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
theorem chiswellEmbed_cayley_bijective {α : Type u} [DecidableEq α] :
    Function.Bijective
      (LyndonLength.chiswellEmbed (cayley α).isTree_pathMetric
        (cayley α).isIsometricAction_pathMetric (cayleyBaseVertex α)
        basedLength_cayleyBaseVertex) := by
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
  toFun p := ⟨(g • p.val.1, g • p.val.2), by rw [hG.dist_smul_smul, p.property]⟩
  invFun p := ⟨(g⁻¹ • p.val.1, g⁻¹ • p.val.2), by rw [hG.dist_smul_smul, p.property]⟩
  left_inv p := Subtype.ext (Prod.ext (inv_smul_smul g p.val.1) (inv_smul_smul g p.val.2))
  right_inv p := Subtype.ext (Prod.ext (smul_inv_smul g p.val.1) (smul_inv_smul g p.val.2))

/-- The automorphism of `d.toSerreGraph` induced by an element `g : G` of an isometric action. -/
private noncomputable def IsIsometricAction.toSerreGraphIso (hG : d.IsIsometricAction G) (g : G) :
    d.toSerreGraph.Aut where
  equivV := d.toSerreGraphVertexEquiv.trans
    ((MulAction.toPerm g).trans d.toSerreGraphVertexEquiv.symm)
  equivE := d.toSerreGraphDartEquiv.trans
    ((smulUnitDistEquiv hG g).trans d.toSerreGraphDartEquiv.symm)
  map_src e := d.toSerreGraphVertexEquiv.injective (by simp [smulUnitDistEquiv])
  map_rev e := d.toSerreGraphDartEquiv.injective (Subtype.ext (by simp [smulUnitDistEquiv]))

/-- An isometric action of `G` on a `ℤ`-metric space `(X, d)` induces a group action by graph
automorphisms on the unit-distance Serre graph `d.toSerreGraph`. -/
noncomputable def IsIsometricAction.toSerreGraphAut (hG : d.IsIsometricAction G) :
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
theorem IsIsometricAction.toSerreGraphVertexEquiv_symm_smul (hG : d.IsIsometricAction G) (g : G)
    (x : X) :
    hG.toSerreGraphAut g • d.toSerreGraphVertexEquiv.symm x =
      d.toSerreGraphVertexEquiv.symm (g • x) :=
  d.toSerreGraphVertexEquiv.injective (by simp)

@[simp]
theorem IsIsometricAction.toSerreGraphDartEquiv_smul (hG : d.IsIsometricAction G) (g : G)
    (e : d.toSerreGraph.E) :
    (d.toSerreGraphDartEquiv (hG.toSerreGraphAut g • e)).val =
      (g • (d.toSerreGraphDartEquiv e).val.1, g • (d.toSerreGraphDartEquiv e).val.2) := by
  simp [SerreGraph.Aut.smul_dart_def, IsIsometricAction.toSerreGraphAut,
    IsIsometricAction.toSerreGraphIso, smulUnitDistEquiv]

/-- If `g ^ 2 • x = x` in a `ℤ`-tree `(X, d)` and `d x (g • x)` is odd, then `g` reverses the
middle dart of `[x, g • x]` in `d.toSerreGraph`. -/
private theorem IsTree.exists_toSerreGraphAut_smul_eq_rev_of_odd (hd : d.IsTree)
    (hG : d.IsIsometricAction G) {g : G} {x : X} (hx : g ^ 2 • x = x)
    (hodd : Odd (d x (g • x))) :
    ∃ e : d.toSerreGraph.E, hG.toSerreGraphAut g • e = d.toSerreGraph.rev e := by
  obtain ⟨f, hf0, hfD, hf, -⟩ := d.isSegment_iff.1 (hd.isSegment_segment x (g • x))
  set D := d x (g • x)
  have hD₀ : 0 ≤ D := d.nonneg x (g • x)
  obtain ⟨k, hkD⟩ := hodd
  have hk : k ∈ Icc 0 D := ⟨by omega, by omega⟩
  have hk1 : k + 1 ∈ Icc 0 D := ⟨by omega, by omega⟩
  have huv : d (f k) (f (k + 1)) = 1 := by
    rw [hf.dist_eq hk hk1, sub_add_cancel_left, abs_neg, abs_one]
  refine ⟨d.toSerreGraphDartEquiv.symm ⟨(f k, f (k + 1)), huv⟩,
    d.toSerreGraphDartEquiv.injective (Subtype.ext ?_)⟩
  rw [hG.toSerreGraphDartEquiv_smul, toSerreGraphDartEquiv_rev, Equiv.apply_symm_apply]
  have hDk : D - k = k + 1 := by omega
  have hDk1 : D - (k + 1) = k := by omega
  exact Prod.ext
    ((hd.smul_apply_of_sq_smul_eq hG hx hf0 hfD hf hk).trans (congrArg f hDk))
    ((hd.smul_apply_of_sq_smul_eq hG hx hf0 hfD hf hk1).trans (congrArg f hDk1))

/-- In a `ℤ`-tree `(X, d)` with an isometric action of `G`, an element `g` reverses a dart of
`d.toSerreGraph` if and only if `g` is a metric inversion on `X`. -/
theorem IsTree.exists_toSerreGraphAut_smul_eq_rev_iff (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (g : G) :
    (∃ e : d.toSerreGraph.E, hG.toSerreGraphAut g • e = d.toSerreGraph.rev e) ↔
      IsInversion X g := by
  rw [isInversion_iff]
  refine ⟨?_, fun ⟨hne, hsq⟩ => ?_⟩
  · rintro ⟨e, hrev⟩
    have hval := congrArg (fun f => (d.toSerreGraphDartEquiv f).val) hrev
    rw [hG.toSerreGraphDartEquiv_smul, toSerreGraphDartEquiv_rev] at hval
    rcases heq : d.toSerreGraphDartEquiv e with ⟨⟨u, v⟩, huv⟩
    rw [heq] at hval
    have hgu : g • u = v := congrArg Prod.fst hval
    have hgv : g • v = u := congrArg Prod.snd hval
    refine ⟨fun hz => ?_, isElliptic_iff.2 ⟨u, by rw [pow_two, mul_smul, hgu, hgv]⟩⟩
    obtain ⟨z, hz⟩ := isElliptic_iff.1 hz
    have hzv : d z v = d z u := by rw [← hz, ← hgu, hG.dist_smul_smul, hz]
    obtain ⟨k, hk⟩ := hd.even_dist_add_dist_sub_dist z u v
    rw [hzv, huv] at hk
    omega
  · obtain ⟨x, hx⟩ := isElliptic_iff.1 hsq
    exact hd.exists_toSerreGraphAut_smul_eq_rev_of_odd hG hx
      (Int.not_even_iff_odd.1 (hd.not_even_dist_smul_of_sq_smul_eq hG hne hx))

/-- An inversion-free isometric action of `G` on a `ℤ`-tree `(X, d)` defines a simplicial `G`-tree
with vertices `X` and unit-distance darts; use `IsTree.toGTreeVertexEquiv` and
`IsTree.toGTreeDartEquiv` to pass between the `G`-tree and `X`. -/
noncomputable def IsTree.toGTree (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) : GTree.{u, u} G where
  toSerreGraph := d.toSerreGraph
  isTree := hd.isTree_toSerreGraph
  action := hG.toSerreGraphAut
  action_smul_ne_rev g e he :=
    hinv g ((hd.exists_toSerreGraphAut_smul_eq_rev_iff hG g).1
      ⟨e, by rwa [SerreGraph.Aut.smul_dart_def]⟩)

/-- The vertices of `hd.toGTree hG hinv` are identified with `X`. -/
noncomputable def IsTree.toGTreeVertexEquiv (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) : (hd.toGTree hG hinv).V ≃ X :=
  d.toSerreGraphVertexEquiv

/-- The darts of `hd.toGTree hG hinv` are identified with ordered pairs `(x, y)` at unit
distance. -/
noncomputable def IsTree.toGTreeDartEquiv (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) :
    (hd.toGTree hG hinv).E ≃ { p : X × X // d p.1 p.2 = 1 } :=
  d.toSerreGraphDartEquiv

@[simp]
theorem IsTree.toGTreeVertexEquiv_src (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) (e : (hd.toGTree hG hinv).E) :
    hd.toGTreeVertexEquiv hG hinv ((hd.toGTree hG hinv).src e) =
      (hd.toGTreeDartEquiv hG hinv e).val.1 :=
  d.toSerreGraphVertexEquiv_src e

@[simp]
theorem IsTree.toGTreeVertexEquiv_tgt (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) (e : (hd.toGTree hG hinv).E) :
    hd.toGTreeVertexEquiv hG hinv ((hd.toGTree hG hinv).tgt e) =
      (hd.toGTreeDartEquiv hG hinv e).val.2 :=
  d.toSerreGraphVertexEquiv_tgt e

@[simp]
theorem IsTree.toGTreeDartEquiv_rev (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) (e : (hd.toGTree hG hinv).E) :
    (hd.toGTreeDartEquiv hG hinv ((hd.toGTree hG hinv).rev e)).val =
      ((hd.toGTreeDartEquiv hG hinv e).val.2, (hd.toGTreeDartEquiv hG hinv e).val.1) :=
  d.toSerreGraphDartEquiv_rev e

@[simp]
theorem IsTree.toGTreeVertexEquiv_smul (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) (g : G) (v : (hd.toGTree hG hinv).V) :
    hd.toGTreeVertexEquiv hG hinv (g • v) = g • hd.toGTreeVertexEquiv hG hinv v :=
  hG.toSerreGraphVertexEquiv_smul g v

@[simp]
theorem IsTree.toGTreeVertexEquiv_symm_smul (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) (g : G) (x : X) :
    g • (hd.toGTreeVertexEquiv hG hinv).symm x =
      (hd.toGTreeVertexEquiv hG hinv).symm (g • x) :=
  (hd.toGTreeVertexEquiv hG hinv).injective (by simp)

@[simp]
theorem IsTree.toGTreeDartEquiv_smul (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) (g : G) (e : (hd.toGTree hG hinv).E) :
    (hd.toGTreeDartEquiv hG hinv (g • e)).val =
      (g • (hd.toGTreeDartEquiv hG hinv e).val.1, g • (hd.toGTreeDartEquiv hG hinv e).val.2) :=
  hG.toSerreGraphDartEquiv_smul g e

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
theorem IsTree.toGTree_dist (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) (u v : (hd.toGTree hG hinv).V) :
    ((hd.toGTree hG hinv).dist u v : ℤ) =
      d (hd.toGTreeVertexEquiv hG hinv u) (hd.toGTreeVertexEquiv hG hinv v) :=
  hd.isGeodesic.toSerreGraph_dist u v

@[simp]
theorem IsTree.basedLength_toGTree (hd : d.IsTree) (hG : d.IsIsometricAction G)
    (hinv : ∀ g : G, ¬IsInversion X g) (x : X) :
    (hd.toGTree hG hinv).isTree_pathMetric.basedLength
      (hd.toGTree hG hinv).isIsometricAction_pathMetric
      ((hd.toGTreeVertexEquiv hG hinv).symm x) = hd.basedLength hG x := by
  ext g
  simp

end ToSerreGraphAut

end LambdaMetric

/-! ### Free `ℤ`-valued length functions and free `G`-tree actions -/

namespace LyndonLength

section ChiswellGTree

variable {G : Type u} [Group G] {l : LyndonLength G ℤ} (hl : l.IsFree)

private theorem IsFree.isTree_chiswellMetric (hl : l.IsFree) : l.chiswellMetric.IsTree :=
  l.isTree_chiswellMetric hl.exists_coe_eq_gromovProduct

private theorem IsFree.isFreeAction_chiswellTree (hl : l.IsFree) :
    LambdaMetric.IsFreeAction G l.ChiswellTree :=
  (l.isFreeAction_chiswellTree_iff hl.exists_coe_eq_gromovProduct).2 hl

private theorem IsFree.not_isInversion_chiswellTree (hl : l.IsFree) (g : G) :
    ¬LambdaMetric.IsInversion l.ChiswellTree g :=
  hl.isFreeAction_chiswellTree.not_isInversion g

/-- The Chiswell `G`-tree attached to a free `ℤ`-valued Lyndon length function on `G`. Use
`IsFree.chiswellGTreeVertexEquiv` and `IsFree.chiswellGTreeDartEquiv` to pass between the `G`-tree
and `l.ChiswellTree`. -/
noncomputable def IsFree.chiswellGTree : GTree.{u, u} G :=
  hl.isTree_chiswellMetric.toGTree l.isIsometricAction_chiswellMetric
    hl.not_isInversion_chiswellTree

/-- The vertices of `hl.chiswellGTree` are identified with `l.ChiswellTree`. -/
noncomputable def IsFree.chiswellGTreeVertexEquiv : hl.chiswellGTree.V ≃ l.ChiswellTree :=
  hl.isTree_chiswellMetric.toGTreeVertexEquiv l.isIsometricAction_chiswellMetric
    hl.not_isInversion_chiswellTree

/-- The darts of `hl.chiswellGTree` are identified with ordered pairs in `l.ChiswellTree` at unit
distance. -/
noncomputable def IsFree.chiswellGTreeDartEquiv :
    hl.chiswellGTree.E ≃ { p : l.ChiswellTree × l.ChiswellTree // l.chiswellMetric p.1 p.2 = 1 } :=
  hl.isTree_chiswellMetric.toGTreeDartEquiv l.isIsometricAction_chiswellMetric
    hl.not_isInversion_chiswellTree

/-- The root vertex of `hl.chiswellGTree` corresponding to `ChiswellTree.root l`. -/
noncomputable def IsFree.chiswellGTreeRoot : hl.chiswellGTree.V :=
  hl.chiswellGTreeVertexEquiv.symm (ChiswellTree.root l)

@[simp]
theorem IsFree.chiswellGTreeVertexEquiv_chiswellGTreeRoot :
    hl.chiswellGTreeVertexEquiv hl.chiswellGTreeRoot = ChiswellTree.root l :=
  hl.chiswellGTreeVertexEquiv.apply_symm_apply (ChiswellTree.root l)

@[simp]
theorem IsFree.chiswellGTreeVertexEquiv_src (e : hl.chiswellGTree.E) :
    hl.chiswellGTreeVertexEquiv (hl.chiswellGTree.src e) = (hl.chiswellGTreeDartEquiv e).val.1 :=
  hl.isTree_chiswellMetric.toGTreeVertexEquiv_src l.isIsometricAction_chiswellMetric
    hl.not_isInversion_chiswellTree e

@[simp]
theorem IsFree.chiswellGTreeVertexEquiv_tgt (e : hl.chiswellGTree.E) :
    hl.chiswellGTreeVertexEquiv (hl.chiswellGTree.tgt e) = (hl.chiswellGTreeDartEquiv e).val.2 :=
  hl.isTree_chiswellMetric.toGTreeVertexEquiv_tgt l.isIsometricAction_chiswellMetric
    hl.not_isInversion_chiswellTree e

@[simp]
theorem IsFree.chiswellGTreeDartEquiv_rev (e : hl.chiswellGTree.E) :
    (hl.chiswellGTreeDartEquiv (hl.chiswellGTree.rev e)).val =
      ((hl.chiswellGTreeDartEquiv e).val.2, (hl.chiswellGTreeDartEquiv e).val.1) :=
  hl.isTree_chiswellMetric.toGTreeDartEquiv_rev l.isIsometricAction_chiswellMetric
    hl.not_isInversion_chiswellTree e

@[simp]
theorem IsFree.chiswellGTreeVertexEquiv_smul (g : G) (v : hl.chiswellGTree.V) :
    hl.chiswellGTreeVertexEquiv (g • v) = g • hl.chiswellGTreeVertexEquiv v :=
  hl.isTree_chiswellMetric.toGTreeVertexEquiv_smul l.isIsometricAction_chiswellMetric
    hl.not_isInversion_chiswellTree g v

@[simp]
theorem IsFree.chiswellGTreeVertexEquiv_symm_smul (g : G) (x : l.ChiswellTree) :
    g • hl.chiswellGTreeVertexEquiv.symm x = hl.chiswellGTreeVertexEquiv.symm (g • x) :=
  hl.chiswellGTreeVertexEquiv.injective (by simp)

@[simp]
theorem IsFree.chiswellGTreeDartEquiv_smul (g : G) (e : hl.chiswellGTree.E) :
    (hl.chiswellGTreeDartEquiv (g • e)).val =
      (g • (hl.chiswellGTreeDartEquiv e).val.1, g • (hl.chiswellGTreeDartEquiv e).val.2) :=
  hl.isTree_chiswellMetric.toGTreeDartEquiv_smul l.isIsometricAction_chiswellMetric
    hl.not_isInversion_chiswellTree g e

@[simp]
theorem IsFree.chiswellGTree_dist (u v : hl.chiswellGTree.V) :
    (hl.chiswellGTree.dist u v : ℤ) =
      l.chiswellMetric (hl.chiswellGTreeVertexEquiv u) (hl.chiswellGTreeVertexEquiv v) :=
  hl.isTree_chiswellMetric.toGTree_dist l.isIsometricAction_chiswellMetric
    hl.not_isInversion_chiswellTree u v

/-- On `hl.chiswellGTree`, an element of `G` acts hyperbolically if and only if it is
nontrivial. -/
@[simp]
theorem IsFree.chiswellGTree_isHyperbolic_iff {g : G} :
    hl.chiswellGTree.IsHyperbolic g ↔ g ≠ 1 := by
  refine ⟨GTree.IsHyperbolic.ne_one, fun hg => ?_⟩
  rw [IsFree.chiswellGTree, LambdaMetric.IsTree.toGTree_isHyperbolic_iff]
  exact LambdaMetric.isFreeAction_iff.1 hl.isFreeAction_chiswellTree g hg

/-- On `hl.chiswellGTree`, an element of `G` is elliptic if and only if it is `1`. -/
@[simp]
theorem IsFree.chiswellGTree_isElliptic_iff {g : G} :
    hl.chiswellGTree.IsElliptic g ↔ g = 1 := by
  rw [← hl.chiswellGTree.not_isHyperbolic_iff, hl.chiswellGTree_isHyperbolic_iff, not_not]

/-- The based length function of `hl.chiswellGTree` at `hl.chiswellGTreeRoot` recovers `l`. -/
@[simp]
theorem IsFree.basedLength_chiswellGTree :
    hl.chiswellGTree.isTree_pathMetric.basedLength hl.chiswellGTree.isIsometricAction_pathMetric
      hl.chiswellGTreeRoot = l :=
  (hl.isTree_chiswellMetric.basedLength_toGTree l.isIsometricAction_chiswellMetric
    hl.not_isInversion_chiswellTree (ChiswellTree.root l)).trans l.basedLength_chiswellTree_root

end ChiswellGTree

/-- A group `G` admits a free `ℤ`-valued Lyndon length function if and only if it acts on a
simplicial `G`-tree in which every nontrivial element is hyperbolic. -/
theorem exists_isFree_int_iff (G : Type u) [Group G] :
    (∃ l : LyndonLength G ℤ, l.IsFree) ↔
      ∃ T : GTree.{u, u} G, ∀ g : G, g ≠ 1 → T.IsHyperbolic g := by
  refine ⟨fun ⟨l, hl⟩ => ⟨hl.chiswellGTree, fun _ hg => hl.chiswellGTree_isHyperbolic_iff.2 hg⟩,
    ?_⟩
  rintro ⟨T, hT⟩
  obtain ⟨v⟩ : Nonempty T.V := inferInstance
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
