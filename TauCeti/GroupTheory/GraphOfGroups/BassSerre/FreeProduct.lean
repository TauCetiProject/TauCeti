/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Tree
public import TauCeti.GroupTheory.GraphOfGroups.FreeProduct
public import TauCeti.GroupTheory.GTree.Restrict

/-!
# The Bass–Serre tree of a free product

For a family of groups `M : ι → Type*` and a type `X`, the free product `P = (∗ᵢ Mᵢ) ∗ F(X)` acts
on the Bass–Serre tree of its graph of groups `freeProduct M X` over the star of a rose, through
the identification of `P` with the fundamental group. This is the tree of the free product: `P`
acts on it with trivial dart stabilizers, the vertex `vertex i` has the factor `Mᵢ` as its
stabilizer, the vertices `vertex i` lie in distinct orbits, and every vertex is a translate of one
of them or has trivial stabilizer. So the nontrivial vertex stabilizers are conjugates of the
factors, and the quotient graph is the star of a rose, with the orbit of `vertex i` at `tip i`.
For a Grushko decomposition `G₁ ∗ ⋯ ∗ G_p ∗ F_q` this is the Bass–Serre tree of the graph of
groups of Guirardel and Levitt's Figure 1.

For `X` empty, restricting along `Monoid.Coprod.inl`, which is then bijective, gives a tree of the
free product `∗ᵢ Mᵢ` itself with the same properties: the tree from which Kurosh's subgroup
theorem is read off, by restricting the action to a subgroup.

## Main definitions

* `TauCeti.GraphOfGroups.freeProductTree`: the tree of the free product.
* `TauCeti.GraphOfGroups.freeProductTree.vertex`: the vertex whose stabilizer is the factor `Mᵢ`.
* `TauCeti.GraphOfGroups.freeProductTree.quotientIso`: the quotient graph is the star of a rose.

## Main results

* `TauCeti.GraphOfGroups.stabilizer_freeProductTree_dart_eq_bot`: dart stabilizers are trivial.
* `TauCeti.GraphOfGroups.stabilizer_freeProductTree_vertex`: the stabilizer of `vertex i` is the
  factor `Mᵢ`.
* `TauCeti.GraphOfGroups.stabilizer_freeProductTree_eq_bot_or_exists_smul_vertex_eq`: every
  vertex has trivial stabilizer or is a translate of some `vertex i`.
* `TauCeti.GraphOfGroups.freeProductTree.eq_of_smul_vertex_eq`: the vertices `vertex i` lie in
  distinct orbits.
* `TauCeti.GraphOfGroups.exists_gTree_coprodI`: the free product `∗ᵢ Mᵢ` acts on a tree with
  the properties above.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12, and §5.5, Theorem 14.
* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), Introduction
  (Figure 1) and §3.2.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5 and the stabilizers of its vertices
  and edges, p. 7.
-/

public section

universe u v w

namespace TauCeti.GraphOfGroups

open Monoid _root_.MulAction SerreGraph

variable {ι : Type u} (M : ι → Type w) [∀ i, Group (M i)] (X : Type v)

-- The identification of the free product `(∗ᵢ Mᵢ) ∗ F(X)` with the fundamental group of its graph
-- of groups at the center.
private noncomputable def toπ₁ :
    Coprod (CoprodI M) (FreeGroup X) →* π₁ (freeProduct M X) (starRose.center ι X) :=
  (π₁Equiv (freeProduct M X) (starRose.center ι X) (starRoseTree ι X)).symm.toMonoidHom.comp
    (freeProductHom M X)

-- The tree path from the center to `tip i`, along the spoke, as an `𝔸`-path.
private noncomputable def spokePath (i : ι) :
    (freeProduct M X).Path ⟨starRose.center ι X⟩ ⟨starRose.tip X i⟩ :=
  (dartPrefunctor (freeProduct M X)).mapPath
    ((starRoseTree ι X).path (starRose.center ι X) (starRose.tip X i))

/-- The tree of the free product `(∗ᵢ Mᵢ) ∗ F(X)`: the Bass–Serre tree of its graph of groups,
based at the center, restricted (`GTree.comap`) along the identification of the free product with
the fundamental group. It is not minimal in general: for a single factor `M i` and `X` empty the
whole group fixes the vertex `freeProductTree.vertex M X i`, the vertex over the unique tip. -/
noncomputable def freeProductTree :
    GTree.{max u v w, max u v w} (Coprod (CoprodI M) (FreeGroup X)) :=
  (bassSerreTree (freeProduct M X) (starRose.center ι X)).comap (toπ₁ M X)

/-- The vertex of the tree of a free product whose stabilizer is the factor `M i`
(`stabilizer_freeProductTree_vertex`): the coset of the tree path from the center to `tip i`. -/
noncomputable def freeProductTree.vertex (i : ι) : (freeProductTree M X).V :=
  bassSerreVertex (spokePath M X i)

variable {M X}

private theorem toπ₁_bijective : Function.Bijective (toπ₁ M X) :=
  (π₁Equiv (freeProduct M X) (starRose.center ι X) (starRoseTree ι X)).symm.bijective.comp
    (freeProductHom_bijective M X)

-- `toπ₁` sends `m ∈ M i` to the class of the loop `[c, tip i]_T m [tip i, c]_T`.
private theorem toπ₁_inl_of {i : ι} (m : M i) :
    toπ₁ M X (Coprod.inl (CoprodI.of m)) = π₁.vertexHom (spokePath M X i) m :=
  (congrArg _ (freeProductHom_inl_of M X m)).trans (π₁Equiv_symm_of ..)

/-- The free product `(∗ᵢ Mᵢ) ∗ F(X)` acts on its tree with trivial dart stabilizers. -/
@[simp] theorem stabilizer_freeProductTree_dart_eq_bot (e : (freeProductTree M X).E) :
    stabilizer (Coprod (CoprodI M) (FreeGroup X)) e = ⊥ := by
  -- The edge groups are trivial, so is the stabilizer of the dart in the fundamental group.
  refine (GTree.stabilizer_comap_dart _ _ e).trans ?_
  rw [stabilizer_bassSerreTree_dart_eq_bot, MonoidHom.comap_bot,
    (toπ₁ M X).ker_eq_bot toπ₁_bijective.1]

/-- The stabilizer of the vertex `vertex i` of the tree of a free product is the factor `M i`. -/
@[simp] theorem stabilizer_freeProductTree_vertex (i : ι) :
    stabilizer (Coprod (CoprodI M) (FreeGroup X)) (freeProductTree.vertex M X i) =
      (Coprod.inl.comp (CoprodI.of (i := i)) :
        M i →* Coprod (CoprodI M) (FreeGroup X)).range := by
  have h : (π₁.vertexHom (spokePath M X i)).range =
      (Coprod.inl.comp (CoprodI.of (i := i))).range.map (toπ₁ M X) := by
    rw [← MonoidHom.range_comp]
    exact congrArg MonoidHom.range (MonoidHom.ext fun m ↦ (toπ₁_inl_of (M := M) (X := X) m).symm)
  refine (GTree.stabilizer_comap_vertex _ _ _).trans ?_
  rw [freeProductTree.vertex, stabilizer_bassSerreVertex, h,
    Subgroup.comap_map_eq_self_of_injective toπ₁_bijective.1]

/-- A vertex of the tree of a free product has trivial stabilizer or is a translate of one of
the vertices `vertex i`, whose stabilizers are the factors. -/
theorem stabilizer_freeProductTree_eq_bot_or_exists_smul_vertex_eq
    (a : (freeProductTree M X).V) :
    stabilizer (Coprod (CoprodI M) (FreeGroup X)) a = ⊥ ∨
      ∃ (g : Coprod (CoprodI M) (FreeGroup X)) (i : ι),
        g • freeProductTree.vertex M X i = a := by
  obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective a
  rcases starRose.eq_center_or_eq_tip b with rfl | ⟨i, rfl⟩
  · -- The vertex group at the center is trivial, so is the stabilizer of a vertex over it.
    refine .inl ((GTree.stabilizer_comap_vertex _ _ _).trans ?_)
    rw [stabilizer_bassSerreVertex_eq_bot, MonoidHom.comap_bot,
      (toπ₁ M X).ker_eq_bot toπ₁_bijective.1]
  · -- A vertex over `tip i` is a translate of `vertex i`.
    obtain ⟨g, hg⟩ := exists_smul_bassSerreVertex_eq (spokePath M X i) p
    obtain ⟨g, rfl⟩ := toπ₁_bijective.2 g
    exact .inr ⟨g, i, (GTree.comap_smul_vertex _ _ g _).trans hg⟩

/-- The vertices `vertex i` and `vertex j` of the tree of a free product lie in distinct orbits
when `i ≠ j`. -/
theorem freeProductTree.eq_of_smul_vertex_eq {g : Coprod (CoprodI M) (FreeGroup X)}
    {i j : ι} (h : g • freeProductTree.vertex M X i = freeProductTree.vertex M X j) : i = j := by
  -- The projection to the star of a rose is invariant and sends `vertex i` to `tip i`.
  have := congrArg (bassSerreProjection (freeProduct M X) (starRose.center ι X)).mapV
    ((GTree.comap_smul_vertex _ _ g _).symm.trans h)
  rw [bassSerreProjection_mapV_smul] at this
  simpa [freeProductTree.vertex] using this

variable (M X) in
/-- The quotient graph of the tree of a free product is the star of a rose: the orbit of a vertex
or dart goes to the vertex or dart of the star of a rose that it lies over. -/
noncomputable def freeProductTree.quotientIso :
    (freeProductTree M X).quotient.Iso (starRose ι X) :=
  ((bassSerreTree _ _).comapQuotientIso (toπ₁ M X) toπ₁_bijective.2).trans
    (bassSerreQuotientIso _ _ ((starRose ι X).connected_iff.1 (starRose_connected ι X)).2)

/-- The orbit of `vertex i` is the vertex `tip i` of the star of a rose. -/
@[simp] theorem freeProductTree.quotientIso_vertex (i : ι) :
    (freeProductTree.quotientIso M X).equivV
      ((freeProductTree M X).quotientMap.mapV (freeProductTree.vertex M X i)) =
        starRose.tip X i := by
  refine (congrArg (bassSerreQuotientIso (freeProduct M X) (starRose.center ι X) _).equivV
    (GTree.comapQuotientIso_equivV_quotientMap _ (toπ₁ M X) toπ₁_bijective.2
      (bassSerreVertex (spokePath M X i)))).trans ?_
  rw [← SerreGraph.Iso.toHom_mapV, bassSerreQuotientIso_toHom,
    bassSerreQuotientHom_mapV_quotientMap, bassSerreProjection_mapV_bassSerreVertex]

variable (M) in
/-- **The tree of a free product.** The free product `∗ᵢ Mᵢ` acts without inversions on a tree
with trivial dart stabilizers, with a vertex `t i` for each `i` whose stabilizer is the factor
`Mᵢ`, such that every vertex with nontrivial stabilizer is a translate of some `t i`, and no
translate of `t i` is `t i'` for `i ≠ i'`. The tree is `freeProductTree M PEmpty`, restricted
along `Monoid.Coprod.inl`. -/
theorem exists_gTree_coprodI :
    ∃ (T : GTree.{max u w, max u w} (CoprodI M)) (t : ι → T.V),
      (∀ e : T.E, stabilizer (CoprodI M) e = ⊥) ∧
      (∀ i, stabilizer (CoprodI M) (t i) = (CoprodI.of (M := M) (i := i)).range) ∧
      (∀ y : T.V, stabilizer (CoprodI M) y = ⊥ ∨ ∃ i, ∃ g : CoprodI M, g • t i = y) ∧
      (∀ i i' (g : CoprodI M), g • t i = t i' → i = i') := by
  -- With no free generators, `inl` is bijective: composed with `toπ₁` it is `coprodIEquivπ₁`.
  have hinl : Function.Bijective
      (Coprod.inl : CoprodI M →* Coprod (CoprodI M) (FreeGroup PEmpty.{1})) := by
    have : (toπ₁ M PEmpty.{1}).comp Coprod.inl = (coprodIEquivπ₁ M).toMonoidHom :=
      CoprodI.ext_hom _ _ fun i ↦ MonoidHom.ext fun m ↦
        (toπ₁_inl_of (X := PEmpty) m).trans (coprodIEquivπ₁_of M m).symm
    rw [← toπ₁_bijective.of_comp_iff', ← MonoidHom.coe_comp, this]
    exact (coprodIEquivπ₁ M).bijective
  refine ⟨(freeProductTree M PEmpty.{1}).comap Coprod.inl, freeProductTree.vertex M PEmpty,
    fun e ↦ ?_, fun i ↦ ?_, fun y ↦ ?_, fun i i' g h ↦ freeProductTree.eq_of_smul_vertex_eq
      ((GTree.comap_smul_vertex _ _ g _).symm.trans h)⟩
  · refine (GTree.stabilizer_comap_dart _ _ e).trans ?_
    rw [stabilizer_freeProductTree_dart_eq_bot, MonoidHom.comap_bot, Coprod.inl.ker_eq_bot hinl.1]
  · refine (GTree.stabilizer_comap_vertex _ _ _).trans ?_
    rw [stabilizer_freeProductTree_vertex, MonoidHom.range_comp,
      Subgroup.comap_map_eq_self_of_injective hinl.1]
  · rcases stabilizer_freeProductTree_eq_bot_or_exists_smul_vertex_eq y with h | ⟨g, i, hg⟩
    · refine .inl ((GTree.stabilizer_comap_vertex _ _ _).trans ?_)
      rw [h, MonoidHom.comap_bot, Coprod.inl.ker_eq_bot hinl.1]
    · obtain ⟨g, rfl⟩ := hinl.2 g
      exact .inr ⟨i, g, (GTree.comap_smul_vertex _ _ g _).trans hg⟩

end TauCeti.GraphOfGroups
