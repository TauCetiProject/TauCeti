/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree
public import TauCeti.GroupTheory.GraphOfGroups.FreeProduct
public import TauCeti.GroupTheory.GTree.Restrict

/-!
# The tree of a free product

For a family of groups `M : ι → Type*` and a type `X`, the free product `P = (∗ᵢ Mᵢ) ∗ F(X)` acts
on the Bass–Serre tree of its graph of groups `freeProduct M X` over the star of a rose, through
the identification of `P` with the fundamental group. This is the tree of the free product: `P`
acts on it with trivial dart stabilizers, the vertex `vertex i` has the factor `Mᵢ` as its
stabilizer, the vertices `vertex i` lie in distinct orbits, and every vertex is a translate of one
of them or has trivial stabilizer. So the nontrivial vertex stabilizers are conjugates of the
factors. For a Grushko decomposition `G₁ ∗ ⋯ ∗ G_p ∗ F_q` this is the Bass–Serre tree of the
graph of groups of Guirardel and Levitt's Figure 1; for `X` empty it is a tree of the free product
`∗ᵢ Mᵢ` with trivial edge stabilizers, the setting of Kurosh's subgroup theorem.

## Main definitions

* `TauCeti.GraphOfGroups.freeProductTree`: the tree of the free product.
* `TauCeti.GraphOfGroups.freeProductTree.vertex`: the vertex whose stabilizer is the factor `Mᵢ`.

## Main results

* `TauCeti.GraphOfGroups.stabilizer_freeProductTree_dart`: dart stabilizers are trivial.
* `TauCeti.GraphOfGroups.stabilizer_freeProductTree_vertex`: the stabilizer of `vertex i` is the
  factor `Mᵢ`.
* `TauCeti.GraphOfGroups.stabilizer_freeProductTree_eq_bot_or`: every vertex has trivial
  stabilizer or is a translate of some `vertex i`.
* `TauCeti.GraphOfGroups.freeProductTree.eq_of_smul_vertex_eq`: the vertices `vertex i` lie in
  distinct orbits.

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

open _root_.MulAction SerreGraph

variable {ι : Type u} (M : ι → Type w) [∀ i, Group (M i)] (X : Type v)

-- The identification of the free product `(∗ᵢ Mᵢ) ∗ F(X)` with the fundamental group of its graph
-- of groups at the center.
private noncomputable def toπ₁ :
    Monoid.Coprod (Monoid.CoprodI M) (FreeGroup X) →* π₁ (freeProduct M X) (starRose.center ι X) :=
  (π₁Equiv (freeProduct M X) (starRose.center ι X) (starRoseTree ι X)).symm.toMonoidHom.comp
    (freeProductHom M X)

-- The tree path from the center to `tip i`, along the spoke, as an `𝔸`-path.
private noncomputable def spokePath (i : ι) :
    (freeProduct M X).Path ⟨starRose.center ι X⟩ ⟨starRose.tip X i⟩ :=
  (dartPrefunctor (freeProduct M X)).mapPath
    ((starRoseTree ι X).path (starRose.center ι X) (starRose.tip X i))

/-- The tree of the free product `(∗ᵢ Mᵢ) ∗ F(X)`: the Bass–Serre tree of its graph of groups,
based at the center, restricted (`GTree.comap`) along the identification of the free product with
the fundamental group. It is not minimal in general: for a single factor and `X` empty it is a
star whose center is fixed by the whole group. -/
noncomputable def freeProductTree :
    GTree.{max u v w, max u v w} (Monoid.Coprod (Monoid.CoprodI M) (FreeGroup X)) :=
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
    toπ₁ M X (Monoid.Coprod.inl (Monoid.CoprodI.of m)) = π₁.vertexHom (spokePath M X i) m :=
  (congrArg (π₁Equiv (freeProduct M X) (starRose.center ι X) (starRoseTree ι X)).symm
    (freeProductHom_inl_of M X m)).trans (π₁Equiv_symm_of (freeProduct M X)
      (starRose.center ι X) (starRoseTree ι X) (starRose.tip X i) m)

-- A subgroup of the fundamental group which is the image of a trivial group pulls back to `⊥`.
private theorem comap_toπ₁_range_eq_bot {A : Type*} [Group A] [Subsingleton A]
    (f : A →* π₁ (freeProduct M X) (starRose.center ι X)) : f.range.comap (toπ₁ M X) = ⊥ := by
  rw [MonoidHom.range_eq_bot_iff.2 (Subsingleton.elim f 1), MonoidHom.comap_bot,
    (toπ₁ M X).ker_eq_bot toπ₁_bijective.1]

/-- The free product `(∗ᵢ Mᵢ) ∗ F(X)` acts on its tree with trivial dart stabilizers. -/
theorem stabilizer_freeProductTree_dart (e : (freeProductTree M X).E) :
    stabilizer (Monoid.Coprod (Monoid.CoprodI M) (FreeGroup X)) e = ⊥ := by
  refine (GTree.stabilizer_comap_dart _ _ e).trans ?_
  obtain ⟨b, b', p, e, rfl⟩ := bassSerreDart_surjective e
  -- The edge groups are trivial, so is the stabilizer of the dart in the fundamental group.
  rw [stabilizer_bassSerreDart, MonoidHom.map_range]
  exact comap_toπ₁_range_eq_bot _

/-- The stabilizer of the vertex `vertex i` of the tree of a free product is the factor `M i`. -/
theorem stabilizer_freeProductTree_vertex (i : ι) :
    stabilizer (Monoid.Coprod (Monoid.CoprodI M) (FreeGroup X)) (freeProductTree.vertex M X i) =
      (Monoid.Coprod.inl.comp (Monoid.CoprodI.of (i := i)) :
        M i →* Monoid.Coprod (Monoid.CoprodI M) (FreeGroup X)).range := by
  refine (GTree.stabilizer_comap_vertex _ _ _).trans ?_
  rw [freeProductTree.vertex, stabilizer_bassSerreVertex]
  -- `toπ₁` is injective and sends `M i` onto the stabilizer `[c, tip i]_T A_{tip i} [tip i, c]_T`.
  ext x
  refine ⟨fun ⟨m, hm⟩ ↦ ⟨m, toπ₁_bijective.1 ((toπ₁_inl_of (X := X) (i := i) m).trans hm)⟩, ?_⟩
  rintro ⟨m, rfl⟩
  exact ⟨m, (toπ₁_inl_of (X := X) m).symm⟩

/-- A vertex of the tree of a free product has trivial stabilizer or is a translate of one of
the vertices `vertex i`, whose stabilizers are the factors. -/
theorem stabilizer_freeProductTree_eq_bot_or (a : (freeProductTree M X).V) :
    stabilizer (Monoid.Coprod (Monoid.CoprodI M) (FreeGroup X)) a = ⊥ ∨
      ∃ (g : Monoid.Coprod (Monoid.CoprodI M) (FreeGroup X)) (i : ι),
        g • freeProductTree.vertex M X i = a := by
  obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective a
  rcases starRose.eq_center_or_eq_tip b with rfl | ⟨i, rfl⟩
  · -- The vertex group at the center is trivial, so is the stabilizer of a vertex over it.
    have : Subsingleton ((freeProduct M X).vertexGroup (starRose.center ι X)) :=
      inferInstanceAs (Subsingleton PUnit)
    refine .inl ((GTree.stabilizer_comap_vertex _ _ _).trans ?_)
    rw [stabilizer_bassSerreVertex]
    exact comap_toπ₁_range_eq_bot _
  · -- A vertex over `tip i` is a translate of `vertex i`.
    obtain ⟨g, hg⟩ := exists_smul_bassSerreVertex_eq (spokePath M X i) p
    obtain ⟨g, rfl⟩ := toπ₁_bijective.2 g
    exact .inr ⟨g, i, hg⟩

/-- The vertices `vertex i` and `vertex j` of the tree of a free product lie in distinct orbits
when `i ≠ j`. -/
theorem freeProductTree.eq_of_smul_vertex_eq {g : Monoid.Coprod (Monoid.CoprodI M) (FreeGroup X)}
    {i j : ι} (h : g • freeProductTree.vertex M X i = freeProductTree.vertex M X j) : i = j := by
  -- The projection to the star of a rose is invariant and sends `vertex i` to `tip i`.
  have := congrArg (bassSerreProjection (freeProduct M X) (starRose.center ι X)).mapV
    ((GTree.comap_smul_vertex _ _ g _).symm.trans h)
  rw [bassSerreProjection_mapV_smul] at this
  simpa [freeProductTree.vertex] using this

end TauCeti.GraphOfGroups
