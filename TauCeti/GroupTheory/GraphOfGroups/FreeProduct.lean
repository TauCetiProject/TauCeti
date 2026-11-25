/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.StarRose
public import TauCeti.GroupTheory.GraphOfGroups.Presentation
public import TauCeti.GroupTheory.CoprodI
public import TauCeti.GroupTheory.GraphOfGroups.SpanningTree

/-!
# The graph of groups of a free product

For a family of groups `M : ι → Type*` and a type `X`, the free product `(∗ᵢ Mᵢ) ∗ F(X)` is the
fundamental group of a graph of groups with trivial edge groups over the star of a rose: the
central vertex carries the trivial group, the vertex `tip i` carries `Mᵢ`, and there is one loop
at the center for each `x : X`.

## Main definitions

* `TauCeti.GraphOfGroups.freeProduct`: the graph of groups.
* `TauCeti.GraphOfGroups.freeProductHom`: the homomorphism from `(∗ᵢ Mᵢ) ∗ F(X)` to the
  fundamental group of `freeProduct` with respect to the spokes.
* `TauCeti.GraphOfGroups.coprodIEquivπ₁`: the isomorphism of the free product `∗ᵢ Mᵢ` with the
  fundamental group of `freeProduct M PEmpty` at the center.

## Main results

* `TauCeti.GraphOfGroups.freeProductHom_bijective`: `freeProductHom` is bijective.

## Implementation notes

The vertex groups are defined by cases on `Option ι`, the vertices of `starRose ι X`, and
`freeProduct` and `freeProductVertexGroup` are exposed, so that the vertex group at `tip i` reduces
to `M i` and an element of `M i` can be used directly in it.

## References

* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), Introduction,
  Figure 1, and §3.2.
* J.-P. Serre, *Trees*, Chapter I, §5.1.
-/

public section

universe u v w

namespace TauCeti.GraphOfGroups

open SerreGraph

variable {ι : Type u} (M : ι → Type w) [∀ i, Group (M i)] (X : Type v)

/-- The vertex groups of the graph of groups of a free product: the trivial group at the center
`none` and `M i` at the vertex `some i`. -/
@[expose] def freeProductVertexGroup : Option ι → Type w
  | none => PUnit
  | some i => M i

/-- The group structure on the vertex groups of the graph of groups of a free product. -/
instance freeProductVertexGroup.instGroup : ∀ o, Group (freeProductVertexGroup M o)
  | none => inferInstanceAs (Group PUnit)
  | some i => inferInstanceAs (Group (M i))

/-- The graph of groups of the free product `(∗ᵢ Mᵢ) ∗ F(X)`, over the star of a rose: the group
`M i` at the vertex `tip i`, the trivial group at the center, and trivial edge groups. -/
@[expose] def freeProduct : GraphOfGroups.{u, max u v, w, 0} (starRose ι X) where
  vertexGroup := freeProductVertexGroup M
  instGroupVertexGroup := freeProductVertexGroup.instGroup M
  edgeGroup _ := PUnit
  ω _ := 1
  ω_injective _ := Function.injective_of_subsingleton _

/-- The edge groups of the graph of groups of a free product are trivial. -/
instance freeProduct.subsingleton_edgeGroup (y : (starRose ι X).GeomEdge) :
    Subsingleton ((freeProduct M X).edgeGroup y) :=
  inferInstanceAs (Subsingleton PUnit)

/-- The vertex group at the center of the graph of groups of a free product is trivial. -/
instance freeProduct.subsingleton_vertexGroup_center :
    Subsingleton ((freeProduct M X).vertexGroup (starRose.center ι X)) :=
  inferInstanceAs (Subsingleton PUnit)

/-- The homomorphism from the free product `(∗ᵢ Mᵢ) ∗ F(X)` to the fundamental group of its graph
of groups with respect to the spokes: `M i` goes to the vertex group at `tip i` and the
generator `x` to the dart of its petal. -/
def freeProductHom : Monoid.Coprod (Monoid.CoprodI M) (FreeGroup X) →*
    π₁Tree (freeProduct M X) (starRoseTree ι X).darts :=
  Monoid.Coprod.lift
    (Monoid.CoprodI.lift fun i =>
      π₁Tree.of (𝔸 := freeProduct M X) (starRoseTree ι X).darts (starRose.tip X i))
    (FreeGroup.lift fun x => π₁Tree.edge (𝔸 := freeProduct M X) (starRoseTree ι X).darts
      (starRose.petal ι x))

@[simp] theorem freeProductHom_inl_of {i : ι} (m : M i) :
    freeProductHom M X (Monoid.Coprod.inl (Monoid.CoprodI.of m)) =
      π₁Tree.of (𝔸 := freeProduct M X) (starRoseTree ι X).darts (starRose.tip X i) m :=
  (Monoid.Coprod.lift_apply_inl ..).trans (Monoid.CoprodI.lift_of ..)

@[simp] theorem freeProductHom_inr_of (x : X) :
    freeProductHom M X (Monoid.Coprod.inr (FreeGroup.of x)) =
      π₁Tree.edge (𝔸 := freeProduct M X) (starRoseTree ι X).darts (starRose.petal ι x) :=
  (Monoid.Coprod.lift_apply_inr ..).trans (FreeGroup.lift_apply_of ..)

/-- The homomorphism `freeProductHom` is bijective: the free product `(∗ᵢ Mᵢ) ∗ F(X)` is the
fundamental group of its graph of groups. -/
theorem freeProductHom_bijective : Function.Bijective (freeProductHom M X) := by
  have : Subsingleton (freeProductVertexGroup M none) :=
    freeProduct.subsingleton_vertexGroup_center M X
  -- The vertex factors: the factor at the center is trivial.
  let e₁ : Monoid.CoprodI M ≃* Monoid.CoprodI (freeProduct M X).vertexGroup :=
    (Monoid.CoprodI.optionEquivOfSubsingleton (freeProductVertexGroup M)).symm
  have he₁ (i : ι) (m : M i) :
      Monoid.CoprodI.lift (π₁Tree.of (starRoseTree ι X).darts) (e₁ (.of m)) =
        π₁Tree.of (𝔸 := freeProduct M X) (starRoseTree ι X).darts (starRose.tip X i) m :=
    (congrArg _ (Monoid.CoprodI.optionEquivOfSubsingleton_symm_of (M := freeProductVertexGroup M)
      m)).trans (Monoid.CoprodI.lift_of ..)
  -- The free factor: the petals are the darts of the orientation outside the spokes.
  let e₂ : X ≃ ↥(starRoseOrientation ι X \ (starRoseTree ι X).darts) :=
    (starRose.petalEquiv ι X).trans
      (Set.equivOfEq (by rw [starRoseTree_darts]))
  have h : freeProductHom M X = (π₁Tree.ofCoprod (freeProduct M X) (starRoseTree ι X).darts
      (starRoseOrientation ι X)).comp
        (MulEquiv.coprodCongr e₁ (FreeGroup.freeGroupCongr e₂)).toMonoidHom := by
    ext <;> simp [he₁, e₂]
  exact h ▸ (π₁Tree.ofCoprod_bijective _ (isOrientation_starRoseOrientation ι X)
    (starRoseTree ι X).rev_mem).comp (MulEquiv.bijective _)

/-- The free product `∗ᵢ Mᵢ` is the fundamental group at the center of its graph of groups over the
star: `m ∈ Mᵢ` goes to the class of the loop that runs along the spoke `i`, reads `m` at its tip
and comes back (`coprodIEquivπ₁_of`). -/
noncomputable def coprodIEquivπ₁ :
    Monoid.CoprodI M ≃* π₁ (freeProduct M PEmpty.{1}) (starRose.center ι PEmpty) :=
  (MulEquiv.ofBijective ((freeProductHom M PEmpty).comp Monoid.Coprod.inl)
    ((freeProductHom_bijective M PEmpty).comp ⟨Monoid.Coprod.inl_injective, fun x =>
      ⟨Monoid.Coprod.fst x, by
        induction x using Monoid.Coprod.induction_on with
        | inl m => simp
        | inr n => simp [Subsingleton.elim n 1]
        | mul x y hx hy => simp [hx, hy]⟩⟩)).trans
    (π₁Equiv _ _ (starRoseTree ι _)).symm

/-- `coprodIEquivπ₁` sends `m ∈ Mᵢ` to the class of the loop that runs from the center along the
spoke `i`, reads `m` at the tip `i` and comes back. -/
@[simp] theorem coprodIEquivπ₁_of {i : ι} (m : M i) :
    coprodIEquivπ₁ M (Monoid.CoprodI.of m) = π₁.vertexHom
      ((dartPrefunctor (freeProduct M PEmpty.{1})).mapPath
        ((starRoseTree ι PEmpty).path (starRose.center ι PEmpty) (starRose.tip _ i))) m := by
  simp only [coprodIEquivπ₁, MulEquiv.trans_apply, MulEquiv.ofBijective_apply,
    MonoidHom.comp_apply, freeProductHom_inl_of]
  exact π₁Equiv_symm_of ..

end TauCeti.GraphOfGroups
