/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.CompStruct
public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import TauCeti.AlgebraicTopology.SimplicialSet.StrictSegal

/-!
# The essential image of the nerve

A simplicial set is isomorphic to the nerve of a category exactly when it is strict Segal
(`SSet.mem_essImage_nerveFunctor_iff`): nerves are strict Segal, and conversely a strict Segal
simplicial set `X` is the nerve of its homotopy category `X.HomotopyCategory`. Equivalently, the
unit `X ⟶ nerve X.HomotopyCategory` of Mathlib's adjunction `nerveAdjunction` is an isomorphism
exactly when `X` is strict Segal (`SSet.isIso_nerveAdjunction_unit_app_iff`).

The point is that the morphisms of the homotopy category of a strict Segal simplicial set are
exactly its edges (`SSet.HomotopyCategory.homMk_bijective`). Mathlib's homotopy category is a
quotient of the category of paths of edges, so this needs two facts. Every composite of edges is
again an edge, the third edge of the triangle with the given spine, so every morphism is
represented by an edge. Two edges that represent the same morphism are homotopic in the sense of
Mathlib's `SSet.Truncated.HomotopyCategory₂`, through a triangle whose spine is the first edge
followed by an identity; in a strict Segal simplicial set that triangle is degenerate, so the two
edges are equal.

Hence the morphism from the `2`-truncation of `X` to the `2`-truncated nerve of its homotopy
category that corresponds to the identity functor under Mathlib's
`SSet.Truncated.HomotopyCategory.functorEquiv` is bijective on edges, so it is an isomorphism
(`SSet.Truncated.isIso_of_isStrictSegal`). Strict Segal simplicial sets and nerves are
`2`-coskeletal, which extends the isomorphism to all dimensions.

## Main results

* `SSet.HomotopyCategory.homMk_bijective`: in a strict Segal simplicial set, the edges from `x` to
  `y` are the morphisms from `x` to `y` in the homotopy category.
* `SSet.isIso_homToNerveMk_id`: for strict Segal `X`, the morphism from the `2`-truncation of `X`
  to the `2`-truncated nerve of `X.HomotopyCategory` given by the identity functor is an
  isomorphism.
* `SSet.mem_essImage_nerveFunctor_iff`: a simplicial set is isomorphic to the nerve of a category
  exactly when it is strict Segal.
* `SSet.isIso_nerveAdjunction_unit_app_iff`: the unit of `nerveAdjunction` at `X` is an isomorphism
  exactly when `X` is strict Segal.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS 34 (1968), 105--112.
-/

public section

open CategoryTheory Simplicial SimplexCategory.Truncated

universe u

namespace SSet

variable {X : SSet.{u}} [X.IsStrictSegal]

namespace HomotopyCategory

/-- In a strict Segal simplicial set, every morphism of the homotopy category is represented by
an edge, since every composite of two edges is again represented by an edge. -/
lemma exists_homMk_eq {x y : X.HomotopyCategory} (f : x ⟶ y) :
    ∃ e : Edge (objEquiv x) (objEquiv y), homMk e = f := by
  induction f using hom_rec with
  | homMk e => exact ⟨e, rfl⟩
  | comp f g hf hg =>
    obtain ⟨e, rfl⟩ := hf
    obtain ⟨e', rfl⟩ := hg
    exact ⟨e.comp e', (homMk_comp_homMk (e.compStruct e')).symm⟩

/-- In a strict Segal simplicial set, two parallel edges representing the same morphism of the
homotopy category are equal. -/
lemma homMk_injective {x y : X _⦋0⦌} :
    Function.Injective (homMk : Edge x y → (mk x ⟶ mk y)) := by
  intro e e' h
  -- Compare with the homotopy category whose morphisms are homotopy classes of edges.
  let G : X.HomotopyCategory ⥤ Truncated.HomotopyCategory₂ ((truncation 2).obj X) :=
    Truncated.HomotopyCategory.lift (fun x ↦ .mk x) (fun e ↦ Truncated.HomotopyCategory₂.homMk e)
      (fun _ ↦ rfl) (fun h ↦ h.homotopyCategory₂_fac)
  have hG (e : Edge x y) : G.map (homMk e) = Truncated.HomotopyCategory₂.homMk e.toTruncated :=
    Truncated.HomotopyCategory.lift_map_homMk _ _ _ _ _
  obtain ⟨hc⟩ := (Truncated.HomotopyCategory₂.homMk_eq_iff_homotopicL).1
    ((hG e).symm.trans ((congr_arg G.map h).trans (hG e')))
  exact (Edge.CompStruct.compId e).eq_of_isStrictSegal (Edge.CompStruct.ofTruncated hc)

/-- In a strict Segal simplicial set, the edges from `x` to `y` are exactly the morphisms from `x`
to `y` in the homotopy category. -/
theorem homMk_bijective {x y : X _⦋0⦌} :
    Function.Bijective (homMk : Edge x y → (mk x ⟶ mk y)) :=
  ⟨homMk_injective, exists_homMk_eq⟩

/-- In a strict Segal simplicial set, two edges define the same arrow of the homotopy category
exactly when they are equal as `1`-simplices. -/
lemma arrowMk_homMk_eq_arrowMk_homMk_iff {x y x' y' : X _⦋0⦌} {e : Edge x y}
    {e' : Edge x' y'} : Arrow.mk (homMk e) = Arrow.mk (homMk e') ↔ e.edge = e'.edge := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨h₁, h₂, h⟩ := (Arrow.mk_eq_mk_iff _ _).1 h
    obtain rfl : x = x' := congr_arg objEquiv h₁
    obtain rfl : y = y' := congr_arg objEquiv h₂
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
    rw [homMk_injective h]
  · obtain rfl : x = x' := by rw [← e.src_eq, ← e'.src_eq, h]
    obtain rfl : y = y' := by rw [← e.tgt_eq, ← e'.tgt_eq, h]
    rw [Edge.ext h]

end HomotopyCategory

omit [X.IsStrictSegal] in
open HomotopyCategory in
/-- The morphism from the `2`-truncation of `X` to the `2`-truncated nerve of its homotopy
category corresponding to the identity functor sends an edge `s` to the morphism it represents.
This is Mathlib's `SSet.Truncated.HomotopyCategory.homToNerveMk_app_one`, rederived from
`homToNerveMk_app_edge`: the statement of the former mentions an auxiliary proof that is private
to its module, so the kernel cannot check its uses outside Mathlib. -/
private lemma homToNerveMk_id_app_one (s : X _⦋1⦌) :
    (Truncated.HomotopyCategory.homToNerveMk (𝟭 X.HomotopyCategory)).app (.op ⦋1⦌₂) s =
      ComposableArrows.mk₁ (homMk (Edge.mk' s)) :=
  Truncated.HomotopyCategory.homToNerveMk_app_edge _ (Edge.mk' s).toTruncated

open HomotopyCategory in
/-- For a strict Segal simplicial set `X`, the morphism from the `2`-truncation of `X` to the
`2`-truncated nerve of its homotopy category corresponding to the identity functor is an
isomorphism: it is bijective on edges by `SSet.HomotopyCategory.homMk_bijective`. -/
instance isIso_homToNerveMk_id :
    IsIso (Truncated.HomotopyCategory.homToNerveMk (𝟭 X.HomotopyCategory)) := by
  refine Truncated.isIso_of_isStrictSegal (n := 1) _ ⟨fun s t h ↦ ?_, fun A ↦ ?_⟩
  · rw [homToNerveMk_id_app_one, homToNerveMk_id_app_one] at h
    exact (arrowMk_homMk_eq_arrowMk_homMk_iff (e := Edge.mk' s) (e' := Edge.mk' t)).1
      (congr_arg ComposableArrows.arrowEquiv h)
  · obtain ⟨_, _, f, rfl⟩ := ComposableArrows.mk₁_surjective A
    obtain ⟨e, rfl⟩ := exists_homMk_eq f
    exact ⟨e.edge, Truncated.HomotopyCategory.homToNerveMk_app_edge _ e.toTruncated⟩

/-- A simplicial set is isomorphic to the nerve of a category exactly when it is strict Segal. A
strict Segal simplicial set is the nerve of its homotopy category. -/
theorem mem_essImage_nerveFunctor_iff {X : SSet.{u}} :
    nerveFunctor.{u, u}.essImage X ↔ X.IsStrictSegal := by
  refine ⟨fun ⟨C, ⟨e⟩⟩ ↦ IsStrictSegal.of_iso (X := nerve C) e,
    fun _ ↦ ⟨Cat.of X.HomotopyCategory, ⟨?_⟩⟩⟩
  -- Both sides are `2`-coskeletal, and their `2`-truncations are identified by the unit.
  exact (SimplicialObject.isoCoskOfIsCoskeletal X 2 ≪≫
    (Truncated.cosk 2).mapIso
      (asIso (Truncated.HomotopyCategory.homToNerveMk (𝟭 X.HomotopyCategory))) ≪≫
    (Nerve.cosk₂Iso.app (Cat.of X.HomotopyCategory)).symm).symm

/-- The unit `X ⟶ nerve X.HomotopyCategory` of the adjunction between simplicial sets and
categories is an isomorphism exactly when `X` is strict Segal. -/
theorem isIso_nerveAdjunction_unit_app_iff {X : SSet.{u}} :
    IsIso (nerveAdjunction.unit.app X) ↔ X.IsStrictSegal :=
  nerveAdjunction.isIso_unit_app_iff_mem_essImage.trans mem_essImage_nerveFunctor_iff

end SSet
