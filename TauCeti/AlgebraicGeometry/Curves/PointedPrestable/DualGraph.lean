/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.DualGraph
public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.Category

/-!
# The dual graph of a pointed prestable curve

Let `P` be an `n`-pointed prestable curve over `Spec K` for a separably closed field `K`. Its total
space `P.total` is a proper connected nodal curve over `K` and its `n` markings are sections landing
in the smooth locus of `P.toBase`. Specializing `AlgebraicGeometry.Scheme.dualGraph` to `P.total`
and `P.marking` yields the combinatorial dual graph `P.dualGraph : DualGraph (Fin n)`.

This file packages the dual graph API in the category of pointed prestable curves:

* **General properties over connected bases**: the structure morphism `P.total ↘ S` is a prestable
  family (`TauCeti.AlgebraicGeometry.PointedPrestableFamily.prestableFamily_over`), the total space
  over a connected base is connected
  (`TauCeti.AlgebraicGeometry.PointedPrestableFamily.connectedSpace_total`), and distinct markings
  take distinct values at every base point
  (`TauCeti.AlgebraicGeometry.PointedPrestableFamily.marking_apply_injective`).
* **The dual graph and its components**: `PointedPrestableFamily.dualGraph`, the equivalence
  `PointedPrestableFamily.dualGraphIrreducibleComponentsEquiv` with `irreducibleComponents P.total`,
  the normalized component curves `PointedPrestableFamily.normalizedComponent`, and compatibility
  with `PointedPrestableFamily.reindex` (`PointedPrestableFamily.reindexDualGraphIso`).
* **Smooth validation**: when `P.toBase` is smooth, `P.dualGraph` has first Betti number zero and
  combinatorial arithmetic genus equal to `P.total.genus K`
  (`PointedPrestableFamily.arithmeticGenus_dualGraph_eq_genus_of_smooth`).
* **Functoriality under pointed isomorphisms**: any isomorphism `e : P ≅ Q` of pointed prestable
  curves induces an isomorphism `PointedPrestableFamily.dualGraphIsoOfIso e` of dual graphs,
  respecting `Iso.refl`, `Iso.trans`, and `Iso.symm`, and preserving `firstBetti`,
  `arithmeticGenus`, `IsStable`, and `IsSemistable`.
* **Invariance under extensions of separably closed fields**: for any extension `L / K` of separably
  closed fields, pulling `P` back along `Spec L ⟶ Spec K` induces a canonical isomorphism of dual
  graphs (`PointedPrestableFamily.dualGraphIsoPullback`).

## References

* [The Stacks Project, Tag 0E6S](https://stacks.math.columbia.edu/tag/0E6S): prestable curves.
* [The Stacks Project, Tag 0E6X](https://stacks.math.columbia.edu/tag/0E6X): semistable and stable
  curves.
* F. F. Knudsen, *The projectivity of the moduli space of stable curves, II: The stacks `M_{g,n}`*,
  Math. Scand. 52 (1983), 161–199, Definition 1.1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.PointedPrestableFamily

universe u

section General

variable {S : Scheme.{u}} {n : ℕ} (P : PointedPrestableFamily S n)

/-- Viewed through `P.instOverTotal`, the structure morphism `P.total ↘ S` is a prestable family. -/
instance prestableFamily_over : PrestableFamily (P.total ↘ S) :=
  P.over_eq_toBase.symm ▸ P.prestableFamily

/-- The total space of a pointed prestable family over a connected base is connected, its structure
morphism being open and geometrically connected. -/
instance connectedSpace_total [ConnectedSpace S] : ConnectedSpace P.total :=
  GeometricallyConnected.connectedSpace P.toBase P.toBase.isOpenMap

/-- Evaluating the markings of `P` at any point of the base is injective. -/
theorem marking_apply_injective (s : S) : Function.Injective (fun i ↦ P.marking i s) :=
  fun _ _ h ↦ Classical.not_not.mp fun hij ↦ P.marking_apply_ne hij s h

/-- Each marking lands in the smooth locus of `P.total ↘ S`. -/
theorem range_marking_subset_smoothLocus_over (i : Fin n) :
    Set.range (P.marking i) ⊆ (P.total ↘ S).smoothLocus := by
  have aux : ∀ (f : P.total ⟶ S) [LocallyOfFinitePresentation f],
      f = P.toBase → Set.range (P.marking i) ⊆ f.smoothLocus := by
    rintro _ _ rfl
    exact P.range_marking_subset_smoothLocus i
  exact aux (P.total ↘ S) P.over_eq_toBase

end General

section SepClosed

variable {K : Type u} [Field K] [IsSepClosed K] {m n : ℕ}
  (P Q R : PointedPrestableFamily (Spec (.of K)) n)

/-- **The dual graph of an `n`-pointed prestable curve over a separably closed field.** -/
@[expose]
def dualGraph : DualGraph (Fin n) :=
  P.total.dualGraph
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    P.marking P.range_marking_subset_smoothLocus_over

/-- Equivalence between vertices of `P.dualGraph` and irreducible components of `P.total`. -/
def dualGraphIrreducibleComponentsEquiv :
    P.dualGraph.Vertex ≃ irreducibleComponents P.total :=
  P.total.dualGraphIrreducibleComponentsEquiv
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    P.marking P.range_marking_subset_smoothLocus_over

/-- The normalized component scheme of `P.total` corresponding to a vertex `v` of `P.dualGraph`. -/
abbrev normalizedComponent (v : P.dualGraph.Vertex) : Scheme.{u} :=
  P.total.dualGraphComponent
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K))) v

@[simp]
theorem genus_dualGraph (v : P.dualGraph.Vertex) :
    P.dualGraph.genus v = (P.normalizedComponent v).genus K :=
  P.total.genus_dualGraph _ P.marking P.range_marking_subset_smoothLocus_over v

/-- The `i`-th marking of `P.dualGraph` is the unique irreducible component of `P.total` containing
the marked point `P.marking i default`. -/
theorem marking_dualGraph_eq_iff (i : Fin n) (v : P.dualGraph.Vertex) :
    P.dualGraph.marking i = v ↔
      P.marking i default ∈ (P.dualGraphIrreducibleComponentsEquiv v : Set P.total) :=
  P.total.marking_dualGraph_eq_iff _ P.marking P.range_marking_subset_smoothLocus_over i v

/-- The number of vertices of `P.dualGraph` equals the number of irreducible components of
`P.total`. -/
theorem card_vertex_dualGraph :
    Fintype.card P.dualGraph.Vertex = Nat.card (irreducibleComponents P.total) :=
  P.total.card_vertex_dualGraph _ P.marking P.range_marking_subset_smoothLocus_over

/-- The number of edges of `P.dualGraph` equals the number of singular points of `P.total`. -/
theorem card_edge_dualGraph :
    Fintype.card P.dualGraph.Edge = Nat.card (P.total.singularLocus K).support :=
  P.total.card_edge_dualGraph _ P.marking P.range_marking_subset_smoothLocus_over

/-- Reindexing the markings of `P` along `e : Fin m ↪ Fin n` reindexes `P.dualGraph` up to canonical
isomorphism. -/
def reindexDualGraphIso (e : Fin m ↪ Fin n) :
    (P.reindex e).dualGraph.Iso (P.dualGraph.reindex e) :=
  let e_tot : (P.reindex e).total ≅ P.total :=
    { hom := 𝟙 P.total
      inv := 𝟙 P.total }
  have hre := P.total.reindex_dualGraph
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    P.marking P.range_marking_subset_smoothLocus_over e
  (Scheme.dualGraphIsoOfIso
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := (P.reindex e).total ↘ Spec (.of K)))
    e_tot
    (by
      rw [over_eq_toBase, over_eq_toBase]
      exact Category.id_comp P.toBase)
    (P.marking ∘ e) (P.reindex e).marking
    (fun i ↦ P.range_marking_subset_smoothLocus_over (e i))
    (P.reindex e).range_marking_subset_smoothLocus_over
    (fun i ↦ Category.comp_id (P.marking (e i)))).trans
    (hre.symm ▸ DualGraph.Iso.refl (P.dualGraph.reindex e))

/-- When `P.toBase` is smooth, `P.dualGraph` is a single-vertex tree whose combinatorial arithmetic
genus coincides with the cohomological genus `P.total.genus K`. -/
theorem arithmeticGenus_dualGraph_eq_genus_of_smooth [Smooth P.toBase] :
    haveI : Smooth (P.total ↘ Spec (.of K)) := P.over_eq_toBase.symm ▸ ‹Smooth P.toBase›
    letI := P.total.smoothOfRelativeDimension_one_of_smooth
      (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    letI := finiteDimensional_cohomology_one_trivial_of_smooth K P.total
    P.dualGraph.firstBetti = 0 ∧ P.dualGraph.arithmeticGenus = P.total.genus K := by
  have : Smooth (P.total ↘ Spec (.of K)) := P.over_eq_toBase.symm ▸ ‹Smooth P.toBase›
  exact P.total.arithmeticGenus_dualGraph_eq_genus_of_smooth _ _ _

/-! ### Functoriality under isomorphisms of pointed prestable curves -/

section Iso

variable {P Q R}

/-- The isomorphism of total spaces underlying an isomorphism of pointed prestable families. -/
def totalIso {S : Scheme.{u}} {P Q : PointedPrestableFamily S n} (e : P ≅ Q) :
    P.total ≅ Q.total where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := by rw [← comp_hom, e.hom_inv_id, id_hom]
  inv_hom_id := by rw [← comp_hom, e.inv_hom_id, id_hom]

@[simp]
theorem totalIso_hom {S : Scheme.{u}} {P Q : PointedPrestableFamily S n} (e : P ≅ Q) :
    (totalIso e).hom = e.hom.hom :=
  (rfl)

@[simp]
theorem totalIso_inv {S : Scheme.{u}} {P Q : PointedPrestableFamily S n} (e : P ≅ Q) :
    (totalIso e).inv = e.inv.hom :=
  (rfl)

/-- An isomorphism `e : P ≅ Q` of `n`-pointed prestable curves over `Spec K` induces a canonical
isomorphism `P.dualGraph.Iso Q.dualGraph` of dual graphs. -/
def dualGraphIsoOfIso (e : P ≅ Q) : P.dualGraph.Iso Q.dualGraph :=
  Scheme.dualGraphIsoOfIso
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := Q.total ↘ Spec (.of K)))
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    (totalIso e)
    (by rw [totalIso_hom, over_eq_toBase, over_eq_toBase, e.hom.hom_comp_toBase])
    Q.marking P.marking
    Q.range_marking_subset_smoothLocus_over P.range_marking_subset_smoothLocus_over
    (fun i ↦ e.hom.marking_comp_hom i)

@[simp]
theorem dualGraphIsoOfIso_refl (P : PointedPrestableFamily (Spec (.of K)) n) :
    dualGraphIsoOfIso (Iso.refl P) = DualGraph.Iso.refl P.dualGraph :=
  Scheme.dualGraphIsoOfIso_refl _ P.marking P.range_marking_subset_smoothLocus_over

theorem dualGraphIsoOfIso_trans (e₁ : P ≅ Q) (e₂ : Q ≅ R) :
    dualGraphIsoOfIso (e₁ ≪≫ e₂) = (dualGraphIsoOfIso e₁).trans (dualGraphIsoOfIso e₂) :=
  Scheme.dualGraphIsoOfIso_trans _ _ _
    (totalIso e₁) (by rw [totalIso_hom, over_eq_toBase, over_eq_toBase, e₁.hom.hom_comp_toBase])
    (totalIso e₂) (by rw [totalIso_hom, over_eq_toBase, over_eq_toBase, e₂.hom.hom_comp_toBase])
    R.marking Q.marking P.marking
    R.range_marking_subset_smoothLocus_over Q.range_marking_subset_smoothLocus_over
    P.range_marking_subset_smoothLocus_over
    (fun i ↦ e₁.hom.marking_comp_hom i) (fun i ↦ e₂.hom.marking_comp_hom i)

@[simp]
theorem dualGraphIsoOfIso_symm (e : P ≅ Q) :
    dualGraphIsoOfIso e.symm = (dualGraphIsoOfIso e).symm :=
  Scheme.dualGraphIsoOfIso_symm _ _
    (totalIso e) (by rw [totalIso_hom, over_eq_toBase, over_eq_toBase, e.hom.hom_comp_toBase])
    Q.marking P.marking
    Q.range_marking_subset_smoothLocus_over P.range_marking_subset_smoothLocus_over
    (fun i ↦ e.hom.marking_comp_hom i)

theorem firstBetti_dualGraph_eq_of_iso (e : P ≅ Q) :
    P.dualGraph.firstBetti = Q.dualGraph.firstBetti :=
  (dualGraphIsoOfIso e).firstBetti_eq

theorem arithmeticGenus_dualGraph_eq_of_iso (e : P ≅ Q) :
    P.dualGraph.arithmeticGenus = Q.dualGraph.arithmeticGenus :=
  (dualGraphIsoOfIso e).arithmeticGenus_eq

theorem isStable_dualGraph_iff_of_iso (e : P ≅ Q) :
    P.dualGraph.IsStable ↔ Q.dualGraph.IsStable :=
  (dualGraphIsoOfIso e).isStable_iff

theorem isSemistable_dualGraph_iff_of_iso (e : P ≅ Q) :
    P.dualGraph.IsSemistable ↔ Q.dualGraph.IsSemistable :=
  (dualGraphIsoOfIso e).isSemistable_iff

end Iso

/-! ### Base change along extensions of separably closed fields -/

section BaseChange

variable (L : Type u) [Field L] [IsSepClosed L] [Algebra K L]

/-- **Invariance of the dual graph of a pointed prestable curve under extensions of separably
closed fields.** Pulling `P` back along `Spec L ⟶ Spec K` induces a canonical isomorphism of dual
graphs. -/
def dualGraphIsoPullback :
    (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).dualGraph.Iso P.dualGraph :=
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  Scheme.dualGraphIsoOfIsPullback
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := P.total ↘ Spec (.of K)))
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne
      (f := (P.pullback g).total ↘ Spec (.of L)))
    (g := Limits.pullback.fst P.toBase g)
    (by
      rw [over_eq_toBase, over_eq_toBase]
      exact IsPullback.of_hasPullback P.toBase g)
    P.marking (P.pullback g).marking
    P.range_marking_subset_smoothLocus_over
    (P.pullback g).range_marking_subset_smoothLocus_over
    (P.pullback_marking_fst g)

@[simp]
theorem firstBetti_dualGraph_pullback :
    (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).dualGraph.firstBetti =
      P.dualGraph.firstBetti :=
  (P.dualGraphIsoPullback L).firstBetti_eq

@[simp]
theorem arithmeticGenus_dualGraph_pullback :
    (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).dualGraph.arithmeticGenus =
      P.dualGraph.arithmeticGenus :=
  (P.dualGraphIsoPullback L).arithmeticGenus_eq

@[simp]
theorem isStable_dualGraph_pullback_iff :
    (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).dualGraph.IsStable ↔
      P.dualGraph.IsStable :=
  (P.dualGraphIsoPullback L).isStable_iff

@[simp]
theorem isSemistable_dualGraph_pullback_iff :
    (P.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).dualGraph.IsSemistable ↔
      P.dualGraph.IsSemistable :=
  (P.dualGraphIsoPullback L).isSemistable_iff

end BaseChange

end SepClosed

end TauCeti.AlgebraicGeometry.PointedPrestableFamily
