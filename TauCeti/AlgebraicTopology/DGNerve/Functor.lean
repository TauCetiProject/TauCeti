/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.HomotopyCategory
public import TauCeti.CategoryTheory.DG.Functor.Basic
import TauCeti.CategoryTheory.EqToHom

/-!
# Functoriality of the differential graded nerve

A differential graded functor acts on every coherence of a dg simplex by its map on the
corresponding homogeneous morphisms. This commutes with faces and degeneracies, including
collapsed coherences, and gives a simplicial map between the differential graded nerves.
The construction preserves identities and composition strictly.

The comparison between the homotopy category of the dg nerve and the degree-zero homology
category is natural under these maps. Thus a functor constructed at the dg level induces the
same ordinary functor whether one first takes the dg nerve or first takes degree-zero homology.
This is needed when transporting functors between dg models to their enhancements.

## Main declarations

* `CategoryTheory.EnrichedFunctor.mapDGNerveSimplex`: the image of a dg simplex.
* `CategoryTheory.EnrichedFunctor.mapDGNerve`: the induced map of simplicial sets.
* `CategoryTheory.EnrichedFunctor.mapDGNerve_comp_fromHomotopyCategory`: compatibility with
  the comparison to the degree-zero homology category.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.6 and Remark 1.3.1.11.
-/

public section

open CategoryTheory Finset Simplicial TauCeti TauCeti.DGNerve

universe v u u₁ u₂ u₃

namespace CategoryTheory.EnrichedFunctor

noncomputable section

variable {R : Type v} [CommRing R]

section Simplex

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [DGCategory R C] [DGCategory R D] [DGCategory R E]
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)
  (G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) D E)

/-- The image of a dg simplex under a DG functor: apply the functor to its objects and
its homogeneous map to each coherence. -/
-- The object formula must reduce so that the types of the coherences in the API agree.
@[expose]
def mapDGNerveSimplex {n : ℕ} (x : Simplex R C n) : Simplex R D n where
  obj i := F.obj (x.obj i)
  coh i j S d hij hS hd := F.dgMap d (x.coh i j S d hij hS hd)
  coh_self i := by simp
  dgDifferential_coh i j S d hij hS hd := by
    rw [← dgMap_dgDifferential, x.dgDifferential_coh]
    simp only [boundary_def, map_sum, map_zsmul_unit, map_sub, dgMap_dgComp]

/-- A DG functor applies its object map at every vertex of a dg simplex. -/
@[simp]
theorem mapDGNerveSimplex_obj {n : ℕ} (x : Simplex R C n) (i : Fin (n + 1)) :
    (F.mapDGNerveSimplex x).obj i = F.obj (x.obj i) :=
  (rfl)

/-- A DG functor applies its degree-`d` map to every degree-`d` coherence. -/
@[simp]
theorem mapDGNerveSimplex_coh {n : ℕ} (x : Simplex R C n) (i j : Fin (n + 1))
    (S : Finset (Fin (n + 1))) (d : ℤ) (hij : i ≤ j) (hS : S ⊆ Ioo i j)
    (hd : d + #S = 0) :
    (F.mapDGNerveSimplex x).coh i j S d hij hS hd =
      F.dgMap d (x.coh i j S d hij hS hd) :=
  (rfl)

/-- Taking the image under a DG functor commutes with all simplicial operators. -/
theorem mapDGNerveSimplex_map {n m : ℕ} (x : Simplex R C n)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    F.mapDGNerveSimplex (x.map α) = (F.mapDGNerveSimplex x).map α := by
  refine Simplex.ext rfl fun i j S d hij hS hd ↦ heq_of_eq ?_
  simp only [mapDGNerveSimplex_coh, Simplex.map_obj, Function.comp_apply]
  rw [Simplex.map_coh, Simplex.map_coh]
  by_cases h : #(S.image α) = #S ∧ S.image α ⊆ Ioo (α i) (α j)
  · rw [Simplex.mapCoh_eq_coh _ _ h, Simplex.mapCoh_eq_coh _ _ h,
      mapDGNerveSimplex_coh]
    -- Unfold the simplex object map in the endpoint types of these coherences.
    rfl
  · rw [Simplex.mapCoh_eq_zero _ _ h, Simplex.mapCoh_eq_zero _ _ h]
    exact (F.dgMap d).map_zero

/-- The identity DG functor fixes every dg simplex. -/
@[simp]
theorem id_mapDGNerveSimplex {n : ℕ} (x : Simplex R C n) :
    (EnrichedFunctor.id (CochainComplex (ModuleCat.{v} R) ℤ) C).mapDGNerveSimplex x = x := by
  refine Simplex.ext rfl fun i j S d hij hS hd ↦ heq_of_eq ?_
  rw [mapDGNerveSimplex_coh, id_dgMap]

/-- The image of a dg simplex under a composite is its iterated image. -/
@[simp]
theorem comp_mapDGNerveSimplex {n : ℕ} (x : Simplex R C n) :
    (F.comp (CochainComplex (ModuleCat.{v} R) ℤ) G).mapDGNerveSimplex x =
      G.mapDGNerveSimplex (F.mapDGNerveSimplex x) := by
  refine Simplex.ext rfl fun i j S d hij hS hd ↦ heq_of_eq ?_
  rw [mapDGNerveSimplex_coh, comp_dgMap, mapDGNerveSimplex_coh, mapDGNerveSimplex_coh]
  -- The composite object map and the two simplex object maps agree definitionally.
  rfl

/-- A DG functor sends the vertex of an object to the vertex of its image. -/
@[simp]
theorem mapDGNerveSimplex_vertex (X : C) :
    F.mapDGNerveSimplex (Simplex.vertex X) = Simplex.vertex (F.obj X) :=
  Simplex.ext_zero rfl

end Simplex

section SimplicialMap

-- A simplicial map has source and target in the same universe. The simplex construction
-- above allows independently sized object types; here both categories live in `Type u`.
variable {C D E : Type u} [DGCategory R C] [DGCategory R D] [DGCategory R E]
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)
  (G : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) D E)

/-- The simplicial map of differential graded nerves induced by a DG functor. -/
def mapDGNerve : dgNerve R C ⟶ dgNerve R D where
  app _ := ↾fun x ↦ F.mapDGNerveSimplex x
  naturality _ _ α := by
    ext x
    exact F.mapDGNerveSimplex_map x α.unop.toOrderHom

/-- The induced simplicial map acts by applying the DG functor to a dg simplex. -/
@[simp]
theorem mapDGNerve_app {Δ : SimplexCategoryᵒᵖ} (x : (dgNerve R C).obj Δ) :
    F.mapDGNerve.app Δ x = F.mapDGNerveSimplex x :=
  (rfl)

/-- The image of a vertex corresponds to the image object under the DG functor. -/
@[simp]
theorem dgNerveEquiv_mapDGNerveSimplex (x : (dgNerve R C) _⦋0⦌) :
    dgNerveEquiv R D (F.mapDGNerveSimplex x) = F.obj (dgNerveEquiv R C x) := by
  simp only [dgNerveEquiv_apply R D (F.mapDGNerveSimplex x), dgNerveEquiv_apply R C x,
    F.mapDGNerveSimplex_obj x 0]

/-- The dg nerve of the identity DG functor is the identity simplicial map. -/
@[simp]
theorem id_mapDGNerve :
    (EnrichedFunctor.id (CochainComplex (ModuleCat.{v} R) ℤ) C).mapDGNerve = 𝟙 (dgNerve R C) := by
  ext Δ x
  exact id_mapDGNerveSimplex x

/-- The dg nerve preserves composition of DG functors. -/
@[simp]
theorem comp_mapDGNerve :
    (F.comp (CochainComplex (ModuleCat.{v} R) ℤ) G).mapDGNerve =
      F.mapDGNerve ≫ G.mapDGNerve := by
  ext Δ x
  exact F.comp_mapDGNerveSimplex G x

/-- The comparison from the homotopy category of the dg nerve to `H⁰` commutes with
DG functors. In particular, the functor induced by the enhanced map is the usual `H⁰(F)`. -/
theorem mapDGNerve_comp_fromHomotopyCategory :
    SSet.mapHomotopyCategory F.mapDGNerve ⋙ dgNerve.fromHomotopyCategory R D =
      dgNerve.fromHomotopyCategory R C ⋙ F.mapDGHomotopyCategory := by
  -- First identify the object maps through the vertex comparison.
  have hobj (x : (dgNerve R C) _⦋0⦌) :
      (SSet.mapHomotopyCategory F.mapDGNerve ⋙ dgNerve.fromHomotopyCategory R D).obj
          (SSet.HomotopyCategory.mk x) =
        (dgNerve.fromHomotopyCategory R C ⋙ F.mapDGHomotopyCategory).obj
          (SSet.HomotopyCategory.mk x) := by
    rw [Functor.comp_obj, SSet.mapHomotopyCategory_obj_mk,
      dgNerve.fromHomotopyCategory_obj_mk, Functor.comp_obj,
      dgNerve.fromHomotopyCategory_obj_mk, mapDGHomotopyCategory_obj_of]
    rw [mapDGNerve_app, dgNerveEquiv_mapDGNerveSimplex]
  -- State endpoint identities before passing through truncation, so their dimensions
  -- are explicit when rewriting the simplex object map.
  have hmap (z : (dgNerve R C) _⦋0⦌) (X : C) (hz : Simplex.obj z 0 = X) :
      Simplex.obj (F.mapDGNerve.app (Opposite.op ⦋0⦌) z) 0 = F.obj X := by
    rw [mapDGNerve_app, F.mapDGNerveSimplex_obj z 0, hz]
  have hfrom (z : (dgNerve R C) _⦋0⦌) (X : C) (hz : Simplex.obj z 0 = X) :
      (dgNerve.fromHomotopyCategory R C).obj (SSet.HomotopyCategory.mk z) =
        DGHomotopyCategory.of R X := by
    rw [dgNerve.fromHomotopyCategory_obj_mk, dgNerveEquiv_apply, hz]
  -- It remains to compare edge generators: both maps apply dgMap to their coherence.
  refine SSet.Truncated.HomotopyCategory.functor_ext (fun x ↦ hobj x) (fun x y e ↦ ?_)
  let e' : (dgNerve R C).Edge x y := SSet.Edge.ofTruncated e
  let c : dgCycles R (e'.edge.obj 0) (e'.edge.obj 1) :=
    ⟨_, e'.edge.coh_zero_one_mem_dgCycles⟩
  have hx : Simplex.obj x 0 = e'.edge.obj 0 :=
    congrArg (fun z : (dgNerve R C) _⦋0⦌ ↦ Simplex.obj z 0) e'.src_eq.symm
  have hy : Simplex.obj y 0 = e'.edge.obj 1 :=
    congrArg (fun z : (dgNerve R C) _⦋0⦌ ↦ Simplex.obj z 0) e'.tgt_eq.symm
  have hx' := hmap x _ hx
  have hy' := hmap y _ hy
  have hl := dgNerve.fromHomotopyCategory_map_homMk_heq R D (e'.map F.mapDGNerve)
    hx' hy' (F.dgMap 0 c.1) (F.dgMap_mem_dgCycles c.2) (by
      rw [SSet.Edge.map_edge, mapDGNerve_app]
      exact heq_of_eq (F.mapDGNerveSimplex_coh e'.edge 0 1 ∅ 0
        (by decide) (empty_subset _) (by simp)))
  have hr := F.mapDGHomotopyCategory.map_heq
    (hfrom x _ hx) (hfrom y _ hy)
    (dgNerve.fromHomotopyCategory_map_homMk_heq R C e' hx hy c.1 c.2 HEq.rfl)
  rw [mapDGHomotopyCategory_map_homOf] at hr
  exact (conj_eqToHom_iff_heq' _ _ _ _).2 (hl.trans hr.symm)

end SimplicialMap

end

end CategoryTheory.EnrichedFunctor
