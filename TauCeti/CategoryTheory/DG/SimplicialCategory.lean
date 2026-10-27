/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Forget
public import TauCeti.Algebra.Homology.Monoidal.TruncLE
public import TauCeti.AlgebraicTopology.DoldKan.Monoidal
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.SimplicialGroup
public import TauCeti.CategoryTheory.DG.Basic

/-!
# The simplicial enrichment of a differential graded category

A differential graded category `C` over `R` has Hom complexes `Hom(X, Y)`, cochain complexes of
`R`-modules.  Its *simplicial enrichment* `C_Δ` (J. Lurie, *Higher Algebra*, Construction 1.3.1.13)
has the same objects and, as mapping simplicial set from `X` to `Y`, the underlying simplicial set
of `DK(τ_{≥ 0} Hom(X, Y))`: the good truncation `τ_{≥ 0}` puts `Hom^{-n}(X, Y)` in homological
degree `n > 0` and the degree-zero cycles in degree `0`, and the Dold–Kan functor `DK = Γ` turns
this connective chain complex into a simplicial module.  Composition is induced by the lax monoidal
structures of the good truncation, of `Γ` (the Alexander–Whitney map) and of the forgetful functor
from modules to types, so `C_Δ` is a category enriched in simplicial sets, with Mathlib's factor
order `Hom(X, Y) × Hom(Y, Z) ⟶ Hom(X, Z)` for the enriched composition.  Its mapping simplicial sets
are Kan complexes, since they underlie simplicial modules.  The homotopy-coherent nerve of `C_Δ` is
the comparison target for the differential graded nerve.

On vertices the enrichment recovers the closed degree-zero morphisms of `C`: the vertices of
`DK(τ_{≥ 0} K)` are the degree-zero cycles of `K` (`TauCeti.dgMappingSpaceVertexEquiv`), the
enriched identity is the constant simplex on `TauCeti.dgId`
(`TauCeti.DGSimplicialCategory.eId_eq_const`), and the enriched composition of two vertices is
their composition `TauCeti.dgComp` (`TauCeti.DGSimplicialCategory.dgMappingSpaceVertexEquiv_eComp`).

## Main definitions

* `TauCeti.dgMappingSpaceFunctor`: the lax monoidal functor `K ↦ DK(τ_{≥ 0} K)` from cochain
  complexes of `R`-modules to simplicial sets.
* `TauCeti.DGSimplicialCategory`: the simplicial enrichment `C_Δ` of a differential graded
  category `C`, as Mathlib's `CategoryTheory.TransportEnrichment` along that functor.
* `TauCeti.dgMappingSpaceVertexEquiv`: the vertices of `DK(τ_{≥ 0} K)` are the degree-zero cycles
  of `K`.

## Main results

* `TauCeti.DGSimplicialCategory.eHom_eq`: the mapping simplicial set from `X` to `Y` is
  `DK(τ_{≥ 0} Hom(X, Y))`.
* The instance `SSet.KanComplex (X ⟶[SSet] Y)`: the mapping simplicial sets are Kan complexes.
* `TauCeti.DGSimplicialCategory.eId_eq_const` and
  `TauCeti.DGSimplicialCategory.dgMappingSpaceVertexEquiv_eId`: the enriched identity is the
  constant simplex on the identity of `C`.
* `TauCeti.DGSimplicialCategory.dgMappingSpaceVertexEquiv_eComp`: on vertices, the enriched
  composition is the composition of closed degree-zero morphisms.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.13 and Remark 1.3.1.14.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Opposite HomologicalComplex ComplexShape
  Idempotents.DoldKan Functor.LaxMonoidal

open scoped Simplicial

universe v u

namespace TauCeti

variable (R : Type v) [CommRing R]

/-- The functor sending a cochain complex `K` of `R`-modules to the simplicial set
`DK(τ_{≥ 0} K)`. -/
def dgMappingSpaceFunctor : CochainComplex (ModuleCat.{v} R) ℤ ⥤ SSet.{v} :=
  embeddingDownNat.truncLE'Functor (ModuleCat.{v} R) ⋙ Γ ⋙
    (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget (ModuleCat.{v} R))

/-- The lax monoidal structure of `K ↦ DK(τ_{≥ 0} K)`: the composite of the lax monoidal good
truncation, the lax monoidal Dold–Kan functor `Γ` and the lax monoidal forgetful functor from
modules to types, applied degreewise. -/
instance : (dgMappingSpaceFunctor R).LaxMonoidal :=
  inferInstanceAs (embeddingDownNat.truncLE'Functor (ModuleCat.{v} R) ⋙ Γ ⋙
    (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget (ModuleCat.{v} R))).LaxMonoidal

/-- The degree-zero inclusion `DK(τ_{≥ 0} K)₀ ≅ (τ_{≥ 0} K)₀ ⟶ K⁰` of the vertices of the mapping
space into the degree-zero term of `K`. -/
private def vertexHom (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    (Γ.obj (K.truncLE' embeddingDownNat)) _⦋0⦌ ⟶ K.X 0 :=
  (ΓObjZeroIso _).hom ≫ K.truncLE'ToX 0 ≫ (K.XIsoOfEq (by simp)).hom

private instance (K : CochainComplex (ModuleCat.{v} R) ℤ) : Mono (vertexHom R K) := by
  unfold vertexHom
  infer_instance

@[reassoc]
private lemma vertexHom_d (K : CochainComplex (ModuleCat.{v} R) ℤ) (j : ℤ) :
    vertexHom R K ≫ K.d 0 j = 0 := by
  rw [vertexHom, Category.assoc, Category.assoc, XIsoOfEq_hom_comp_d, K.truncLE'ToX_zero_d,
    Limits.comp_zero]

private lemma exists_vertexHom_eq (K : CochainComplex (ModuleCat.{v} R) ℤ) (x : K.X 0)
    (hx : K.d 0 1 x = 0) : ∃ y, vertexHom R K y = x := by
  refine ⟨(ΓObjZeroIso (K.truncLE' embeddingDownNat)).inv
    ((K.truncLE'XIsoCycles embeddingDownNat (by simp)
      ((boundaryLE_embeddingDownNat_iff 0).2 rfl)).inv (K.cyclesMk x 1 (by simp) hx)), ?_⟩
  simp only [vertexHom, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  rw [← ConcreteCategory.comp_apply, CochainComplex.truncLE'ToX_zero_comp_XIsoOfEq_hom,
    ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  exact K.i_cyclesMk x 1 _ hx

/-- The vertices of `DK(τ_{≥ 0} K)` are the degree-zero cycles of `K`: a vertex of `Γ(τ_{≥ 0} K)`
is an element of `(τ_{≥ 0} K)₀ = Z⁰ K`, included into `K⁰`. -/
def dgMappingSpaceVertexEquiv (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    ((dgMappingSpaceFunctor R).obj K) _⦋0⦌ ≃ {x : K.X 0 // K.d 0 1 x = 0} :=
  Equiv.ofBijective (fun y ↦ ⟨vertexHom R K y,
      -- the zero morphism of modules sends every element to `0`
      ConcreteCategory.congr_hom (vertexHom_d R K 1) y⟩)
    ⟨fun _ _ h ↦ (ModuleCat.mono_iff_injective (vertexHom R K)).1 inferInstance
        (congrArg Subtype.val h),
      fun x ↦ (exists_vertexHom_eq R K x.1 x.2).imp fun _ h ↦ Subtype.ext h⟩

private lemma dgMappingSpaceVertexEquiv_apply_coe (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (y : ((dgMappingSpaceFunctor R).obj K) _⦋0⦌) :
    (dgMappingSpaceVertexEquiv R K y).1 = vertexHom R K y :=
  (rfl)

@[reassoc]
private lemma Γ_map_truncLE'Map_app_zero_comp_vertexHom {K L : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K ⟶ L) :
    (Γ.map (truncLE'Map f embeddingDownNat)).app (op ⦋0⦌) ≫ vertexHom R L =
      vertexHom R K ≫ f.f 0 := by
  rw [vertexHom, Γ_map_app_zero_comp_ΓObjZeroIso_hom_assoc,
    CochainComplex.truncLE'Map_f_truncLE'ToX_assoc, XIsoOfEq_hom_naturality, vertexHom,
    Category.assoc, Category.assoc]

private lemma singleObjXIsoOfEq_inv_comp_XIsoOfEq_hom {k : ℤ} (hk : k = 0) :
    (singleObjXIsoOfEq (up ℤ) 0 (𝟙_ (ModuleCat.{v} R)) k hk).inv ≫
        ((𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)).XIsoOfEq hk).hom =
      (singleObjXSelf (up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv := by
  subst hk
  rw [XIsoOfEq_rfl, Iso.refl_hom]
  exact Category.comp_id _

private lemma ε_Γ_app_zero_comp_vertexHom :
    (ε (Γ : ChainComplex (ModuleCat.{v} R) ℕ ⥤ _)).app (op ⦋0⦌) ≫
        (Γ.map (CochainComplex.truncLE'Unit R)).app (op ⦋0⦌) ≫ vertexHom R _ =
      (singleObjXSelf (up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv := by
  rw [vertexHom, Γ_map_app_zero_comp_ΓObjZeroIso_hom_assoc, Γ_ε_app_zero_comp_ΓObjZeroIso_hom_assoc,
    CochainComplex.truncLE'Unit_f_truncLE'ToX_assoc, Iso.inv_hom_id_assoc,
    singleObjXIsoOfEq_inv_comp_XIsoOfEq_hom]

private lemma ιTensorObj_comp_XIsoOfEq_hom (K L : CochainComplex (ModuleCat.{v} R) ℤ) {p q n : ℤ}
    (hp : p = 0) (hq : q = 0) (hn : n = 0) (h : p + q = n) :
    ιTensorObj K L p q n h ≫ ((K ⊗ L).XIsoOfEq hn).hom =
      ((K.XIsoOfEq hp).hom ⊗ₘ (L.XIsoOfEq hq).hom) ≫ ιTensorObj K L 0 0 0 (by simp) := by
  subst hp hq hn
  rw [XIsoOfEq_rfl, XIsoOfEq_rfl, XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_hom, Iso.refl_hom,
    tensorHom_id, id_whiskerRight, Category.id_comp]
  exact Category.comp_id _

private lemma μ_Γ_app_zero_comp_vertexHom (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    (μ (Γ : ChainComplex (ModuleCat.{v} R) ℕ ⥤ _) _ _).app (op ⦋0⦌) ≫
        (Γ.map (CochainComplex.truncLE'TensorHom K L)).app (op ⦋0⦌) ≫ vertexHom R (K ⊗ L) =
      (vertexHom R K ⊗ₘ vertexHom R L) ≫ ιTensorObj K L 0 0 0 (by simp) := by
  rw [vertexHom, Γ_map_app_zero_comp_ΓObjZeroIso_hom_assoc, Γ_μ_app_zero_comp_ΓObjZeroIso_hom_assoc]
  dsimp only [Monoidal.tensorObj_obj]
  simp only [Category.assoc]
  rw [CochainComplex.ι_truncLE'TensorHom_f_truncLE'ToX_assoc,
    ιTensorObj_comp_XIsoOfEq_hom R K L (by simp) (by simp),
    tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, vertexHom, vertexHom]
  simp only [Category.assoc]

/-- The identification of the vertices of `DK(τ_{≥ 0} K)` with the degree-zero cycles of `K` is
natural in `K`. -/
@[simp]
lemma dgMappingSpaceVertexEquiv_map {K L : CochainComplex (ModuleCat.{v} R) ℤ} (f : K ⟶ L)
    (y : ((dgMappingSpaceFunctor R).obj K) _⦋0⦌) :
    (dgMappingSpaceVertexEquiv R L (((dgMappingSpaceFunctor R).map f).app (op ⦋0⦌) y)).1 =
      f.f 0 (dgMappingSpaceVertexEquiv R K y).1 := by
  rw [dgMappingSpaceVertexEquiv_apply_coe, dgMappingSpaceVertexEquiv_apply_coe]
  exact ConcreteCategory.congr_hom (Γ_map_truncLE'Map_app_zero_comp_vertexHom R f) y

/-- On vertices, the unit of the lax monoidal functor `dgMappingSpaceFunctor` picks out the
element `1` of the degree-zero term `R` of the unit complex. -/
lemma dgMappingSpaceVertexEquiv_ε (x : (𝟙_ SSet.{v}) _⦋0⦌) :
    (dgMappingSpaceVertexEquiv R _ ((ε (dgMappingSpaceFunctor R)).app (op ⦋0⦌) x)).1 =
      (singleObjXSelf (up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv (1 : R) := by
  refine (ConcreteCategory.congr_hom (ε_Γ_app_zero_comp_vertexHom R)
    (ε (CategoryTheory.forget (ModuleCat.{v} R)) x)).trans ?_
  rw [ModuleCat.forget_ε_apply]

/-- On vertices, the tensorator of the lax monoidal functor `dgMappingSpaceFunctor` sends a pair
of cycles to their tensor product, in degree zero of the tensor product complex. -/
lemma dgMappingSpaceVertexEquiv_μ (K L : CochainComplex (ModuleCat.{v} R) ℤ)
    (y : ((dgMappingSpaceFunctor R).obj K) _⦋0⦌) (z : ((dgMappingSpaceFunctor R).obj L) _⦋0⦌) :
    (dgMappingSpaceVertexEquiv R _ ((μ (dgMappingSpaceFunctor R) K L).app (op ⦋0⦌) (y, z))).1 =
      ιTensorObj K L 0 0 0 (by simp)
        ((dgMappingSpaceVertexEquiv R K y).1 ⊗ₜ (dgMappingSpaceVertexEquiv R L z).1) := by
  refine (ConcreteCategory.congr_hom (μ_Γ_app_zero_comp_vertexHom R K L)
    (μ (CategoryTheory.forget (ModuleCat.{v} R)) _ _ (y, z))).trans ?_
  rw [ModuleCat.forget_μ_apply]
  exact congrArg (ιTensorObj K L 0 0 0 (by simp))
    (ModuleCat.MonoidalCategory.tensorHom_tmul (vertexHom R K) (vertexHom R L) y z)

/-- **The simplicial enrichment of a differential graded category** `C_Δ`: the objects of `C`,
with mapping simplicial sets `DK(τ_{≥ 0} Hom(X, Y))` (`TauCeti.DGSimplicialCategory.eHom_eq`) and
composition induced by the lax monoidal structure of `TauCeti.dgMappingSpaceFunctor`. -/
abbrev DGSimplicialCategory (C : Type u) := TransportEnrichment (dgMappingSpaceFunctor R) C

variable {R} {C : Type u} [DGCategory R C]

namespace DGSimplicialCategory

/-- The mapping simplicial set of the simplicial enrichment from `X` to `Y` is the underlying
simplicial set of `DK(τ_{≥ 0} Hom(X, Y))`. -/
lemma eHom_eq (X Y : DGSimplicialCategory R C) :
    (X ⟶[SSet.{v}] Y) = (dgMappingSpaceFunctor R).obj (dgHomComplex R (C := C) X Y) :=
  (rfl)

/-- The mapping simplicial sets of the simplicial enrichment are Kan complexes, as underlying
simplicial sets of simplicial modules. -/
instance (X Y : DGSimplicialCategory R C) : SSet.KanComplex (X ⟶[SSet.{v}] Y) :=
  SimplicialObject.kanComplex_comp_forget_moduleCat _

/-- The vertex of the mapping space of `X` with itself picked out by the enriched identity is the
identity `TauCeti.dgId` of the differential graded category. -/
lemma dgMappingSpaceVertexEquiv_eId (X : DGSimplicialCategory R C) (x : (𝟙_ SSet.{v}) _⦋0⦌) :
    (dgMappingSpaceVertexEquiv R _ ((eId SSet.{v} X).app (op ⦋0⦌) x)).1 = dgId R (C := C) X := by
  rw [TransportEnrichment.eId_eq, SSet.comp_app, types_comp_apply, dgMappingSpaceVertexEquiv_map,
    dgMappingSpaceVertexEquiv_ε]
  exact (dgId_def R (C := C) X).symm

/-- On vertices, the enriched composition of the simplicial enrichment is the composition
`TauCeti.dgComp` of closed degree-zero morphisms. -/
lemma dgMappingSpaceVertexEquiv_eComp (X Y Z : DGSimplicialCategory R C)
    (f : (X ⟶[SSet.{v}] Y) _⦋0⦌) (g : (Y ⟶[SSet.{v}] Z) _⦋0⦌) :
    (dgMappingSpaceVertexEquiv R _ ((eComp SSet.{v} X Y Z).app (op ⦋0⦌) (f, g))).1 =
      dgComp R (C := C) (dgMappingSpaceVertexEquiv R _ f).1 (dgMappingSpaceVertexEquiv R _ g).1
        (add_zero 0) := by
  refine (dgMappingSpaceVertexEquiv_map R
    (eComp (CochainComplex (ModuleCat.{v} R) ℤ) (C := C) X Y Z)
    ((μ (dgMappingSpaceFunctor R) _ _).app (op ⦋0⦌) (f, g))).trans ?_
  rw [dgMappingSpaceVertexEquiv_μ]
  exact (ConcreteCategory.congr_hom (dgCompMap_def R (C := C) X Y Z 0 0 0 (add_zero 0))
    _).symm.trans (dgCompMap_tmul R (C := C) (add_zero 0) _ _)

/-- **The enriched identity is the constant simplex on the identity**: the enriched identity
`𝟙_ SSet ⟶ (X ⟶[SSet] X)` of the simplicial enrichment is the constant map at the vertex
`TauCeti.dgId X`. -/
lemma eId_eq_const (X : DGSimplicialCategory R C) :
    eId SSet.{v} X = SSet.const ((dgMappingSpaceVertexEquiv R _).symm
      ⟨dgId R (C := C) X, dgDifferential_dgId R (C := C) X⟩) := by
  have h₀ : (eId SSet.{v} X).app (op ⦋0⦌) PUnit.unit = (dgMappingSpaceVertexEquiv R _).symm
      ⟨dgId R (C := C) X, dgDifferential_dgId R (C := C) X⟩ :=
    (Equiv.eq_symm_apply _).2 (Subtype.ext (dgMappingSpaceVertexEquiv_eId X _))
  refine SSet.hom_ext fun n ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_
  -- every simplex of the terminal simplicial set is the degeneracy of its unique vertex
  refine (ConcreteCategory.congr_hom ((eId SSet.{v} X).naturality (n.unop.const ⦋0⦌ 0).op)
    PUnit.unit).trans ?_
  rw [types_comp_apply, h₀]
  simp [SSet.const_app]

end DGSimplicialCategory

end TauCeti
