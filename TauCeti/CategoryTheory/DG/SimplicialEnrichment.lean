/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Forget
public import TauCeti.Algebra.Homology.Monoidal.TruncLE
public import TauCeti.AlgebraicTopology.DoldKan.Monoidal
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.SimplicialGroup
public import TauCeti.CategoryTheory.DG.Basic

/-!
# The simplicial enrichment of a differential graded category

Let `C` be a differential graded category over a commutative ring `R`, with cohomologically graded
Hom complexes `Hom(X, Y)`.  Read homologically, `Hom_m = Hom^{-m}`, and the good truncation
`τ_{≥ 0} Hom(X, Y)` keeps the terms of positive homological degree and the cycles in degree `0`.
Applying the Dold–Kan functor `Γ` and forgetting the linear structure gives a simplicial set
`Map(X, Y) = DK(τ_{≥ 0} Hom(X, Y))`.  Since the good truncation and `Γ` are lax monoidal (the
latter through the Alexander–Whitney map), and the forgetful functor from modules to types is lax
monoidal, the composite functor `TauCeti.dgMappingSpaceFunctor R` from cochain complexes to
simplicial sets is lax monoidal, and transporting the enrichment of `C` along it turns `C` into a
simplicially enriched category `TauCeti.DGSimplicialCategory R C`, the category `C_Δ` of Lurie,
*Higher Algebra*, Construction 1.3.1.13.  Its mapping simplicial sets are Kan complexes, since
they underlie simplicial modules.

The vertices of `Map(X, Y)` are the closed morphisms of degree `0`
(`TauCeti.dgMappingSpaceVertexEquiv`), the enriched identity of `X` is the vertex named by the
identity `TauCeti.dgId R X` (`TauCeti.dgSimplicialCategory_unit`; a map out of the unit `𝟙_ SSet` is
determined by its vertex, `SSet.unitHomEquiv`), and the enriched composition of two vertices is
their composition in `C` (`TauCeti.dgSimplicialCategory_comp`).  The homotopy-coherent nerve of
`C_Δ` is the source of Lurie's comparison map to the differential graded nerve of `C` (*Higher
Algebra*, Construction 1.3.1.16).

The enriched composition of `C` is Mathlib's `Hom(X, Y) ⊗ Hom(Y, Z) ⟶ Hom(X, Z)`, which is also
the composition order of Mathlib's simplicial categories, so no Koszul sign enters the
construction.

## Main definitions and results

* `TauCeti.dgMappingSpaceFunctor`: the lax monoidal functor `K ↦ DK(τ_{≥ 0} K)` from cochain
  complexes of `R`-modules to simplicial sets; its values are Kan complexes.
* `TauCeti.dgMappingSpaceVertex` and `TauCeti.dgMappingSpaceVertexEquiv`: the vertices of
  `DK(τ_{≥ 0} K)` are the cycles of `K` in degree `0`, compatibly with the lax monoidal structure
  (`TauCeti.dgMappingSpaceVertex_ε_app`, `TauCeti.dgMappingSpaceVertex_μ_app`).
* `TauCeti.DGSimplicialCategory`: the simplicial category `C_Δ` of a differential graded category.
* `TauCeti.dgSimplicialCategory_hom`: its mapping simplicial sets are `DK(τ_{≥ 0} Hom(X, Y))`.
* `TauCeti.dgSimplicialCategory_unit` and `TauCeti.dgSimplicialCategory_comp`: on vertices, its
  identities and composition are those of `C`.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.13 and Remark 1.3.1.14.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite HomologicalComplex ComplexShape

open scoped Simplicial

universe v u

namespace TauCeti

variable (R : Type v) [CommRing R]

/-- The functor `K ↦ DK(τ_{≥ 0} K)` from cochain complexes of `R`-modules to simplicial sets:
the good truncation `τ_{≥ 0}` (cycles in degree `0`, `K^{-n}` in degree `n > 0`), followed by the
Dold–Kan functor `Γ` and the forgetful functor from simplicial modules to simplicial sets.  It is
lax monoidal, and it carries the Hom complexes of a differential graded category to the mapping
simplicial sets of its simplicial enrichment `TauCeti.DGSimplicialCategory`. -/
def dgMappingSpaceFunctor : CochainComplex (ModuleCat.{v} R) ℤ ⥤ SSet.{v} :=
  embeddingDownNat.truncLE'Functor (ModuleCat.{v} R) ⋙ Idempotents.DoldKan.Γ ⋙
    (Functor.whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R))

/-- The functor `K ↦ DK(τ_{≥ 0} K)` is lax monoidal, as the composite of the lax monoidal good
truncation, the Dold–Kan functor with its Alexander–Whitney structure, and the forgetful functor
from modules to types. -/
instance : (dgMappingSpaceFunctor R).LaxMonoidal :=
  inferInstanceAs (embeddingDownNat.truncLE'Functor (ModuleCat.{v} R) ⋙ Idempotents.DoldKan.Γ ⋙
    (Functor.whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R))).LaxMonoidal

/-- The simplicial set `DK(τ_{≥ 0} K)` underlies a simplicial module, so it is a Kan complex. -/
instance (K : CochainComplex (ModuleCat.{v} R) ℤ) : ((dgMappingSpaceFunctor R).obj K).KanComplex :=
  inferInstanceAs (SSet.KanComplex (Idempotents.DoldKan.Γ.obj _ ⋙ forget (ModuleCat.{v} R)))

/-- The unit of `TauCeti.dgMappingSpaceFunctor` is that of the composite functor. -/
private lemma dgMappingSpaceFunctor_ε : Functor.LaxMonoidal.ε (dgMappingSpaceFunctor R) =
    Functor.LaxMonoidal.ε ((Functor.whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R))) ≫
      ((Functor.whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R))).map
        (Functor.LaxMonoidal.ε (Idempotents.DoldKan.Γ : ChainComplex (ModuleCat.{v} R) ℕ ⥤ _) ≫
          Idempotents.DoldKan.Γ.map
            (Functor.LaxMonoidal.ε (embeddingDownNat.truncLE'Functor (ModuleCat.{v} R)))) := by
  rw [Functor.map_comp]
  -- the lax monoidal structure of `dgMappingSpaceFunctor` is that of the composite functor
  rfl

/-- The tensorator of `TauCeti.dgMappingSpaceFunctor` is that of the composite functor. -/
private lemma dgMappingSpaceFunctor_μ (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    Functor.LaxMonoidal.μ (dgMappingSpaceFunctor R) K L =
    Functor.LaxMonoidal.μ ((Functor.whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R))) _ _ ≫
      ((Functor.whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R))).map
        (Functor.LaxMonoidal.μ (Idempotents.DoldKan.Γ : ChainComplex (ModuleCat.{v} R) ℕ ⥤ _) _ _ ≫
          Idempotents.DoldKan.Γ.map
            (Functor.LaxMonoidal.μ (embeddingDownNat.truncLE'Functor (ModuleCat.{v} R)) K L)) := by
  rw [Functor.map_comp]
  -- the lax monoidal structure of `dgMappingSpaceFunctor` is that of the composite functor
  rfl

/-! ### Vertices -/

variable {R}

/-- The degree-`0` cochain of `K` named by a vertex of `DK(τ_{≥ 0} K)`: the vertices of `Γ L` are
the elements of `L₀`, and degree `0` of `τ_{≥ 0} K` is the cycles of `K` in degree `0`.  It is a
cycle (`TauCeti.d_dgMappingSpaceVertex`), and every cycle arises from exactly one vertex
(`TauCeti.dgMappingSpaceVertexEquiv`). -/
def dgMappingSpaceVertex (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (x : ((dgMappingSpaceFunctor R).obj K) _⦋0⦌) : K.X 0 :=
  -- `K.truncLE'ToX 0` lands in `K.X (-(0 : ℕ))`, which is `K.X 0` by evaluation
  ((Idempotents.DoldKan.ΓObjZeroIso _).hom ≫ K.truncLE'ToX 0) x

/-- The cochain named by a vertex is a cycle. -/
lemma d_dgMappingSpaceVertex (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (x : ((dgMappingSpaceFunctor R).obj K) _⦋0⦌) : K.d 0 1 (dgMappingSpaceVertex K x) = 0 := by
  have h : ((Idempotents.DoldKan.ΓObjZeroIso _).hom ≫ K.truncLE'ToX 0) ≫ K.d 0 1 = 0 := by
    rw [Category.assoc]
    exact (congrArg (fun t ↦ _ ≫ t) (K.truncLE'ToX_zero_d 1)).trans comp_zero
  exact ConcreteCategory.congr_hom h x

/-- Distinct vertices name distinct cochains. -/
lemma dgMappingSpaceVertex_injective (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    Function.Injective (dgMappingSpaceVertex K) := by
  have : Mono ((Idempotents.DoldKan.ΓObjZeroIso (K.truncLE' embeddingDownNat)).hom ≫
    K.truncLE'ToX 0) := mono_comp _ _
  exact (ModuleCat.mono_iff_injective _).1 this

/-- Every cycle of degree `0` is named by a vertex. -/
lemma exists_dgMappingSpaceVertex_eq (K : CochainComplex (ModuleCat.{v} R) ℤ) (y : K.X 0)
    (hy : K.d 0 1 y = 0) : ∃ x, dgMappingSpaceVertex K x = y := by
  have hφ : ModuleCat.ofHom (LinearMap.toSpanSingleton R (K.X 0) y) ≫ K.d 0 1 = 0 := by
    ext; simp [hy]
  -- the cycle `y`, as a map `R ⟶ K.cycles 0`
  let c := K.liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton R (K.X 0) y)) 1 (by simp) hφ
  have hb : embeddingDownNat.BoundaryLE 0 := (boundaryLE_embeddingDownNat_iff 0).2 rfl
  refine ⟨(Idempotents.DoldKan.ΓObjZeroIso (K.truncLE' embeddingDownNat)).inv
    ((K.truncLE'XIsoCycles embeddingDownNat (embeddingDownNat_f 0) hb).inv (c (1 : R))), ?_⟩
  have key : c ≫ (K.truncLE'XIsoCycles embeddingDownNat (embeddingDownNat_f 0) hb).inv ≫
      (Idempotents.DoldKan.ΓObjZeroIso (K.truncLE' embeddingDownNat)).inv ≫
        (Idempotents.DoldKan.ΓObjZeroIso (K.truncLE' embeddingDownNat)).hom ≫ K.truncLE'ToX 0 =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R (K.X 0) y) := by
    rw [Iso.inv_hom_id_assoc, CochainComplex.truncLE'ToX_def,
      K.truncLE'ToRestriction_f_eq_iso_hom_iCycles_iso_inv embeddingDownNat
        (embeddingDownNat_f 0) hb]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
    exact K.liftCycles_i _ _ _ _
  exact (ConcreteCategory.congr_hom key 1).trans (by simp)

/-- The vertices of `DK(τ_{≥ 0} K)` are the cycles of `K` in degree `0`. -/
def dgMappingSpaceVertexEquiv (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    ((dgMappingSpaceFunctor R).obj K) _⦋0⦌ ≃ {y : K.X 0 // K.d 0 1 y = 0} :=
  Equiv.ofBijective (fun x ↦ ⟨dgMappingSpaceVertex K x, d_dgMappingSpaceVertex K x⟩)
    ⟨fun _ _ h ↦ dgMappingSpaceVertex_injective K (congrArg Subtype.val h),
      fun y ↦ (exists_dgMappingSpaceVertex_eq K y.1 y.2).imp fun _ h ↦ Subtype.ext h⟩

@[simp]
lemma dgMappingSpaceVertexEquiv_apply_coe (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (x : ((dgMappingSpaceFunctor R).obj K) _⦋0⦌) :
    (dgMappingSpaceVertexEquiv K x : K.X 0) = dgMappingSpaceVertex K x :=
  (rfl)

/-- The vertex of the unit of `TauCeti.dgMappingSpaceFunctor` names `1 : R`, in degree `0` of the
unit complex. -/
lemma dgMappingSpaceVertex_ε_app :
    dgMappingSpaceVertex (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))
      ((Functor.LaxMonoidal.ε (dgMappingSpaceFunctor R)).app (op ⦋0⦌) PUnit.unit) =
      (singleObjXSelf (up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv (1 : R) := by
  have h :
      (Functor.LaxMonoidal.ε (Idempotents.DoldKan.Γ : ChainComplex (ModuleCat.{v} R) ℕ ⥤ _)).app
        (op ⦋0⦌) ≫ (Idempotents.DoldKan.Γ.map (Functor.LaxMonoidal.ε
          (embeddingDownNat.truncLE'Functor (ModuleCat.{v} R)))).app (op ⦋0⦌) ≫
        (Idempotents.DoldKan.ΓObjZeroIso _).hom ≫
          (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)).truncLE'ToX 0 =
      (singleObjXSelf (up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv := by
    -- `erw`: the truncation appears both as `truncLE'Functor.obj` and as `truncLE'`
    erw [Idempotents.DoldKan.ΓObjZeroIso_hom_naturality_assoc,
      Idempotents.DoldKan.Γ_ε_app_zero_comp_ΓObjZeroIso_hom_assoc]
    refine (congrArg (fun t ↦ _ ≫ t) (CochainComplex.truncLE'Unit_f_truncLE'ToX R)).trans ?_
    rw [Iso.inv_hom_id_assoc]
    -- both sides are the identification of `R` with degree `0` of the unit complex
    rfl
  rw [dgMappingSpaceFunctor_ε]
  calc _ = (_ ≫ _ ≫ (Idempotents.DoldKan.ΓObjZeroIso _).hom ≫
          (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)).truncLE'ToX 0)
        (Functor.LaxMonoidal.ε (forget (ModuleCat.{v} R)) PUnit.unit) := rfl
    _ = _ := ConcreteCategory.congr_hom h _
    _ = _ := by rw [ModuleCat.ε_forget_apply]

/-- The vertex of the tensorator of `TauCeti.dgMappingSpaceFunctor` on two vertices names the
tensor product of the cycles they name, in degree `0` of the tensor product complex. -/
lemma dgMappingSpaceVertex_μ_app (K L : CochainComplex (ModuleCat.{v} R) ℤ)
    (x : ((dgMappingSpaceFunctor R).obj K) _⦋0⦌) (y : ((dgMappingSpaceFunctor R).obj L) _⦋0⦌) :
    dgMappingSpaceVertex (K ⊗ L) ((Functor.LaxMonoidal.μ (dgMappingSpaceFunctor R) K L).app
      (op ⦋0⦌) (x, y)) =
      ιTensorObj K L 0 0 0 (add_zero 0) (dgMappingSpaceVertex K x ⊗ₜ dgMappingSpaceVertex L y) := by
  have h : (Functor.LaxMonoidal.μ (Idempotents.DoldKan.Γ : ChainComplex (ModuleCat.{v} R) ℕ ⥤ _)
        _ _).app (op ⦋0⦌) ≫ (Idempotents.DoldKan.Γ.map (Functor.LaxMonoidal.μ
          (embeddingDownNat.truncLE'Functor (ModuleCat.{v} R)) K L)).app (op ⦋0⦌) ≫
        (Idempotents.DoldKan.ΓObjZeroIso _).hom ≫ (K ⊗ L).truncLE'ToX 0 =
      (((Idempotents.DoldKan.ΓObjZeroIso _).hom ≫ K.truncLE'ToX 0) ⊗ₘ
        ((Idempotents.DoldKan.ΓObjZeroIso _).hom ≫ L.truncLE'ToX 0)) ≫
          ιTensorObj K L (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) (by simp) := by
    -- `erw`: the truncation appears both as `truncLE'Functor.obj` and as `truncLE'`
    erw [Idempotents.DoldKan.ΓObjZeroIso_hom_naturality_assoc,
      Idempotents.DoldKan.Γ_μ_app_zero_comp_ΓObjZeroIso_hom_assoc]
    refine (congrArg (fun t ↦ _ ≫ t)
      (CochainComplex.ι_truncLE'TensorHom_f_truncLE'ToX (K := K) (L := L) 0 0 0 rfl)).trans ?_
    exact tensorHom_comp_tensorHom_assoc _ _ _ _ _
  rw [dgMappingSpaceFunctor_μ]
  calc _ = (_ ≫ _ ≫ (Idempotents.DoldKan.ΓObjZeroIso _).hom ≫ (K ⊗ L).truncLE'ToX 0)
        (Functor.LaxMonoidal.μ (forget (ModuleCat.{v} R)) _ _ (x, y)) := rfl
    _ = _ := ConcreteCategory.congr_hom h _
    _ = ((((Idempotents.DoldKan.ΓObjZeroIso _).hom ≫ K.truncLE'ToX 0) ⊗ₘ
        ((Idempotents.DoldKan.ΓObjZeroIso _).hom ≫ L.truncLE'ToX 0)) ≫
          ιTensorObj K L (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) (by simp))
          (x ⊗ₜ[R] y) := congrArg _ (ModuleCat.μ_forget_apply x y)
    -- the tensor product of two linear maps on a pure tensor, and `-(0 : ℕ) = 0` by evaluation
    _ = _ := rfl

/-- The vertices of `DK(τ_{≥ 0} K)` are natural in `K`. -/
@[simp]
lemma dgMappingSpaceVertex_map_app {K L : CochainComplex (ModuleCat.{v} R) ℤ} (f : K ⟶ L)
    (x : ((dgMappingSpaceFunctor R).obj K) _⦋0⦌) :
    dgMappingSpaceVertex L (((dgMappingSpaceFunctor R).map f).app (op ⦋0⦌) x) =
      f.f 0 (dgMappingSpaceVertex K x) := by
  have h : (Idempotents.DoldKan.Γ.map (truncLE'Map f embeddingDownNat)).app (op ⦋0⦌) ≫
      (Idempotents.DoldKan.ΓObjZeroIso _).hom ≫ L.truncLE'ToX 0 =
      ((Idempotents.DoldKan.ΓObjZeroIso _).hom ≫ K.truncLE'ToX 0) ≫ f.f 0 := by
    rw [Idempotents.DoldKan.ΓObjZeroIso_hom_naturality_assoc,
      CochainComplex.truncLE'Map_f_truncLE'ToX, Category.assoc]
    -- `f.f (-(0 : ℕ))` is `f.f 0` by evaluation
    rfl
  exact ConcreteCategory.congr_hom h x

/-! ### The simplicial category of a differential graded category -/

variable (R) (C : Type u) [DGCategory R C]

/-- **The simplicial enrichment** `C_Δ` of a differential graded category `C`: the same objects,
with mapping simplicial sets `DK(τ_{≥ 0} Hom(X, Y))` (`TauCeti.dgSimplicialCategory_hom`), and
enriched composition induced by the lax monoidal structures of the good truncation and of the
Dold–Kan functor (Lurie, *Higher Algebra*, Construction 1.3.1.13).  It is the transport of the
enrichment of `C` along `TauCeti.dgMappingSpaceFunctor`; its underlying ordinary category has as
morphisms the maps `𝟙_ SSet ⟶ Map(X, Y)`, that is, the vertices of the mapping simplicial sets.
Mathlib's `SimplicialCategory` instance is found through `CategoryTheory.ForgetEnrichment`. -/
abbrev DGSimplicialCategory : Type u :=
  ForgetEnrichment SSet.{v} (TransportEnrichment (dgMappingSpaceFunctor R) C)

variable {C}

/-- An object of a differential graded category, as an object of its simplicial enrichment. -/
abbrev DGSimplicialCategory.of (X : C) : DGSimplicialCategory R C := X

/-- The mapping simplicial sets of the simplicial enrichment of a differential graded category
are Kan complexes. -/
instance (X Y : DGSimplicialCategory R C) : (X ⟶[SSet.{v}] Y).KanComplex :=
  inferInstanceAs ((dgMappingSpaceFunctor R).obj _).KanComplex

variable {R}

/-- The mapping simplicial set from `X` to `Y` in the simplicial enrichment of a differential
graded category is the underlying simplicial set of `DK(τ_{≥ 0} Hom(X, Y))`. -/
lemma dgSimplicialCategory_hom (X Y : C) :
    (DGSimplicialCategory.of R X ⟶[SSet.{v}] DGSimplicialCategory.of R Y) =
      Idempotents.DoldKan.Γ.obj ((dgHomComplex R X Y).truncLE' embeddingDownNat) ⋙
        forget (ModuleCat.{v} R) :=
  (rfl)

/-- The enriched identity of `X` in the simplicial enrichment of a differential graded category
is the vertex named by the identity `TauCeti.dgId R X`.  A map out of `𝟙_ SSet` is determined by
this vertex (`SSet.unitHomEquiv`), so this identifies the enriched identity with the constant
simplex on `TauCeti.dgId R X`. -/
lemma dgSimplicialCategory_unit (X : C) :
    dgMappingSpaceVertex (dgHomComplex R X X)
      ((eId SSet.{v} (DGSimplicialCategory.of R X)).app (op ⦋0⦌) PUnit.unit) = dgId R X := by
  have h : eId SSet.{v} (DGSimplicialCategory.of R X) =
      Functor.LaxMonoidal.ε (dgMappingSpaceFunctor R) ≫
        (dgMappingSpaceFunctor R).map (eId (CochainComplex (ModuleCat.{v} R) ℤ) X) := rfl
  calc _ = dgMappingSpaceVertex (dgHomComplex R X X) (((dgMappingSpaceFunctor R).map
          (eId (CochainComplex (ModuleCat.{v} R) ℤ) X)).app (op ⦋0⦌)
            ((Functor.LaxMonoidal.ε (dgMappingSpaceFunctor R)).app (op ⦋0⦌) PUnit.unit)) := by
        rw [h]
        -- evaluate the composite of natural transformations at the vertex
        rfl
    _ = dgId R X := by
      rw [dgMappingSpaceVertex_map_app, dgMappingSpaceVertex_ε_app, dgId_def]

/-- On vertices, the enriched composition of the simplicial enrichment of a differential graded
category is the composition of closed degree-`0` morphisms. -/
lemma dgSimplicialCategory_comp {X Y Z : C}
    (f : (DGSimplicialCategory.of R X ⟶[SSet.{v}] DGSimplicialCategory.of R Y) _⦋0⦌)
    (g : (DGSimplicialCategory.of R Y ⟶[SSet.{v}] DGSimplicialCategory.of R Z) _⦋0⦌) :
    dgMappingSpaceVertex (dgHomComplex R X Z) ((eComp SSet.{v} (DGSimplicialCategory.of R X)
      (DGSimplicialCategory.of R Y) (DGSimplicialCategory.of R Z)).app (op ⦋0⦌) (f, g)) =
      dgComp R (dgMappingSpaceVertex (dgHomComplex R X Y) f)
        (dgMappingSpaceVertex (dgHomComplex R Y Z) g) (add_zero 0) := by
  have h : eComp SSet.{v} (DGSimplicialCategory.of R X) (DGSimplicialCategory.of R Y)
      (DGSimplicialCategory.of R Z) = Functor.LaxMonoidal.μ (dgMappingSpaceFunctor R) _ _ ≫
        (dgMappingSpaceFunctor R).map (eComp (CochainComplex (ModuleCat.{v} R) ℤ) X Y Z) := rfl
  calc _ = dgMappingSpaceVertex (dgHomComplex R X Z) (((dgMappingSpaceFunctor R).map
          (eComp (CochainComplex (ModuleCat.{v} R) ℤ) X Y Z)).app (op ⦋0⦌)
            ((Functor.LaxMonoidal.μ (dgMappingSpaceFunctor R) _ _).app (op ⦋0⦌) (f, g))) := by
        rw [h]
        -- evaluate the composite of natural transformations at the vertex
        rfl
    _ = _ := by
      rw [dgMappingSpaceVertex_map_app]
      -- `erw`: the vertices `f` and `g` are typed through the enriched Hom of `C_Δ`
      erw [dgMappingSpaceVertex_μ_app]
      rw [← dgCompMap_tmul, dgCompMap_def]
      -- `-(0 : ℕ) = 0` by evaluation
      rfl

end TauCeti
