/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Forget
public import TauCeti.Algebra.Homology.Monoidal.TruncLE
public import TauCeti.AlgebraicTopology.DoldKan.Monoidal
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.SimplicialGroup
public import TauCeti.CategoryTheory.DG.ClosedCategory
public import TauCeti.CategoryTheory.Monoidal.UnitHom

/-!
# The simplicial category of a differential graded category

A differential graded category `C` over a commutative ring `R` has a simplicially enriched
counterpart `C_Δ` (J. Lurie, *Higher Algebra*, Construction 1.3.1.13): it has the same objects,
and the mapping simplicial set from `X` to `Y` is the underlying simplicial set of the Dold–Kan
image `DK(τ_{≥ 0} Hom(X, Y))` of the good truncation of the Hom complex. Here `τ_{≥ 0}` keeps the
Hom complex in non-positive cohomological degrees and its cycles in degree `0`, reindexed as a
chain complex, so the `n`-th homotopy group of a mapping space is the cohomology `H^{-n}` of the
Hom complex.

The construction transports the enrichment along the composite
`TauCeti.doldKanSSetFunctor R` of three lax monoidal functors: the good truncation
(`CochainComplex.truncLE'FunctorLaxMonoidal`), the Dold–Kan functor `Γ` with its
Alexander–Whitney structure (`CategoryTheory.Idempotents.DoldKan.laxMonoidalΓ`) and the
forgetful functor from simplicial modules to simplicial sets (`ModuleCat.forgetLaxMonoidal`).
The enriched composition is therefore induced by the lax monoidal structures, and its unit and
associativity laws are those of Mathlib's `CategoryTheory.TransportEnrichment`.

Each of the three functors induces bijections on maps out of the tensor units; for the composite,
maps `𝟙_ ⟶ K` from the unit complex, which are the degree-`0` cycles of `K`, are the vertices of
`DK(τ_{≥ 0} K)` (`TauCeti.bijective_ε_comp_doldKanSSetFunctor_map`). The underlying ordinary
category of `C_Δ` is therefore the category of closed degree-zero morphisms of `C`, and `C_Δ` is a
simplicial category in Mathlib's sense (`TauCeti.dgSimplicialCategory`), to which Mathlib's
homotopy coherent nerve `CategoryTheory.SimplicialNerve` applies. Its mapping simplicial sets are
Kan complexes, since simplicial modules are.

## Main definitions and results

* `TauCeti.doldKanSSetFunctor`: the lax monoidal functor `K ↦ DK(τ_{≥ 0} K)` from cochain
  complexes of `R`-modules to simplicial sets.
* `TauCeti.DGSimplicialCategory`: the simplicial category `C_Δ` of a differential graded category.
* `TauCeti.dgSimplicialCategory`: its simplicial category structure.
* `TauCeti.DGSimplicialCategory.sHom_of`: its mapping simplicial sets are `DK(τ_{≥ 0} Hom(X, Y))`.
* `TauCeti.DGSimplicialCategory.homEquiv`, `TauCeti.DGSimplicialCategory.homEquiv_id` and
  `TauCeti.DGSimplicialCategory.homEquiv_comp`: its morphisms are the closed degree-zero morphisms
  of `C`, with their identities and composition.
* `TauCeti.DGSimplicialCategory.eId_of`: the enriched identity is the vertex given by the
  identity morphism.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.13 and Remark 1.3.1.14.
-/

public section

open CategoryTheory MonoidalCategory SimplicialCategory ComplexShape

universe v u

namespace TauCeti

variable (R : Type v) [CommRing R]

/-- The functor sending a cochain complex `K` of `R`-modules to the underlying simplicial set of
the Dold–Kan image `DK(τ_{≥ 0} K)` of its good truncation. -/
noncomputable def doldKanSSetFunctor : CochainComplex (ModuleCat.{v} R) ℤ ⥤ SSet.{v} :=
  embeddingDownNat.truncLE'Functor (ModuleCat.{v} R) ⋙ Idempotents.DoldKan.Γ ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj (forget (ModuleCat.{v} R))

/-- `TauCeti.doldKanSSetFunctor` sends `K` to the simplicial set underlying the simplicial module
`Γ (τ_{≥ 0} K)`. -/
lemma doldKanSSetFunctor_obj (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    (doldKanSSetFunctor R).obj K =
      Idempotents.DoldKan.Γ.obj (K.truncLE' embeddingDownNat) ⋙ forget (ModuleCat.{v} R) :=
  (rfl)

/-- `TauCeti.doldKanSSetFunctor` is lax monoidal, as the composite of the lax monoidal good
truncation, the lax monoidal Dold–Kan functor and the lax monoidal forgetful functor. -/
noncomputable instance : (doldKanSSetFunctor R).LaxMonoidal :=
  inferInstanceAs (embeddingDownNat.truncLE'Functor (ModuleCat.{v} R) ⋙ Idempotents.DoldKan.Γ ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj (forget (ModuleCat.{v} R))).LaxMonoidal

/-- The simplicial sets `DK(τ_{≥ 0} K)` are Kan complexes, as all simplicial modules are. -/
instance (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    SSet.KanComplex ((doldKanSSetFunctor R).obj K) :=
  SimplicialObject.kanComplex_comp_forget_moduleCat _

/-- Maps `𝟙_ ⟶ K` out of the unit complex, which are the degree-`0` cycles of `K`, are the
vertices of `DK(τ_{≥ 0} K)`: `TauCeti.doldKanSSetFunctor` induces bijections on maps out of the
tensor units. -/
lemma bijective_ε_comp_doldKanSSetFunctor_map (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    Function.Bijective fun f : 𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⟶ K ↦
      Functor.LaxMonoidal.ε (doldKanSSetFunctor R) ≫ (doldKanSSetFunctor R).map f :=
  Functor.LaxMonoidal.bijective_ε_comp_map_comp
    (embeddingDownNat.truncLE'Functor (ModuleCat.{v} R))
    (Idempotents.DoldKan.Γ ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj (forget (ModuleCat.{v} R)))
    (fun K ↦ CochainComplex.bijective_ε_comp_truncLE'Functor_map K)
    (Functor.LaxMonoidal.bijective_ε_comp_map_comp _ _
      (Functor.FullyFaithful.bijective_ε_comp_map (F := Idempotents.DoldKan.Γ)
        Idempotents.DoldKan.equivalence.fullyFaithfulInverse)
      (Functor.LaxMonoidal.bijective_ε_comp_map_whiskeringRight _ _
        ModuleCat.bijective_ε_comp_forget_map)) K

/-- The **simplicial category `C_Δ` of a differential graded category** `C` (Lurie, *Higher
Algebra*, Construction 1.3.1.13). Its objects are those of `C`
(`TauCeti.DGSimplicialCategory.of`), its morphisms are the closed degree-zero morphisms of `C`
(`TauCeti.DGSimplicialCategory.homEquiv`), and its mapping simplicial sets are the
simplicial sets `DK(τ_{≥ 0} Hom(X, Y))` (`TauCeti.DGSimplicialCategory.sHom_of`), with the
simplicial category structure `TauCeti.dgSimplicialCategory`. -/
-- Exposed so that the instances below, and statements relating morphisms of `C_Δ` to closed
-- morphisms of `C`, can see that `C_Δ` has the objects and morphisms of the closed category.
@[expose]
def DGSimplicialCategory (C : Type u) [DGCategory R C] : Type u :=
  TransportEnrichment (doldKanSSetFunctor R)
    (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C)

variable {R} {C : Type u} [DGCategory R C]

/-- The object of the differential graded category underlying an object of its simplicial
category. -/
def DGSimplicialCategory.to (X : DGSimplicialCategory R C) : C :=
  X

namespace DGSimplicialCategory

variable (R) in
/-- An object of a differential graded category, regarded as an object of its simplicial
category. -/
-- Exposed for the same reason as `TauCeti.DGSimplicialCategory`.
@[expose]
def of (X : C) : DGSimplicialCategory R C :=
  X

/-- The underlying category of the simplicial category of a differential graded category is its
category of closed degree-zero morphisms. -/
noncomputable instance : Category.{v} (DGSimplicialCategory R C) :=
  inferInstanceAs (Category (TransportEnrichment (doldKanSSetFunctor R)
    (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C)))

@[simp]
lemma to_of (X : C) : (of R X).to = X :=
  (rfl)

@[simp]
lemma of_to (X : DGSimplicialCategory R C) : of R X.to = X :=
  (rfl)

end DGSimplicialCategory

/-- The **simplicial category structure** on the simplicial category `C_Δ` of a differential graded
category: the enrichment transported along `TauCeti.doldKanSSetFunctor`, whose vertices are the
closed degree-zero morphisms (`TauCeti.bijective_ε_comp_doldKanSSetFunctor_map`). -/
noncomputable instance dgSimplicialCategory : SimplicialCategory (DGSimplicialCategory R C) :=
  TransportEnrichment.enrichedOrdinaryCategory
    (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) (doldKanSSetFunctor R)
    (fun K ↦ Equiv.ofBijective _ (bijective_ε_comp_doldKanSSetFunctor_map R K)) (fun _ _ ↦ rfl)

namespace DGSimplicialCategory

/-- The mapping simplicial set of `C_Δ` from `X` to `Y` is `DK(τ_{≥ 0} Hom(X, Y))`. -/
lemma sHom_of (X Y : C) :
    sHom (of R X) (of R Y) = (doldKanSSetFunctor R).obj (dgHomComplex R X Y) :=
  (rfl)

/-- The mapping simplicial sets of `C_Δ` are Kan complexes. -/
instance (X Y : DGSimplicialCategory R C) : SSet.KanComplex (sHom X Y) :=
  inferInstanceAs (SSet.KanComplex ((doldKanSSetFunctor R).obj (dgHomComplex R X.to Y.to)))

variable (R) in
/-- The morphisms of `C_Δ` from `X` to `Y` are the closed degree-zero morphisms of `C`. -/
noncomputable def homEquiv (X Y : C) : (of R X ⟶ of R Y) ≃ dgCycles R X Y :=
  dgClosedHomEquiv R (ForgetEnrichment.of _ X) (ForgetEnrichment.of _ Y)

/-- The identity of `C_Δ` is the identity of the differential graded category. -/
@[simp]
lemma homEquiv_id (X : C) : (homEquiv R X X (𝟙 (of R X)) : DGHom R 0 X X) = dgId R X :=
  (dgClosedHomEquiv_apply_coe R (X := ForgetEnrichment.of _ X) (Y := ForgetEnrichment.of _ X)
    _).trans (dgClosedHom_id R (ForgetEnrichment.of _ X))

/-- Composition in `C_Δ` is the composition of closed degree-zero morphisms. -/
@[simp]
lemma homEquiv_comp {X Y Z : C} (f : of R X ⟶ of R Y) (g : of R Y ⟶ of R Z) :
    (homEquiv R X Z (f ≫ g) : DGHom R 0 X Z) =
      dgCompZero R (homEquiv R X Y f : DGHom R 0 X Y) (homEquiv R Y Z g) :=
  (dgClosedHomEquiv_apply_coe R (X := ForgetEnrichment.of _ X) (Y := ForgetEnrichment.of _ Z)
    _).trans
    ((dgClosedHom_comp R (X := ForgetEnrichment.of _ X) (Y := ForgetEnrichment.of _ Y)
      (Z := ForgetEnrichment.of _ Z) f g).trans
        (congrArg₂ (dgCompZero R)
          (dgClosedHomEquiv_apply_coe R (X := ForgetEnrichment.of _ X)
            (Y := ForgetEnrichment.of _ Y) f).symm
          (dgClosedHomEquiv_apply_coe R (X := ForgetEnrichment.of _ Y)
            (Y := ForgetEnrichment.of _ Z) g).symm))

/-- The enriched identity of `C_Δ` at `X` is the vertex of the mapping simplicial set given by the
identity of `X` in the differential graded category. -/
lemma eId_of (X : C) :
    eId SSet (of R X) = eHomEquiv SSet ((homEquiv R X X).symm
      ⟨dgId R X, (mem_dgCycles R).mpr (dgDifferential_dgId R X)⟩) := by
  rw [← eHomEquiv_id]
  congr 1
  exact (homEquiv R X X).injective (Subtype.ext (by simp))

/-- A morphism of `C_Δ` is regarded as a vertex of the mapping simplicial set by applying
`TauCeti.doldKanSSetFunctor` to the corresponding map out of the unit complex. -/
lemma eHomEquiv_apply {X Y : C} (f : of R X ⟶ of R Y) :
    eHomEquiv SSet f = Functor.LaxMonoidal.ε (doldKanSSetFunctor R) ≫
      (doldKanSSetFunctor R).map (ForgetEnrichment.homTo (CochainComplex (ModuleCat.{v} R) ℤ)
        (dgClosedHomOf R (homEquiv R X Y f).1 (homEquiv R X Y f).2)) := by
  have h : dgClosedHomOf R (homEquiv R X Y f).1 (homEquiv R X Y f).2 = f :=
    (dgClosedHomEquiv_symm_apply R (X := ForgetEnrichment.of _ X) (Y := ForgetEnrichment.of _ Y)
      _).symm.trans ((homEquiv R X Y).symm_apply_apply f)
  rw [h]
  rfl

end DGSimplicialCategory

end TauCeti
