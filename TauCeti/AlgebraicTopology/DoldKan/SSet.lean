/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Forget
public import TauCeti.Algebra.Homology.Monoidal.TruncLE
public import TauCeti.AlgebraicTopology.DoldKan.Monoidal
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.SimplicialGroup
public import TauCeti.CategoryTheory.Monoidal.UnitHom

/-!
# The Dold–Kan simplicial set of a cochain complex

A cochain complex `K` of `R`-modules indexed by `ℤ` has an underlying simplicial set
`DK(τ_{≥ 0} K)`: the Dold–Kan image of its good truncation `τ_{≥ 0} K`, which keeps `K` in
non-positive cohomological degrees and its cycles in degree `0`, reindexed as a chain complex.
Its `n`-th homotopy group is the cohomology `H^{-n}` of `K`. This is the construction of mapping
spaces in the simplicial category of a differential graded category (J. Lurie, *Higher Algebra*,
Construction 1.3.1.13).

The functor `TauCeti.doldKanSSetFunctor R` is the composite of three lax monoidal functors: the
good truncation (`CochainComplex.truncLE'FunctorLaxMonoidal`), the Dold–Kan functor `Γ` with its
Alexander–Whitney structure (`CategoryTheory.Idempotents.DoldKan.laxMonoidalΓ`) and the forgetful
functor from simplicial modules to simplicial sets (`ModuleCat.forgetLaxMonoidal`). Each of the
three induces bijections on maps out of the tensor units; for the composite, maps `𝟙_ ⟶ K` from the
unit complex, which are the degree-`0` cycles of `K`, are the vertices of `DK(τ_{≥ 0} K)`.

## Main definitions and results

* `TauCeti.doldKanSSetFunctor`: the lax monoidal functor `K ↦ DK(τ_{≥ 0} K)` from cochain
  complexes of `R`-modules to simplicial sets, with action on objects, morphisms, unit and
  tensorator `TauCeti.doldKanSSetFunctor_obj`, `TauCeti.doldKanSSetFunctor_map`,
  `TauCeti.doldKanSSetFunctor_ε` and `TauCeti.doldKanSSetFunctor_μ`.
* `TauCeti.bijective_ε_comp_doldKanSSetFunctor_map`: it induces bijections on maps out of the
  tensor units.
* The simplicial sets `DK(τ_{≥ 0} K)` are Kan complexes.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.13.
-/

public section

open CategoryTheory MonoidalCategory ComplexShape

universe v

namespace TauCeti

variable (R : Type v) [CommRing R]

/-- The functor sending a cochain complex `K` of `R`-modules to the underlying simplicial set of
the Dold–Kan image `DK(τ_{≥ 0} K)` of its good truncation. -/
-- Exposed so that the statements of `TauCeti.doldKanSSetFunctor_map`,
-- `TauCeti.doldKanSSetFunctor_ε` and `TauCeti.doldKanSSetFunctor_μ` can identify the objects of
-- this functor with those of its three constituent functors.
@[expose]
noncomputable def doldKanSSetFunctor : CochainComplex (ModuleCat.{v} R) ℤ ⥤ SSet.{v} :=
  embeddingDownNat.truncLE'Functor (ModuleCat.{v} R) ⋙ Idempotents.DoldKan.Γ ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj (forget (ModuleCat.{v} R))

/-- `TauCeti.doldKanSSetFunctor` sends `K` to the simplicial set underlying the simplicial module
`Γ (τ_{≥ 0} K)`. -/
lemma doldKanSSetFunctor_obj (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    (doldKanSSetFunctor R).obj K =
      Idempotents.DoldKan.Γ.obj (K.truncLE' embeddingDownNat) ⋙ forget (ModuleCat.{v} R) :=
  (rfl)

variable {R} in
/-- `TauCeti.doldKanSSetFunctor` sends a morphism `f` to the map of underlying simplicial sets of
`Γ (τ_{≥ 0} f)`. -/
lemma doldKanSSetFunctor_map {K L : CochainComplex (ModuleCat.{v} R) ℤ} (f : K ⟶ L) :
    (doldKanSSetFunctor R).map f =
      Functor.whiskerRight
        (Idempotents.DoldKan.Γ.map ((embeddingDownNat.truncLE'Functor (ModuleCat.{v} R)).map f))
        (forget (ModuleCat.{v} R)) :=
  (rfl)

/-- `TauCeti.doldKanSSetFunctor` is lax monoidal, as the composite of the lax monoidal good
truncation, the lax monoidal Dold–Kan functor and the lax monoidal forgetful functor. -/
noncomputable instance : (doldKanSSetFunctor R).LaxMonoidal :=
  inferInstanceAs (embeddingDownNat.truncLE'Functor (ModuleCat.{v} R) ⋙ Idempotents.DoldKan.Γ ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj (forget (ModuleCat.{v} R))).LaxMonoidal

/-- The unit of `TauCeti.doldKanSSetFunctor` is the composite of the units of the forgetful
functor, of `Γ` and of the good truncation. -/
lemma doldKanSSetFunctor_ε :
    Functor.LaxMonoidal.ε (doldKanSSetFunctor R) =
      Functor.LaxMonoidal.ε
          ((Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj (forget (ModuleCat.{v} R))) ≫
        Functor.whiskerRight
          (Functor.LaxMonoidal.ε Idempotents.DoldKan.Γ ≫ Idempotents.DoldKan.Γ.map
            (Functor.LaxMonoidal.ε (embeddingDownNat.truncLE'Functor (ModuleCat.{v} R))))
          (forget (ModuleCat.{v} R)) :=
  (rfl)

variable {R} in
/-- The tensorator of `TauCeti.doldKanSSetFunctor` is the composite of the tensorators of the
forgetful functor, of `Γ` and of the good truncation. -/
lemma doldKanSSetFunctor_μ (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    Functor.LaxMonoidal.μ (doldKanSSetFunctor R) K L =
      Functor.LaxMonoidal.μ
          ((Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj (forget (ModuleCat.{v} R))) _ _ ≫
        Functor.whiskerRight
          (Functor.LaxMonoidal.μ Idempotents.DoldKan.Γ _ _ ≫ Idempotents.DoldKan.Γ.map
            (Functor.LaxMonoidal.μ (embeddingDownNat.truncLE'Functor (ModuleCat.{v} R)) K L))
          (forget (ModuleCat.{v} R)) :=
  (rfl)

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

end TauCeti
