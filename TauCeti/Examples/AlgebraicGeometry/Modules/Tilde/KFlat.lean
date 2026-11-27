/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.KFlat

/-!
# Unbounded affine K-flat resolution checks

These examples exercise the native free cellular resolution and its natural augmentation on
arbitrary unbounded complexes. The degreewise associated sheaf of a graded free complex is
K-flat, and the complex with one copy of `ℤ` in every integer degree gives an example unbounded
in both directions.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry HomologicalComplex CochainComplex
open TauCeti.AlgebraicGeometry

universe u

section FreeResolution

variable (R : CommRingCat.{u}) (K L : CochainComplex (ModuleCat.{u} R) ℤ)

example : IsKFlat ((kFlatResolutionFunctor
    (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit).obj K) :=
  inferInstance

example : QuasiIso ((kFlatResolutionNatTrans
    (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit).app K) :=
  inferInstance

example : IsKFlat (((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj
    ((kFlatResolutionFunctor
      (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit).obj K)) :=
  inferInstance

example : QuasiIso (((tilde.functor R).mapHomologicalComplex (.up ℤ)).map
    ((kFlatResolutionNatTrans
      (forget (ModuleCat.{u} R) ⋙ ModuleCat.free R) (ModuleCat.adj R).counit).app K)) :=
  inferInstance

-- Naturality of the mapped augmentation, using the native resolution's action on morphisms.
example (f : K ⟶ L) :
    let E := forget (ModuleCat.{u} R) ⋙ ModuleCat.free R
    let p := (ModuleCat.adj R).counit
    let F := (tilde.functor R).mapHomologicalComplex (.up ℤ)
    F.map ((kFlatResolutionFunctor E p).map f) ≫ F.map ((kFlatResolutionNatTrans E p).app L) =
      F.map ((kFlatResolutionNatTrans E p).app K) ≫ F.map f := by
  dsimp only
  simp only [← Functor.map_comp, NatTrans.naturality, Functor.id_map]

-- Arbitrarily large bases in each degree; no upper or lower support bound.
example (I : ℤ → Type u) : IsKFlat (((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj
    (graded (.up ℤ) fun n ↦ (ModuleCat.free R).obj (I n))) := by
  have : AB5OfSize.{0, 0} (Spec R).Modules := AB5OfSize_of_univLE.{0, 0, u, u} _
  have : HasFiniteBiproducts (Spec R).Modules := Abelian.hasFiniteBiproducts
  have : CountableAB4 (Spec R).Modules := CountableAB4.of_countableAB5 _
  have (n : ℤ) : PreservesFiniteLimits (tensorLeft
      ((((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj
        (graded (.up ℤ) fun n ↦ (ModuleCat.free R).obj (I n))).X n)) := by
    simp only [Functor.mapHomologicalComplex_obj_X]
    infer_instance
  exact isKFlat_of_d_eq_zero _ fun _ _ ↦ by
    simp only [Functor.mapHomologicalComplex_obj_d, Functor.map_zero]

end FreeResolution

-- A copy of ℤ in every degree becomes a copy of the structure sheaf in every degree.
-- Supplying Mathlib's instance explicitly avoids inference through the concrete bundled ring.
example :
    let R : CommRingCat.{0} := .of ℤ
    letI := AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor (R := R)
    IsKFlat (((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj
      (graded (.up ℤ) fun _ ↦ ModuleCat.of R R)) := by
  intro R
  let := AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor (R := R)
  have : AB5OfSize.{0, 0} (Spec R).Modules := AB5OfSize_of_univLE.{0, 0, 0, 0} _
  have : HasFiniteBiproducts (Spec R).Modules := Abelian.hasFiniteBiproducts
  have : CountableAB4 (Spec R).Modules := CountableAB4.of_countableAB5 _
  have : PreservesFiniteLimits (tensorLeft
      (C := (Spec R).Modules) ((tilde.functor R).obj (ModuleCat.of R R))) := by
    have : PreservesFiniteLimits (tensorLeft (𝟙_ (Spec R).Modules)) :=
      preservesFiniteLimits_of_natIso (leftUnitorNatIso _).symm
    exact preservesFiniteLimits_of_natIso
      ((curriedTensor (Spec R).Modules).mapIso tildeSelf.symm)
  have (n : ℤ) : PreservesFiniteLimits (tensorLeft
      ((((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj
        (graded (.up ℤ) fun _ ↦ ModuleCat.of R R)).X n)) := by
    simp only [Functor.mapHomologicalComplex_obj_X]
    infer_instance
  exact isKFlat_of_d_eq_zero _ fun _ _ ↦ by
    simp only [Functor.mapHomologicalComplex_obj_d, Functor.map_zero]
