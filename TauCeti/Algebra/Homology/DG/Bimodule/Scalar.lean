/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.Algebra.Homology.DG.Bimodule.Category

/-!
# DG right modules as scalar-left DG bimodules

A DG right `B`-module is canonically a DG `(R, B)`-bimodule, where the ground ring `R`, trivially
graded with zero differential, acts on the left by scalars. This file bundles that conversion as a
faithful linear functor from DG right modules to DG bimodules.

## Main definitions

* `TauCeti.DGRightModuleCat.toScalarBimodule`: a right DG module as a DG bimodule over the ground
  ring on the left.
* `TauCeti.DGRightModuleCat.toScalarBimoduleFunctor`: the conversion as a functor.

## References

* B. Keller, *Deriving DG categories*, Sections 4 and 6.1.
-/

public section

open CategoryTheory

namespace TauCeti.DGRightModuleCat

universe uR uB uM

variable {R : Type uR} {B : Type uB}
  [CommRing R] [Ring B] [Algebra R B]
  {Bₙ : ℤ → Submodule R B} [GradedAlgebra Bₙ]
  {dB : B →ₗ[R] B} {hB : IsDGAlgebra Bₙ dB}

/-- A DG right module over `B`, regarded as a DG `(R, B)`-bimodule through the scalar action of
the ground ring on the left. -/
abbrev toScalarBimodule (M : DGRightModuleCat.{uR, uB, uM} hB) :
    DGBimoduleCat (isDGAlgebra_trivialGrading R) hB where
  toDGRightModuleCat := M
  isDGLeftModule :=
    { isHomogeneous := M.isDGRightModule.isHomogeneous
      sq_zero := M.isDGRightModule.sq_zero
      leibniz := by
        intro p r hr m
        rcases (mem_trivialGrading_iff R R).mp hr with rfl | rfl
        · simp
        · simp }

@[simp]
theorem toScalarBimodule_carrier (M : DGRightModuleCat.{uR, uB, uM} hB) :
    M.toScalarBimodule.carrier = M.carrier := (rfl)

@[simp]
theorem toScalarBimodule_grading (M : DGRightModuleCat.{uR, uB, uM} hB) :
    M.toScalarBimodule.grading = M.grading := (rfl)

@[simp]
theorem toScalarBimodule_differential (M : DGRightModuleCat.{uR, uB, uM} hB) :
    M.toScalarBimodule.differential = M.differential := (rfl)

/-- A right-module morphism as the corresponding morphism of scalar-left bimodules. -/
abbrev toScalarBimoduleMap {M M' : DGRightModuleCat.{uR, uB, uM} hB} (f : M ⟶ M') :
    M.toScalarBimodule ⟶ M'.toScalarBimodule := by
  refine ⟨f, ?_⟩
  rw [mem_dgBimoduleHomSubmodule]
  exact fun r m ↦ f.toLinearMap.map_smul_of_tower r m

@[simp]
theorem toScalarBimoduleMap_apply {M M' : DGRightModuleCat.{uR, uB, uM} hB}
    (f : M ⟶ M') (m : M) : toScalarBimoduleMap f m = f m := (rfl)

@[simp]
theorem toScalarBimoduleMap_id (M : DGRightModuleCat.{uR, uB, uM} hB) :
    toScalarBimoduleMap (𝟙 M) = 𝟙 M.toScalarBimodule :=
  Subtype.ext (DGBimoduleHom.id_val M.toScalarBimodule.isDGBimodule).symm

@[simp]
theorem toScalarBimoduleMap_comp {M M' M'' : DGRightModuleCat.{uR, uB, uM} hB}
    (f : M ⟶ M') (g : M' ⟶ M'') :
    toScalarBimoduleMap (f ≫ g) = toScalarBimoduleMap f ≫ toScalarBimoduleMap g :=
  Subtype.ext (DGBimoduleHom.comp_val (toScalarBimoduleMap g) (toScalarBimoduleMap f)).symm

/-- Viewing right DG modules as scalar-left DG bimodules is a faithful linear functor. -/
abbrev toScalarBimoduleFunctor :
    CategoryTheory.Functor (DGRightModuleCat.{uR, uB, uM} hB)
      (DGBimoduleCat.{uR, uR, uB, uM} (isDGAlgebra_trivialGrading R) hB) where
  obj := toScalarBimodule
  map := toScalarBimoduleMap
  map_id := toScalarBimoduleMap_id
  map_comp := toScalarBimoduleMap_comp

@[simp]
theorem toScalarBimoduleFunctor_obj (M : DGRightModuleCat.{uR, uB, uM} hB) :
    toScalarBimoduleFunctor.obj M = M.toScalarBimodule := (rfl)

@[simp]
theorem toScalarBimoduleFunctor_map {M M' : DGRightModuleCat.{uR, uB, uM} hB} (f : M ⟶ M') :
    toScalarBimoduleFunctor.map f = toScalarBimoduleMap f := (rfl)

instance : (toScalarBimoduleFunctor.{uR, uB, uM} (hB := hB)).Faithful where
  map_injective h := by
    apply hom_ext
    intro m
    exact DFunLike.congr_fun h m

instance : (toScalarBimoduleFunctor.{uR, uB, uM} (hB := hB)).Additive where
  map_add := by
    intro M M' f g
    ext m
    rfl

instance : (toScalarBimoduleFunctor.{uR, uB, uM} (hB := hB)).Linear R where
  map_smul := by
    intro M M' r f
    ext m
    rfl

end TauCeti.DGRightModuleCat
