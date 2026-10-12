/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Exterior powers and restriction of scalars

Restriction of scalars has a natural exterior-power comparison, sending a wedge over the
source ring to the same wedge over the target ring. It need not be an isomorphism. The
construction uses Mathlib's `ModuleCat.exteriorPower.desc` and supplies the sectionwise maps
for exterior powers of pushforwards of module presheaves.
-/

public section

open CategoryTheory

namespace TauCeti.ModuleCat

universe u v w

noncomputable section

variable {S : Type u} {R : Type v} [CommRing S] [CommRing R] (f : S →+* R)

private def restrictScalarsExteriorPowerApp (n : ℕ) (M : ModuleCat.{max u v w} R) :
    ((ModuleCat.restrictScalars f).obj M).exteriorPower n ⟶
      (ModuleCat.restrictScalars f).obj (M.exteriorPower n) :=
  ModuleCat.exteriorPower.desc
    { toFun m := ModuleCat.exteriorPower.mk (M := M) m
      map_update_add' m i a b :=
        (ModuleCat.exteriorPower.mk (M := M)).map_update_add m i a b
      map_update_smul' m i r a :=
        (ModuleCat.exteriorPower.mk (M := M)).map_update_smul m i (f r) a
      map_eq_zero_of_eq' m _ _ h hij :=
        (ModuleCat.exteriorPower.mk (M := M)).map_eq_zero_of_eq m h hij }

private lemma restrictScalarsExteriorPowerApp_mk (n : ℕ)
    (M : ModuleCat.{max u v w} R) (m : Fin n → (ModuleCat.restrictScalars f).obj M) :
    restrictScalarsExteriorPowerApp f n M (ModuleCat.exteriorPower.mk m) =
      ModuleCat.exteriorPower.mk (M := M) m :=
  ModuleCat.exteriorPower.desc_mk _ _

/-- Restriction of scalars carries the natural exterior-power comparison, changing the
coefficient ring of a wedge without changing its factors. -/
def restrictScalarsExteriorPowerComparison (n : ℕ) :
    ModuleCat.restrictScalars.{max u v w} f ⋙ ModuleCat.exteriorPower.functor S n ⟶
      ModuleCat.exteriorPower.functor R n ⋙ ModuleCat.restrictScalars f where
  app := restrictScalarsExteriorPowerApp f n
  naturality {M N} φ := by
    dsimp only [Functor.comp_obj, Functor.comp_map, ModuleCat.exteriorPower.functor]
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro m
    simp only [ModuleCat.AlternatingMap.postcomp_apply, ModuleCat.comp_apply,
      ModuleCat.restrictScalars.map_apply, ModuleCat.exteriorPower.map_mk,
      restrictScalarsExteriorPowerApp_mk, Function.comp_def]
    -- Restriction of scalars gives the concrete-category coercions different bundled objects
    -- with the same carriers, preventing `simp` from matching these two wedge formulas.
    exact (restrictScalarsExteriorPowerApp_mk f n N (φ ∘ m)).trans
      (ModuleCat.exteriorPower.map_mk φ m).symm

/-- The restriction-of-scalars comparison preserves the factors of a decomposable wedge. -/
-- Explicit objects keep the coercion to a function in simp normal form.
@[simp]
theorem restrictScalarsExteriorPowerComparison_app_mk (n : ℕ)
    (M : ModuleCat.{max u v w} R) (m : Fin n → (ModuleCat.restrictScalars f).obj M) :
    (ConcreteCategory.hom
      (X := (ModuleCat.exteriorPower.functor S n).obj ((ModuleCat.restrictScalars f).obj M))
      (Y := (ModuleCat.restrictScalars f).obj ((ModuleCat.exteriorPower.functor R n).obj M))
      ((restrictScalarsExteriorPowerComparison f n).app M))
      (ModuleCat.exteriorPower.mk m) = ModuleCat.exteriorPower.mk (M := M) m :=
  restrictScalarsExteriorPowerApp_mk f n M m

end

end TauCeti.ModuleCat
