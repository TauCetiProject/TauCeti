/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAt
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Flat modules as filtered colimits of finite free modules

For an `R`-module `M`, `FiniteFreeOver R M` is the small category of linear maps
`Rⁿ → M`, with commuting triangles as morphisms. Its tautological diagram consists of
finite free modules and has a cocone with vertex `M` and the given maps as legs.
When `M` is flat, this category is filtered and `flatModuleFilteredFree` proves that
the cocone is colimiting using Mathlib's `Functor.DenseAt` API. Transition maps
need not be injective.

This is the constructive direction of Lazard's theorem. It allows constructions on
finite free modules to be extended to arbitrary flat modules by filtered colimits.
The proof uses Mathlib's finite-presentation factorization and equational criteria
for flatness, formalized by Mitchell Lee and Junyan Xu.

## References

* The Stacks Project, Tags 058D, 058E and 058G.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TauCeti

section Ring

variable (R : Type u) [Ring R] (M : Type u) [AddCommGroup M] [Module R M]

/-- The category of standard finite free modules, with objects the natural-number ranks
and morphisms all linear maps between the corresponding free modules. -/
abbrev FiniteFreeModuleCat :=
  InducedCategory (ModuleCat.{u} R) (fun n : ℕ ↦ ModuleCat.of R (Fin n →₀ R))

/-- The functor sending a rank to its standard finite free module. -/
abbrev finiteFreeModuleInclusion : FiniteFreeModuleCat R ⥤ ModuleCat.{u} R :=
  inducedFunctor _

instance (n : FiniteFreeModuleCat R) : Module.Free R ((finiteFreeModuleInclusion R).obj n) := by
  dsimp [finiteFreeModuleInclusion, inducedFunctor]
  infer_instance

instance (n : FiniteFreeModuleCat R) : Module.Finite R ((finiteFreeModuleInclusion R).obj n) := by
  dsimp [finiteFreeModuleInclusion, inducedFunctor]
  infer_instance

instance (n : FiniteFreeModuleCat R) :
    Module.FinitePresentation R ((finiteFreeModuleInclusion R).obj n) := by
  dsimp [finiteFreeModuleInclusion, inducedFunctor]
  infer_instance

/-- The small category of finite free modules mapping to `M`, retaining all linear
maps that commute with the structure maps to `M`. -/
abbrev FiniteFreeOver :=
  CostructuredArrow (finiteFreeModuleInclusion R) (ModuleCat.of R M)

instance : Nonempty (FiniteFreeOver R M) :=
  ⟨CostructuredArrow.mk (C := FiniteFreeModuleCat R) (S := finiteFreeModuleInclusion R)
    (Y := ((0 : ℕ) : FiniteFreeModuleCat R))
    (ModuleCat.ofHom (0 : (Fin 0 →₀ R) →ₗ[R] M))⟩

end Ring

section CommRing

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

/-- Flatness makes the category of finite free modules over `M` filtered: finite
families of generators admit a common factorization and finite relations can be killed. -/
instance [Module.Flat R M] : IsFiltered (FiniteFreeOver R M) where
  cocone_objs i j := by
    obtain ⟨k, a, y, h⟩ := Module.Flat.exists_factorization_of_finitePresentation
      (i.hom.hom.coprod j.hom.hom)
    let z : FiniteFreeOver R M := CostructuredArrow.mk (C := FiniteFreeModuleCat R)
      (S := finiteFreeModuleInclusion R) (Y := (k : FiniteFreeModuleCat R)) (ModuleCat.ofHom y)
    refine ⟨z,
      CostructuredArrow.homMk (InducedCategory.homMk
        (ModuleCat.ofHom (a.comp (LinearMap.inl R _ _)))) ?_,
      CostructuredArrow.homMk (InducedCategory.homMk
        (ModuleCat.ofHom (a.comp (LinearMap.inr R _ _)))) ?_, trivial⟩
    · ext x
      simpa [z] using (LinearMap.congr_fun h (x, 0)).symm
    · ext x
      simpa [z] using (LinearMap.congr_fun h (0, x)).symm
  cocone_maps {i j} f g := by
    have h : j.hom.hom.comp (f.left.hom.hom - g.left.hom.hom) = 0 := by
      rw [LinearMap.comp_sub]
      exact sub_eq_zero.mpr (congrArg ModuleCat.Hom.hom
        ((CostructuredArrow.w f).trans (CostructuredArrow.w g).symm))
    obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free h
    let z : FiniteFreeOver R M := CostructuredArrow.mk (C := FiniteFreeModuleCat R)
      (S := finiteFreeModuleInclusion R) (Y := (k : FiniteFreeModuleCat R)) (ModuleCat.ofHom y)
    let t : j ⟶ z := CostructuredArrow.homMk
      (InducedCategory.homMk (ModuleCat.ofHom a)) (by
        apply ModuleCat.hom_ext
        exact hy.symm)
    refine ⟨z, t, ?_⟩
    apply CostructuredArrow.hom_ext
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    exact sub_eq_zero.mp (by
      simpa [t, z, LinearMap.comp_sub] using ha)

/-- Every flat module is the filtered colimit of the finite free modules mapping
to it, with the specified structure maps as the colimit legs. -/
def flatModuleFilteredFree [Module.Flat R M] :
    (finiteFreeModuleInclusion R).DenseAt (ModuleCat.of R M) := by
  refine (Functor.denseAtEquiv _ _).symm ?_
  apply isColimitOfReflects (forget (ModuleCat R))
  apply Types.FilteredColimit.isColimitOf'
  -- Elaborate the elementwise criterion on the concrete module carriers.
  all_goals dsimp [Functor.LeftExtension.coconeAt, finiteFreeModuleInclusion, inducedFunctor]
  · intro x
    refine ⟨CostructuredArrow.mk (C := FiniteFreeModuleCat R) (S := finiteFreeModuleInclusion R)
      (Y := ((1 : ℕ) : FiniteFreeModuleCat R))
      (ModuleCat.ofHom (Finsupp.linearCombination R (fun _ : Fin 1 ↦ x))),
      (Finsupp.single (0 : Fin 1) 1 : Fin 1 →₀ R), ?_⟩
    simp
  · intro i x y h
    have hzero : i.hom.hom (x - y) = 0 := by
      simpa [map_sub] using sub_eq_zero.mpr h
    obtain ⟨k, a, z, hz, ha⟩ := Module.Flat.exists_factorization_of_apply_eq_zero_of_free hzero
    refine ⟨CostructuredArrow.mk (C := FiniteFreeModuleCat R) (S := finiteFreeModuleInclusion R)
      (Y := (k : FiniteFreeModuleCat R)) (ModuleCat.ofHom z),
      CostructuredArrow.homMk (InducedCategory.homMk (ModuleCat.ofHom a)) ?_, ?_⟩
    · apply ModuleCat.hom_ext
      exact hz.symm
    · exact sub_eq_zero.mp (by simpa [map_sub] using ha)

end CommRing

end TauCeti
