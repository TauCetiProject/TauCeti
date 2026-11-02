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

This is the implication flat ⇒ filtered colimit of finite free modules in Lazard's theorem.
It allows constructions on finite free modules to be extended to arbitrary flat modules
by filtered colimits.
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

namespace FiniteFreeOver

/-- The object given by a linear map from the standard free module of rank `n`. -/
abbrev mk (n : ℕ) (f : (Fin n →₀ R) →ₗ[R] M) : FiniteFreeOver R M :=
  CostructuredArrow.mk (C := FiniteFreeModuleCat R) (S := finiteFreeModuleInclusion R)
    (Y := (n : FiniteFreeModuleCat R)) (ModuleCat.ofHom f)

@[simp]
theorem mk_left (n : ℕ) (f : (Fin n →₀ R) →ₗ[R] M) : (mk R M n f).left = n := rfl

@[simp]
theorem mk_hom (n : ℕ) (f : (Fin n →₀ R) →ₗ[R] M) :
    (mk R M n f).hom = ModuleCat.ofHom f := rfl

variable {R M}

/-- A linear map commuting with the structure maps defines a morphism over `M`. -/
def homMk {i j : FiniteFreeOver R M}
    (a : (Fin i.left →₀ R) →ₗ[R] (Fin j.left →₀ R))
    (h : j.hom.hom ∘ₗ a = i.hom.hom) : i ⟶ j :=
  CostructuredArrow.homMk (InducedCategory.homMk (ModuleCat.ofHom a))
    (ModuleCat.hom_ext h)

@[simp]
theorem homMk_left_hom_hom {i j : FiniteFreeOver R M}
    (a : (Fin i.left →₀ R) →ₗ[R] (Fin j.left →₀ R))
    (h : j.hom.hom ∘ₗ a = i.hom.hom) : (homMk a h).left.hom.hom = a := (rfl)

end FiniteFreeOver

instance : Nonempty (FiniteFreeOver R M) := ⟨FiniteFreeOver.mk R M 0 0⟩

end Ring

section CommRing

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

/-- For flat `M`, the category `FiniteFreeOver R M` is filtered. -/
instance [Module.Flat R M] : IsFiltered (FiniteFreeOver R M) where
  -- Finite families admit a common factorization, and finite relations can be killed.
  cocone_objs i j := by
    obtain ⟨k, a, y, h⟩ := Module.Flat.exists_factorization_of_finitePresentation
      (i.hom.hom.coprod j.hom.hom)
    let z := FiniteFreeOver.mk R M k y
    refine ⟨z,
      FiniteFreeOver.homMk (a.comp (LinearMap.inl R _ _)) ?_,
      FiniteFreeOver.homMk (a.comp (LinearMap.inr R _ _)) ?_, trivial⟩
    · apply LinearMap.ext
      intro x
      simpa [z] using (LinearMap.congr_fun h (x, 0)).symm
    · apply LinearMap.ext
      intro x
      simpa [z] using (LinearMap.congr_fun h (0, x)).symm
  cocone_maps {i j} f g := by
    have h : j.hom.hom.comp (f.left.hom.hom - g.left.hom.hom) = 0 := by
      rw [LinearMap.comp_sub]
      exact sub_eq_zero.mpr (congrArg ModuleCat.Hom.hom
        ((CostructuredArrow.w f).trans (CostructuredArrow.w g).symm))
    obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free h
    let z := FiniteFreeOver.mk R M k y
    let t : j ⟶ z := FiniteFreeOver.homMk a hy.symm
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
    refine ⟨FiniteFreeOver.mk R M 1 (Finsupp.linearCombination R (fun _ : Fin 1 ↦ x)),
      (Finsupp.single (0 : Fin 1) 1 : Fin 1 →₀ R), ?_⟩
    simp
  · intro i x y h
    have hzero : i.hom.hom (x - y) = 0 := by
      simpa [map_sub] using sub_eq_zero.mpr h
    obtain ⟨k, a, z, hz, ha⟩ := Module.Flat.exists_factorization_of_apply_eq_zero_of_free hzero
    refine ⟨FiniteFreeOver.mk R M k z, FiniteFreeOver.homMk a hz.symm, ?_⟩
    exact sub_eq_zero.mp (by simpa [map_sub] using ha)

end CommRing

end TauCeti
