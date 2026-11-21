/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import TauCeti.Algebra.Coalgebra.Comodule.Trivial
public import TauCeti.Algebra.Coalgebra.Comodule.Preadditive

/-!
# The invariants functor for comodules

For a bialgebra over a commutative ring, taking the fixed submodule of a right comodule
is an additive functor to modules. It is right adjoint to equipping a module with the
trivial coaction, and hence preserves limits. This gives the left-exact functor whose
right derived functors are rational cohomology. Neither flatness of the bialgebra nor
finiteness of coefficient modules is needed for this adjunction.

The construction uses `Comodule.fixedSubcomodule` and `Comodule.Hom.fixedMap`.
The adjunction follows the analogous representation-theoretic construction
`Rep.invariantsAdjunction` in Mathlib.

## References

* J. C. Jantzen, *Representations of Algebraic Groups I*, SFB/MPI 85-9 (1985),
  §§2.10 and 4.2.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.ComoduleCat

universe u v w

variable (R : Type u) (H : Type v) [CommRing R] [Semiring H] [Bialgebra R H]

/-- Equip each module with the trivial coaction and each linear map with its induced
comodule morphism. -/
-- Expose the carrier and coaction for the typed coaction and linear-map equations below.
@[expose, implicit_reducible]
noncomputable def trivialFunctor : ModuleCat.{w} R ⥤ ComoduleCat.{u, v, w} R H where
  obj M := by
    letI := Comodule.trivial (R := R) (C := H) (M := M)
    exact of R H M
  map f := Comodule.Hom.ofTrivial f.hom
  map_id _ := Comodule.Hom.ofTrivial_id
  map_comp f g := Comodule.Hom.ofTrivial_comp g.hom f.hom

/-- The coaction of a module equipped with the trivial coaction. -/
@[simp]
theorem trivialFunctor_coact (M : ModuleCat.{w} R) (m : M) :
    Comodule.coact (R := R) (C := H) (M := (trivialFunctor R H).obj M) m =
      m ⊗ₜ[R] (1 : H) :=
  (rfl)

/-- The underlying linear map of the trivial-comodule functor is unchanged. -/
@[simp]
theorem trivialFunctor_map_toLinearMap {M N : ModuleCat.{w} R} (f : M ⟶ N) :
    ((trivialFunctor R H).map f).toLinearMap = f.hom :=
  (rfl)

/-- The functor of comodule invariants, using the existing fixed subcomodule. -/
-- The map and adjunction equations identify these carriers with the existing fixed submodules.
@[expose, implicit_reducible]
noncomputable def invariantsFunctor : ComoduleCat.{u, v, w} R H ⥤ ModuleCat.{w} R where
  obj M := ModuleCat.of R (Comodule.fixedSubcomodule R H M)
  map f := ModuleCat.ofHom f.fixedMap
  map_id _ := ModuleCat.hom_ext Comodule.Hom.fixedMap_id
  map_comp f g := ModuleCat.hom_ext (Comodule.Hom.fixedMap_comp g f)

/-- The value of the invariants functor is the existing module of fixed vectors. -/
@[simp]
theorem invariantsFunctor_obj (M : ComoduleCat.{u, v, w} R H) :
    (invariantsFunctor R H).obj M = ModuleCat.of R (Comodule.fixedSubcomodule R H M) :=
  (rfl)

/-- The invariants functor acts by the existing restriction to fixed vectors. -/
@[simp]
theorem invariantsFunctor_map_hom {M N : ComoduleCat.{u, v, w} R H} (f : M ⟶ N) :
    ((invariantsFunctor R H).map f).hom = f.fixedMap :=
  (rfl)

instance : (trivialFunctor.{u, v, w} R H).Additive where
  map_add := by intros; ext; rfl

instance : (invariantsFunctor.{u, v, w} R H).Additive where
  map_add := by
    intros
    ext m
    apply Subtype.ext
    simp [invariantsFunctor]

/-- Equipping a module with the trivial coaction is left adjoint to taking invariants.
The counit is the inclusion of invariant vectors. -/
noncomputable def invariantsAdjunction :
    trivialFunctor.{u, v, w} R H ⊣ invariantsFunctor R H where
  unit :=
    { app := fun (M : ModuleCat.{w} R) ↦
        ModuleCat.ofHom <| LinearMap.id.codRestrict _ (by
          intro m
          exact (Comodule.mem_fixedSubcomodule
            (R := R) (C := H) (M := (trivialFunctor R H).obj M)).mpr
              (trivialFunctor_coact R H M m))
      naturality := by
        intros
        ext m
        apply Subtype.ext
        simp [invariantsFunctor, trivialFunctor]
        rfl }
  counit :=
    { app := fun M ↦
        { toLinearMap := SMulMemClass.subtype (Comodule.fixedSubcomodule R H M)
          map_coact := by
            ext m
            -- Identify the chosen trivial coaction before evaluating the tensor map.
            change TensorProduct.map _ LinearMap.id (m ⊗ₜ[R] (1 : H)) = _
            rw [TensorProduct.map_tmul, LinearMap.id_apply]
            exact (Comodule.mem_fixedSubcomodule.mp m.property).symm }
      naturality := by
        intro M N f
        apply Comodule.Hom.toLinearMap_injective
        ext m
        simp [invariantsFunctor, trivialFunctor, LinearMap.comp_apply] }
  left_triangle_components _ := by ext; rfl
  right_triangle_components _ := by
    ext m
    apply Subtype.ext
    simp [invariantsFunctor]
    rfl

/-- The adjunction map factors a morphism from a trivial comodule through invariants,
without changing its underlying vectors. -/
@[simp]
theorem invariantsAdjunction_homEquiv_apply_hom {M : ModuleCat.{w} R}
    {N : ComoduleCat.{u, v, w} R H} (f : (trivialFunctor R H).obj M ⟶ N) :
    (SMulMemClass.subtype (Comodule.fixedSubcomodule R H N)).comp
      (((invariantsAdjunction R H).homEquiv M N f).hom) = f.toLinearMap := by
  rw [Adjunction.homEquiv_unit]
  ext m
  simp [invariantsAdjunction, invariantsFunctor, LinearMap.comp_apply]
  rfl

/-- The inverse adjunction map composes with the inclusion of invariant vectors. -/
@[simp]
theorem invariantsAdjunction_homEquiv_symm_apply_toLinearMap {M : ModuleCat.{w} R}
    {N : ComoduleCat.{u, v, w} R H} (f : M ⟶ (invariantsFunctor R H).obj N) :
    (((invariantsAdjunction R H).homEquiv M N).symm f).toLinearMap =
      (SMulMemClass.subtype (Comodule.fixedSubcomodule R H N)).comp f.hom := by
  simp [invariantsAdjunction, Adjunction.homEquiv_counit]

noncomputable instance : (invariantsFunctor.{u, v, w} R H).IsRightAdjoint :=
  (invariantsAdjunction R H).isRightAdjoint

end TauCeti.ComoduleCat
