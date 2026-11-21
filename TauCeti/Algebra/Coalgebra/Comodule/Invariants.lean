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

For a coalgebra with a distinguished `1` over a commutative ring, taking the fixed submodule
of a right comodule is an additive functor to modules. For a bialgebra it is right adjoint to
equipping a module with the trivial coaction, and hence preserves limits. This gives the left-exact
functor whose right derived functors are rational cohomology. Neither flatness of the bialgebra nor
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

variable (R : Type u) (H : Type v) [CommRing R]

section Coalgebra

variable [AddCommMonoid H] [Module R H] [Coalgebra R H] [One H]

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

-- Simplify the applied map before the bundled map is replaced by `fixedMap`.
/-- On underlying vectors, the map on invariants acts by the original comodule morphism. -/
@[simp↓]
theorem coe_invariantsFunctor_map_apply {M N : ComoduleCat.{u, v, w} R H} (f : M ⟶ N)
    (m : Comodule.fixedSubcomodule R H M) :
    ((invariantsFunctor R H).map f m : Comodule.fixedSubcomodule R H N).val = f (m : M) :=
  Comodule.Hom.fixedMap_apply f m

instance : (invariantsFunctor.{u, v, w} R H).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    rw [ModuleCat.hom_add, LinearMap.add_apply]
    rw [Submodule.coe_add (p := (Comodule.fixedSubcomodule R H N).carrier)
      ((invariantsFunctor R H).map f m) ((invariantsFunctor R H).map g m)]
    simp only [coe_invariantsFunctor_map_apply, ComoduleCat.add_apply]

end Coalgebra

variable [Semiring H] [Bialgebra R H]

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
theorem trivialFunctor_obj_coact_apply (M : ModuleCat.{w} R) (m : M) :
    Comodule.coact (R := R) (C := H) (M := (trivialFunctor R H).obj M) m =
      m ⊗ₜ[R] (1 : H) :=
  (rfl)

/-- The underlying linear map of the trivial-comodule functor is unchanged. -/
@[simp]
theorem trivialFunctor_map_toLinearMap {M N : ModuleCat.{w} R} (f : M ⟶ N) :
    ((trivialFunctor R H).map f).toLinearMap = f.hom :=
  (rfl)

-- Match the bundled application before simplification rewrites its coercions.
/-- The map of the trivial-comodule functor acts by the original module morphism. -/
@[simp↓]
theorem trivialFunctor_map_apply {M N : ModuleCat.{w} R} (f : M ⟶ N) (m : M) :
    (trivialFunctor R H).map f m = f m :=
  (rfl)

instance : (trivialFunctor.{u, v, w} R H).Additive where
  map_add := by
    intros
    apply Comodule.Hom.toLinearMap_injective
    simp

private noncomputable def unitApp (M : ModuleCat.{w} R) :
    M ⟶ (invariantsFunctor R H).obj ((trivialFunctor R H).obj M) :=
  ModuleCat.ofHom (Y := Comodule.fixedSubcomodule R H ((trivialFunctor R H).obj M))
    { toFun := fun m ↦ ⟨m, Comodule.mem_fixedSubcomodule.mpr
        (trivialFunctor_obj_coact_apply R H M m)⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }

@[simp]
private theorem unitApp_apply (M : ModuleCat.{w} R) (m : M) :
    (unitApp R H M m : Comodule.fixedSubcomodule R H ((trivialFunctor R H).obj M)).val = m :=
  (rfl)

private noncomputable def counitApp (N : ComoduleCat.{u, v, w} R H) :
    (trivialFunctor R H).obj ((invariantsFunctor R H).obj N) ⟶ N where
  toLinearMap := SMulMemClass.subtype (Comodule.fixedSubcomodule R H N)
  map_coact := by
    ext m
    rw [LinearMap.comp_apply, trivialFunctor_obj_coact_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearMap.comp_apply]
    exact (Comodule.mem_fixedSubcomodule.mp m.property).symm

private theorem counitApp_apply (N : ComoduleCat.{u, v, w} R H)
    (m : Comodule.fixedSubcomodule R H N) : counitApp R H N m = (m : N) :=
  (rfl)

/-- Equipping a module with the trivial coaction is left adjoint to taking invariants.
The counit is the inclusion of invariant vectors. -/
noncomputable def invariantsAdjunction :
    trivialFunctor.{u, v, w} R H ⊣ invariantsFunctor R H where
  unit :=
    { app := unitApp R H
      naturality := by
        intro M N f
        dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        apply Subtype.ext
        simp only [ModuleCat.comp_apply, unitApp_apply, coe_invariantsFunctor_map_apply,
          trivialFunctor_map_apply] }
  counit :=
    { app := counitApp R H
      naturality := by
        intro M N f
        dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj]
        ext m
        simp only [comp_apply, counitApp_apply, trivialFunctor_map_apply,
          coe_invariantsFunctor_map_apply] }
  left_triangle_components M := by
    ext m
    simp only [comp_apply, id_apply, counitApp_apply, trivialFunctor_map_apply, unitApp_apply]
  right_triangle_components N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    simp only [ModuleCat.comp_apply, coe_invariantsFunctor_map_apply, counitApp_apply,
      unitApp_apply, ModuleCat.id_apply]

-- Match the bundled application before simplification rewrites its coercions.
/-- The unit identifies a module with the invariants of its trivial coaction. -/
@[simp↓]
theorem coe_invariantsAdjunction_unit_app_apply (M : ModuleCat.{w} R) (m : M) :
    ((invariantsAdjunction R H).unit.app M m :
      Comodule.fixedSubcomodule R H ((trivialFunctor R H).obj M)).val = m :=
  (rfl)

/-- The underlying map of the counit is inclusion of the invariant vectors. -/
@[simp]
theorem invariantsAdjunction_counit_app_toLinearMap (N : ComoduleCat.{u, v, w} R H) :
    ((invariantsAdjunction R H).counit.app N).toLinearMap =
      SMulMemClass.subtype (Comodule.fixedSubcomodule R H N) :=
  (rfl)

-- Match the bundled application before simplification rewrites its coercions.
/-- The counit sends a fixed vector to its underlying vector. -/
@[simp↓]
theorem invariantsAdjunction_counit_app_apply (N : ComoduleCat.{u, v, w} R H)
    (m : Comodule.fixedSubcomodule R H N) : (invariantsAdjunction R H).counit.app N m = (m : N) :=
  (rfl)

/-- The adjunction map factors a morphism from a trivial comodule through invariants,
without changing its underlying vectors. -/
@[simp]
theorem coe_invariantsAdjunction_homEquiv_apply_apply {M : ModuleCat.{w} R}
    {N : ComoduleCat.{u, v, w} R H} (f : (trivialFunctor R H).obj M ⟶ N) (m : M) :
    ((invariantsAdjunction R H).homEquiv M N f m : Comodule.fixedSubcomodule R H N).val = f m := by
  rw [Adjunction.homEquiv_unit]
  rw [ModuleCat.comp_apply,
    coe_invariantsFunctor_map_apply R H f ((invariantsAdjunction R H).unit.app M m),
    coe_invariantsAdjunction_unit_app_apply R H M m]

/-- The inverse adjunction map composes with the inclusion of invariant vectors. -/
@[simp]
theorem invariantsAdjunction_homEquiv_symm_apply_toLinearMap {M : ModuleCat.{w} R}
    {N : ComoduleCat.{u, v, w} R H} (f : M ⟶ (invariantsFunctor R H).obj N) :
    (((invariantsAdjunction R H).homEquiv M N).symm f).toLinearMap =
      (SMulMemClass.subtype (Comodule.fixedSubcomodule R H N)).comp f.hom := by
  simp [Adjunction.homEquiv_counit]

-- Match the bundled application before simplification rewrites its coercions.
/-- The inverse adjunction map evaluates the given map and then forgets invariance. -/
@[simp↓]
theorem invariantsAdjunction_homEquiv_symm_apply_apply {M : ModuleCat.{w} R}
    {N : ComoduleCat.{u, v, w} R H} (f : M ⟶ (invariantsFunctor R H).obj N) (m : M) :
    ((invariantsAdjunction R H).homEquiv M N).symm f m =
      (f m : Comodule.fixedSubcomodule R H N).val := by
  rw [Adjunction.homEquiv_counit, comp_apply, trivialFunctor_map_apply,
    invariantsAdjunction_counit_app_apply]

noncomputable instance : (trivialFunctor.{u, v, w} R H).IsLeftAdjoint :=
  (invariantsAdjunction R H).isLeftAdjoint

noncomputable instance : (invariantsFunctor.{u, v, w} R H).IsRightAdjoint :=
  (invariantsAdjunction R H).isRightAdjoint

end TauCeti.ComoduleCat
