/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The ideal-power torsion functor on `ModuleCat`

For an ideal `J` of a commutative ring `R`, this file bundles the `J`-power torsion submodule
`J.primaryComponent M` as an additive left exact endofunctor `Ideal.primaryComponentFunctor J` on
`ModuleCat.{v} R`, with natural inclusion `Ideal.primaryComponentFunctorι J` and objectwise
identification `Ideal.primaryComponentFunctorObjIso J M`.

## Main definitions

* `Ideal.primaryComponentFunctor J`: the `J`-power torsion endofunctor `Γ_J` on `ModuleCat.{v} R`.
* `Ideal.primaryComponentFunctorObjIso J M`: the canonical isomorphism
  `J.primaryComponentFunctor.obj M ≅ ModuleCat.of R (J.primaryComponent M)`.
* `Ideal.primaryComponentFunctorι J`: the natural monomorphism
  `J.primaryComponentFunctor ⟶ 𝟭 (ModuleCat.{v} R)`.

## Main results

* `Ideal.preservesFiniteLimits_primaryComponentFunctor`: `J.primaryComponentFunctor` is left exact.

## References

* A. Grothendieck, *Local Cohomology* (notes by R. Hartshorne), Lecture Notes in Mathematics 41,
  Springer, 1967, Proposition 2.8.
* [The Stacks Project, Tag 0954](https://stacks.math.columbia.edu/tag/0954)
-/

public section

universe v u

open CategoryTheory Limits

namespace Ideal

variable {R : Type u} [CommRing R] (J : Ideal R)

/-- The `J`-power torsion endofunctor `Γ_J` on `ModuleCat.{v} R`, sending a module `M` to its
`J`-primary component `⨆ n, Submodule.torsionBySet R M (J ^ n)`. -/
def primaryComponentFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (J.primaryComponent M)
  map f := ModuleCat.ofHom (Ideal.primaryComponent.map J f.hom)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The canonical isomorphism identifying `J.primaryComponentFunctor.obj M` with
`ModuleCat.of R (J.primaryComponent M)`. -/
def primaryComponentFunctorObjIso (M : ModuleCat.{v} R) :
    J.primaryComponentFunctor.obj M ≅ ModuleCat.of R (J.primaryComponent M) :=
  Iso.refl _

/-- Under `primaryComponentFunctorObjIso`, `J.primaryComponentFunctor.map f` acts as
`Ideal.primaryComponent.map J f.hom`. -/
@[reassoc (attr := simp)]
theorem primaryComponentFunctor_map_comp_objIso_hom {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    J.primaryComponentFunctor.map f ≫ (J.primaryComponentFunctorObjIso N).hom =
      (J.primaryComponentFunctorObjIso M).hom ≫
        ModuleCat.ofHom (Ideal.primaryComponent.map J f.hom) := (rfl)

/-- The natural submodule inclusion `Γ_J(M) ↪ M`. -/
def primaryComponentFunctorι : J.primaryComponentFunctor ⟶ 𝟭 (ModuleCat.{v} R) where
  app M := ModuleCat.ofHom (J.primaryComponent M).subtype
  naturality _ _ _ := by ext; rfl

/-- Elementwise naturality of `primaryComponentFunctorι`: applying `J.primaryComponentFunctor.map f`
followed by `J.primaryComponentFunctorι.app N` applies `f` to `J.primaryComponentFunctorι.app M`. -/
lemma primaryComponentFunctorι_app_map_apply {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (x : J.primaryComponentFunctor.obj M) :
    J.primaryComponentFunctorι.app N (J.primaryComponentFunctor.map f x) =
      f (J.primaryComponentFunctorι.app M x) :=
  ConcreteCategory.congr_hom (J.primaryComponentFunctorι.naturality f) x

/-- Applying `J.primaryComponentFunctorι.app M` to `(J.primaryComponentFunctorObjIso M).inv x`
recovers the underlying element `(x : M)`. -/
lemma primaryComponentFunctorι_app_objIso_inv_apply (M : ModuleCat.{v} R)
    (x : J.primaryComponent M) :
    J.primaryComponentFunctorι.app M ((J.primaryComponentFunctorObjIso M).inv x) = (x : M) := (rfl)

/-- `primaryComponentFunctorObjIso` followed by the submodule inclusion `subtype` is
`primaryComponentFunctorι`. -/
@[reassoc (attr := simp)]
theorem primaryComponentFunctorObjIso_hom_comp_subtype (M : ModuleCat.{v} R) :
    (J.primaryComponentFunctorObjIso M).hom ≫ ModuleCat.ofHom (J.primaryComponent M).subtype =
      J.primaryComponentFunctorι.app M := (rfl)

/-- Under `primaryComponentFunctorObjIso`, elements map to themselves in `M` via
`primaryComponentFunctorι`. -/
@[simp]
lemma coe_primaryComponentFunctorObjIso_hom_apply (M : ModuleCat.{v} R)
    (x : J.primaryComponentFunctor.obj M) :
    ((J.primaryComponentFunctorObjIso M).hom x : M) = J.primaryComponentFunctorι.app M x := (rfl)

/-- Composing `(J.primaryComponentFunctorObjIso M).inv` with `J.primaryComponentFunctorι.app M`
recovers the submodule inclusion `(J.primaryComponent M).subtype`. -/
@[reassoc (attr := simp)]
theorem primaryComponentFunctorObjIso_inv_comp_ι_app (M : ModuleCat.{v} R) :
    (J.primaryComponentFunctorObjIso M).inv ≫ J.primaryComponentFunctorι.app M =
      ModuleCat.ofHom (J.primaryComponent M).subtype := (rfl)

instance (M : ModuleCat.{v} R) : Mono (J.primaryComponentFunctorι.app M) :=
  (ModuleCat.mono_iff_injective _).2 (Submodule.subtype_injective _)

instance : Mono J.primaryComponentFunctorι :=
  NatTrans.mono_of_mono_app _

instance : J.primaryComponentFunctor.Additive where
  map_add {_ _ _ _} := by ext; rfl

/-- The `J`-power torsion functor `Γ_J` is left exact: an element of `B` killed by `J ^ n` whose
image in `C` vanishes lifts along a monomorphism `A ⟶ B` to an element of `A` killed by `J ^ n`. -/
noncomputable instance preservesFiniteLimits_primaryComponentFunctor :
    PreservesFiniteLimits J.primaryComponentFunctor := by
  refine J.primaryComponentFunctor.preservesFiniteLimits_iff_forall_exact_map_and_mono.mpr
    fun S hS ↦ ?_
  have hf : Function.Injective S.f := hS.moduleCat_injective_f
  refine ⟨(S.map J.primaryComponentFunctor).moduleCat_exact_iff.mpr fun y hy ↦ ?_,
    (ModuleCat.mono_iff_injective _).mpr fun _ _ hxy ↦ Subtype.ext (hf (congrArg Subtype.val hxy))⟩
  have hyker : y.val ∈ (Ideal.primaryComponent.map J S.g.hom).ker.map
      (J.primaryComponent S.X₂).subtype := ⟨y, hy, rfl⟩
  rw [Ideal.primaryComponent.map_ker_eq] at hyker
  obtain ⟨⟨z, hz⟩, hzt, hzx⟩ := hyker
  let e : S.X₁ ≃ₗ[R] LinearMap.ker S.g.hom := (LinearEquiv.ofInjective S.f.hom hf).trans
    (LinearEquiv.ofEq _ _ hS.exact.moduleCat_range_eq_ker)
  refine ⟨⟨e.symm ⟨z, hz⟩,
    Ideal.primaryComponent_map_mem J e.symm.toLinearMap ⟨⟨z, hz⟩, hzt⟩⟩, Subtype.ext ?_⟩
  exact (congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩)).trans hzx

end Ideal
