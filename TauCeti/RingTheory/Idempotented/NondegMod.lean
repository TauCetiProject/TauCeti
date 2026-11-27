/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
public import TauCeti.RingTheory.Idempotented.Basic

/-!
# The category of nondegenerate modules over an idempotented algebra

Let `H` be a nonunital algebra over a commutative ring `A`. A module over `H` is a module over its
unitization `A ⊕ H`, and `NondegMod A H` is the full subcategory of `ModuleCat (Unitization A H)` on
the nondegenerate modules, those with `H • M = M`. For the Hecke algebra of a locally profinite
group, with coefficients in which small compact open subgroups have invertible pro-order, these
are the smooth representations.

When `H` is idempotented this subcategory is closed under subobjects, quotients, finite limits and
all colimits, so it is abelian and the inclusion is exact and preserves colimits. The inclusion
also has a right adjoint, the nondegenerate part `M ↦ H • M`, so that limits of nondegenerate
modules are the nondegenerate parts of the limits of modules.

## Main definitions

* `TauCeti.nondegenerateModuleProperty A H`: the property of a module over `A ⊕ H` of being
  nondegenerate.
* `TauCeti.NondegMod A H`: the category of nondegenerate modules.
* `TauCeti.nondegeneratePartFunctor A H`: the nondegenerate part, as a functor to `NondegMod A H`.
* `TauCeti.nondegeneratePartAdjunction A H`: the inclusion is left adjoint to the nondegenerate
  part.

## Main results

* `TauCeti.isNondegenerate_of_isColimit`: a colimit of nondegenerate modules is nondegenerate.
* `TauCeti.isNondegenerate_of_isLimit`: over an idempotented algebra, a finite limit of
  nondegenerate modules is nondegenerate.
* the instance `HasColimits` on `TauCeti.NondegMod A H`, and for idempotented `H`, the instances
  `Abelian` and `HasLimits` on it and `Coreflective` on its inclusion into modules.
* `TauCeti.nondegeneratePartAdjunction_counit_app`: the counit of the coreflection is the
  inclusion `H • M → M`; `TauCeti.coe_nondegeneratePartAdjunction_unit_app` and
  `TauCeti.coe_nondegeneratePartAdjunction_homEquiv_apply` compute its unit and hom-equivalence.

## References

* J. N. Bernstein, *Le "centre" de Bernstein*, edited by P. Deligne, in *Représentations des groupes
  réductifs sur un corps local*, Hermann, Paris (1984), §1.1.
-/

public section

universe v u₁ u₂

open CategoryTheory Limits

namespace TauCeti

variable (A : Type u₁) (H : Type u₂) [CommRing A] [NonUnitalRing H] [Module A H]
  [IsScalarTower A H H] [SMulCommClass A H H]

/-- The property of a module over the unitization `A ⊕ H` of being nondegenerate. -/
def nondegenerateModuleProperty : ObjectProperty (ModuleCat.{v} (Unitization A H)) :=
  fun M ↦ IsNondegenerate A H M

/-- The category of nondegenerate modules over a nonunital `A`-algebra `H`: the full subcategory
of modules `M` over the unitization `A ⊕ H` with `H • M = M`. -/
abbrev NondegMod := (nondegenerateModuleProperty.{v} A H).FullSubcategory

variable {A H}

/-- An object of `ModuleCat (Unitization A H)` satisfies `nondegenerateModuleProperty A H` exactly
when it is nondegenerate. -/
@[simp]
theorem nondegenerateModuleProperty_iff (M : ModuleCat.{v} (Unitization A H)) :
    nondegenerateModuleProperty A H M ↔ IsNondegenerate A H M :=
  Iff.rfl

/-- The point of a colimit cocone of nondegenerate modules is nondegenerate. -/
theorem isNondegenerate_of_isColimit {J : Type*} [Category J]
    {F : J ⥤ ModuleCat.{v} (Unitization A H)} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ j, IsNondegenerate A H (F.obj j)) : IsNondegenerate A H c.pt := by
  let N := nondegeneratePart A H c.pt
  -- The quotient map by `H • c.pt` vanishes on every leg of the cocone, hence vanishes.
  have hq : (ModuleCat.ofHom N.mkQ : c.pt ⟶ ModuleCat.of _ (c.pt ⧸ N)) = 0 := by
    refine hc.hom_ext fun j ↦ ?_
    ext x
    have hx : x ∈ nondegeneratePart A H (F.obj j) :=
      (hF j).nondegeneratePart_eq_top ▸ Submodule.mem_top
    simpa [Submodule.Quotient.mk_eq_zero] using
      map_nondegeneratePart_le (c.ι.app j).hom (Submodule.mem_map_of_mem hx)
  refine isNondegenerate_iff_nondegeneratePart_eq_top.2 (eq_top_iff.2 fun m _ ↦ ?_)
  simpa [Submodule.Quotient.mk_eq_zero] using congrArg (fun f ↦ f.hom m) hq

/-- Over an idempotented algebra, the point of a limit cone over a diagram of nondegenerate
modules indexed by a category with finitely many objects is nondegenerate. -/
theorem isNondegenerate_of_isLimit [IsIdempotented H] {J : Type} [SmallCategory J] [Finite J]
    {F : J ⥤ ModuleCat.{v} (Unitization A H)} {c : Cone F} (hc : IsLimit c)
    (hF : ∀ j, IsNondegenerate A H (F.obj j)) : IsNondegenerate A H c.pt := by
  classical
  have := Fintype.ofFinite J
  rw [isNondegenerate_iff]
  intro x
  choose e _ he using fun j ↦ isNondegenerate_iff.1 (hF j) (c.π.app j x)
  obtain ⟨f, hf, hfe⟩ := IsIdempotented.exists_isIdempotentElem (Finset.univ.image e)
  refine ⟨f, hf, Concrete.isLimit_ext F hc _ _ fun j ↦ ?_⟩
  rw [map_smul]
  exact inr_smul_eq_of_mul_eq (he j) (hfe _ (Finset.mem_image_of_mem e (Finset.mem_univ j))).1

namespace NondegMod

/-- The underlying module of an object of `NondegMod A H` is nondegenerate. -/
theorem isNondegenerate (M : NondegMod.{v} A H) : IsNondegenerate A H M.obj :=
  M.property

instance : (nondegenerateModuleProperty.{v} A H).ContainsZero :=
  ⟨⟨ModuleCat.of _ PUnit, ModuleCat.isZero_of_subsingleton _,
    isNondegenerate_iff_nondegeneratePart_eq_top.2 (Subsingleton.elim _ _)⟩⟩

instance : (nondegenerateModuleProperty.{v} A H).IsClosedUnderQuotients where
  prop_of_epi f hf hX :=
    IsNondegenerate.of_surjective hX f.hom ((ModuleCat.epi_iff_surjective f).1 hf)

instance (J : Type*) [Category J] :
    (nondegenerateModuleProperty.{v} A H).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨h⟩
    exact isNondegenerate_of_isColimit h.isColimit h.prop_diag_obj

/-- Nondegenerate modules have all colimits, computed on underlying modules. -/
instance : HasColimits (NondegMod.{v} A H) := ⟨fun _ _ ↦ inferInstance⟩

variable [IsIdempotented H]

instance : (nondegenerateModuleProperty.{v} A H).IsClosedUnderSubobjects where
  prop_of_mono f hf hY :=
    IsNondegenerate.of_injective hY f.hom ((ModuleCat.mono_iff_injective f).1 hf)

instance : (nondegenerateModuleProperty.{v} A H).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape _ _ _ := ⟨by
    rintro X ⟨h⟩
    exact isNondegenerate_of_isLimit h.isLimit h.prop_diag_obj⟩

/-- Over an idempotented algebra, nondegenerate modules form an abelian category. -/
instance : Abelian (NondegMod.{v} A H) := inferInstance

end NondegMod

variable (A H) [IsIdempotented H]

/-- The nondegenerate part `H • M`, as a functor from modules over the unitization `A ⊕ H` to
nondegenerate modules. -/
@[expose, simps obj_obj map]
def nondegeneratePartFunctor : ModuleCat.{v} (Unitization A H) ⥤ NondegMod.{v} A H where
  obj M := ⟨ModuleCat.of _ (nondegeneratePart A H M),
    (nondegenerateModuleProperty_iff _).2 isNondegenerate_nondegeneratePart⟩
  map f := ObjectProperty.homMk (ModuleCat.ofHom (f.hom.restrict fun _ hx ↦
    map_nondegeneratePart_le f.hom (Submodule.mem_map_of_mem hx)))

/-- The inclusion of nondegenerate modules is left adjoint to the nondegenerate part: a
homomorphism from a nondegenerate module lands in the nondegenerate part of its target. -/
def nondegeneratePartAdjunction :
    (nondegenerateModuleProperty.{v} A H).ι ⊣ nondegeneratePartFunctor.{v} A H :=
  Adjunction.mkOfHomEquiv
    { homEquiv X M :=
        { toFun f := ObjectProperty.homMk (ModuleCat.ofHom (f.hom.codRestrict _ fun x ↦
            map_nondegeneratePart_le f.hom (Submodule.mem_map_of_mem
              (((nondegenerateModuleProperty_iff _).1 X.property).nondegeneratePart_eq_top ▸
                Submodule.mem_top))))
          invFun g := ModuleCat.ofHom ((nondegeneratePart A H M).subtype ∘ₗ g.hom.hom)
          left_inv _ := by ext; simp [nondegeneratePartFunctor]
          -- Corestricting `subtype ∘ₗ g` to `H • M` gives back `g` by eta for subtypes, linear maps
          -- and the hom structures. `simp` cannot see it: the codomain of `g` is
          -- `(nondegeneratePartFunctor A H).obj M`, which is `H • M` only after unfolding the
          -- functor, so `LinearMap.codRestrict_apply` and `Subtype.coe_eta` do not match.
          right_inv _ := rfl } }

/-- The hom-equivalence of `TauCeti.nondegeneratePartAdjunction` corestricts a homomorphism
`X → M` out of a nondegenerate module to the nondegenerate part `H • M`. -/
theorem coe_nondegeneratePartAdjunction_homEquiv_apply (X : NondegMod.{v} A H)
    (M : ModuleCat.{v} (Unitization A H)) (f : X.obj ⟶ M) (x : X.obj) :
    Subtype.val (((nondegeneratePartAdjunction.{v} A H).homEquiv X M f).hom.hom x) = f.hom x := by
  rw [nondegeneratePartAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  -- This is the `toFun` field followed by `LinearMap.codRestrict_apply`. It is intended to hold
  -- by `rfl`: `simp` cannot apply `ObjectProperty.homMk_hom` or `ConcreteCategory.hom_ofHom`
  -- here, since the target object `(nondegeneratePartFunctor A H).obj M` is `H • M` only after
  -- unfolding the functor.
  rfl

/-- The inverse hom-equivalence of `TauCeti.nondegeneratePartAdjunction` composes a homomorphism
into `H • M` with the inclusion `H • M → M`. -/
theorem nondegeneratePartAdjunction_homEquiv_symm_apply (X : NondegMod.{v} A H)
    (M : ModuleCat.{v} (Unitization A H)) (g : X ⟶ (nondegeneratePartFunctor.{v} A H).obj M) :
    ((nondegeneratePartAdjunction.{v} A H).homEquiv X M).symm g =
      ModuleCat.ofHom ((nondegeneratePart A H M).subtype ∘ₗ g.hom.hom) := by
  rw [nondegeneratePartAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  -- This is the `invFun` field, so it holds by `rfl`.
  rfl

/-- The unit of `TauCeti.nondegeneratePartAdjunction` at a nondegenerate module `X` sends `x` to
itself, viewed in `H • X = X`. -/
theorem coe_nondegeneratePartAdjunction_unit_app (X : NondegMod.{v} A H) (x : X.obj) :
    Subtype.val (((nondegeneratePartAdjunction.{v} A H).unit.app X).hom.hom x) = x := by
  rw [← Adjunction.homEquiv_id, coe_nondegeneratePartAdjunction_homEquiv_apply]
  simp

/-- The counit of `TauCeti.nondegeneratePartAdjunction` is the inclusion `H • M → M`. -/
@[simp]
theorem nondegeneratePartAdjunction_counit_app (M : ModuleCat.{v} (Unitization A H)) :
    (nondegeneratePartAdjunction.{v} A H).counit.app M =
      ModuleCat.ofHom (nondegeneratePart A H M).subtype := by
  rw [← Adjunction.homEquiv_symm_id, nondegeneratePartAdjunction_homEquiv_symm_apply,
    ObjectProperty.FullSubcategory.id_hom, ModuleCat.hom_id]
  exact congrArg ModuleCat.ofHom (LinearMap.comp_id _)

instance : Coreflective (nondegenerateModuleProperty.{v} A H).ι where
  R := nondegeneratePartFunctor.{v} A H
  adj := nondegeneratePartAdjunction.{v} A H

/-- Nondegenerate modules have all limits: the limit of a diagram of nondegenerate modules is the
nondegenerate part of its limit as modules. -/
instance : HasLimits (NondegMod.{v} A H) :=
  hasLimits_of_coreflective (nondegenerateModuleProperty.{v} A H).ι

end TauCeti
