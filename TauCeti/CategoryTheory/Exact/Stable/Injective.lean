/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Injective
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Additive
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.FactorThrough
public import TauCeti.CategoryTheory.Linear.HomCokernel
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Injective stable Hom spaces

For an exact structure `E`, the injective stable category is the additive quotient by
maps factoring through relatively injective objects. This is the costable category used
on the Hom side of Auslander–Reiten duality; the algebra need not be self-injective.

An inflation `i : X ⟶ I` with relatively injective target computes its Hom spaces:
`HomCokernel R i Y` is canonically the space of maps `X ⟶ Y` in the injective stable
category. Indeed, a map factors through a relative injective exactly when it extends
across `i`. The comparison works for any such inflation, so it does not depend on a
choice of injective envelope or a minimal presentation. It is natural in the target.

The quotient category and its additive and linear structures use
`ObjectProperty.factorIdeal` and `MorphismIdeal.quotientFunctor`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections IV.1–IV.2.
* T. Bühler, *Exact Categories*, Expositiones Mathematicae **28** (2010), 1–69,
  Section 11.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits

universe u v t

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] (E : ExactStructure C)

/-- The ideal of morphisms factoring through objects injective relative to `E`. -/
def injectiveStableIdeal : MorphismIdeal C :=
  E.isInjective.factorIdeal

/-- The additive category obtained by killing morphisms through relative injectives. -/
abbrev InjectiveStableCategory := E.injectiveStableIdeal.Quotient

/-- The quotient functor to the injective stable category. -/
abbrev injectiveStableFunctor : C ⥤ E.InjectiveStableCategory :=
  E.injectiveStableIdeal.quotientFunctor

/-- Membership in the injective stable ideal is equivalent to a single factorization
through a relative injective object. -/
@[simp]
theorem mem_injectiveStableIdeal_iff {X Y : C} {f : X ⟶ Y} :
    f ∈ E.injectiveStableIdeal.hom X Y ↔ E.isInjective.FactorsThrough f := by
  rw [injectiveStableIdeal, ObjectProperty.mem_factorIdeal_iff]

/-- A morphism vanishes in the injective stable category exactly when it factors
through a relative injective. -/
@[simp high]
theorem injectiveStableFunctor_map_eq_zero_iff {X Y : C} {f : X ⟶ Y} :
    E.injectiveStableFunctor.map f = 0 ↔ E.isInjective.FactorsThrough f := by
  rw [MorphismIdeal.quotientFunctor_map_eq_zero_iff, mem_injectiveStableIdeal_iff]

/-- Precisely the relative injective objects become zero in the injective stable category. -/
@[simp high]
theorem isZero_injectiveStableFunctor_obj_iff (X : C) :
    IsZero (E.injectiveStableFunctor.obj X) ↔ E.isInjective X := by
  rw [MorphismIdeal.isZero_quotientFunctor_obj_iff, mem_injectiveStableIdeal_iff,
    ObjectProperty.factorsThrough_id_iff]

section Linear

variable (R : Type t) [Ring R] [Linear R C]
  {X I Y Z : C}

/-- An injective stable morphism is zero exactly when its representative belongs to
the image of restriction from a fixed inflation into a relative injective. -/
theorem injectiveStableFunctor_map_eq_zero_iff_mem_range (i : X ⟶ I)
    (hi : E.IsInflation i) (hI : E.isInjective I) (f : X ⟶ Y) :
    E.injectiveStableFunctor.map f = 0 ↔ f ∈ (Linear.leftComp R Y i).range := by
  rw [injectiveStableFunctor_map_eq_zero_iff,
    E.factorsThrough_injective_iff_exists_extension i hi hI, LinearMap.mem_range]
  rfl

/-- The Hom cokernel of an inflation into a relative injective is the Hom space in the
injective stable category. The equivalence sends the class of a map to its stable image. -/
noncomputable def homCokernelEquivInjectiveStableHom (i : X ⟶ I)
    (hi : E.IsInflation i) (hI : E.isInjective I) (Y : C) :
    HomCokernel R i Y ≃ₗ[R]
      (E.injectiveStableFunctor.obj X ⟶ E.injectiveStableFunctor.obj Y) := by
  let q := E.injectiveStableFunctor.mapLinearMap R (X := X) (Y := Y)
  have hker : LinearMap.ker q = (Linear.leftComp R Y i).range := by
    ext f
    exact E.injectiveStableFunctor_map_eq_zero_iff_mem_range R i hi hI f
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (q.quotKerEquivOfSurjective E.injectiveStableFunctor.map_surjective)

/-- The Hom-cokernel comparison sends a representative to its injective stable image. -/
@[simp]
theorem homCokernelEquivInjectiveStableHom_mk (i : X ⟶ I)
    (hi : E.IsInflation i) (hI : E.isInjective I) (f : X ⟶ Y) :
    E.homCokernelEquivInjectiveStableHom R i hi hI Y (Submodule.Quotient.mk f) =
      E.injectiveStableFunctor.map f := by
  rw [homCokernelEquivInjectiveStableHom, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk]
  -- The quotient's carrier uses the function underlying `mapLinearMap`.
  erw [LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- The inverse comparison gives the class of any representative of a stable morphism. -/
@[simp]
theorem homCokernelEquivInjectiveStableHom_symm_map (i : X ⟶ I)
    (hi : E.IsInflation i) (hI : E.isInjective I) (f : X ⟶ Y) :
    (E.homCokernelEquivInjectiveStableHom R i hi hI Y).symm
      (E.injectiveStableFunctor.map f) = Submodule.Quotient.mk f := by
  apply (E.homCokernelEquivInjectiveStableHom R i hi hI Y).injective
  simp

/-- The comparison with injective stable Hom commutes with postcomposition. -/
theorem homCokernelEquivInjectiveStableHom_naturality (i : X ⟶ I)
    (hi : E.IsInflation i) (hI : E.isInjective I) (g : Y ⟶ Z) (x : HomCokernel R i Y) :
    E.homCokernelEquivInjectiveStableHom R i hi hI Z (HomCokernel.map R i g x) =
      E.homCokernelEquivInjectiveStableHom R i hi hI Y x ≫
        E.injectiveStableFunctor.map g := by
  induction x using Submodule.Quotient.induction_on with
  | _ f => simp

end Linear

end TauCeti.ExactStructure
