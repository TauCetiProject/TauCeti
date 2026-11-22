/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.YonedaExt.BaerSum
public import TauCeti.CategoryTheory.Exact.YonedaExt.LongExact
public import TauCeti.CategoryTheory.Exact.YonedaExt.TrivialIdeal
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Linear

/-!
# `Ext¹` and the injectively trivial ideal through a conflation with injective middle term

Let `E` be an exact structure and `e : X ⟶ I ⟶ Z` a conflation whose middle term `I` is relatively
injective. Since `Ext¹_E(W, I) = 0`, the long exact sequence of `e` makes the connecting map
`Hom(W, Z) → Ext¹_E(W, X)`, `u ↦ u^* [e]`, surjective, with kernel the morphisms factoring through
the deflation `I ⟶ Z`. Dually, a morphism `X ⟶ Y` is injectively trivial exactly when it extends
across the inflation `X ⟶ I`. In an `R`-linear category this gives two `R`-linear identifications
of cokernels of `Hom` maps:

* `Ext¹_E(W, X) ≅ coker (Hom(W, I) → Hom(W, Z))`;
* `(E/ℐ)(X, Y) ≅ coker (Hom(I, Y) → Hom(X, Y))`.

These are the categorical sides of the contravariant and covariant defects of `e`, the two sides
of Auslander's defect formula.

## Main definitions

* `TauCeti.ExactStructure.InjectivePresentation.extension`: an injective presentation as an
  extension.
* `TauCeti.ExactStructure.Extension.homQuotientEquivExt1`:
  `Ext¹_E(W, X) ≅ coker (Hom(W, I) → Hom(W, Z))`.
* `TauCeti.ExactStructure.Extension.homQuotientEquivCostableHom`:
  `(E/ℐ)(X, Y) ≅ coker (Hom(I, Y) → Hom(X, Y))`.

## Main results

* `TauCeti.ExactStructure.Extension.exists_mk_pullback_eq_of_isInjective`: every class in
  `Ext¹_E(W, X)` is a base change of `[e]`.
* `TauCeti.ExactStructure.Extension.mem_injectivelyTrivialIdeal_iff_of_isInjective`: a morphism
  out of `X` is injectively trivial exactly when it extends across the inflation of `e`.

## References

* H. Krause, *A short proof for Auslander's defect formula*, Linear Algebra Appl. **365** (2003),
  267–270.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C} {W X Y Z : C}

/-- An injective presentation `X ⟶ I ⟶ K` as an extension of `K` by `X`. -/
def InjectivePresentation.extension (P : E.InjectivePresentation X) : E.Extension P.K X :=
  ⟨P.I, P.i, P.p, P.zero, P.conflation⟩

/-- The middle term of the extension of an injective presentation `X ⟶ I ⟶ K` is `I`. -/
@[simp]
theorem InjectivePresentation.extension_obj (P : E.InjectivePresentation X) :
    P.extension.obj = P.I :=
  (rfl)

/-- The short complex of the extension of an injective presentation is `X ⟶ I ⟶ K`. -/
@[simp]
theorem InjectivePresentation.extension_shortComplex (P : E.InjectivePresentation X) :
    P.extension.shortComplex = ShortComplex.mk P.i P.p P.zero :=
  (rfl)

/-- The middle term of the extension of an injective presentation is relatively injective. -/
theorem InjectivePresentation.isInjective_extension_obj (P : E.InjectivePresentation X) :
    E.isInjective P.extension.obj :=
  P.isInjective

namespace Extension

variable (e : E.Extension Z X) (he : E.isInjective e.obj)
include he

/-- **Every class is a base change of a conflation with injective middle term.** If the middle
term of `e : X ⟶ I ⟶ Z` is relatively injective, every class `ξ ∈ Ext¹_E(W, X)` is `u^* [e]`
for some `u : W ⟶ Z`. -/
theorem exists_mk_pullback_eq_of_isInjective (ξ : E.Ext1 W X) :
    ∃ u : W ⟶ Z, (Ext1.mk e).pullback u = ξ :=
  (Ext1.pushout_f_eq_zero_iff e ξ).mp ((isInjective_iff_forall_ext1_eq_zero _).mp he W _)

/-- **Injectively trivial morphisms through an injective conflation.** If the middle term of
`e : X ⟶ I ⟶ Z` is relatively injective, a morphism `f : X ⟶ Y` is injectively trivial exactly
when it extends across the inflation `X ⟶ I`. -/
theorem mem_injectivelyTrivialIdeal_iff_of_isInjective (f : X ⟶ Y) :
    f ∈ E.injectivelyTrivialIdeal.hom X Y ↔ ∃ t : e.obj ⟶ Y, e.f ≫ t = f := by
  refine ⟨fun h ↦ mem_injectivelyTrivialIdeal_iff.mp h (E.isInflation_f e.conflation), ?_⟩
  rintro ⟨t, rfl⟩
  exact mem_injectivelyTrivialIdeal_iff.mpr fun _ i hi ↦
    ⟨he.factorThru hi e.f ≫ t, by rw [isInjective.comp_factorThru_assoc]⟩

omit he

section Linear

variable (R : Type*) [Ring R] [Linear R C]

/-- The connecting map `u ↦ u^* [e]`, as an `R`-linear map `Hom(W, Z) → Ext¹_E(W, X)`. -/
private noncomputable def connectingLinearMap (W : C) : (W ⟶ Z) →ₗ[R] E.Ext1 W X where
  toFun u := (Ext1.mk e).pullback u
  map_add' u v := Ext1.pullback_add _ u v
  map_smul' r u := Ext1.pullback_smul r _ u

include he

/-- **`Ext¹` as a cokernel.** If the middle term of `e : X ⟶ I ⟶ Z` is relatively injective,
`u ↦ u^* [e]` identifies the cokernel of `Hom(W, I) → Hom(W, Z)` with `Ext¹_E(W, X)`. -/
noncomputable def homQuotientEquivExt1 (W : C) :
    ((W ⟶ Z) ⧸ LinearMap.range (Linear.rightComp R W e.g)) ≃ₗ[R] E.Ext1 W X :=
  Submodule.quotEquivOfEq _ _ (by
      ext u
      rw [LinearMap.mem_range, LinearMap.mem_ker]
      exact (e.exact_comp_g_mk_pullback W u).symm) ≪≫ₗ
    (connectingLinearMap e R W).quotKerEquivOfSurjective
      (e.exists_mk_pullback_eq_of_isInjective he)

/-- The class of `u : W ⟶ Z` corresponds to the base change `u^* [e]`. -/
@[simp]
theorem homQuotientEquivExt1_mk {W : C} (u : W ⟶ Z) :
    e.homQuotientEquivExt1 he R W (Submodule.Quotient.mk u) = (Ext1.mk e).pullback u :=
  (rfl)

/-- **Costable `Hom` as a cokernel.** If the middle term of `e : X ⟶ I ⟶ Z` is relatively
injective, the quotient functor identifies the cokernel of `Hom(I, Y) → Hom(X, Y)` with the
`Hom` space `(E/ℐ)(X, Y)` of the quotient by the injectively trivial ideal. -/
noncomputable def homQuotientEquivCostableHom (Y : C) :
    ((X ⟶ Y) ⧸ LinearMap.range (Linear.leftComp R Y e.f)) ≃ₗ[R]
      (E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
        E.injectivelyTrivialIdeal.quotientFunctor.obj Y) :=
  Submodule.quotEquivOfEq _ _ (by
      ext f
      rw [LinearMap.mem_range, MorphismIdeal.mem_homSubmodule,
        e.mem_injectivelyTrivialIdeal_iff_of_isInjective he]
      rfl) ≪≫ₗ
    E.injectivelyTrivialIdeal.homLinearEquiv R X Y

/-- The class of `f : X ⟶ Y` corresponds to its image in the quotient category. -/
@[simp]
theorem homQuotientEquivCostableHom_mk {Y : C} (f : X ⟶ Y) :
    e.homQuotientEquivCostableHom he R Y (Submodule.Quotient.mk f) =
      E.injectivelyTrivialIdeal.quotientFunctor.map f := by
  simp [homQuotientEquivCostableHom]

end Linear

end Extension

end ExactStructure

end TauCeti
