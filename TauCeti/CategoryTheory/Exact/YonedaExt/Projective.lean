/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.YonedaExt.BaerSum
public import TauCeti.CategoryTheory.Exact.YonedaExt.LongExact
public import TauCeti.CategoryTheory.Exact.YonedaExt.TrivialIdeal
public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Linear

/-!
# `Ext¹` and the projective stable category through a conflation with projective middle term

Let `E` be an exact structure and `e : X ⟶ P ⟶ Z` a conflation whose middle term `P` is relatively
projective. Since `Ext¹_E(P, W) = 0`, the long exact sequence of `e` makes the connecting map
`Hom(X, W) → Ext¹_E(Z, W)`, `v ↦ v_* [e]`, surjective, with kernel the morphisms extending along
the inflation `X ⟶ P`. Dually, a morphism `Y ⟶ Z` factors through a relative projective exactly
when it lifts along the deflation `P ⟶ Z`. In an `R`-linear category this gives two `R`-linear
identifications of cokernels of `Hom` maps:

* `Ext¹_E(Z, W) ≅ coker (Hom(P, W) → Hom(X, W))`;
* `(E/𝒫)(Y, Z) ≅ coker (Hom(Y, P) → Hom(Y, Z))`, in the projective stable category.

These are the categorical sides of the covariant and contravariant defects of `e`, and are dual to
`TauCeti/CategoryTheory/Exact/YonedaExt/Injective.lean`.

## Main definitions

* `TauCeti.ExactStructure.ProjectivePresentation.extension`: a projective presentation as an
  extension.
* `TauCeti.ExactStructure.Extension.homQuotientEquivExt1OfIsProjective`:
  `Ext¹_E(Z, W) ≅ coker (Hom(P, W) → Hom(X, W))`.
* `TauCeti.ExactStructure.Extension.homQuotientEquivStableHom`:
  `(E/𝒫)(Y, Z) ≅ coker (Hom(Y, P) → Hom(Y, Z))`.

## Main results

* `TauCeti.ExactStructure.Extension.exists_mk_pushout_eq_of_isProjective`: every class in
  `Ext¹_E(Z, W)` is a cobase change of `[e]`.
* `TauCeti.ExactStructure.Extension.mem_projectiveStableIdeal_iff_of_isProjective`: a morphism
  into `Z` factors through a relative projective exactly when it lifts along the deflation of `e`.

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

/-- A projective presentation `K ⟶ P ⟶ X` as an extension of `X` by `K`. -/
def ProjectivePresentation.extension (P : E.ProjectivePresentation X) : E.Extension X P.K :=
  ⟨P.P, P.i, P.p, P.zero, P.conflation⟩

/-- The middle term of the extension of a projective presentation `K ⟶ P ⟶ X` is `P`. -/
@[simp]
theorem ProjectivePresentation.extension_obj (P : E.ProjectivePresentation X) :
    P.extension.obj = P.P :=
  (rfl)

/-- The short complex of the extension of a projective presentation is `K ⟶ P ⟶ X`. -/
@[simp]
theorem ProjectivePresentation.extension_shortComplex (P : E.ProjectivePresentation X) :
    P.extension.shortComplex = ShortComplex.mk P.i P.p P.zero :=
  (rfl)

/-- The middle term of the extension of a projective presentation is relatively projective. -/
theorem ProjectivePresentation.isProjective_extension_obj (P : E.ProjectivePresentation X) :
    E.isProjective P.extension.obj :=
  P.isProjective

namespace Extension

variable (e : E.Extension Z X) (he : E.isProjective e.obj)
include he

/-- **Every class is a cobase change of a conflation with projective middle term.** If the middle
term of `e : X ⟶ P ⟶ Z` is relatively projective, every class `ξ ∈ Ext¹_E(Z, W)` is `v_* [e]`
for some `v : X ⟶ W`. -/
theorem exists_mk_pushout_eq_of_isProjective (ξ : E.Ext1 Z W) :
    ∃ v : X ⟶ W, (Ext1.mk e).pushout v = ξ :=
  (Ext1.pullback_g_eq_zero_iff e ξ).mp ((isProjective_iff_forall_ext1_eq_zero _).mp he W _)

/-- **Projectively stable morphisms through a projective conflation.** If the middle term of
`e : X ⟶ P ⟶ Z` is relatively projective, a morphism `f : Y ⟶ Z` factors through a relative
projective exactly when it lifts along the deflation `P ⟶ Z`. -/
theorem mem_projectiveStableIdeal_iff_of_isProjective (f : Y ⟶ Z) :
    f ∈ E.projectiveStableIdeal.hom Y Z ↔ ∃ t : Y ⟶ e.obj, t ≫ e.g = f := by
  rw [mem_projectiveStableIdeal_iff]
  refine ⟨fun hf ↦ ?_, fun ⟨t, ht⟩ ↦ ht ▸ ObjectProperty.factorsThrough_comp _ he t e.g⟩
  obtain ⟨Q, hQ, a, b, rfl⟩ := (ObjectProperty.factorsThrough_iff _ _).mp hf
  exact ⟨a ≫ hQ.factorThru (E.isDeflation_g e.conflation) b, by simp⟩

omit he

section Linear

variable (R : Type*) [Ring R] [Linear R C]

/-- The connecting map `v ↦ v_* [e]`, as an `R`-linear map `Hom(X, W) → Ext¹_E(Z, W)`. -/
private noncomputable def pushoutConnectingLinearMap (W : C) : (X ⟶ W) →ₗ[R] E.Ext1 Z W where
  toFun v := (Ext1.mk e).pushout v
  map_add' u v := Ext1.pushout_add _ u v
  map_smul' r v := Ext1.pushout_smul r _ v

include he

/-- **`Ext¹` as a cokernel.** If the middle term of `e : X ⟶ P ⟶ Z` is relatively projective,
`v ↦ v_* [e]` identifies the cokernel of `Hom(P, W) → Hom(X, W)` with `Ext¹_E(Z, W)`. -/
noncomputable def homQuotientEquivExt1OfIsProjective (W : C) :
    ((X ⟶ W) ⧸ LinearMap.range (Linear.leftComp R W e.f)) ≃ₗ[R] E.Ext1 Z W :=
  Submodule.quotEquivOfEq _ _ (by
      ext v
      rw [LinearMap.mem_range, LinearMap.mem_ker]
      exact (e.exact_f_comp_mk_pushout W v).symm) ≪≫ₗ
    (pushoutConnectingLinearMap e R W).quotKerEquivOfSurjective
      (e.exists_mk_pushout_eq_of_isProjective he)

/-- The class of `v : X ⟶ W` corresponds to the cobase change `v_* [e]`. -/
@[simp]
theorem homQuotientEquivExt1OfIsProjective_mk {W : C} (v : X ⟶ W) :
    e.homQuotientEquivExt1OfIsProjective he R W (Submodule.Quotient.mk v) =
      (Ext1.mk e).pushout v :=
  (rfl)

/-- **Stable `Hom` as a cokernel.** If the middle term of `e : X ⟶ P ⟶ Z` is relatively
projective, the quotient functor identifies the cokernel of `Hom(Y, P) → Hom(Y, Z)` with the
`Hom` space of the projective stable category. -/
noncomputable def homQuotientEquivStableHom (Y : C) :
    ((Y ⟶ Z) ⧸ LinearMap.range (Linear.rightComp R Y e.g)) ≃ₗ[R]
      (E.projectiveStableFunctor.obj Y ⟶ E.projectiveStableFunctor.obj Z) :=
  Submodule.quotEquivOfEq _ _ (by
      ext f
      rw [LinearMap.mem_range, MorphismIdeal.mem_homSubmodule,
        e.mem_projectiveStableIdeal_iff_of_isProjective he]
      rfl) ≪≫ₗ
    E.projectiveStableIdeal.homLinearEquiv R Y Z

/-- The class of `f : Y ⟶ Z` corresponds to its image in the projective stable category. -/
@[simp]
theorem homQuotientEquivStableHom_mk {Y : C} (f : Y ⟶ Z) :
    e.homQuotientEquivStableHom he R Y (Submodule.Quotient.mk f) =
      E.projectiveStableFunctor.map f := by
  simp [homQuotientEquivStableHom]

end Linear

end Extension

end ExactStructure

end TauCeti
