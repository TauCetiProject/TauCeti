/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Sites.Abelian
public import TauCeti.Algebra.Homology.ShortComplex.FunctorCategory
public import TauCeti.CategoryTheory.Preadditive.FreeYoneda
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Functor

/-!
# Čech complexes of injective sheaves

Let `C` be a category with finite products and let `U : ι → C` be a family of objects. For an
injective presheaf of abelian groups `P` on `C`, and in particular for the underlying presheaf of
an injective abelian sheaf on a site, the Čech complex `Č(U, P)` is exact in every positive degree
(`TauCeti.CategoryTheory.exactAt_cechComplexFunctor_obj_of_injective`). No hypothesis on `U` is
needed: `U` need not cover anything. This is the input that replaces the flasqueness of injective
sheaves on a topological space in Leray's acyclicity theorem for a site.

The proof is the classical one. Write `ℤ[X]` for the free abelian presheaf on the representable
presheaf of `X`. Since `P(X) = Hom(ℤ[X], P)` naturally in `X`, the Čech complex of `P` is obtained
by applying the exact functor `Hom(-, P)` to the complex of presheaves
`⋯ ⟶ ⨁ ℤ[U (a 0) × U (a 1)] ⟶ ⨁ ℤ[U (a 0)]`, which is the Čech complex of the presheaf
`X ↦ ℤ[X]` with values in the opposite category. This complex is exact in positive degrees,
since it is so at every object `W`: there it is the Čech complex of the presheaf `S ↦ ℤ[S]` on
types for the family of sets `Hom(W, U i)`, because `Hom(W, -)` preserves products
(`CategoryTheory.Functor.exactAt_cechComplexFunctor_obj_comp_iff`). That complex is exact in
positive degrees, by the extra degeneracy of a family with a member receiving a map from the point
when some `Hom(W, U i)` is nonempty, and because all its terms vanish otherwise.

## Main results

* `TauCeti.CategoryTheory.exactAt_cechComplexFunctor_obj_free_op`: the Čech complex of the free
  abelian group functor, as a presheaf on types with values in the opposite category, is exact
  in positive degrees for every family of types.
* `TauCeti.CategoryTheory.exactAt_cechComplexFunctor_obj_freeYoneda_op`: the Čech complex of the
  free abelian presheaves on representables is exact in positive degrees.
* `TauCeti.CategoryTheory.exactAt_cechComplexFunctor_obj_of_injective`: the Čech complex of an
  injective presheaf of abelian groups is exact in positive degrees.
* `TauCeti.CategoryTheory.exactAt_cechComplexFunctor_obj_obj_of_injective`: the same for an
  injective abelian sheaf on a site.

## References

The formalization is adapted from split 5 of the
[lookahead development](https://github.com/roed-math/TauCeti-w2-fresh/tree/lookahead/SchemeAndStackFoundations/leray-spectral-sequence).

* [Stacks: Tag 03AU](https://stacks.math.columbia.edu/tag/03AU), proof of Lemma 21.9.6,
  for the free complex of a family and vanishing for injective presheaves.
* [Stacks: Tag 03AV](https://stacks.math.columbia.edu/tag/03AV), Lemmas 21.10.1–21.10.2,
  for passage from injective sheaves to injective presheaves.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace TauCeti.CategoryTheory

section Types

variable {ι : Type v} (S : ι → Type v)

/-- For a family of types `S`, the Čech complex of the presheaf `X ↦ ℤ[X]` on types, with values
in the opposite category of abelian groups, is exact in positive degrees. If some `S i` is
nonempty, the point maps to it and the augmented Čech complex is exact; otherwise every product
`S (a 0) × ⋯ × S (a n)` is empty and every term vanishes. -/
theorem exactAt_cechComplexFunctor_obj_free_op (n : ℕ) :
    ((cechComplexFunctor S).obj AddCommGrpCat.free.{v}.op).ExactAt (n + 1) := by
  by_cases h : ∃ i, Nonempty (S i)
  · obtain ⟨i, ⟨s⟩⟩ := h
    exact ((quasiIso_cechAugmentation_iff S Types.isTerminalPUnit _).1
      (quasiIso_cechAugmentation_of_hom S Types.isTerminalPUnit _ (i₀ := i)
        (TypeCat.ofHom fun _ ↦ s))).2 n
  · push Not at h
    refine ShortComplex.exact_of_isZero_X₂ _ ?_
    -- The middle Čech term is the product over all tuples of members.
    change IsZero (∏ᶜ fun a : Fin (n + 2) → ι ↦
      AddCommGrpCat.free.{v}.op.obj (op (∏ᶜ fun j ↦ S (a j))))
    refine (IsZero.iff_id_eq_zero _).2 (Pi.hom_ext _ _ fun a ↦ IsZero.eq_of_tgt ?_ _ _)
    have : IsEmpty (∏ᶜ fun j ↦ S (a j)) :=
      ⟨fun x ↦ (h (a 0)).false ((Pi.π (fun j ↦ S (a j)) 0).hom x)⟩
    have : Subsingleton (AddCommGrpCat.free.obj (∏ᶜ fun j ↦ S (a j))) :=
      inferInstanceAs (Subsingleton (FreeAbelianGroup (∏ᶜ fun j ↦ S (a j))))
    exact (AddCommGrpCat.isZero_of_subsingleton _).op

end Types

section Presheaf

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type v} (U : ι → C)

/-- The Čech complex of the presheaf `X ↦ ℤ[X]` of free abelian presheaves on representables, with
values in the opposite category of presheaves of abelian groups, is exact in positive degrees.
Evaluated at an object `W`, it is the Čech complex of `S ↦ ℤ[S]` on types for the family of sets
`Hom(W, U i)`. -/
theorem exactAt_cechComplexFunctor_obj_freeYoneda_op (n : ℕ) :
    ((cechComplexFunctor U).obj
      (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free.{v}).op).ExactAt
        (n + 1) := by
  rw [HomologicalComplex.exactAt_iff, ← ShortComplex.exact_unop_iff,
    ShortComplex.exact_iff_evaluation]
  intro W
  -- Evaluation commutes with taking the unop of a short complex.
  change (((((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj W).op.mapHomologicalComplex
    _).obj ((cechComplexFunctor U).obj
      (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free.{v}).op)).sc
        (n + 1)).unop.Exact
  rw [ShortComplex.exact_unop_iff]
  have (n : ℕ) : PreservesLimitsOfShape (Discrete (Fin (n + 1) → ι))
      ((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj W).op :=
    preservesLimitsOfShape_op _ _
  have e := (cechComplexFunctorMapIso U ((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj W).op).app
    (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free.{v}).op
  refine (exactAt_iff_of_quasiIsoAt e.hom _).2 ?_
  -- Evaluation of a representable is the hom functor `Hom(W.unop, -)`.
  change ((cechComplexFunctor U).obj ((coyoneda.obj W).op ⋙
    AddCommGrpCat.free.{v}.op)).ExactAt (n + 1)
  rw [Functor.exactAt_cechComplexFunctor_obj_comp_iff _ _ _
    (fun _ _ ↦ inferInstance)]
  exact exactAt_cechComplexFunctor_obj_free_op _ n

/-- **The Čech complex of an injective presheaf is exact in positive degrees**, for every family
`U`. It is obtained by applying the exact functor `Hom(-, P)` to the Čech complex of the free
abelian presheaves on representables. -/
theorem exactAt_cechComplexFunctor_obj_of_injective (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [Injective P]
    (n : ℕ) : ((cechComplexFunctor U).obj P).ExactAt (n + 1) := by
  have := (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj P).1 inferInstance
  have := Functor.preservesHomology_of_preservesEpis_and_kernels (preadditiveYoneda.obj P)
  have : PreservesLimitsOfSize.{v, v} (preadditiveYoneda.obj P) := preservesLimitsOfSize_shrink _
  have h₀ : (((preadditiveYoneda.obj P).mapHomologicalComplex _).obj ((cechComplexFunctor U).obj
      (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free.{v}).op)).ExactAt (n + 1) :=
    (exactAt_cechComplexFunctor_obj_freeYoneda_op U n).map (preadditiveYoneda.obj P)
  have h₁ := (exactAt_iff_of_quasiIsoAt ((cechComplexFunctorMapIso U
    (preadditiveYoneda.obj P)).app (yoneda ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free.{v}).op).hom (n + 1)).1 h₀
  have h₂ := (exactAt_iff_of_quasiIsoAt ((cechComplexFunctor U).mapIso
    P.freeYonedaHomIso).hom (n + 1)).1 h₁
  have h₃ := (exactAt_iff_of_quasiIsoAt ((cechComplexFunctorMapIso U
    AddCommGrpCat.uliftFunctor.{u}).app P).hom (n + 1)).2 h₂
  exact (ShortComplex.exact_map_iff_of_faithful _ AddCommGrpCat.uliftFunctor.{u}).1 h₃

/-- The Čech complex of an injective abelian sheaf for any family is exact in positive degrees:
its underlying presheaf is injective, since sheafification preserves monomorphisms. -/
theorem exactAt_cechComplexFunctor_obj_obj_of_injective {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}] (I : Sheaf J AddCommGrpCat.{v}) [Injective I] (n : ℕ) :
    ((cechComplexFunctor U).obj I.obj).ExactAt (n + 1) := by
  have : Injective I.obj := (sheafificationAdjunction J _).map_injective I inferInstance
  exact exactAt_cechComplexFunctor_obj_of_injective U I.obj n

end Presheaf

end TauCeti.CategoryTheory
