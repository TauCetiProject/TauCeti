/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.YonedaExt.LocalDuality
public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Biproduct

/-!
# Dualizing forms on `Ext¹`

Let `E` be an exact structure on an `R`-linear category and `D = Hom_R(-, Q)` a duality as in
`TauCeti/CategoryTheory/Exact/YonedaExt/LocalDuality.lean`. A linear form
`φ : Ext¹_E(Z, T) → Q` is *dualizing* when both pairings it induces are bijective:

* `(E/ℐ)(X, T) ≅ D Ext¹_E(Z, X)` for every `X`, so that `T` represents `D Ext¹_E(Z, -)` on `E/ℐ`;
* `(E/𝒫)(Z, B) ≅ D Ext¹_E(B, T)` for every `B`, so that `Z` represents `D Ext¹_E(-, T)` on `E/𝒫`.

These are the pointwise data from which the Auslander–Reiten translate is assembled into a fully
faithful functor `E/𝒫 ⥤ E/ℐ`, following the proof of [INP, Prop. 3.7].

This file shows that, when every `Ext¹` has finite length, dualizing forms exist at every object of
a Krull–Schmidt category in which every indecomposable non-projective object ends an almost-split
conflation. The local theorem gives them at such objects; the zero form from a projective to an
injective object is dualizing; and dualizing forms are transported along isomorphisms and
assembled over finite biproducts, by the sum of the forms of the summands. The last step needs no
finiteness: a morphism or class into or out of a biproduct is determined by its components.

## Main definitions

* `TauCeti.ExactStructure.IsDualizingForm φ`: both pairings induced by `φ` are bijective.

## Main results

* `TauCeti.ExactStructure.isDualizingForm_of_isAlmostSplit`: a linear form not vanishing on an
  almost-split class is dualizing.
* `TauCeti.ExactStructure.isDualizingForm_zero`,
  `TauCeti.ExactStructure.IsDualizingForm.comp_pullback`,
  `TauCeti.ExactStructure.IsDualizingForm.comp_pushout` and
  `TauCeti.ExactStructure.IsDualizingForm.biproduct`: the closure properties.
* `TauCeti.ExactStructure.exists_isDualizingForm`: in a Krull–Schmidt category with almost-split
  conflations ending at every indecomposable non-projective object, every object carries a
  dualizing form.

## References

* O. Iyama, H. Nakaoka, Y. Palu, *Auslander–Reiten theory in extriangulated categories*,
  arXiv:1805.03776 (v3), Proposition 3.7 and Lemma 3.10, over a field.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C} {R : Type*} [CommRing R] [Linear R C] {Q : Type w}
  [AddCommGroup Q] [Module R Q]

/-- A linear form `φ : Ext¹_E(Z, T) → Q` is **dualizing** when both pairings it induces are
bijective: `(E/ℐ)(X, T) ≅ D Ext¹_E(Z, X)` for every `X`, and `(E/𝒫)(Z, B) ≅ D Ext¹_E(B, T)` for
every `B`. -/
structure IsDualizingForm {Z T : C} (φ : E.Ext1 Z T →ₗ[R] Q) : Prop where
  /-- `T` represents `D Ext¹_E(Z, -)` on `E/ℐ`, with universal element `φ`. -/
  bijective_costablePairing (X : C) : Function.Bijective (costablePairing φ X)
  /-- `Z` represents `D Ext¹_E(-, T)` on `E/𝒫`, with universal element `φ`. -/
  bijective_stablePairing (B : C) : Function.Bijective (stablePairing φ B)

/-- **The zero form between a projective and an injective object** is dualizing. -/
theorem isDualizingForm_zero {Z T : C} (hZ : E.isProjective Z) (hT : E.isInjective T) :
    IsDualizingForm (0 : E.Ext1 Z T →ₗ[R] Q) := by
  refine ⟨fun X ↦ ?_, fun B ↦ ?_⟩
  · have := subsingleton_of_forall_eq 0 ((isProjective_iff_forall_ext1_eq_zero Z).mp hZ X)
    have : Subsingleton (E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
        E.injectivelyTrivialIdeal.quotientFunctor.obj T) :=
      ⟨((MorphismIdeal.isZero_quotientFunctor_obj_iff _ T).mpr
        ((id_mem_injectivelyTrivialIdeal_iff T).mpr hT)).eq_of_tgt⟩
    exact Function.bijective_of_subsingleton' _
  · have := subsingleton_of_forall_eq 0 ((isInjective_iff_forall_ext1_eq_zero T).mp hT B)
    have : Subsingleton (E.projectivelyTrivialIdeal.quotientFunctor.obj Z ⟶
        E.projectivelyTrivialIdeal.quotientFunctor.obj B) :=
      ⟨((MorphismIdeal.isZero_quotientFunctor_obj_iff _ Z).mpr
        ((id_mem_projectivelyTrivialIdeal_iff Z).mpr hZ)).eq_of_src⟩
    exact Function.bijective_of_subsingleton' _

/-- **Transport along an isomorphism.** If `φ : Ext¹_E(Z, T) → Q` is dualizing and `e : Z ≅ Z'`,
then `ξ ↦ φ(e^* ξ)` on `Ext¹_E(Z', T)` is dualizing. -/
theorem IsDualizingForm.comp_pullback {Z Z' T : C} {φ : E.Ext1 Z T →ₗ[R] Q}
    (hφ : IsDualizingForm φ) (e : Z ≅ Z') :
    IsDualizingForm (φ ∘ₗ Ext1.pullbackLinearMap R e.hom) := by
  refine ⟨fun X ↦ ?_, fun B ↦ ?_⟩
  · have : ⇑(costablePairing (φ ∘ₗ Ext1.pullbackLinearMap R e.hom) X) =
        ⇑(LinearEquiv.arrowCongr (Ext1.pullbackLinearEquiv R (X := X) e.symm)
          (LinearEquiv.refl R Q)) ∘ ⇑(costablePairing φ X) := by
      funext x
      obtain ⟨a, rfl⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective x
      ext ξ
      simp [Ext1.pushout_pullback]
    rw [this]
    exact (LinearEquiv.bijective _).comp (hφ.bijective_costablePairing X)
  · exact bijective_stablePairing_comp_pullback (hφ.bijective_stablePairing B) inferInstance

/-- **Transport along an isomorphism.** If `φ : Ext¹_E(Z, T) → Q` is dualizing and `e : T' ≅ T`,
then `ξ ↦ φ(e_* ξ)` on `Ext¹_E(Z, T')` is dualizing. -/
theorem IsDualizingForm.comp_pushout {Z T T' : C} {φ : E.Ext1 Z T →ₗ[R] Q}
    (hφ : IsDualizingForm φ) (e : T' ≅ T) :
    IsDualizingForm (φ ∘ₗ Ext1.pushoutLinearMap R e.hom) := by
  refine ⟨fun X ↦ bijective_costablePairing_comp_pushout (hφ.bijective_costablePairing X)
    inferInstance, fun B ↦ ?_⟩
  have : ⇑(stablePairing (φ ∘ₗ Ext1.pushoutLinearMap R e.hom) B) =
      ⇑(LinearEquiv.arrowCongr (Ext1.pushoutLinearEquiv R (Z := B) e.symm)
        (LinearEquiv.refl R Q)) ∘ ⇑(stablePairing φ B) := by
    funext x
    obtain ⟨c, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective x
    ext η
    simp [Ext1.pushout_pullback]
  rw [this]
  exact (LinearEquiv.bijective _).comp (hφ.bijective_stablePairing B)

/-! ### Assembly over a finite biproduct -/

section Biproduct

variable {J : Type*} [Fintype J] {Z T : J → C} [HasBiproduct Z] [HasBiproduct T]
  (φ : ∀ j, E.Ext1 (Z j) (T j) →ₗ[R] Q)

/-- The sum of the forms `φ j`, evaluated on a class pulled back from the summand `Z j`. -/
private theorem sum_apply_pushout_pullback_π (j : J) {X : C} (ζ : E.Ext1 (Z j) X)
    (a : X ⟶ ⨁ T) :
    (∑ k, φ k ∘ₗ Ext1.pushoutLinearMap R (biproduct.π T k) ∘ₗ
      Ext1.pullbackLinearMap R (biproduct.ι Z k)) ((ζ.pullback (biproduct.π Z j)).pushout a) =
      φ j (ζ.pushout (a ≫ biproduct.π T j)) := by
  classical
  rw [LinearMap.sum_apply, Finset.sum_eq_single j]
  · simp [Ext1.pushout_pullback]
  · intro k _ hk
    simp [Ext1.pushout_pullback, biproduct.ι_π_ne _ hk]
  · simp

/-- The sum of the forms `φ j`, evaluated on a class pushed out to the summand `T j`. -/
private theorem sum_apply_pullback_pushout_ι (j : J) {B : C} (η : E.Ext1 B (T j))
    (c : ⨁ Z ⟶ B) :
    (∑ k, φ k ∘ₗ Ext1.pushoutLinearMap R (biproduct.π T k) ∘ₗ
      Ext1.pullbackLinearMap R (biproduct.ι Z k)) ((η.pushout (biproduct.ι T j)).pullback c) =
      φ j (η.pullback (biproduct.ι Z j ≫ c)) := by
  classical
  rw [LinearMap.sum_apply, Finset.sum_eq_single j]
  · simp [← Ext1.pushout_pullback]
  · intro k _ hk
    simp [← Ext1.pushout_pullback, biproduct.ι_π_ne _ hk.symm]
  · simp

/-- **The costable pairing of a sum over a finite biproduct.** If `costablePairing (φ j) X` is
bijective for every `j`, so is the costable pairing at `X` of the form
`ξ ↦ ∑ j, φ j (π_j (ξ ι_j))` on `Ext¹_E(⨁ Z, ⨁ T)`. -/
theorem bijective_costablePairing_biproduct {X : C}
    (hφ : ∀ j, Function.Bijective (costablePairing (φ j) X)) :
    Function.Bijective (costablePairing (∑ j, φ j ∘ₗ Ext1.pushoutLinearMap R (biproduct.π T j) ∘ₗ
      Ext1.pullbackLinearMap R (biproduct.ι Z j)) X) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun f ↦ ?_⟩
  · -- Each component `a ≫ π_j` of a representative `a` pairs to zero, so lies in `ℐ`.
    obtain ⟨a, rfl⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective x
    rw [MorphismIdeal.quotientFunctor_map_eq_zero_iff, MorphismIdeal.mem_biproduct_right_iff]
    refine fun j ↦ (MorphismIdeal.quotientFunctor_map_eq_zero_iff _).mp <|
      (injective_iff_map_eq_zero _).mp (hφ j).1 _ (LinearMap.ext fun ζ ↦ ?_)
    rw [costablePairing_map, ← sum_apply_pushout_pullback_π, ← costablePairing_map, hx,
      LinearMap.zero_apply, LinearMap.zero_apply]
  · -- Assemble the morphism from the preimages of the restrictions of `f` to the summands.
    have hb : ∀ j, ∃ b : X ⟶ T j, costablePairing (φ j) X
        (E.injectivelyTrivialIdeal.quotientFunctor.map b) =
          f ∘ₗ Ext1.pullbackLinearMap R (biproduct.π Z j) := fun j ↦ by
      obtain ⟨x, hx⟩ := (hφ j).2 (f ∘ₗ Ext1.pullbackLinearMap R (biproduct.π Z j))
      obtain ⟨b, rfl⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective x
      exact ⟨b, hx⟩
    choose b hb using hb
    refine ⟨E.injectivelyTrivialIdeal.quotientFunctor.map (biproduct.lift b),
      LinearMap.ext fun ξ ↦ ?_⟩
    rw [costablePairing_map, ← ξ.pullback_id, ← biproduct.total, Ext1.pullback_sum,
      Ext1.sum_pushout, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Ext1.pullback_pullback, sum_apply_pushout_pullback_π, biproduct.lift_π,
      ← costablePairing_map, hb, LinearMap.comp_apply, Ext1.pullbackLinearMap_apply]

/-- **The stable pairing of a sum over a finite biproduct.** If `stablePairing (φ j) B` is
bijective for every `j`, so is the stable pairing at `B` of the form
`ξ ↦ ∑ j, φ j (π_j (ξ ι_j))` on `Ext¹_E(⨁ Z, ⨁ T)`. -/
theorem bijective_stablePairing_biproduct {B : C}
    (hφ : ∀ j, Function.Bijective (stablePairing (φ j) B)) :
    Function.Bijective (stablePairing (∑ j, φ j ∘ₗ Ext1.pushoutLinearMap R (biproduct.π T j) ∘ₗ
      Ext1.pullbackLinearMap R (biproduct.ι Z j)) B) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun f ↦ ?_⟩
  · -- Each restriction `ι_j ≫ c` of a representative `c` pairs to zero, so lies in `𝒫`.
    obtain ⟨c, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective x
    rw [MorphismIdeal.quotientFunctor_map_eq_zero_iff, MorphismIdeal.mem_biproduct_left_iff]
    refine fun j ↦ (MorphismIdeal.quotientFunctor_map_eq_zero_iff _).mp <|
      (injective_iff_map_eq_zero _).mp (hφ j).1 _ (LinearMap.ext fun η ↦ ?_)
    rw [stablePairing_map, ← sum_apply_pullback_pushout_ι, ← stablePairing_map, hx,
      LinearMap.zero_apply, LinearMap.zero_apply]
  · -- Assemble the morphism from the preimages of the restrictions of `f` to the summands.
    have hc : ∀ j, ∃ c : Z j ⟶ B, stablePairing (φ j) B
        (E.projectivelyTrivialIdeal.quotientFunctor.map c) =
          f ∘ₗ Ext1.pushoutLinearMap R (biproduct.ι T j) := fun j ↦ by
      obtain ⟨x, hx⟩ := (hφ j).2 (f ∘ₗ Ext1.pushoutLinearMap R (biproduct.ι T j))
      obtain ⟨c, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective x
      exact ⟨c, hx⟩
    choose c hc using hc
    refine ⟨E.projectivelyTrivialIdeal.quotientFunctor.map (biproduct.desc c),
      LinearMap.ext fun η ↦ ?_⟩
    rw [stablePairing_map, ← η.pushout_id, ← biproduct.total, Ext1.pushout_sum,
      Ext1.sum_pullback, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Ext1.pushout_pushout, sum_apply_pullback_pushout_ι, biproduct.ι_desc,
      ← stablePairing_map, hc, LinearMap.comp_apply, Ext1.pushoutLinearMap_apply]

variable {φ} in
/-- **Assembly over a finite biproduct.** If `φ j : Ext¹_E(Z j, T j) → Q` is dualizing for every
`j`, then `ξ ↦ ∑ j, φ j (π_j (ξ ι_j))` on `Ext¹_E(⨁ Z, ⨁ T)` is dualizing. -/
theorem IsDualizingForm.biproduct (hφ : ∀ j, IsDualizingForm (φ j)) :
    IsDualizingForm (∑ j, φ j ∘ₗ Ext1.pushoutLinearMap R (biproduct.π T j) ∘ₗ
      Ext1.pullbackLinearMap R (biproduct.ι Z j)) :=
  ⟨fun X ↦ bijective_costablePairing_biproduct φ fun j ↦ (hφ j).bijective_costablePairing X,
    fun B ↦ bijective_stablePairing_biproduct φ fun j ↦ (hφ j).bijective_stablePairing B⟩

end Biproduct

section Duality

variable [Module.Injective R Q] [Small.{w} R]
  (hQ : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] Q) = 1)
include hQ

/-- **A form not vanishing on an almost-split class is dualizing**, when every `Ext¹` into the
left-hand end and out of the right-hand end has finite length. -/
theorem isDualizingForm_of_isAlmostSplit {Z T : C} (e : E.Extension Z T)
    (he : e.shortComplex.IsAlmostSplit) {φ : E.Ext1 Z T →ₗ[R] Q} (hφ : φ (Ext1.mk e) ≠ 0)
    (hB : ∀ B, IsFiniteLength R (E.Ext1 B T)) (hX : ∀ X, IsFiniteLength R (E.Ext1 Z X)) :
    IsDualizingForm φ :=
  ⟨fun X ↦ (bijective_costablePairing_of_isAlmostSplit hQ e he hφ (hX X)).1,
    fun B ↦ (bijective_stablePairing_of_isAlmostSplit hQ e he hφ (hB B)).1⟩

/-- **Dualizing forms exist everywhere** in a Krull–Schmidt exact category in which every `Ext¹`
has finite length and every indecomposable non-projective object ends an almost-split
conflation. -/
theorem exists_isDualizingForm [HasFiniteBiproducts C] [IsKrullSchmidt C]
    (hfin : ∀ Z X : C, IsFiniteLength R (E.Ext1 Z X))
    (hAR : ∀ Z : C, Indecomposable Z → ¬ E.isProjective Z →
      ∃ (T : C) (e : E.Extension Z T), e.shortComplex.IsAlmostSplit) (Z : C) :
    ∃ (T : C) (φ : E.Ext1 Z T →ₗ[R] Q), IsDualizingForm φ := by
  -- Decompose `Z` into objects with local endomorphism rings, and sum their forms: the zero form
  -- at a projective summand, and a form of its almost-split conflation at any other summand.
  have hind : ∀ P : C, IsLocalRing (End P) →
      ∃ (T : C) (φ : E.Ext1 P T →ₗ[R] Q), IsDualizingForm φ := fun P hP ↦ by
    by_cases hproj : E.isProjective P
    · exact ⟨0, 0, isDualizingForm_zero hproj (E.isInjective.prop_of_isZero (isZero_zero C))⟩
    · obtain ⟨T, e, he⟩ := hAR P ((IsKrullSchmidt.indecomposable_iff_isLocalRing_end P).mpr hP)
        hproj
      obtain ⟨φ, hφ⟩ :=
        exists_apply_mk_ne_zero_of_isAlmostSplit (nontrivial_linearMap_of_isMaximal hQ) e he
      exact ⟨T, φ, isDualizingForm_of_isAlmostSplit hQ e he hφ (fun B ↦ hfin B T)
        (fun X ↦ hfin P X)⟩
  obtain ⟨n, P, hP, ⟨i⟩⟩ := IsKrullSchmidt.exists_iso_biproduct Z
  choose T φ hφ using fun k ↦ hind (P k) (hP k)
  exact ⟨⨁ T, _, (IsDualizingForm.biproduct hφ).comp_pullback i.symm⟩

end Duality

end ExactStructure

end TauCeti
