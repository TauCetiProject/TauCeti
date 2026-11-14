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
conflation. The local theorem gives them at such objects; at a projective object the zero form on
`Ext¹_E(Z, 0)` is dualizing; and dualizing forms are transported along isomorphisms and assembled
over finite biproducts, by the sum of the forms of the summands.

## Main definitions

* `TauCeti.ExactStructure.IsDualizingForm φ`: both pairings induced by `φ` are bijective.

## Main results

* `TauCeti.ExactStructure.isDualizingForm_of_isAlmostSplit`: a linear form not vanishing on an
  almost-split class is dualizing.
* `TauCeti.ExactStructure.isDualizingForm_zero_of_isProjective`,
  `TauCeti.ExactStructure.IsDualizingForm.ofIso` and
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

/-- A function between subsingletons is bijective once its codomain is inhabited by its image. -/
private theorem bijective_of_subsingleton {α β : Type*} [Subsingleton α] [Subsingleton β]
    (f : α → β) (a : α) : Function.Bijective f :=
  ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨a, Subsingleton.elim _ _⟩⟩

/-- **The zero form at a projective object.** If `Z` is projective, the zero form on
`Ext¹_E(Z, 0)` is dualizing: every module in sight vanishes. -/
theorem isDualizingForm_zero_of_isProjective {Z : C} (hZ : E.isProjective Z) :
    IsDualizingForm (0 : E.Ext1 Z 0 →ₗ[R] Q) := by
  have hExt : ∀ X, Subsingleton (E.Ext1 Z X) := fun X ↦
    ⟨fun a b ↦ by rw [(isProjective_iff_forall_ext1_eq_zero Z).mp hZ X a,
      (isProjective_iff_forall_ext1_eq_zero Z).mp hZ X b]⟩
  have hExt0 : ∀ B, Subsingleton (E.Ext1 B (0 : C)) := fun B ↦ ⟨fun a b ↦ by
    have h0 : 𝟙 (0 : C) = 0 := (isZero_zero C).eq_of_src _ _
    rw [← a.pushout_id, ← b.pushout_id, h0, Ext1.pushout_zero, Ext1.pushout_zero]⟩
  have hDual : ∀ {M : Type _} [AddCommGroup M] [Module R M] [Subsingleton M],
      Subsingleton (M →ₗ[R] Q) := fun {_ _ _ _} ↦
    ⟨fun f g ↦ LinearMap.ext fun m ↦ by rw [Subsingleton.elim m 0, map_zero, map_zero]⟩
  refine ⟨fun X ↦ ?_, fun B ↦ ?_⟩
  · have := hExt X
    have : Subsingleton (E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
        E.injectivelyTrivialIdeal.quotientFunctor.obj 0) :=
      ⟨fun a b ↦ (E.injectivelyTrivialIdeal.quotientFunctor.map_isZero (isZero_zero C)).eq_of_tgt
        a b⟩
    have := hDual (M := E.Ext1 Z X)
    exact bijective_of_subsingleton _ 0
  · have := hExt0 B
    have : Subsingleton (E.projectivelyTrivialIdeal.quotientFunctor.obj Z ⟶
        E.projectivelyTrivialIdeal.quotientFunctor.obj B) :=
      ⟨fun a b ↦ ((MorphismIdeal.isZero_quotientFunctor_obj_iff _ Z).mpr
        ((id_mem_projectivelyTrivialIdeal_iff Z).mpr hZ)).eq_of_src a b⟩
    have := hDual (M := E.Ext1 B (0 : C))
    exact bijective_of_subsingleton _ 0

/-- **Transport along an isomorphism.** If `φ : Ext¹_E(Z, T) → Q` is dualizing and `e : Z ≅ Z'`,
then `ξ ↦ φ(e^* ξ)` on `Ext¹_E(Z', T)` is dualizing. -/
theorem IsDualizingForm.ofIso {Z Z' T : C} {φ : E.Ext1 Z T →ₗ[R] Q} (hφ : IsDualizingForm φ)
    (e : Z ≅ Z') : IsDualizingForm (φ ∘ₗ Ext1.pullbackLinearMap R e.hom) := by
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
  · have : ⇑(stablePairing (φ ∘ₗ Ext1.pullbackLinearMap R e.hom) B) =
        ⇑(stablePairing φ B) ∘
          ⇑((E.projectivelyTrivialIdeal.quotientFunctor.mapIso e).symm.homCongr (Iso.refl _)) := by
      funext x
      obtain ⟨c, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective x
      ext η
      simp [Iso.homCongr_apply, ← Functor.map_comp]
    rw [this]
    exact (hφ.bijective_stablePairing B).comp (Equiv.bijective _)

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

/-- **Assembly over a finite biproduct.** If `φ j : Ext¹_E(Z j, T j) → Q` is dualizing for every
`j`, then `ξ ↦ ∑ j, φ j (π_j (ξ ι_j))` on `Ext¹_E(⨁ Z, ⨁ T)` is dualizing, when every `Ext¹` has
finite length. Each of the four pairings is non-degenerate because a nonzero morphism or class
into or out of a biproduct is nonzero on some summand. -/
theorem IsDualizingForm.biproduct [HasFiniteBiproducts C]
    (hfin : ∀ Z X : C, IsFiniteLength R (E.Ext1 Z X)) {J : Type} [Fintype J]
    {Z T : J → C} {φ : ∀ j, E.Ext1 (Z j) (T j) →ₗ[R] Q} (hφ : ∀ j, IsDualizingForm (φ j)) :
    IsDualizingForm (∑ j, φ j ∘ₗ Ext1.pushoutLinearMap R (biproduct.π T j) ∘ₗ
      Ext1.pullbackLinearMap R (biproduct.ι Z j)) := by
  classical
  set Φ := ∑ j, φ j ∘ₗ Ext1.pushoutLinearMap R (biproduct.π T j) ∘ₗ
    Ext1.pullbackLinearMap R (biproduct.ι Z j)
  have hΦ : ∀ ξ, Φ ξ = ∑ j, φ j ((ξ.pullback (biproduct.ι Z j)).pushout (biproduct.π T j)) :=
    fun ξ ↦ by simp [Φ]
  -- The flipped pairings of the summands are injective.
  have hcf : ∀ j X, Function.Injective (costablePairing (φ j) X).flip := fun j X ↦
    injective_flip_of_surjective
      (nontrivial_linearMap_of_isMaximal hQ) ((hφ j).bijective_costablePairing X).2
  have hsf : ∀ j B, Function.Injective (stablePairing (φ j) B).flip := fun j B ↦
    injective_flip_of_surjective
      (nontrivial_linearMap_of_isMaximal hQ) ((hφ j).bijective_stablePairing B).2
  refine ⟨fun X ↦ ?_, fun B ↦ ?_⟩
  · refine (bijective_of_injective_of_injective_flip hQ ?_ ?_ (hfin _ X)).2.1
    · -- A morphism `a : X ⟶ ⨁ T` outside `ℐ` has a component `a ≫ π_j` outside `ℐ`.
      refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
      obtain ⟨a, rfl⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective x
      rw [MorphismIdeal.quotientFunctor_map_eq_zero_iff,
        MorphismIdeal.mem_biproduct_right_iff]
      intro j
      by_contra haj
      rw [← MorphismIdeal.quotientFunctor_map_eq_zero_iff] at haj
      obtain ⟨ξ, hξ⟩ : ∃ ξ, costablePairing (φ j) X _ ξ ≠ 0 := by
        by_contra! h
        exact haj (((hφ j).bijective_costablePairing X).1 (LinearMap.ext h |>.trans
          (map_zero _).symm))
      refine hξ ?_
      have := congrArg (fun f ↦ f (ξ.pullback (biproduct.π Z j))) hx
      simp only [costablePairing_map, hΦ, LinearMap.zero_apply] at this ⊢
      rw [← this, Finset.sum_eq_single j]
      · simp [Ext1.pushout_pullback]
      · intro k _ hk
        simp [Ext1.pushout_pullback, biproduct.ι_π_ne _ hk]
      · simp
    · -- A nonzero class on `⨁ Z` restricts to a nonzero class on some summand.
      refine (injective_iff_map_eq_zero _).mpr fun ξ hξ ↦ ?_
      have hj : ∀ j, ξ.pullback (biproduct.ι Z j) = 0 := fun j ↦ by
        refine hcf j X (LinearMap.ext fun x ↦ ?_)
        obtain ⟨a, rfl⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective x
        have := congrArg (fun f ↦ f (E.injectivelyTrivialIdeal.quotientFunctor.map
          (a ≫ biproduct.ι T j))) hξ
        simp only [LinearMap.flip_apply, costablePairing_map, hΦ, LinearMap.zero_apply,
          map_zero] at this ⊢
        rw [← this, Finset.sum_eq_single j]
        · rw [Ext1.pushout_pullback, Ext1.pushout_pushout, Category.assoc, biproduct.ι_π_self,
            Category.comp_id]
        · intro k _ hk
          rw [Ext1.pushout_pullback, Ext1.pushout_pushout, Category.assoc,
            biproduct.ι_π_ne _ hk.symm, Limits.comp_zero, Ext1.pushout_zero, map_zero]
        · simp
      rw [← ξ.pullback_id, ← biproduct.total, Ext1.pullback_sum]
      simp [← Ext1.pullback_pullback, hj]
  · refine (bijective_of_injective_of_injective_flip hQ ?_ ?_ (hfin B _)).2.1
    · -- A morphism `c : ⨁ Z ⟶ B` outside `𝒫` has a component `ι_j ≫ c` outside `𝒫`.
      refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
      obtain ⟨c, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective x
      rw [MorphismIdeal.quotientFunctor_map_eq_zero_iff,
        MorphismIdeal.mem_biproduct_left_iff]
      intro j
      by_contra hcj
      rw [← MorphismIdeal.quotientFunctor_map_eq_zero_iff] at hcj
      obtain ⟨η, hη⟩ : ∃ η, stablePairing (φ j) B _ η ≠ 0 := by
        by_contra! h
        exact hcj (((hφ j).bijective_stablePairing B).1 (LinearMap.ext h |>.trans
          (map_zero _).symm))
      refine hη ?_
      have := congrArg (fun f ↦ f (η.pushout (biproduct.ι T j))) hx
      simp only [stablePairing_map, hΦ, LinearMap.zero_apply] at this ⊢
      rw [← this, Finset.sum_eq_single j]
      · simp [← Ext1.pushout_pullback]
      · intro k _ hk
        simp [← Ext1.pushout_pullback, biproduct.ι_π_ne _ hk.symm]
      · simp
    · -- A nonzero class into `⨁ T` has a nonzero projection to some summand.
      refine (injective_iff_map_eq_zero _).mpr fun η hη ↦ ?_
      have hj : ∀ j, η.pushout (biproduct.π T j) = 0 := fun j ↦ by
        refine hsf j B (LinearMap.ext fun x ↦ ?_)
        obtain ⟨c, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective x
        have := congrArg (fun f ↦ f (E.projectivelyTrivialIdeal.quotientFunctor.map
          (biproduct.π Z j ≫ c))) hη
        simp only [LinearMap.flip_apply, stablePairing_map, hΦ, LinearMap.zero_apply,
          map_zero] at this ⊢
        rw [← this, Finset.sum_eq_single j]
        · rw [Ext1.pullback_pullback, ← Category.assoc, biproduct.ι_π_self, Category.id_comp,
            Ext1.pushout_pullback]
        · intro k _ hk
          rw [Ext1.pullback_pullback, ← Category.assoc, biproduct.ι_π_ne _ hk, Limits.zero_comp,
            Ext1.pullback_zero,
            Ext1.zero_pushout, map_zero]
        · simp
      rw [← η.pushout_id, ← biproduct.total, Ext1.pushout_sum]
      simp [← Ext1.pushout_pushout, hj]

/-- **Dualizing forms exist everywhere** in a Krull–Schmidt exact category with finite `Ext¹` in
which every indecomposable non-projective object ends an almost-split conflation. Decompose an
object into objects with local endomorphism rings: the projective ones carry the zero form, the
others the form of their almost-split conflation, and the forms are summed over the biproduct. -/
theorem exists_isDualizingForm [HasFiniteBiproducts C] [IsKrullSchmidt C]
    (hfin : ∀ Z X : C, IsFiniteLength R (E.Ext1 Z X))
    (hAR : ∀ Z : C, Indecomposable Z → ¬ E.isProjective Z →
      ∃ (T : C) (e : E.Extension Z T), e.shortComplex.IsAlmostSplit) (Z : C) :
    ∃ (T : C) (φ : E.Ext1 Z T →ₗ[R] Q), IsDualizingForm φ := by
  classical
  have hind : ∀ P : C, IsLocalRing (End P) →
      ∃ (T : C) (φ : E.Ext1 P T →ₗ[R] Q), IsDualizingForm φ := fun P hP ↦ by
    by_cases hproj : E.isProjective P
    · exact ⟨0, 0, isDualizingForm_zero_of_isProjective hproj⟩
    · obtain ⟨T, e, he⟩ := hAR P ((IsKrullSchmidt.indecomposable_iff_isLocalRing_end P).mpr hP)
        hproj
      obtain ⟨φ, hφ⟩ := exists_apply_ne_zero_of_forall_isMaximal
        (nontrivial_linearMap_of_isMaximal hQ)
        (fun h0 ↦ e.not_isAlmostSplit_of_mk_eq_zero h0 he)
      exact ⟨T, φ, isDualizingForm_of_isAlmostSplit hQ e he hφ (fun B ↦ hfin B T)
        (fun X ↦ hfin P X)⟩
  obtain ⟨n, P, hP, ⟨i⟩⟩ := IsKrullSchmidt.exists_iso_biproduct Z
  choose T φ hφ using fun k ↦ hind (P k) (hP k)
  exact ⟨⨁ T, _, (IsDualizingForm.biproduct hQ hfin hφ).ofIso i.symm⟩

end Duality

end ExactStructure

end TauCeti
