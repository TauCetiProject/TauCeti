/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.YonedaExt.DualizingForm

/-!
# Auslander–Reiten duality for exact categories

Let `E` be an exact structure on an `R`-linear category, `𝒫` and `ℐ` its ideals of projectively
and injectively trivial morphisms, and `D = Hom_R(-, Q)` a duality preserving length as in
`TauCeti/CategoryTheory/Exact/YonedaExt/LocalDuality.lean`. An **Auslander–Reiten duality** is an
equivalence `τ : E/𝒫 ≌ E/ℐ` together with isomorphisms
`Ext¹_E(Z, X) ≅ D ((E/ℐ)(X, τ Z))` natural in `X` and in `Z`.

This file constructs one when the category is Krull–Schmidt, every `Ext¹` has finite length, and
almost-split conflations end at every indecomposable non-projective object and start at every
indecomposable non-injective object. No enough projectives or injectives are assumed.

The construction follows [INP, Prop. 3.7 and Thm. 3.6]. A dualizing form
`φ_Z : Ext¹_E(Z, T_Z) → Q` at every object (`TauCeti.ExactStructure.exists_isDualizingForm`) makes
`T_Z` represent `D Ext¹_E(Z, -)` on `E/ℐ`, so by the Yoneda lemma `Z ↦ T_Z` is a functor: `τ u` for
`u : Z ⟶ Z'` is the unique morphism with `φ_{Z'}(τ(u)_* ζ) = φ_Z(u^* ζ)` ([INP, Lemma 3.10]). On
morphisms `τ` is the composite of the two bijective pairings
`(E/𝒫)(Z, Z') ≅ D Ext¹_E(Z', T_Z) ≅ (E/ℐ)(T_Z, T_{Z'})`, hence fully faithful. It is essentially
surjective because the left-hand end `X` of an almost-split conflation ending at `Z` also
represents `D Ext¹_E(Z, -)`, so that `T_Z ≅ X` in `E/ℐ`.

## Main definitions

* `TauCeti.ExactStructure.AuslanderReitenDuality E R Q`: an Auslander–Reiten duality.
* `TauCeti.ExactStructure.DualizingForms E R Q`: a choice of dualizing form at every object, and
  `TauCeti.ExactStructure.DualizingForms.functor`, the translate `E/𝒫 ⥤ E/ℐ` it determines.

## Main results

* `TauCeti.ExactStructure.DualizingForms.fullyFaithfulFunctor`: the translate is fully faithful.
* `TauCeti.ExactStructure.nonempty_auslanderReitenDuality`: **existence of almost-split
  conflations gives an Auslander–Reiten duality.**

## References

* O. Iyama, H. Nakaoka, Y. Palu, *Auslander–Reiten theory in extriangulated categories*,
  arXiv:1805.03776 (v3), Definition 3.4, Theorem 3.6, Proposition 3.7 and Lemma 3.10, over a field.
* H. Enomoto, *Classifications of exact structures and Cohen–Macaulay-finite algebras*, Adv. Math.
  **335** (2018), 838–877, arXiv:1705.02163, Theorem A.9, under enough projectives and injectives.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable (E : ExactStructure C) (R : Type*) [CommRing R] [Linear R C] (Q : Type w)
  [AddCommGroup Q] [Module R Q]

/-- **An Auslander–Reiten duality** of an exact category: an equivalence
`τ : E/𝒫 ⥤ E/ℐ` from the projectively stable to the injectively stable category, with
isomorphisms `Ext¹_E(Z, X) ≅ D ((E/ℐ)(X, τ Z))` natural in `X` and in `Z`. -/
structure AuslanderReitenDuality where
  /-- The translate `τ : E/𝒫 ⥤ E/ℐ`. -/
  functor : E.projectivelyTrivialIdeal.Quotient ⥤ E.injectivelyTrivialIdeal.Quotient
  /-- The translate is an equivalence. -/
  isEquivalence : functor.IsEquivalence
  /-- The duality `Ext¹_E(Z, X) ≅ D ((E/ℐ)(X, τ Z))`. -/
  iso (Z X : C) : E.Ext1 Z X ≃ₗ[R] ((E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
    functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) →ₗ[R] Q)
  /-- Naturality in `X`. -/
  iso_pushout {Z X X' : C} (v : X ⟶ X') (ξ : E.Ext1 Z X)
    (a : E.injectivelyTrivialIdeal.quotientFunctor.obj X' ⟶
      functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) :
    iso Z X' (ξ.pushout v) a = iso Z X ξ (E.injectivelyTrivialIdeal.quotientFunctor.map v ≫ a)
  /-- Naturality in `Z`. -/
  iso_pullback {Z Z' X : C} (u : Z' ⟶ Z) (ξ : E.Ext1 Z X)
    (a : E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
      functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z')) :
    iso Z' X (ξ.pullback u) a =
      iso Z X ξ (a ≫ functor.map (E.projectivelyTrivialIdeal.quotientFunctor.map u))

variable {E R Q} in
/-- **Representing objects are unique in `E/ℐ`.** If `T` and `T'` both represent
`D Ext¹_E(Z, -)` on `E/ℐ`, with universal elements `φ` and `φ'`, they are isomorphic in `E/ℐ`. -/
noncomputable def costableIsoOfBijective {Z T T' : C} {φ : E.Ext1 Z T →ₗ[R] Q}
    {φ' : E.Ext1 Z T' →ₗ[R] Q} (h : ∀ X, Function.Bijective (costablePairing φ X))
    (h' : ∀ X, Function.Bijective (costablePairing φ' X)) :
    E.injectivelyTrivialIdeal.quotientFunctor.obj T ≅
      E.injectivelyTrivialIdeal.quotientFunctor.obj T' := by
  -- The two comparison maps, characterized on representatives.
  have key : ∀ {T₁ T₂ : C} {φ₁ : E.Ext1 Z T₁ →ₗ[R] Q} {φ₂ : E.Ext1 Z T₂ →ₗ[R] Q},
      (∀ X, Function.Bijective (costablePairing φ₂ X)) →
      ∃ b : T₁ ⟶ T₂, ∀ ξ : E.Ext1 Z T₁, φ₂ (ξ.pushout b) = φ₁ ξ := fun {T₁ T₂ φ₁ φ₂} h₂ ↦ by
    obtain ⟨x, hx⟩ := (h₂ T₁).2 φ₁
    obtain ⟨b, rfl⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective x
    exact ⟨b, fun ξ ↦ by rw [← costablePairing_map, hx]⟩
  have inv_eq : ∀ {T₁ T₂ : C} {φ₁ : E.Ext1 Z T₁ →ₗ[R] Q} {φ₂ : E.Ext1 Z T₂ →ₗ[R] Q},
      (∀ X, Function.Bijective (costablePairing φ₁ X)) → ∀ {b : T₁ ⟶ T₂} {b' : T₂ ⟶ T₁},
      (∀ ξ : E.Ext1 Z T₁, φ₂ (ξ.pushout b) = φ₁ ξ) →
      (∀ ζ : E.Ext1 Z T₂, φ₁ (ζ.pushout b') = φ₂ ζ) →
      E.injectivelyTrivialIdeal.quotientFunctor.map (b ≫ b') = 𝟙 _ :=
    fun {T₁ T₂ φ₁ φ₂} h₁ b b' hb hb' ↦ by
      refine (h₁ T₁).1 ?_
      rw [← E.injectivelyTrivialIdeal.quotientFunctor.map_id]
      ext ξ
      rw [costablePairing_map, costablePairing_map, ← Ext1.pushout_pushout, hb', hb,
        Ext1.pushout_id]
  exact {
    hom := E.injectivelyTrivialIdeal.quotientFunctor.map (key h').choose
    inv := E.injectivelyTrivialIdeal.quotientFunctor.map (key h).choose
    hom_inv_id := by
      rw [← Functor.map_comp]
      exact inv_eq h (key h').choose_spec (key h).choose_spec
    inv_hom_id := by
      rw [← Functor.map_comp]
      exact inv_eq h' (key h).choose_spec (key h').choose_spec }

/-- A choice of a **dualizing form** `φ_Z : Ext¹_E(Z, T_Z) → Q` at every object `Z`. -/
structure DualizingForms where
  /-- The object `T_Z` representing `D Ext¹_E(Z, -)` on `E/ℐ`. -/
  obj : C → C
  /-- The dualizing form `φ_Z`. -/
  form (Z : C) : E.Ext1 Z (obj Z) →ₗ[R] Q
  /-- The form `φ_Z` is dualizing. -/
  isDualizingForm (Z : C) : IsDualizingForm (form Z)

namespace DualizingForms

variable {E R Q} (D : E.DualizingForms R Q)

/-- The isomorphism `(E/ℐ)(X, T_Z) ≅ D Ext¹_E(Z, X)` given by the form `φ_Z`. -/
noncomputable def costableEquiv (Z X : C) :
    (E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
        E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z)) ≃ₗ[R] (E.Ext1 Z X →ₗ[R] Q) :=
  LinearEquiv.ofBijective (costablePairing (D.form Z) X)
    ((D.isDualizingForm Z).bijective_costablePairing X)

/-- The translate on morphisms: `τ u : T_Z ⟶ T_{Z'}` is the morphism corresponding to the linear
form `ζ ↦ φ_Z(u^* ζ)` on `Ext¹_E(Z', T_Z)`. -/
noncomputable def translateMap {Z Z' : C} (u : Z ⟶ Z') :
    E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z) ⟶
      E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z') :=
  (D.costableEquiv Z' (D.obj Z)).symm
    (stablePairing (D.form Z) Z' (E.projectivelyTrivialIdeal.quotientFunctor.map u))

theorem costablePairing_translateMap {Z Z' : C} (u : Z ⟶ Z') :
    costablePairing (D.form Z') (D.obj Z) (D.translateMap u) =
      stablePairing (D.form Z) Z' (E.projectivelyTrivialIdeal.quotientFunctor.map u) :=
  (D.costableEquiv Z' (D.obj Z)).apply_symm_apply _

/-- **The defining property of the translate**: for a representative `b` of `τ u`,
`φ_{Z'}(b_* ζ) = φ_Z(u^* ζ)` for every `ζ ∈ Ext¹_E(Z', T_Z)`. -/
theorem form_pushout {Z Z' : C} (u : Z ⟶ Z') {b : D.obj Z ⟶ D.obj Z'}
    (hb : E.injectivelyTrivialIdeal.quotientFunctor.map b = D.translateMap u)
    (ζ : E.Ext1 Z' (D.obj Z)) : D.form Z' (ζ.pushout b) = D.form Z (ζ.pullback u) := by
  have := congrArg (fun f ↦ f ζ) (D.costablePairing_translateMap u)
  simpa [← hb] using this

/-- The translate as a functor `C ⥤ E/ℐ`. -/
@[expose] noncomputable def translate : C ⥤ E.injectivelyTrivialIdeal.Quotient where
  obj Z := E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z)
  map u := D.translateMap u
  map_id Z := by
    refine ((D.isDualizingForm Z).bijective_costablePairing (D.obj Z)).1 ?_
    rw [costablePairing_translateMap, ← E.injectivelyTrivialIdeal.quotientFunctor.map_id]
    ext ζ
    rw [stablePairing_map, costablePairing_map, Ext1.pullback_id, Ext1.pushout_id]
  map_comp {Z Z' Z''} u w := by
    obtain ⟨bu, hbu⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective (D.translateMap u)
    obtain ⟨bw, hbw⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective (D.translateMap w)
    refine ((D.isDualizingForm Z'').bijective_costablePairing (D.obj Z)).1 ?_
    rw [costablePairing_translateMap, ← hbu, ← hbw, ← Functor.map_comp]
    ext ζ
    rw [stablePairing_map, costablePairing_map, ← Ext1.pushout_pushout, D.form_pushout w hbw,
      Ext1.pushout_pullback, D.form_pushout u hbu, Ext1.pullback_pullback]

instance : D.translate.Additive where
  map_add {Z Z'} u u' := by
    change D.translateMap (u + u') = D.translateMap u + D.translateMap u'
    simp only [translateMap, Functor.map_add, map_add]

theorem translate_map {Z Z' : C} (u : Z ⟶ Z') : D.translate.map u = D.translateMap u := rfl

theorem projectivelyTrivialIdeal_le_kerIdeal_translate :
    E.projectivelyTrivialIdeal ≤ D.translate.kerIdeal := fun Z Z' u hu ↦ by
  rw [Functor.mem_kerIdeal_hom, translate_map, translateMap,
    (MorphismIdeal.quotientFunctor_map_eq_zero_iff _).mpr hu, map_zero, map_zero]
  rfl

/-- **The Auslander–Reiten translate** `τ : E/𝒫 ⥤ E/ℐ` determined by dualizing forms. -/
@[expose] noncomputable def functor :
    E.projectivelyTrivialIdeal.Quotient ⥤ E.injectivelyTrivialIdeal.Quotient :=
  E.projectivelyTrivialIdeal.lift D.translate D.projectivelyTrivialIdeal_le_kerIdeal_translate

theorem functor_map_quotientFunctor_map {Z Z' : C} (u : Z ⟶ Z') :
    D.functor.map (E.projectivelyTrivialIdeal.quotientFunctor.map u) = D.translateMap u :=
  rfl

/-- On morphisms, the translate is the composite of the two bijective pairings
`(E/𝒫)(Z, Z') ≅ D Ext¹_E(Z', T_Z) ≅ (E/ℐ)(T_Z, T_{Z'})`. -/
theorem functor_map_eq {Z Z' : C}
    (x : E.projectivelyTrivialIdeal.quotientFunctor.obj Z ⟶
      E.projectivelyTrivialIdeal.quotientFunctor.obj Z') :
    D.functor.map x = (D.costableEquiv Z' (D.obj Z)).symm (stablePairing (D.form Z) Z' x) := by
  obtain ⟨u, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective x
  rw [functor_map_quotientFunctor_map, translateMap]

instance : D.functor.Faithful where
  map_injective {W W'} := by
    obtain ⟨Z⟩ := W
    obtain ⟨Z'⟩ := W'
    intro x y hxy
    rw [functor_map_eq, functor_map_eq] at hxy
    exact ((D.isDualizingForm Z).bijective_stablePairing Z').1
      ((D.costableEquiv Z' (D.obj Z)).symm.injective hxy)

instance : D.functor.Full where
  map_surjective {W W'} := by
    obtain ⟨Z⟩ := W
    obtain ⟨Z'⟩ := W'
    intro y
    obtain ⟨x, hx⟩ := ((D.isDualizingForm Z).bijective_stablePairing Z').2
      (D.costableEquiv Z' (D.obj Z) y)
    exact ⟨x, (D.functor_map_eq x).trans
      (by rw [hx]; exact (D.costableEquiv Z' (D.obj Z)).symm_apply_apply y)⟩

/-- **The translate is fully faithful**: on morphisms it is a composite of two bijections. -/
noncomputable def fullyFaithfulFunctor : D.functor.FullyFaithful :=
  .ofFullyFaithful _

section Duality

variable [Module.Injective R Q] [Small.{w} R]
  (hQ : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] Q) = 1)
  (hfin : ∀ Z X : C, IsFiniteLength R (E.Ext1 Z X))

/-- **The duality** `Ext¹_E(Z, X) ≅ D ((E/ℐ)(X, τ Z))`: the flip of the pairing of the form
`φ_Z`, bijective because `Ext¹_E(Z, X)` has finite length. -/
@[expose] noncomputable def iso (Z X : C) :
    E.Ext1 Z X ≃ₗ[R] ((E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
      D.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) →ₗ[R] Q) :=
  LinearEquiv.ofBijective (costablePairing (D.form Z) X).flip
    (bijective_of_injective_of_injective_flip hQ
      ((D.isDualizingForm Z).bijective_costablePairing X).1
      (injective_flip_of_surjective hQ ((D.isDualizingForm Z).bijective_costablePairing X).2)
      (hfin Z X)).2.2

theorem iso_apply (Z X : C) (ξ : E.Ext1 Z X)
    (a : E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
      E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z)) :
    D.iso hQ hfin Z X ξ a = costablePairing (D.form Z) X a ξ :=
  rfl

theorem iso_pushout {Z X X' : C} (v : X ⟶ X') (ξ : E.Ext1 Z X)
    (a : E.injectivelyTrivialIdeal.quotientFunctor.obj X' ⟶
      D.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) :
    D.iso hQ hfin Z X' (ξ.pushout v) a =
      D.iso hQ hfin Z X ξ (E.injectivelyTrivialIdeal.quotientFunctor.map v ≫ a) := by
  obtain ⟨a, rfl⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective (X := X')
    (Y := D.obj Z) a
  change costablePairing (D.form Z) X' (E.injectivelyTrivialIdeal.quotientFunctor.map a)
      (ξ.pushout v) = costablePairing (D.form Z) X
        (E.injectivelyTrivialIdeal.quotientFunctor.map v ≫
          E.injectivelyTrivialIdeal.quotientFunctor.map a) ξ
  rw [← Functor.map_comp, costablePairing_map, costablePairing_map, Ext1.pushout_pushout]

theorem iso_pullback {Z Z' X : C} (u : Z' ⟶ Z) (ξ : E.Ext1 Z X)
    (a : E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
      D.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z')) :
    D.iso hQ hfin Z' X (ξ.pullback u) a =
      D.iso hQ hfin Z X ξ
        (a ≫ D.functor.map (E.projectivelyTrivialIdeal.quotientFunctor.map u)) := by
  obtain ⟨a, rfl⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective (X := X)
    (Y := D.obj Z') a
  obtain ⟨b, hb⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective (D.translateMap u)
  change costablePairing (D.form Z') X (E.injectivelyTrivialIdeal.quotientFunctor.map a)
      (ξ.pullback u) = costablePairing (D.form Z) X
        (E.injectivelyTrivialIdeal.quotientFunctor.map a ≫ D.translateMap u) ξ
  rw [← hb, ← Functor.map_comp, costablePairing_map, costablePairing_map, ← Ext1.pushout_pushout,
    D.form_pushout u hb, Ext1.pushout_pullback]

omit [Module.Injective R Q] [Small.{w} R] in
/-- The translate of a zero object is zero. -/
theorem isZero_translate_obj_zero : IsZero (D.translate.obj 0) := by
  have h0 : ∀ ζ : E.Ext1 (0 : C) (D.obj 0), ζ = 0 := fun ζ ↦ by
    rw [← ζ.pullback_id, show 𝟙 (0 : C) = 0 from (isZero_zero C).eq_of_src _ _, Ext1.pullback_zero]
  refine (IsZero.iff_id_eq_zero _).mpr (((D.isDualizingForm 0).bijective_costablePairing _).1 ?_)
  ext ζ
  rw [h0 ζ, map_zero, map_zero]

include hQ hfin in
/-- **The translate is essentially surjective** when almost-split conflations start at every
indecomposable non-injective object: the left-hand end `X` of an almost-split conflation ending
at `Z` represents `D Ext¹_E(Z, -)` on `E/ℐ`, as does `T_Z`, so `τ Z ≅ X`. -/
theorem essSurj_functor [HasFiniteBiproducts C] [IsKrullSchmidt C]
    (hleft : ∀ X : C, Indecomposable X → ¬ E.isInjective X →
      ∃ (Z : C) (e : E.Extension Z X), e.shortComplex.IsAlmostSplit) :
    D.functor.EssSurj := by
  refine ⟨fun Y ↦ ?_⟩
  obtain ⟨X⟩ := Y
  obtain ⟨n, P, hP, ⟨i⟩⟩ := IsKrullSchmidt.exists_iso_biproduct X
  have hk : ∀ k, ∃ Z : C,
      Nonempty (D.translate.obj Z ≅ E.injectivelyTrivialIdeal.quotientFunctor.obj (P k)) := by
    intro k
    by_cases hinj : E.isInjective (P k)
    · exact ⟨0, ⟨D.isZero_translate_obj_zero.iso ((MorphismIdeal.isZero_quotientFunctor_obj_iff
        _ _).mpr ((id_mem_injectivelyTrivialIdeal_iff _).mpr hinj))⟩⟩
    · obtain ⟨Z, e, he⟩ := hleft (P k)
        ((IsKrullSchmidt.indecomposable_iff_isLocalRing_end _).mpr (hP k)) hinj
      obtain ⟨φ, hφ⟩ := exists_apply_ne_zero_of_forall_isMaximal hQ
        (fun h0 ↦ e.not_isAlmostSplit_of_mk_eq_zero h0 he)
      exact ⟨Z, ⟨costableIsoOfBijective ((D.isDualizingForm Z).bijective_costablePairing)
        fun X' ↦ (bijective_costablePairing_of_isAlmostSplit hQ e he hφ (hfin Z X')).1⟩⟩
  choose Z hZ using hk
  exact ⟨E.projectivelyTrivialIdeal.quotientFunctor.obj (⨁ Z),
    ⟨D.translate.mapBiproduct Z ≪≫ biproduct.mapIso (fun k ↦ (hZ k).some) ≪≫
      (E.injectivelyTrivialIdeal.quotientFunctor.mapBiproduct P).symm ≪≫
        E.injectivelyTrivialIdeal.quotientFunctor.mapIso i.symm⟩⟩

end Duality

end DualizingForms

/-- **Existence of almost-split conflations gives an Auslander–Reiten duality.** Let `E` be an
exact structure on a Krull–Schmidt `R`-linear category with every `Ext¹` of finite length, in which
an almost-split conflation ends at every indecomposable non-projective object and one starts at
every indecomposable non-injective object. Then `E` has an Auslander–Reiten duality
`τ : E/𝒫 ≌ E/ℐ`, `Ext¹_E(Z, X) ≅ D ((E/ℐ)(X, τ Z))`. -/
theorem nonempty_auslanderReitenDuality [HasFiniteBiproducts C] [IsKrullSchmidt C]
    [Module.Injective R Q] [Small.{w} R]
    (hQ : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] Q) = 1)
    (hfin : ∀ Z X : C, IsFiniteLength R (E.Ext1 Z X))
    (hright : ∀ Z : C, Indecomposable Z → ¬ E.isProjective Z →
      ∃ (T : C) (e : E.Extension Z T), e.shortComplex.IsAlmostSplit)
    (hleft : ∀ X : C, Indecomposable X → ¬ E.isInjective X →
      ∃ (Z : C) (e : E.Extension Z X), e.shortComplex.IsAlmostSplit) :
    Nonempty (E.AuslanderReitenDuality R Q) := by
  choose T φ hφ using exists_isDualizingForm (Q := Q) hQ hfin hright
  let D : E.DualizingForms R Q := ⟨T, φ, hφ⟩
  have := D.essSurj_functor hQ hfin hleft
  exact ⟨{ functor := D.functor
           isEquivalence := { }
           iso := D.iso hQ hfin
           iso_pushout := D.iso_pushout hQ hfin
           iso_pullback := D.iso_pullback hQ hfin }⟩

end ExactStructure

end TauCeti
