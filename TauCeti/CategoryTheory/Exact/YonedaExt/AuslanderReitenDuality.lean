/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.YonedaExt.DualizingForm
import TauCeti.CategoryTheory.Functor.LocalEnd
import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Uniqueness

/-!
# Auslander–Reiten duality for exact categories

Let `E` be an exact structure on an `R`-linear category, `𝒫` and `ℐ` its ideals of projectively
and injectively trivial morphisms, and `D = Hom_R(-, Q)` a duality preserving length as in
`TauCeti/CategoryTheory/Exact/YonedaExt/LocalDuality.lean`. An **Auslander–Reiten duality** is an
equivalence `τ : E/𝒫 ≌ E/ℐ` together with isomorphisms
`Ext¹_E(Z, X) ≅ D ((E/ℐ)(X, τ Z))` natural in `X` and in `Z`.

For a Krull–Schmidt category in which every `Ext¹` has finite length, this file shows that such a
duality exists exactly when almost-split conflations end at every indecomposable non-projective
object and start at every indecomposable non-injective object, and that the left-hand end of the
almost-split conflation ending at `Z` is then `τ Z`. No enough projectives or injectives are
assumed.

The construction follows [INP, Prop. 3.7 and Thm. 3.6]. A dualizing form
`φ_Z : Ext¹_E(Z, T_Z) → Q` at every object (`TauCeti.ExactStructure.exists_isDualizingForm`) makes
`T_Z` represent `D Ext¹_E(Z, -)` on `E/ℐ`, so by the Yoneda lemma `Z ↦ T_Z` is a functor: `τ u` for
`u : Z ⟶ Z'` is the unique morphism with `φ_{Z'}(τ(u)_* ζ) = φ_Z(u^* ζ)` ([INP, Lemma 3.10]). On
morphisms `τ` is the composite of the two bijective pairings
`(E/𝒫)(Z, Z') ≅ D Ext¹_E(Z', T_Z) ≅ (E/ℐ)(T_Z, T_{Z'})`, hence fully faithful. It is essentially
surjective because the left-hand end `X` of an almost-split conflation ending at `Z` also
represents `D Ext¹_E(Z, -)`, so that `T_Z ≅ X` in `E/ℐ`.

Conversely, given a duality, `τ Z` represents `D Ext¹_E(Z, -)` on `E/ℐ` with universal element
`ξ ↦ (linearEquiv ξ)(𝟙)`, which is a dualizing form. For `Z` indecomposable and not projective,
`τ Z` has a local endomorphism ring, so it is isomorphic in `E/ℐ` to an object with a local
endomorphism ring, and the local theorem gives an almost-split conflation ending at `Z`; dually
through `τ⁻¹`.

## Main definitions

* `TauCeti.ExactStructure.AuslanderReitenDuality E R Q`: an Auslander–Reiten duality.
* `TauCeti.ExactStructure.DualizingForms E R Q`: a choice of dualizing form at every object, and
  `TauCeti.ExactStructure.DualizingForms.functor`, the translate `E/𝒫 ⥤ E/ℐ` it determines.

## Main results

* `TauCeti.ExactStructure.DualizingForms.fullyFaithfulFunctor`: the translate is fully faithful.
* `TauCeti.ExactStructure.nonempty_auslanderReitenDuality`: existence of almost-split
  conflations gives an Auslander–Reiten duality.
* `TauCeti.ExactStructure.AuslanderReitenDuality.isDualizingForm_form`: the universal element of a
  duality is a dualizing form.
* `AuslanderReitenDuality.exists_isAlmostSplit_of_indecomposable_of_not_isProjective` and
  `AuslanderReitenDuality.exists_isAlmostSplit_of_indecomposable_of_not_isInjective`, in
  `TauCeti.ExactStructure`: the converse.
* `TauCeti.ExactStructure.nonempty_auslanderReitenDuality_iff`: **the existence theorem**.
* `TauCeti.ExactStructure.AuslanderReitenDuality.isoTranslateOfIsAlmostSplit`: the left-hand end of
  the almost-split conflation ending at `Z` is `τ Z` in `E/ℐ`.

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
  linearEquiv (Z X : C) : E.Ext1 Z X ≃ₗ[R] ((E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
    functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) →ₗ[R] Q)
  /-- Naturality in `X`. -/
  linearEquiv_pushout {Z X X' : C} (v : X ⟶ X') (ξ : E.Ext1 Z X)
    (a : E.injectivelyTrivialIdeal.quotientFunctor.obj X' ⟶
      functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) :
    linearEquiv Z X' (ξ.pushout v) a =
      linearEquiv Z X ξ (E.injectivelyTrivialIdeal.quotientFunctor.map v ≫ a)
  /-- Naturality in `Z`. -/
  linearEquiv_pullback {Z Z' X : C} (u : Z' ⟶ Z) (ξ : E.Ext1 Z X)
    (a : E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
      functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z')) :
    linearEquiv Z' X (ξ.pullback u) a =
      linearEquiv Z X ξ (a ≫ functor.map (E.projectivelyTrivialIdeal.quotientFunctor.map u))

attribute [instance] AuslanderReitenDuality.isEquivalence
attribute [simp] AuslanderReitenDuality.linearEquiv_pushout
  AuslanderReitenDuality.linearEquiv_pullback

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

@[simp]
theorem costableEquiv_apply (Z X : C)
    (x : E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
      E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z)) :
    D.costableEquiv Z X x = costablePairing (D.form Z) X x :=
  (rfl)

@[simp]
theorem costablePairing_costableEquiv_symm (Z X : C) (f : E.Ext1 Z X →ₗ[R] Q) :
    costablePairing (D.form Z) X ((D.costableEquiv Z X).symm f) = f :=
  (D.costableEquiv Z X).apply_symm_apply f

@[simp]
theorem costableEquiv_symm_costablePairing (Z X : C)
    (x : E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
      E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z)) :
    (D.costableEquiv Z X).symm (costablePairing (D.form Z) X x) = x :=
  (D.costableEquiv Z X).symm_apply_apply x

/-- The translate on morphisms: `τ u : T_Z ⟶ T_{Z'}` is the morphism corresponding to the linear
form `ζ ↦ φ_Z(u^* ζ)` on `Ext¹_E(Z', T_Z)`. -/
noncomputable def translateMap {Z Z' : C} (u : Z ⟶ Z') :
    E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z) ⟶
      E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z') :=
  (D.costableEquiv Z' (D.obj Z)).symm
    (stablePairing (D.form Z) Z' (E.projectivelyTrivialIdeal.quotientFunctor.map u))

@[simp]
theorem costablePairing_translateMap {Z Z' : C} (u : Z ⟶ Z') :
    costablePairing (D.form Z') (D.obj Z) (D.translateMap u) =
      stablePairing (D.form Z) Z' (E.projectivelyTrivialIdeal.quotientFunctor.map u) :=
  D.costablePairing_costableEquiv_symm Z' (D.obj Z) _

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

@[simp]
theorem translate_obj (Z : C) :
    D.translate.obj Z = E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z) :=
  rfl

@[simp]
theorem translate_map {Z Z' : C} (u : Z ⟶ Z') : D.translate.map u = D.translateMap u := rfl

@[simp]
theorem translateMap_id (Z : C) : D.translateMap (𝟙 Z) = 𝟙 _ :=
  D.translate.map_id Z

@[simp]
theorem translateMap_comp {Z Z' Z'' : C} (u : Z ⟶ Z') (w : Z' ⟶ Z'') :
    D.translateMap (u ≫ w) = D.translateMap u ≫ D.translateMap w :=
  D.translate.map_comp u w

@[simp]
theorem translateMap_add {Z Z' : C} (u u' : Z ⟶ Z') :
    D.translateMap (u + u') = D.translateMap u + D.translateMap u' := by
  simp only [translateMap, Functor.map_add, map_add]

@[simp]
theorem translateMap_smul {Z Z' : C} (r : R) (u : Z ⟶ Z') :
    D.translateMap (r • u) = r • D.translateMap u := by
  simp only [translateMap, Functor.map_smul, map_smul]

theorem translateMap_eq_zero {Z Z' : C} {u : Z ⟶ Z'}
    (hu : u ∈ E.projectivelyTrivialIdeal.hom Z Z') : D.translateMap u = 0 := by
  rw [translateMap, (MorphismIdeal.quotientFunctor_map_eq_zero_iff _).mpr hu, map_zero, map_zero]

instance : D.translate.Additive where
  map_add := D.translateMap_add _ _

instance : D.translate.Linear R where
  map_smul u r := D.translateMap_smul r u

@[simp]
theorem translateMap_zero (Z Z' : C) : D.translateMap (0 : Z ⟶ Z') = 0 :=
  D.translate.map_zero Z Z'

@[simp]
theorem translateMap_neg {Z Z' : C} (u : Z ⟶ Z') : D.translateMap (-u) = -D.translateMap u :=
  D.translate.map_neg

@[simp]
theorem translateMap_sub {Z Z' : C} (u u' : Z ⟶ Z') :
    D.translateMap (u - u') = D.translateMap u - D.translateMap u' :=
  D.translate.map_sub

@[simp]
theorem translateMap_sum {Z Z' : C} {ι : Type*} (u : ι → (Z ⟶ Z')) (s : Finset ι) :
    D.translateMap (∑ i ∈ s, u i) = ∑ i ∈ s, D.translateMap (u i) :=
  D.translate.map_sum u s

theorem projectivelyTrivialIdeal_le_kerIdeal_translate :
    E.projectivelyTrivialIdeal ≤ D.translate.kerIdeal := fun _ _ _ hu ↦
  (Functor.mem_kerIdeal_hom _).mpr (D.translateMap_eq_zero hu)

/-- **The Auslander–Reiten translate** `τ : E/𝒫 ⥤ E/ℐ` determined by dualizing forms. -/
@[expose] noncomputable def functor :
    E.projectivelyTrivialIdeal.Quotient ⥤ E.injectivelyTrivialIdeal.Quotient :=
  E.projectivelyTrivialIdeal.lift D.translate D.projectivelyTrivialIdeal_le_kerIdeal_translate

@[simp]
theorem functor_obj_quotientFunctor_obj (Z : C) :
    D.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z) =
      E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z) :=
  rfl

@[simp]
theorem functor_map_quotientFunctor_map {Z Z' : C} (u : Z ⟶ Z') :
    D.functor.map (E.projectivelyTrivialIdeal.quotientFunctor.map u) = D.translateMap u :=
  rfl

@[simp]
theorem quotientFunctor_comp_functor :
    E.projectivelyTrivialIdeal.quotientFunctor ⋙ D.functor = D.translate :=
  CategoryTheory.Quotient.lift_spec _ _ fun _ _ _ _ h ↦
    E.projectivelyTrivialIdeal.map_eq_of_rel _ D.projectivelyTrivialIdeal_le_kerIdeal_translate h

instance : D.functor.Additive :=
  inferInstanceAs (E.projectivelyTrivialIdeal.lift D.translate
    D.projectivelyTrivialIdeal_le_kerIdeal_translate).Additive

instance : D.functor.Linear R :=
  inferInstanceAs ((E.projectivelyTrivialIdeal.lift D.translate
    D.projectivelyTrivialIdeal_le_kerIdeal_translate).Linear R)

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

/-- **The translate is fully faithful.** -/
noncomputable def fullyFaithfulFunctor : D.functor.FullyFaithful :=
  .ofFullyFaithful _

section Duality

variable [Module.Injective R Q] [Small.{w} R]
  (hQ : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] Q) = 1)

/-- **The duality** `Ext¹_E(Z, X) ≅ D ((E/ℐ)(X, τ Z))` when `Ext¹_E(Z, X)` has finite length: the
flip of the costable pairing of the form `φ_Z`. -/
noncomputable def linearEquiv {Z X : C} (hZX : IsFiniteLength R (E.Ext1 Z X)) :
    E.Ext1 Z X ≃ₗ[R] ((E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
      E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z)) →ₗ[R] Q) :=
  LinearEquiv.ofBijective (costablePairing (D.form Z) X).flip
    (bijective_of_injective_of_injective_flip hQ
      ((D.isDualizingForm Z).bijective_costablePairing X).1
      (injective_flip_of_surjective
        (nontrivial_linearMap_of_isMaximal hQ)
        ((D.isDualizingForm Z).bijective_costablePairing X).2)
      hZX).2.2

@[simp]
theorem linearEquiv_apply {Z X : C} (hZX : IsFiniteLength R (E.Ext1 Z X)) (ξ : E.Ext1 Z X)
    (a : E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
      E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z)) :
    D.linearEquiv hQ hZX ξ a = costablePairing (D.form Z) X a ξ :=
  (rfl)

/-- **Naturality of the duality in `X`**, under cobase change. -/
theorem linearEquiv_pushout {Z X X' : C} (v : X ⟶ X') (hX : IsFiniteLength R (E.Ext1 Z X))
    (hX' : IsFiniteLength R (E.Ext1 Z X')) (ξ : E.Ext1 Z X)
    (a : E.injectivelyTrivialIdeal.quotientFunctor.obj X' ⟶
      E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z)) :
    D.linearEquiv hQ hX' (ξ.pushout v) a =
      D.linearEquiv hQ hX ξ (E.injectivelyTrivialIdeal.quotientFunctor.map v ≫ a) := by
  obtain ⟨a, rfl⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective a
  rw [linearEquiv_apply, linearEquiv_apply, ← Functor.map_comp, costablePairing_map,
    costablePairing_map, Ext1.pushout_pushout]

/-- **Naturality of the duality in `Z`**, under base change. -/
theorem linearEquiv_pullback {Z Z' X : C} (u : Z' ⟶ Z) (hZ : IsFiniteLength R (E.Ext1 Z X))
    (hZ' : IsFiniteLength R (E.Ext1 Z' X)) (ξ : E.Ext1 Z X)
    (a : E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
      E.injectivelyTrivialIdeal.quotientFunctor.obj (D.obj Z')) :
    D.linearEquiv hQ hZ' (ξ.pullback u) a = D.linearEquiv hQ hZ ξ (a ≫ D.translateMap u) := by
  obtain ⟨a, rfl⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective a
  obtain ⟨b, hb⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective (D.translateMap u)
  rw [linearEquiv_apply, linearEquiv_apply, ← hb, ← Functor.map_comp, costablePairing_map,
    costablePairing_map, ← Ext1.pushout_pushout, D.form_pushout u hb, Ext1.pushout_pullback]

include hQ in
/-- **The translate is essentially surjective** in a Krull–Schmidt category in which every `Ext¹`
has finite length and almost-split conflations start at every indecomposable non-injective
object. -/
theorem essSurj_functor [HasFiniteBiproducts C] [IsKrullSchmidt C]
    (hfin : ∀ Z X : C, IsFiniteLength R (E.Ext1 Z X))
    (hleft : ∀ X : C, Indecomposable X → ¬ E.isInjective X →
      ∃ (Z : C) (e : E.Extension Z X), e.shortComplex.IsAlmostSplit) :
    D.functor.EssSurj := by
  refine ⟨fun Y ↦ ?_⟩
  obtain ⟨X⟩ := Y
  obtain ⟨n, P, hP, ⟨i⟩⟩ := IsKrullSchmidt.exists_iso_biproduct X
  -- Each summand `P k` is a translate: of `0` if it is injective, and otherwise of the right-hand
  -- end of its almost-split conflation, both objects representing `D Ext¹_E(Z, -)` on `E/ℐ`.
  have hk : ∀ k, ∃ Z : C,
      Nonempty (D.translate.obj Z ≅ E.injectivelyTrivialIdeal.quotientFunctor.obj (P k)) := by
    intro k
    by_cases hinj : E.isInjective (P k)
    · exact ⟨0, ⟨(D.translate.map_isZero (isZero_zero C)).iso
        ((MorphismIdeal.isZero_quotientFunctor_obj_iff _ _).mpr
          ((id_mem_injectivelyTrivialIdeal_iff _).mpr hinj))⟩⟩
    · obtain ⟨Z, e, he⟩ := hleft (P k)
        ((IsKrullSchmidt.indecomposable_iff_isLocalRing_end _).mpr (hP k)) hinj
      obtain ⟨φ, hφ⟩ :=
        exists_apply_mk_ne_zero_of_isAlmostSplit (nontrivial_linearMap_of_isMaximal hQ) e he
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
           linearEquiv Z X := D.linearEquiv hQ (hfin Z X)
           linearEquiv_pushout v ξ a := D.linearEquiv_pushout hQ v (hfin _ _) (hfin _ _) ξ a
           linearEquiv_pullback u ξ a := D.linearEquiv_pullback hQ u (hfin _ _) (hfin _ _) ξ a }⟩

/-! ### The converse -/

namespace AuslanderReitenDuality

variable {E R Q} (A : E.AuslanderReitenDuality R Q)

instance : A.functor.Additive := Functor.additive_of_preserves_binary_products _

/-- The translate `τ Z`, as an object of `C`. -/
abbrev translateObj (Z : C) : C :=
  (A.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)).as

/-- The universal element `ξ ↦ (linearEquiv ξ)(𝟙)` of `D Ext¹_E(Z, τ Z)`. -/
noncomputable def form (Z : C) : E.Ext1 Z (A.translateObj Z) →ₗ[R] Q :=
  LinearMap.applyₗ (𝟙 (A.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z))) ∘ₗ
    (A.linearEquiv Z (A.translateObj Z)).toLinearMap

@[simp]
theorem form_apply (Z : C) (ξ : E.Ext1 Z (A.translateObj Z)) :
    A.form Z ξ =
      A.linearEquiv Z (A.translateObj Z) ξ
        (𝟙 (A.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z))) :=
  (rfl)

@[simp]
theorem costablePairing_form (Z X : C)
    (x : E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
      A.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z)) (ξ : E.Ext1 Z X) :
    costablePairing (A.form Z) X x ξ = A.linearEquiv Z X ξ x := by
  obtain ⟨a, rfl⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective (X := X)
    (Y := A.translateObj Z) x
  rw [costablePairing_map, form_apply, A.linearEquiv_pushout]
  exact congrArg (A.linearEquiv Z X ξ) (Category.comp_id _)

@[simp]
theorem stablePairing_form (Z B : C)
    (x : E.projectivelyTrivialIdeal.quotientFunctor.obj Z ⟶
      E.projectivelyTrivialIdeal.quotientFunctor.obj B) (η : E.Ext1 B (A.translateObj Z)) :
    stablePairing (A.form Z) B x η = A.linearEquiv B (A.translateObj Z) η (A.functor.map x) := by
  obtain ⟨u, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective x
  rw [stablePairing_map, form_apply, A.linearEquiv_pullback]
  exact congrArg (A.linearEquiv B (A.translateObj Z) η) (Category.id_comp _)

section Converse

variable [Module.Injective R Q] [Small.{w} R]
  (hQ : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] Q) = 1)
include A hQ

/-- **`τ Z` represents `D Ext¹_E(Z, -)` on `E/ℐ`**, with universal element `A.form Z`: the costable
pairing of `A.form Z` at `X` is bijective when `Ext¹_E(Z, X)` has finite length. -/
theorem bijective_costablePairing_form {Z X : C} (hZX : IsFiniteLength R (E.Ext1 Z X)) :
    Function.Bijective (costablePairing (A.form Z) X) := by
  have hflip : (costablePairing (A.form Z) X) = (A.linearEquiv Z X).toLinearMap.flip :=
    LinearMap.ext fun x ↦ LinearMap.ext fun ξ ↦ A.costablePairing_form Z X x ξ
  rw [hflip]
  exact (bijective_of_injective_of_injective_flip hQ
    (injective_flip_of_surjective
      (nontrivial_linearMap_of_isMaximal hQ) (A.linearEquiv Z X).surjective)
    (A.linearEquiv Z X).injective hZX).2.1

/-- **`Z` represents `D Ext¹_E(-, τ Z)` on `E/𝒫`**, with universal element `A.form Z`: the stable
pairing of `A.form Z` at `B` is bijective when `Ext¹_E(B, τ Z)` has finite length. -/
theorem bijective_stablePairing_form {Z B : C}
    (hBZ : IsFiniteLength R (E.Ext1 B (A.translateObj Z))) :
    Function.Bijective (stablePairing (A.form Z) B) := by
  have h : ⇑(stablePairing (A.form Z) B) =
      ⇑(costablePairing (A.form B) (A.translateObj Z)) ∘ A.functor.map :=
    funext fun x ↦ LinearMap.ext fun η ↦ by
      rw [Function.comp_apply, A.stablePairing_form, A.costablePairing_form]
  rw [h]
  exact (A.bijective_costablePairing_form hQ hBZ).comp
    ((Functor.FullyFaithful.ofFullyFaithful A.functor).map_bijective _ _)

/-- **The universal element of an Auslander–Reiten duality is dualizing**, when every `Ext¹` out
of `Z` and into `τ Z` has finite length. -/
theorem isDualizingForm_form {Z : C} (hZ : ∀ X, IsFiniteLength R (E.Ext1 Z X))
    (hτZ : ∀ B, IsFiniteLength R (E.Ext1 B (A.translateObj Z))) : IsDualizingForm (A.form Z) :=
  ⟨fun X ↦ A.bijective_costablePairing_form hQ (hZ X),
    fun B ↦ A.bijective_stablePairing_form hQ (hτZ B)⟩

/-- **The translate is the left-hand end of the almost-split conflation**: if `T ⟶ Y ⟶ Z` is
almost split and every `Ext¹_E(Z, X)` has finite length, then `T ≅ τ Z` in `E/ℐ`. -/
noncomputable def isoTranslateOfIsAlmostSplit {Z T : C} (hZ : ∀ X, IsFiniteLength R (E.Ext1 Z X))
    (e : E.Extension Z T) (he : e.shortComplex.IsAlmostSplit) :
    E.injectivelyTrivialIdeal.quotientFunctor.obj T ≅
      A.functor.obj (E.projectivelyTrivialIdeal.quotientFunctor.obj Z) :=
  costableIsoOfBijective
    (fun X ↦ (bijective_costablePairing_of_isAlmostSplit hQ e he
      (exists_apply_mk_ne_zero_of_isAlmostSplit
        (nontrivial_linearMap_of_isMaximal hQ) e he).choose_spec (hZ X)).1)
    fun X ↦ A.bijective_costablePairing_form hQ (hZ X)

variable [HasFiniteBiproducts C] [IsKrullSchmidt C]

/-- **An Auslander–Reiten duality gives almost-split conflations ending at every indecomposable
non-projective object `Z`** of a Krull–Schmidt category, when every `Ext¹_E(Z, X)` has finite
length. -/
theorem exists_isAlmostSplit_of_indecomposable_of_not_isProjective {Z : C}
    (hZX : ∀ X, IsFiniteLength R (E.Ext1 Z X)) (hZ : Indecomposable Z)
    (hZp : ¬ E.isProjective Z) :
    ∃ (T : C) (e : E.Extension Z T), e.shortComplex.IsAlmostSplit := by
  -- `τ Z` has a local endomorphism ring, so it is isomorphic in `E/ℐ` to an object `T` with a
  -- local endomorphism ring, which then represents `D Ext¹_E(Z, -)` on `E/ℐ`.
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end Z).mp hZ
  have := E.projectivelyTrivialIdeal.quotientFunctor.isLocalRing_end_obj
    ((MorphismIdeal.isZero_quotientFunctor_obj_iff _ Z).not.mpr
      ((id_mem_projectivelyTrivialIdeal_iff Z).not.mpr hZp))
  have : IsLocalRing (End (E.injectivelyTrivialIdeal.quotientFunctor.obj (A.translateObj Z))) :=
    (A.functor.isLocalRing_end_obj_iff _).mpr this
  obtain ⟨T, hT, ⟨i⟩⟩ := IsKrullSchmidt.exists_isLocalRing_end_iso_obj
    E.injectivelyTrivialIdeal.quotientFunctor (A.translateObj Z)
  obtain ⟨b, hb⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective i.inv
  have hb' : IsIso (E.injectivelyTrivialIdeal.quotientFunctor.map b) := hb ▸ inferInstance
  refine ⟨T, exists_isAlmostSplit_of_bijective_costablePairing hQ ?_ (hZX T) fun X ↦
    bijective_costablePairing_comp_pushout (A.bijective_costablePairing_form hQ (hZX X)) hb'⟩
  -- `T` is not injective: in `E/ℐ` it is isomorphic to `τ Z`, which is nonzero.
  intro hTi
  rw [← id_mem_injectivelyTrivialIdeal_iff, ← MorphismIdeal.isZero_quotientFunctor_obj_iff] at hTi
  exact one_ne_zero (α := End (E.injectivelyTrivialIdeal.quotientFunctor.obj (A.translateObj Z)))
    (End.ext ((hTi.of_iso i).eq_of_src _ _))

/-- **An Auslander–Reiten duality gives almost-split conflations starting at every indecomposable
non-injective object `X`** of a Krull–Schmidt category, when every `Ext¹` has finite length. -/
theorem exists_isAlmostSplit_of_indecomposable_of_not_isInjective
    (hfin : ∀ Z X : C, IsFiniteLength R (E.Ext1 Z X)) {X : C} (hX : Indecomposable X)
    (hXi : ¬ E.isInjective X) :
    ∃ (Z : C) (e : E.Extension Z X), e.shortComplex.IsAlmostSplit := by
  -- `X` is `τ W` in `E/ℐ` for some `W` with a local endomorphism ring in `E/𝒫`, which is
  -- isomorphic there to an object `Z` with a local endomorphism ring; then `X` represents
  -- `D Ext¹_E(Z, -)` on `E/ℐ`.
  have := (IsKrullSchmidt.indecomposable_iff_isLocalRing_end X).mp hX
  have := E.injectivelyTrivialIdeal.quotientFunctor.isLocalRing_end_obj
    ((MorphismIdeal.isZero_quotientFunctor_obj_iff _ X).not.mpr
      ((id_mem_injectivelyTrivialIdeal_iff X).not.mpr hXi))
  set W := A.functor.objPreimage (E.injectivelyTrivialIdeal.quotientFunctor.obj X)
  let w := A.functor.objObjPreimageIso (E.injectivelyTrivialIdeal.quotientFunctor.obj X)
  have : IsLocalRing (End (E.projectivelyTrivialIdeal.quotientFunctor.obj W.as)) :=
    (A.functor.isLocalRing_end_obj_iff W).mp w.symm.endRingEquiv.isLocalRing
  obtain ⟨Z, hZ, ⟨i⟩⟩ := IsKrullSchmidt.exists_isLocalRing_end_iso_obj
    E.projectivelyTrivialIdeal.quotientFunctor W.as
  obtain ⟨b, hb⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective (X := X)
    (Y := A.translateObj Z) (A.functor.mapIso i.symm ≪≫ w).inv
  have hb' : IsIso (E.injectivelyTrivialIdeal.quotientFunctor.map b) := hb ▸ inferInstance
  exact ⟨Z, exists_isAlmostSplit_of_bijective_costablePairing hQ hXi (hfin Z X) fun X' ↦
    bijective_costablePairing_comp_pushout (A.bijective_costablePairing_form hQ (hfin Z X')) hb'⟩

end Converse

end AuslanderReitenDuality

/-- **Existence of almost-split conflations is equivalent to an Auslander–Reiten duality.** For an
exact structure on a Krull–Schmidt `R`-linear category with every `Ext¹` of finite length,
almost-split conflations end at every indecomposable non-projective object and start at every
indecomposable non-injective object exactly when there is an Auslander–Reiten duality
`τ : E/𝒫 ≌ E/ℐ`, `Ext¹_E(Z, X) ≅ D ((E/ℐ)(X, τ Z))`. -/
theorem nonempty_auslanderReitenDuality_iff [HasFiniteBiproducts C] [IsKrullSchmidt C]
    [Module.Injective R Q] [Small.{w} R]
    (hQ : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] Q) = 1)
    (hfin : ∀ Z X : C, IsFiniteLength R (E.Ext1 Z X)) :
    Nonempty (E.AuslanderReitenDuality R Q) ↔
      (∀ Z : C, Indecomposable Z → ¬ E.isProjective Z →
        ∃ (T : C) (e : E.Extension Z T), e.shortComplex.IsAlmostSplit) ∧
      (∀ X : C, Indecomposable X → ¬ E.isInjective X →
        ∃ (Z : C) (e : E.Extension Z X), e.shortComplex.IsAlmostSplit) :=
  ⟨fun ⟨A⟩ ↦ ⟨fun Z hZ hZp ↦
      A.exists_isAlmostSplit_of_indecomposable_of_not_isProjective hQ (hfin Z) hZ hZp,
    fun _ hX hXi ↦ A.exists_isAlmostSplit_of_indecomposable_of_not_isInjective hQ hfin hX hXi⟩,
    fun ⟨h₁, h₂⟩ ↦ nonempty_auslanderReitenDuality E R Q hQ hfin h₁ h₂⟩

end ExactStructure

end TauCeti
