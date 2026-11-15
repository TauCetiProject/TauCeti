/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Cogenerator
public import TauCeti.CategoryTheory.Exact.YonedaExt.AlmostSplit
public import TauCeti.CategoryTheory.Exact.YonedaExt.BaerSum
public import TauCeti.CategoryTheory.Exact.YonedaExt.TrivialIdeal
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Linear
import TauCeti.CategoryTheory.Preadditive.Radical.TopDual

/-!
# The local Auslander–Reiten duality of an exact category

Let `E` be an exact structure on an `R`-linear category, `𝒫` and `ℐ` its ideals of projectively
and injectively trivial morphisms, and `D = Hom_R(-, Q)` the dual into an injective `R`-module `Q`
for which each `Hom_R(R ⧸ 𝔪, Q)` has length one, so that `D` preserves length and is a duality on
modules of finite length. Over a commutative Artinian ring, or whenever `R ⧸ J(R)` is semisimple,
an injective hull of `R ⧸ J(R)` is such a module
(`TauCeti/RingTheory/MatlisDuality/Semilocal.lean`). Fix objects `A` and `T` and a linear form
`φ : Ext¹_E(A, T) → Q`. It induces two pairings, both written as a map to a dual:

* `stablePairing φ B : (E/𝒫)(A, B) → D Ext¹_E(B, T)`, `c ↦ (η ↦ φ(c^* η))`;
* `costablePairing φ X : (E/ℐ)(X, T) → D Ext¹_E(A, X)`, `a ↦ (ξ ↦ φ(a_* ξ))`.

By the Yoneda lemma, a natural isomorphism `(E/𝒫)(A, -) ≅ D Ext¹_E(-, T)` is the same as a linear
form `φ` for which every `stablePairing φ B` is bijective, `φ` being the image of the identity of
`A`; dually, every `costablePairing φ X` is bijective exactly when `(E/ℐ)(-, T) ≅ D Ext¹_E(A, -)`,
that is, when `T` represents `D Ext¹_E(A, -)` on `E/ℐ`.

**The local theorem** says that, for `A` and `T` with local endomorphism rings, `A` not projective
and `T` not injective, and the relevant `Ext¹` of finite length, an almost-split conflation
`T ⟶ Y ⟶ A` exists exactly when one of these pairings is perfect, for some `φ`:

* If `δ ∈ Ext¹_E(A, T)` is the class of an almost-split conflation and `φ(δ) ≠ 0`, both pairings
  are non-degenerate, because every nonzero class and every nontrivial morphism reaches `δ`: a
  nonzero `ξ ∈ Ext¹_E(A, X)` satisfies `a_* ξ = δ` for some `a : X ⟶ T`, and a morphism
  `a : X ⟶ T` outside `ℐ` satisfies `a_* ξ = δ` for some `ξ`; dually on the other side. As `D`
  preserves length, a non-degenerate pairing with one side of finite length is perfect.
* Conversely, if one pairing is perfect, the dual of the top of the local ring `End(A)`, resp.
  `End(T)`, gives a nonzero class `δ` killed by base change along every morphism into `A` that is
  not a split epimorphism, resp. by cobase change along every morphism out of `T` that is not a
  split monomorphism. Such a class is almost split by the extension-class criterion.

No enough projectives or injectives are assumed, and `R` need not be Artinian.

## Main definitions

* `TauCeti.ExactStructure.stablePairing φ B` and `TauCeti.ExactStructure.costablePairing φ X`: the
  two pairings induced by a linear form `φ : Ext¹_E(A, T) → Q`.

## Main results

* `TauCeti.ExactStructure.Extension.exists_pushout_eq_mk_of_isRightAlmostSplit`,
  `TauCeti.ExactStructure.Extension.exists_pullback_eq_mk_of_isLeftAlmostSplit`,
  `TauCeti.ExactStructure.Extension.exists_pullback_eq_mk_of_notMem_projectivelyTrivialIdeal` and
  `TauCeti.ExactStructure.Extension.exists_pushout_eq_mk_of_notMem_injectivelyTrivialIdeal`: every
  nonzero class and every nontrivial morphism reaches an almost-split class.
* `TauCeti.ExactStructure.bijective_stablePairing_of_isAlmostSplit` and
  `TauCeti.ExactStructure.bijective_costablePairing_of_isAlmostSplit`: an almost-split conflation
  gives the dualities `(E/𝒫)(A, B) ≅ D Ext¹_E(B, T)` and `Ext¹_E(A, X) ≅ D ((E/ℐ)(X, T))`.
* `TauCeti.ExactStructure.exists_isAlmostSplit_of_bijective_stablePairing` and
  `TauCeti.ExactStructure.exists_isAlmostSplit_of_bijective_costablePairing`: the converses.
* `TauCeti.ExactStructure.tfae_exists_isAlmostSplit`: **the local theorem**.

## References

* O. Iyama, H. Nakaoka, Y. Palu, *Auslander–Reiten theory in extriangulated categories*,
  arXiv:1805.03776 (v3), Lemma 2.13 and Proposition 3.3, over a field.
* H. Enomoto, *Classifications of exact structures and Cohen–Macaulay-finite algebras*, Adv. Math.
  **335** (2018), 838–877, arXiv:1705.02163, Proposition A.5, for the one-sided form over a complete
  local ring.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C} {A T : C}

/-! ### Every nonzero class reaches an almost-split class -/

namespace Extension

/-- If the deflation of `e : T ⟶ Y ⟶ A` is right almost split, every nonzero class
`ξ ∈ Ext¹_E(A, X)` is carried onto `[e]` by cobase change along some `a : X ⟶ T`. -/
theorem exists_pushout_eq_mk_of_isRightAlmostSplit (e : E.Extension A T)
    (he : IsRightAlmostSplit e.g) {X : C} {ξ : E.Ext1 A X} (hξ : ξ ≠ 0) :
    ∃ a : X ⟶ T, ξ.pushout a = Ext1.mk e := by
  induction ξ using Ext1.induction with
  | h e' =>
    rw [ne_eq, Ext1.mk_eq_zero_iff_isSplitEpi] at hξ
    obtain ⟨t, ht⟩ := he.factors _ e'.g hξ
    refine ⟨e.isKernelCokernelPair.lift (e'.f ≫ t) (by simp [ht]), ?_⟩
    rw [Ext1.pushout_mk_eq_pullback_mk (c := 𝟙 A) t (e.isKernelCokernelPair.lift_f _ _).symm
      (by rw [ht, Category.comp_id]), Ext1.pullback_id]

/-- If the inflation of `e : T ⟶ Y ⟶ A` is left almost split, every nonzero class
`η ∈ Ext¹_E(B, T)` is carried onto `[e]` by base change along some `c : A ⟶ B`. -/
theorem exists_pullback_eq_mk_of_isLeftAlmostSplit (e : E.Extension A T)
    (he : IsLeftAlmostSplit e.f) {B : C} {η : E.Ext1 B T} (hη : η ≠ 0) :
    ∃ c : A ⟶ B, η.pullback c = Ext1.mk e := by
  induction η using Ext1.induction with
  | h e' =>
    rw [ne_eq, Ext1.mk_eq_zero_iff_isSplitMono] at hη
    obtain ⟨t, ht⟩ := he.factors _ e'.f hη
    refine ⟨e.isKernelCokernelPair.desc (t ≫ e'.g) (by simp [reassoc_of% ht]), ?_⟩
    rw [← Ext1.pushout_mk_eq_pullback_mk (a := 𝟙 T) t (by rw [ht, Category.id_comp])
      (e.isKernelCokernelPair.g_desc _ _).symm, Ext1.pushout_id]

/-- If the deflation of `e : T ⟶ Y ⟶ A` is right almost split, every morphism `c : A ⟶ B` that is
not projectively trivial carries some class `η ∈ Ext¹_E(B, T)` onto `[e]` by base change. -/
theorem exists_pullback_eq_mk_of_notMem_projectivelyTrivialIdeal (e : E.Extension A T)
    (he : IsRightAlmostSplit e.g) {B : C} {c : A ⟶ B}
    (hc : c ∉ E.projectivelyTrivialIdeal.hom A B) :
    ∃ η : E.Ext1 B T, η.pullback c = Ext1.mk e := by
  rw [mem_projectivelyTrivialIdeal_iff_forall_ext1] at hc
  push Not at hc
  obtain ⟨W, ζ, hζ⟩ := hc
  obtain ⟨a, ha⟩ := e.exists_pushout_eq_mk_of_isRightAlmostSplit he hζ
  exact ⟨ζ.pushout a, by rw [Ext1.pushout_pullback, ha]⟩

/-- If the inflation of `e : T ⟶ Y ⟶ A` is left almost split, every morphism `a : X ⟶ T` that is
not injectively trivial carries some class `ξ ∈ Ext¹_E(A, X)` onto `[e]` by cobase change. -/
theorem exists_pushout_eq_mk_of_notMem_injectivelyTrivialIdeal (e : E.Extension A T)
    (he : IsLeftAlmostSplit e.f) {X : C} {a : X ⟶ T}
    (ha : a ∉ E.injectivelyTrivialIdeal.hom X T) :
    ∃ ξ : E.Ext1 A X, ξ.pushout a = Ext1.mk e := by
  rw [mem_injectivelyTrivialIdeal_iff_forall_ext1] at ha
  push Not at ha
  obtain ⟨W, ζ, hζ⟩ := ha
  obtain ⟨u, hu⟩ := e.exists_pullback_eq_mk_of_isLeftAlmostSplit he hζ
  exact ⟨ζ.pullback u, by rw [← Ext1.pushout_pullback, hu]⟩

end Extension

/-! ### The two pairings -/

section Pairing

variable {R : Type*} [CommRing R] [Linear R C] {Q : Type w} [AddCommGroup Q] [Module R Q]

/-- The pairing `(A ⟶ B) × Ext¹_E(B, T) → Q`, `(c, η) ↦ φ(c^* η)`, on morphisms of `C`. -/
noncomputable def pullbackPairing (φ : E.Ext1 A T →ₗ[R] Q) (B : C) :
    (A ⟶ B) →ₗ[R] E.Ext1 B T →ₗ[R] Q where
  toFun c := φ ∘ₗ Ext1.pullbackLinearMap R c
  map_add' c d := by ext η; simp [Ext1.pullback_add]
  map_smul' r c := by ext η; simp [Ext1.pullback_smul]

/-- The pairing `(X ⟶ T) × Ext¹_E(A, X) → Q`, `(a, ξ) ↦ φ(a_* ξ)`, on morphisms of `C`. -/
noncomputable def pushoutPairing (φ : E.Ext1 A T →ₗ[R] Q) (X : C) :
    (X ⟶ T) →ₗ[R] E.Ext1 A X →ₗ[R] Q where
  toFun a := φ ∘ₗ Ext1.pushoutLinearMap R a
  map_add' a b := by ext ξ; simp [Ext1.pushout_add]
  map_smul' r a := by ext ξ; simp [Ext1.pushout_smul]

@[simp]
theorem pullbackPairing_apply (φ : E.Ext1 A T →ₗ[R] Q) {B : C} (c : A ⟶ B) (η : E.Ext1 B T) :
    pullbackPairing φ B c η = φ (η.pullback c) := by
  simp [pullbackPairing]

@[simp]
theorem pushoutPairing_apply (φ : E.Ext1 A T →ₗ[R] Q) {X : C} (a : X ⟶ T) (ξ : E.Ext1 A X) :
    pushoutPairing φ X a ξ = φ (ξ.pushout a) := by
  simp [pushoutPairing]

/-- **The pairing on the projectively stable category**: a linear form `φ : Ext¹_E(A, T) → Q`
induces `(E/𝒫)(A, B) → D Ext¹_E(B, T)`, `c ↦ (η ↦ φ(c^* η))`. It is well defined because a
projectively trivial morphism kills `Ext¹` by base change. -/
noncomputable def stablePairing (φ : E.Ext1 A T →ₗ[R] Q) (B : C) :
    (E.projectivelyTrivialIdeal.quotientFunctor.obj A ⟶
        E.projectivelyTrivialIdeal.quotientFunctor.obj B) →ₗ[R] E.Ext1 B T →ₗ[R] Q :=
  (E.projectivelyTrivialIdeal.homSubmodule R A B).liftQ (pullbackPairing φ B)
      (fun c hc ↦ LinearMap.mem_ker.mpr <| LinearMap.ext fun η ↦ by
        simp [(mem_projectivelyTrivialIdeal_iff_forall_ext1.mp
          ((MorphismIdeal.mem_homSubmodule R _ c).mp hc)) T η]) ∘ₗ
    (E.projectivelyTrivialIdeal.homLinearEquiv R A B).symm.toLinearMap

/-- **The pairing on the injectively stable category**: a linear form `φ : Ext¹_E(A, T) → Q`
induces `(E/ℐ)(X, T) → D Ext¹_E(A, X)`, `a ↦ (ξ ↦ φ(a_* ξ))`. It is well defined because an
injectively trivial morphism kills `Ext¹` by cobase change. -/
noncomputable def costablePairing (φ : E.Ext1 A T →ₗ[R] Q) (X : C) :
    (E.injectivelyTrivialIdeal.quotientFunctor.obj X ⟶
        E.injectivelyTrivialIdeal.quotientFunctor.obj T) →ₗ[R] E.Ext1 A X →ₗ[R] Q :=
  (E.injectivelyTrivialIdeal.homSubmodule R X T).liftQ (pushoutPairing φ X)
      (fun a ha ↦ LinearMap.mem_ker.mpr <| LinearMap.ext fun ξ ↦ by
        simp [(mem_injectivelyTrivialIdeal_iff_forall_ext1.mp
          ((MorphismIdeal.mem_homSubmodule R _ a).mp ha)) A ξ]) ∘ₗ
    (E.injectivelyTrivialIdeal.homLinearEquiv R X T).symm.toLinearMap

@[simp]
theorem stablePairing_map (φ : E.Ext1 A T →ₗ[R] Q) {B : C} (c : A ⟶ B) (η : E.Ext1 B T) :
    stablePairing φ B (E.projectivelyTrivialIdeal.quotientFunctor.map c) η = φ (η.pullback c) := by
  simp [stablePairing]

@[simp]
theorem costablePairing_map (φ : E.Ext1 A T →ₗ[R] Q) {X : C} (a : X ⟶ T) (ξ : E.Ext1 A X) :
    costablePairing φ X (E.injectivelyTrivialIdeal.quotientFunctor.map a) ξ = φ (ξ.pushout a) := by
  simp [costablePairing]

end Pairing

/-! ### The local theorem -/

section Duality

variable {R : Type*} [CommRing R] [Linear R C] {Q : Type w} [AddCommGroup Q] [Module R Q]
  [Module.Injective R Q] [Small.{w} R]
  (hQ : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] Q) = 1)
include hQ

/-- **An almost-split class makes the stable pairing perfect.** If `e : T ⟶ Y ⟶ A` is almost
split and `φ([e]) ≠ 0`, then `stablePairing φ B : (E/𝒫)(A, B) → D Ext¹_E(B, T)` and its flip are
bijective whenever `Ext¹_E(B, T)` has finite length. -/
theorem bijective_stablePairing_of_isAlmostSplit (e : E.Extension A T)
    (he : e.shortComplex.IsAlmostSplit) {φ : E.Ext1 A T →ₗ[R] Q} (hφ : φ (Ext1.mk e) ≠ 0)
    {B : C} (hB : IsFiniteLength R (E.Ext1 B T)) :
    Function.Bijective (stablePairing φ B) ∧ Function.Bijective (stablePairing φ B).flip := by
  refine (bijective_of_injective_of_injective_flip hQ ?_ ?_ hB).2
  · refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
    obtain ⟨c, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective x
    rw [MorphismIdeal.quotientFunctor_map_eq_zero_iff]
    by_contra hc
    obtain ⟨η, hη⟩ := e.exists_pullback_eq_mk_of_notMem_projectivelyTrivialIdeal
      he.isRightAlmostSplit_g hc
    exact hφ (by rw [← hη, ← stablePairing_map, hx, LinearMap.zero_apply])
  · refine (injective_iff_map_eq_zero _).mpr fun η hη ↦ ?_
    by_contra hne
    obtain ⟨c, hc⟩ := e.exists_pullback_eq_mk_of_isLeftAlmostSplit he.isLeftAlmostSplit_f hne
    exact hφ (by
      rw [← hc, ← stablePairing_map, ← LinearMap.flip_apply, hη, LinearMap.zero_apply])

/-- **An almost-split class makes the costable pairing perfect.** If `e : T ⟶ Y ⟶ A` is almost
split and `φ([e]) ≠ 0`, then `costablePairing φ X : (E/ℐ)(X, T) → D Ext¹_E(A, X)` and its flip
are bijective whenever `Ext¹_E(A, X)` has finite length. -/
theorem bijective_costablePairing_of_isAlmostSplit (e : E.Extension A T)
    (he : e.shortComplex.IsAlmostSplit) {φ : E.Ext1 A T →ₗ[R] Q} (hφ : φ (Ext1.mk e) ≠ 0)
    {X : C} (hX : IsFiniteLength R (E.Ext1 A X)) :
    Function.Bijective (costablePairing φ X) ∧ Function.Bijective (costablePairing φ X).flip := by
  refine (bijective_of_injective_of_injective_flip hQ ?_ ?_ hX).2
  · refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
    obtain ⟨a, rfl⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective x
    rw [MorphismIdeal.quotientFunctor_map_eq_zero_iff]
    by_contra ha
    obtain ⟨ξ, hξ⟩ := e.exists_pushout_eq_mk_of_notMem_injectivelyTrivialIdeal
      he.isLeftAlmostSplit_f ha
    exact hφ (by rw [← hξ, ← costablePairing_map, hx, LinearMap.zero_apply])
  · refine (injective_iff_map_eq_zero _).mpr fun ξ hξ ↦ ?_
    by_contra hne
    obtain ⟨a, ha⟩ := e.exists_pushout_eq_mk_of_isRightAlmostSplit he.isRightAlmostSplit_g hne
    exact hφ (by
      rw [← ha, ← costablePairing_map, ← LinearMap.flip_apply, hξ, LinearMap.zero_apply])

/-- **The converse from the stable pairing.** Let `A` and `T` have local endomorphism rings, with
`A` not projective and `Ext¹_E(A, T)` of finite length. If `stablePairing φ B` is bijective for
every `B`, there is an almost-split conflation `T ⟶ Y ⟶ A`. -/
theorem exists_isAlmostSplit_of_bijective_stablePairing [IsLocalRing (End A)]
    [IsLocalRing (End T)] (hA : ¬ E.isProjective A) (hAT : IsFiniteLength R (E.Ext1 A T))
    {φ : E.Ext1 A T →ₗ[R] Q} (hφ : ∀ B, Function.Bijective (stablePairing φ B)) :
    ∃ e : E.Extension A T, e.shortComplex.IsAlmostSplit := by
  have hflip : ∀ B, Function.Injective (stablePairing φ B).flip := fun B ↦
    injective_flip_of_surjective (nontrivial_linearMap_of_isMaximal hQ) (hφ B).2
  -- The class `δ` dual to a linear form on the top of `(E/𝒫)(A, A)`.
  obtain ⟨ψ, hψ1, hψ⟩ := MorphismIdeal.exists_linearMap_quotient_end
    (nontrivial_linearMap_of_isMaximal hQ) E.projectivelyTrivialIdeal A
    ((id_mem_projectivelyTrivialIdeal_iff A).not.mpr hA)
  obtain ⟨δ, hδ⟩ := (bijective_of_injective_of_injective_flip hQ (hφ A).1 (hflip A) hAT).2.2.2 ψ
  have hδc : ∀ c : A ⟶ A,
      φ (δ.pullback c) = ψ (E.projectivelyTrivialIdeal.quotientFunctor.map c) := fun c ↦ by
    rw [← hδ, LinearMap.flip_apply, stablePairing_map]
  obtain ⟨e, rfl⟩ := Ext1.mk_surjective δ
  refine ⟨e, (e.isAlmostSplit_iff_ext1_pullback).mpr ⟨fun h0 ↦ hψ1 ?_, fun W u hu ↦ hflip W ?_⟩⟩
  · rw [← hδc, h0, Ext1.zero_pullback, map_zero]
  · -- `u^* δ` pairs to zero with every `c : A ⟶ W`, since `c ≫ u` is not invertible.
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨c, rfl⟩ := E.projectivelyTrivialIdeal.quotientFunctor.map_surjective x
    rw [map_zero, LinearMap.zero_apply, LinearMap.flip_apply, stablePairing_map,
      Ext1.pullback_pullback, hδc]
    exact hψ _ fun _ ↦ hu (IsSplitEpi.mk' ⟨inv (c ≫ u) ≫ c,
      by rw [Category.assoc, IsIso.inv_hom_id]⟩)

/-- **The converse from the costable pairing.** Let `A` and `T` have local endomorphism rings,
with `T` not injective and `Ext¹_E(A, T)` of finite length. If `costablePairing φ X` is bijective
for every `X`, that is, if `T` represents `D Ext¹_E(A, -)` on `E/ℐ` with universal element `φ`,
there is an almost-split conflation `T ⟶ Y ⟶ A`. -/
theorem exists_isAlmostSplit_of_bijective_costablePairing [IsLocalRing (End A)]
    [IsLocalRing (End T)] (hT : ¬ E.isInjective T) (hAT : IsFiniteLength R (E.Ext1 A T))
    {φ : E.Ext1 A T →ₗ[R] Q} (hφ : ∀ X, Function.Bijective (costablePairing φ X)) :
    ∃ e : E.Extension A T, e.shortComplex.IsAlmostSplit := by
  have hflip : ∀ X, Function.Injective (costablePairing φ X).flip := fun X ↦
    injective_flip_of_surjective (nontrivial_linearMap_of_isMaximal hQ) (hφ X).2
  -- The class `δ` dual to a linear form on the top of `(E/ℐ)(T, T)`.
  obtain ⟨ψ, hψ1, hψ⟩ := MorphismIdeal.exists_linearMap_quotient_end
    (nontrivial_linearMap_of_isMaximal hQ) E.injectivelyTrivialIdeal T
    ((id_mem_injectivelyTrivialIdeal_iff T).not.mpr hT)
  obtain ⟨δ, hδ⟩ := (bijective_of_injective_of_injective_flip hQ (hφ T).1 (hflip T) hAT).2.2.2 ψ
  have hδa : ∀ a : T ⟶ T,
      φ (δ.pushout a) = ψ (E.injectivelyTrivialIdeal.quotientFunctor.map a) := fun a ↦ by
    rw [← hδ, LinearMap.flip_apply, costablePairing_map]
  obtain ⟨e, rfl⟩ := Ext1.mk_surjective δ
  refine ⟨e, (e.isAlmostSplit_iff_ext1_pushout).mpr ⟨fun h0 ↦ hψ1 ?_, fun W v hv ↦ hflip W ?_⟩⟩
  · rw [← hδa, h0, Ext1.zero_pushout, map_zero]
  · -- `v_* δ` pairs to zero with every `a : W ⟶ T`, since `v ≫ a` is not invertible.
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := E.injectivelyTrivialIdeal.quotientFunctor.map_surjective x
    rw [map_zero, LinearMap.zero_apply, LinearMap.flip_apply, costablePairing_map,
      Ext1.pushout_pushout, hδa]
    exact hψ _ fun _ ↦ hv (IsSplitMono.mk' ⟨a ≫ inv (v ≫ a),
      by rw [← Category.assoc, IsIso.hom_inv_id]⟩)

variable (R Q) in
/-- **The local theorem.** Let `A` and `T` be objects with local endomorphism rings, `A` not
projective and `T` not injective, such that `Ext¹_E(B, T)` and `Ext¹_E(A, X)` have finite length
for all `B` and `X`. The following are equivalent:

1. there is an almost-split conflation `T ⟶ Y ⟶ A`;
2. `(E/𝒫)(A, -) ≅ D Ext¹_E(-, T)`: for some `φ`, every `stablePairing φ B` is bijective;
3. `(E/ℐ)(-, T) ≅ D Ext¹_E(A, -)`, that is, `T` represents `D Ext¹_E(A, -)` on `E/ℐ`: for some
   `φ`, every `costablePairing φ X` is bijective.

In 1 ⇒ 2 and 1 ⇒ 3, any `φ` not vanishing on the almost-split class works. -/
theorem tfae_exists_isAlmostSplit [IsLocalRing (End A)] [IsLocalRing (End T)]
    (hA : ¬ E.isProjective A) (hT : ¬ E.isInjective T)
    (hB : ∀ B, IsFiniteLength R (E.Ext1 B T)) (hX : ∀ X, IsFiniteLength R (E.Ext1 A X)) :
    List.TFAE [∃ e : E.Extension A T, e.shortComplex.IsAlmostSplit,
      ∃ φ : E.Ext1 A T →ₗ[R] Q, ∀ B, Function.Bijective (stablePairing φ B),
      ∃ φ : E.Ext1 A T →ₗ[R] Q, ∀ X, Function.Bijective (costablePairing φ X)] := by
  have hne : ∀ e : E.Extension A T, e.shortComplex.IsAlmostSplit → Ext1.mk e ≠ 0 :=
    fun e he h0 ↦ e.not_isAlmostSplit_of_mk_eq_zero h0 he
  have hsep := nontrivial_linearMap_of_isMaximal hQ
  tfae_have 1 → 2 := fun ⟨e, he⟩ ↦
    have ⟨φ, hφ⟩ := exists_apply_ne_zero_of_forall_isMaximal hsep (hne e he)
    ⟨φ, fun B ↦ (bijective_stablePairing_of_isAlmostSplit hQ e he hφ (hB B)).1⟩
  tfae_have 1 → 3 := fun ⟨e, he⟩ ↦
    have ⟨φ, hφ⟩ := exists_apply_ne_zero_of_forall_isMaximal hsep (hne e he)
    ⟨φ, fun X ↦ (bijective_costablePairing_of_isAlmostSplit hQ e he hφ (hX X)).1⟩
  tfae_have 2 → 1 := fun ⟨_, hφ⟩ ↦
    exists_isAlmostSplit_of_bijective_stablePairing hQ hA (hB A) hφ
  tfae_have 3 → 1 := fun ⟨_, hφ⟩ ↦
    exists_isAlmostSplit_of_bijective_costablePairing hQ hT (hB A) hφ
  tfae_finish

end Duality

end ExactStructure

end TauCeti
