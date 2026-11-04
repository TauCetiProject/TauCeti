/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.AdicSpace.Pullback.Affinoid
import Mathlib.NumberTheory.Padics.PadicNumbers
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StronglyNoetherian
import TauCeti.RingTheory.Huber.Padic.Field
import TauCeti.RingTheory.Huber.Prod
import TauCeti.RingTheory.Huber.Restricted.Noetherian
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Complete
import TauCeti.RingTheory.Huber.WeightedEval.OpenMapping

/-!
# Checks for fibre products of affinoid adic spaces

Concrete checks for `TauCeti.AdicSpace.affinoid_isPullback` and its stably sheafy and
completed-pushout companions:

1. **Relative `p`-adic polydiscs**: for any prime `p` and `m, n : ℕ`, the completed tensor product
   of `ℚ_[p]⟨X₁, …, Xₘ⟩` and `ℚ_[p]⟨Y₁, …, Yₙ⟩` over `ℚ_[p]` gives an unconditional pullback
   square in `AdicSpace.{0}` whose projections are adic and locally of weakly finite type.
2. **Split two-adic self-product separating ordered sheets**: `ℚ_[2] × ℚ_[2]` is topologically of
   finite type over `ℚ_[2]`, so its self-product over `Spa(ℚ_[2], ℤ_[2])` is an unconditional
   pullback in `AdicSpace.{0}` with two distinct points lifting the two ordered pairs of sheets.
3. **Identity base change**: for any morphism `f : (A, A⁺) → (B, B⁺)` of complete Hausdorff sheafy
   Huber pairs (not necessarily adic), pulling `f` back along `𝟙` gives a pullback square in
   `AdicSpace`.
4. **Empty factor**: pulling back along a morphism into a complete Hausdorff zero Huber pair gives
   an empty pullback adic space.
-/

open CategoryTheory TauCeti TauCeti.Huber TauCeti.PreAdicSpace TauCeti.ValuationSpectrum
  TauCeti.AdicSpace

namespace AffinoidPullbackChecks

universe u

/-- **Relative `p`-adic polydiscs**: `Spa(ℚ_[p]⟨X₁, …, Xₘ⟩) ×_{Spa ℚ_[p]} Spa(ℚ_[p]⟨Y₁, …, Yₙ⟩)`
is unconditionally a pullback in `AdicSpace.{0}`, with projections that are adic and locally of
weakly finite type. -/
example (p : ℕ) [Fact p.Prime] (m n : ℕ) :
    let S := Pair.powerBounded ℚ_[p]
    let T := Pair.powerBounded (restrictedMvPowerSeriesCompletion m ℚ_[p])
    let U := Pair.powerBounded (restrictedMvPowerSeriesCompletion n ℚ_[p])
    have hm := (isStrictlyTopologicallyFiniteType_algebraMap (A := ℚ_[p]) m)
      |>.isTopologicallyFiniteType
    have hn := (isStrictlyTopologicallyFiniteType_algebraMap (A := ℚ_[p]) n)
      |>.isTopologicallyFiniteType
    haveI : IsAdicHom (algebraMap ℚ_[p] (restrictedMvPowerSeriesCompletion m ℚ_[p])) := hm.isAdicHom
    haveI : IsAdicHom (algebraMap ℚ_[p] (restrictedMvPowerSeriesCompletion n ℚ_[p])) := hn.isAdicHom
    have := hm.isTateRing
    have := hm.isStronglyNoetherian
    have := hn.isTateRing
    have := hn.isStronglyNoetherian
    let f : S.Hom T :=
      { toRingHom := algebraMap ℚ_[p] _
        continuous_toRingHom := continuous_algebraMap_restrictedMvPowerSeriesCompletion m ℚ_[p]
        map_mem_plus _ ha := by
          rw [Pair.powerBounded_plus] at ha ⊢
          exact mem_powerBoundedSubring.mpr <| (mem_powerBoundedSubring.mp ha).map_of_isTateRing
            (continuous_algebraMap_restrictedMvPowerSeriesCompletion m ℚ_[p]).continuousAt }
    let g : S.Hom U :=
      { toRingHom := algebraMap ℚ_[p] _
        continuous_toRingHom := continuous_algebraMap_restrictedMvPowerSeriesCompletion n ℚ_[p]
        map_mem_plus _ ha := by
          rw [Pair.powerBounded_plus] at ha ⊢
          exact mem_powerBoundedSubring.mpr <| (mem_powerBoundedSubring.mp ha).map_of_isTateRing
            (continuous_algebraMap_restrictedMvPowerSeriesCompletion n ℚ_[p]).continuousAt }
    let hS := isSheafyForEveryPresentation_of_isStronglyNoetherian S.isRingOfIntegralElements
    let hT := isSheafyForEveryPresentation_of_isStronglyNoetherian T.isRingOfIntegralElements
    let hU := isSheafyForEveryPresentation_of_isStronglyNoetherian U.isRingOfIntegralElements
    let hTU := isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_left
      T U isStablySheafyRing_of_isStronglyNoetherian hn
    IsPullback
      (comapOfPair hT hTU (Pair.completedTensor.inl ℚ_[p] T U))
      (comapOfPair hU hTU (Pair.completedTensor.inr ℚ_[p] T U))
      (comapOfPair hS hT f) (comapOfPair hS hU g) ∧
    LocallyOfWeaklyFiniteType (comapOfPair hT hTU (Pair.completedTensor.inl ℚ_[p] T U)) ∧
    LocallyOfWeaklyFiniteType (comapOfPair hU hTU (Pair.completedTensor.inr ℚ_[p] T U)) := by
  intro S T U hm hn _ _ _ _ f g hS hT hU hTU
  have := hm.isAdicHom
  have := hn.isAdicHom
  exact ⟨affinoid_isPullback_of_isStablySheafyRing_left hS hU
      isStablySheafyRing_of_isStronglyNoetherian hn f g rfl rfl,
    locallyOfWeaklyFiniteType_comapOfPair_completedTensor_inl hT hTU hn,
    locallyOfWeaklyFiniteType_comapOfPair_completedTensor_inr hU hTU hm⟩

/-- **Split two-adic self-product**: `Spa(ℚ_[2] × ℚ_[2]) ×_{Spa ℚ_[2]} Spa(ℚ_[2] × ℚ_[2])` is an
unconditional pullback in `AdicSpace.{0}` and contains two distinct points whose first projections
distinguish the two sheets of `ℚ_[2] × ℚ_[2]`. -/
example :
    have hcont : Continuous (algebraMap ℚ_[2] (ℚ_[2] × ℚ_[2])) := by fun_prop
    haveI : IsAdicHom (algebraMap ℚ_[2] (ℚ_[2] × ℚ_[2])) := IsAdicHom.of_isTateRing hcont
    have htft : IsTopologicallyFiniteType (algebraMap ℚ_[2] (ℚ_[2] × ℚ_[2])) := by
      set b : Fin 2 → ℚ_[2] × ℚ_[2] := ![(1, 0), (0, 1)]
      have hb : IsWeightBounded (algebraMap ℚ_[2] (ℚ_[2] × ℚ_[2])) (fun _ ↦ {1}) b :=
        (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun i ↦ by
          fin_cases i <;> simp [b]
      have hspan : Submodule.span ℚ_[2] (Set.range b) = ⊤ := by
        rw [eq_top_iff]
        rintro ⟨x, y⟩ -
        have hxy : (x, y) = x • b 0 + y • b 1 := by ext <;> simp [b]
        rw [hxy]
        exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
      refine isTopologicallyFiniteType_iff.mpr
        ⟨2, fun _ ↦ {1}, fun _ ↦ Set.finite_singleton 1, isWeightFamily_one_weight,
          weightedEvalHomCompletion isWeightFamily_one_weight hcont.continuousAt hb,
          isOpenQuotientMap_weightedEvalHomCompletion hcont isWeightFamily_one_weight hb hspan,
          RingHom.ext fun a ↦ ?_⟩
      rw [RingHom.comp_apply, algebraMap_completion_weightedRestrictedSubring_apply,
        weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]
    let S := Pair.powerBounded ℚ_[2]
    let T := Pair.powerBounded (ℚ_[2] × ℚ_[2])
    let f : S.Hom T :=
      { toRingHom := algebraMap ℚ_[2] (ℚ_[2] × ℚ_[2])
        continuous_toRingHom := hcont
        map_mem_plus _ ha := by
          rw [Pair.powerBounded_plus] at ha ⊢
          exact mem_powerBoundedSubring.mpr <|
            (mem_powerBoundedSubring.mp ha).map_of_isTateRing hcont.continuousAt }
    let hS := isSheafyForEveryPresentation_of_isStronglyNoetherian S.isRingOfIntegralElements
    have := htft.isStronglyNoetherian
    let hB : IsStablySheafyRing (ℚ_[2] × ℚ_[2]) := isStablySheafyRing_of_isStronglyNoetherian
    let hT := hB.isSheafyRing.isSheafyForEveryPresentation T.isRingOfIntegralElements
    let hTT := isSheafyForEveryPresentation_completedTensor_of_isStablySheafyRing_left
      T T hB htft
    IsPullback
      (comapOfPair hT hTT (Pair.completedTensor.inl ℚ_[2] T T))
      (comapOfPair hT hTT (Pair.completedTensor.inr ℚ_[2] T T))
      (comapOfPair hS hT f) (comapOfPair hS hT f) ∧
    ∃ z₁ z₂ : (ofPair (T.completedTensor ℚ_[2] T) hTT).obj, z₁ ≠ z₂ := by
  intro hcont htft S T f hS _ hB hT hTT
  have : IsAdicHom (algebraMap ℚ_[2] (ℚ_[2] × ℚ_[2])) := htft.isAdicHom
  refine ⟨affinoid_isPullback_of_isStablySheafyRing_left hS hT hB htft f f rfl rfl, ?_⟩
  have hne : (spa S.plus).Nonempty := Set.nonempty_iff_ne_empty.mpr fun h ↦
    not_subsingleton ℚ_[2] ((spa_eq_empty_iff_subsingleton _ S.isRingOfIntegralElements).mp h)
  let x₀ : spa S.plus := ⟨hne.some, hne.some_mem⟩
  let p₁ : Pair.Hom T S :=
    { toRingHom := RingHom.fst _ _
      continuous_toRingHom := continuous_fst
      map_mem_plus a ha := by
        rw [Pair.powerBounded_plus] at ha ⊢
        rw [powerBoundedSubring_prod] at ha
        exact ha.1 }
  let p₂ : Pair.Hom T S :=
    { toRingHom := RingHom.snd _ _
      continuous_toRingHom := continuous_snd
      map_mem_plus a ha := by
        rw [Pair.powerBounded_plus] at ha ⊢
        rw [powerBoundedSubring_prod] at ha
        exact ha.2 }
  let y₁ : (ofPair T hT).obj := (ofPairHomeomorph T hT).symm (p₁.spaComap x₀)
  let y₂ : (ofPair T hT).obj := (ofPairHomeomorph T hT).symm (p₂.spaComap x₀)
  have hy₁ : (comapOfPair hS hT f).hom.base y₁ = (ofPairHomeomorph S hS).symm x₀ := by
    rw [comapOfPair_base_ofPairHomeomorph_symm]
    have hcomp : p₁.comp f = Pair.Hom.id S := by ext; simp [p₁, f]
    have hc := congrFun (Pair.Hom.spaComap_comp p₁ f) x₀
    rw [Function.comp_apply, hcomp, Pair.Hom.spaComap_id] at hc
    rw [← hc]
    rfl
  have hy₂ : (comapOfPair hS hT f).hom.base y₂ = (ofPairHomeomorph S hS).symm x₀ := by
    rw [comapOfPair_base_ofPairHomeomorph_symm]
    have hcomp : p₂.comp f = Pair.Hom.id S := by ext; simp [p₂, f]
    have hc := congrFun (Pair.Hom.spaComap_comp p₂ f) x₀
    rw [Function.comp_apply, hcomp, Pair.Hom.spaComap_id] at hc
    rw [← hc]
    rfl
  obtain ⟨z₁, hz₁, -⟩ := exists_ofPair_completedTensor_point hS hT hT hTT f f rfl rfl
    y₁ y₂ (hy₁.trans hy₂.symm)
  obtain ⟨z₂, hz₂, -⟩ := exists_ofPair_completedTensor_point hS hT hT hTT f f rfl rfl
    y₂ y₁ (hy₂.trans hy₁.symm)
  refine ⟨z₁, z₂, fun h ↦ ?_⟩
  have hyeq : y₁ = y₂ := by rw [← hz₁, h, hz₂]
  have hspv : (p₁.spaComap x₀).1 = (p₂.spaComap x₀).1 :=
    congrArg Subtype.val ((ofPairHomeomorph T hT).symm.injective hyeq)
  have hvle : (p₁.spaComap x₀).1.toValuativeRel.vle ((0, 1) : ℚ_[2] × ℚ_[2]) 0 := by
    rw [Pair.Hom.spaComap_val, comap_vle]
    simp [p₁]
  rw [hspv, Pair.Hom.spaComap_val, comap_vle] at hvle
  simp [p₂] at hvle

/-- **Identity base change**: pulling any morphism of complete Hausdorff sheafy Huber pairs back
along the identity yields a pullback square in `AdicSpace`, with no adicness assumption on `f`. -/
example {A B : Type u}
    [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T0Space A] [IsHuberRing A]
    [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T0Space B] [IsHuberRing B]
    {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus)
    (hT : IsSheafyForEveryPresentation T.plus)
    (f : Pair.Hom S T) :
    IsPullback (comapOfPair hT hT (Pair.Hom.id T)) (comapOfPair hS hT f)
      (comapOfPair hS hT f) (comapOfPair hS hS (Pair.Hom.id S)) :=
  isPullback_ofPair_of_isCompletedPushout hS hT hS hT
    { condition := by simp
      existsUnique_desc := fun _ _ _ _ _ _ _ _ _ a _ hab ↦
        ⟨a, ⟨by simp, by simpa using hab⟩, fun _ ⟨hχ, _⟩ ↦ by simpa using hχ⟩ }

/-- **Empty factor**: pulling back along a morphism into a complete Hausdorff subsingleton Huber
pair yields a pullback square in `AdicSpace` with empty underlying space. -/
example {A B C : Type u}
    [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T0Space A] [IsHuberRing A]
    [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T0Space B] [IsHuberRing B]
    [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [CompleteSpace C] [T0Space C] [IsHuberRing C] [Subsingleton C]
    {S : Pair A} {T : Pair B} {U : Pair C}
    (hS : IsSheafyForEveryPresentation S.plus)
    (hT : IsSheafyForEveryPresentation T.plus)
    (hU : IsSheafyForEveryPresentation U.plus)
    (f : Pair.Hom S T) (g : Pair.Hom S U) (i : Pair.Hom T U) :
    IsPullback (comapOfPair hT hU i) (comapOfPair hU hU (Pair.Hom.id U))
      (comapOfPair hS hT f) (comapOfPair hS hU g) ∧
    IsEmpty (ofPair U hU).obj := by
  refine ⟨isPullback_ofPair_of_isCompletedPushout hS hT hU hU
    { condition := by ext; exact Subsingleton.elim _ _
      existsUnique_desc := fun _ _ _ _ _ _ _ _ _ _ b _ ↦ by
        have := b.toRingHom.codomain_trivial
        exact ⟨b, ⟨by ext; exact Subsingleton.elim _ _, by simp⟩,
          fun _ ⟨_, hχ⟩ ↦ by simpa using hχ⟩ }, ⟨fun z ↦ ?_⟩⟩
  have hz : spa U.plus = ∅ :=
    (spa_eq_empty_iff_subsingleton U.plus U.isRingOfIntegralElements).mpr inferInstance
  obtain ⟨v, hm⟩ := ofPairHomeomorph U hU z
  rw [hz] at hm
  exact hm

end AffinoidPullbackChecks
