/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.RatLoc
import TauCeti.RingTheory.Huber.LocalizationTopology.Evaluation
import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction
import TauCeti.RingTheory.Huber.LocalizationTopology.Trivial
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Laurent.Basic

/-!
# Models of the completed rational localisation `A⟨T/s⟩`

`TauCeti.Huber.ratLoc` fixes one canonical carrier for the completed rational localisation
`A⟨T/s⟩`. In practice callers work with arbitrary topological `A`-algebras `B` (such as `A` itself
at denominator `1`, a Tate algebra `A⟨X⟩`, or a limit over presentations) that are *isomorphic as
topological `A`-algebras* to `A⟨T/s⟩`.

This file defines `TauCeti.Huber.IsRationalCompletion P T s hT B`, proves its invariance under
pair-of-definition changes and bicontinuous `A`-algebra equivalences, transfers the structural and
universal properties of `ratLoc`, and establishes Kedlaya–Liu's surjectivity lemma for the
difference map on a two-piece simple Laurent cover (`IsRationalCompletion.surjective_sub_laurent`,
Kedlaya–Liu, Lemma 2.4.22).

## Main definitions

* `TauCeti.Huber.IsRationalCompletion P T s hT B`: `B` is isomorphic as a topological `A`-algebra
  to the completed rational localisation `A⟨T/s⟩`.

## Main results

* `TauCeti.Huber.isRationalCompletion_iff_ratLoc`, `TauCeti.Huber.isRationalCompletion_ratLoc`, and
  `TauCeti.Huber.IsRationalCompletion.congr_pairOfDefinition`: comparison with `ratLoc` and
  independence of the pair of definition `P`.
* `TauCeti.Huber.IsRationalCompletion.ringHom_ext_of_continuous`,
  `TauCeti.Huber.IsRationalCompletion.existsUnique_continuous_algHom`,
  `TauCeti.Huber.IsRationalCompletion.existsUnique_continuous_algHom_of_refines`, and
  `TauCeti.Huber.IsRationalCompletion.denseRange_of_comp_algebraMap_eq`: uniqueness, universal
  property, functoriality along refinements, and density at a shared denominator.
* `TauCeti.Huber.isRationalCompletion_self_denom_one` and
  `TauCeti.Huber.IsRationalCompletion.subsingleton_of_denom_zero`: behaviour at denominators `1`
  and `0`.
* `TauCeti.Huber.IsRationalCompletion.existsUnique_laurentLeftAlgHom`,
  `TauCeti.Huber.IsRationalCompletion.existsUnique_laurentRightAlgHom`, and
  `TauCeti.Huber.IsRationalCompletion.surjective_sub_laurent`: transition maps and surjectivity of
  `(b₁, b₂) ↦ ρ₁ b₁ - ρ₂ b₂` on a simple Laurent cover.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.4, Lemma 2.4.22.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], §8.1–8.2.
-/

public section

namespace TauCeti.Huber

open UniformSpace TauCeti.Localization

section Basic

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- `B` is a model of the completed rational localisation `A⟨T/s⟩` for the pair of definition `P`:
there is a bicontinuous `A`-algebra isomorphism from `ratLoc P T s _` onto `B`. -/
def IsRationalCompletion (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (B : Type*) [CommRing B] [TopologicalSpace B] [Algebra A B] : Prop :=
  ∃ e : ratLoc P T s (P.hasDenominatorPower_of_isOpen_span T s _ hT) ≃ₐ[A] B,
    Continuous e ∧ Continuous e.symm

/-- `IsRationalCompletion` is equivalent to the existence of a bicontinuous `A`-algebra equivalence
from `ratLoc P T s _`. -/
theorem isRationalCompletion_iff_ratLoc (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (B : Type*) [CommRing B] [TopologicalSpace B] [Algebra A B] :
    IsRationalCompletion P T s hT B ↔
      ∃ e : ratLoc P T s (P.hasDenominatorPower_of_isOpen_span T s _ hT) ≃ₐ[A] B,
        Continuous e ∧ Continuous e.symm :=
  Iff.rfl

/-- Unfolding `IsRationalCompletion` directly in terms of `Completion (Localization.Away s)`. -/
theorem isRationalCompletion_def (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (B : Type*) [CommRing B] [TopologicalSpace B] [Algebra A B] :
    IsRationalCompletion P T s hT B ↔
      let S := Localization.Away s
      let hden := P.hasDenominatorPower_of_isOpen_span T s S hT
      letI := P.locUniformSpace T s S hden
      letI := P.isUniformAddGroup_locUniformSpace T s S hden
      letI := P.isTopologicalRing_locUniformSpace T s S hden
      ∃ e : Completion S ≃+* B, Continuous e ∧ Continuous e.symm ∧
        e.toRingHom.comp (P.toCompletionLoc T s S hden) = algebraMap A B := by
  refine ⟨fun ⟨e, he, he'⟩ ↦ ⟨e.toRingEquiv, he, he', RingHom.ext fun a ↦ by
    simpa [algebraMap_ratLoc] using e.commutes a⟩, fun ⟨e, he, he', hcomp⟩ ↦
      ⟨AlgEquiv.ofRingEquiv (f := e) fun a ↦ by
        rw [algebraMap_ratLoc]; exact congrArg (· a) hcomp, he, he'⟩⟩

/-- The canonical completed rational localisation `ratLoc` is a model of `A⟨T/s⟩`. -/
theorem isRationalCompletion_ratLoc (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) :
    IsRationalCompletion P T s hT
      (ratLoc P T s (P.hasDenominatorPower_of_isOpen_span T s _ hT)) :=
  ⟨AlgEquiv.refl, continuous_id, continuous_id⟩

/-- `IsRationalCompletion` is independent of the chosen pair of definition `P`. -/
theorem IsRationalCompletion.congr_pairOfDefinition {P : PairOfDefinition A} {T : Finset A}
    {s : A} {hT : IsOpen (Ideal.span (T : Set A) : Set A)}
    {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra A B]
    (h : IsRationalCompletion P T s hT B) (P' : PairOfDefinition A) :
    IsRationalCompletion P' T s hT B := by
  rw [isRationalCompletion_def] at h ⊢
  let S := Localization.Away s
  have hden := P.hasDenominatorPower_of_isOpen_span T s S hT
  have hden' := P'.hasDenominatorPower_of_isOpen_span T s S hT
  have hu := PairOfDefinition.locUniformSpace_congr_pairOfDefinition P P' T s S hden hden'
  have hto := PairOfDefinition.toCompletionLoc_heq_pairOfDefinition P P' T s S hden hden'
  let F (u : UniformSpace S) (_ : @IsUniformAddGroup S u _)
      (_ : @IsTopologicalRing S u.toTopologicalSpace _) (φ : A →+* @Completion S u) : Prop :=
    ∃ e : Completion S ≃+* B, Continuous e ∧ Continuous e.symm ∧ e.toRingHom.comp φ = algebraMap A B
  have hF : F (P.locUniformSpace T s S hden) (P.isUniformAddGroup_locUniformSpace T s S hden)
        (P.isTopologicalRing_locUniformSpace T s S hden) (P.toCompletionLoc T s S hden) =
      F (P'.locUniformSpace T s S hden') (P'.isUniformAddGroup_locUniformSpace T s S hden')
        (P'.isTopologicalRing_locUniformSpace T s S hden') (P'.toCompletionLoc T s S hden') := by
    congr!
  exact hF.mp h

/-- Equivalence form of `IsRationalCompletion.congr_pairOfDefinition`. -/
theorem isRationalCompletion_congr_pairOfDefinition (P P' : PairOfDefinition A) (T : Finset A)
    (s : A) (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (B : Type*) [CommRing B] [TopologicalSpace B] [Algebra A B] :
    IsRationalCompletion P T s hT B ↔ IsRationalCompletion P' T s hT B :=
  ⟨fun h ↦ h.congr_pairOfDefinition P', fun h ↦ h.congr_pairOfDefinition P⟩

/-- `IsRationalCompletion` transfers along any bicontinuous `A`-algebra equivalence. -/
theorem IsRationalCompletion.of_algEquiv {P : PairOfDefinition A} {T : Finset A} {s : A}
    {hT : IsOpen (Ideal.span (T : Set A) : Set A)}
    {B B' : Type*} [CommRing B] [TopologicalSpace B] [Algebra A B]
    [CommRing B'] [TopologicalSpace B'] [Algebra A B']
    (h : IsRationalCompletion P T s hT B) (e : B ≃ₐ[A] B')
    (he : Continuous e) (he' : Continuous e.symm) :
    IsRationalCompletion P T s hT B' :=
  let ⟨f, hf, hf'⟩ := h
  ⟨f.trans e, he.comp hf, hf'.comp he'⟩

section ModelProperties

variable {P : PairOfDefinition A} {T : Finset A} {s : A}
  {hT : IsOpen (Ideal.span (T : Set A) : Set A)}
  {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra A B]

/-- The structure map `A → B` into a rational completion is continuous. -/
theorem IsRationalCompletion.continuous_algebraMap (h : IsRationalCompletion P T s hT B) :
    Continuous (algebraMap A B) := by
  obtain ⟨e, he, -⟩ := h
  exact (he.comp (continuous_algebraMap_ratLoc P T s _)).congr e.commutes

/-- The denominator `s` becomes a unit in any model of `A⟨T/s⟩`. -/
theorem IsRationalCompletion.isUnit_algebraMap (h : IsRationalCompletion P T s hT B) :
    IsUnit (algebraMap A B s) := by
  obtain ⟨e, -, -⟩ := h
  simpa [e.commutes s] using (isUnit_algebraMap_ratLoc P T s _).map e.toRingHom

/-- Any model of `A⟨T/s⟩` is Hausdorff. -/
theorem IsRationalCompletion.t2Space (h : IsRationalCompletion P T s hT B) : T2Space B := by
  obtain ⟨e, -, he'⟩ := h
  exact .of_injective_continuous e.symm.injective he'

/-- Any topological-ring model of `A⟨T/s⟩` is a Huber ring. -/
theorem IsRationalCompletion.isHuberRing [IsTopologicalRing B]
    (h : IsRationalCompletion P T s hT B) : IsHuberRing B := by
  obtain ⟨e, he, he'⟩ := h
  exact IsHuberRing.of_isOpenQuotientMap (f := e.toRingHom)
    (Homeomorph.mk e.toEquiv he he').isOpenQuotientMap

/-- Over a Tate ring `A`, any topological-ring model of `A⟨T/s⟩` is a Tate ring. -/
theorem IsRationalCompletion.isTateRing [IsTateRing A] [IsTopologicalRing B]
    (h : IsRationalCompletion P T s hT B) : IsTateRing B := by
  have := h.isHuberRing
  exact IsTateRing.of_continuous h.continuous_algebraMap

/-- Two continuous ring homomorphisms out of a model of `A⟨T/s⟩` into a Hausdorff semiring that
agree after `algebraMap A B` are equal. -/
theorem IsRationalCompletion.ringHom_ext_of_continuous (h : IsRationalCompletion P T s hT B)
    {C : Type*} [Semiring C] [TopologicalSpace C] [T2Space C]
    {f g : B →+* C} (hf : Continuous f) (hg : Continuous g)
    (hfg : f.comp (algebraMap A B) = g.comp (algebraMap A B)) : f = g := by
  obtain ⟨e, he, -⟩ := h
  have hfe := P.completion_locTopology_ringHom_ext_of_continuous T s (Localization.Away s)
    (P.hasDenominatorPower_of_isOpen_span T s _ hT) (f.comp e.toRingHom) (g.comp e.toRingHom)
    (hf.comp he) (hg.comp he) (RingHom.ext fun a ↦ by
      change f (e (P.toCompletionLoc T s _ _ a)) = g (e (P.toCompletionLoc T s _ _ a))
      rw [← algebraMap_ratLoc, e.commutes]
      exact congrArg (· a) hfg)
  exact RingHom.ext fun x ↦ by simpa using congrArg (· (e.symm x)) hfe

/-- Two continuous `A`-algebra homomorphisms out of a model of `A⟨T/s⟩` into a Hausdorff
`A`-algebra are equal. -/
theorem IsRationalCompletion.algHom_ext_of_continuous (h : IsRationalCompletion P T s hT B)
    {C : Type*} [CommSemiring C] [TopologicalSpace C] [T2Space C] [Algebra A C]
    {f g : B →ₐ[A] C} (hf : Continuous f) (hg : Continuous g) : f = g :=
  AlgHom.toRingHom_injective <| h.ringHom_ext_of_continuous hf hg
    (RingHom.ext fun a ↦ (f.commutes a).trans (g.commutes a).symm)

/-- **Universal property of a model of `A⟨T/s⟩`.** If `C` is a complete Hausdorff nonarchimedean
`A`-algebra whose structure map `A → C` is continuous at zero, sends `s` to a unit, and makes each
fraction `t / s` (`t ∈ T`) power-bounded, then there is a unique continuous `A`-algebra
homomorphism `B →ₐ[A] C`. -/
theorem IsRationalCompletion.existsUnique_continuous_algHom (h : IsRationalCompletion P T s hT B)
    {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [NonarchimedeanRing C]
    [CompleteSpace C] [T0Space C] [Algebra A C]
    (hc : ContinuousAt (algebraMap A C) 0) (hs : IsUnit (algebraMap A C s))
    (hpow : ∀ t ∈ T, IsPowerBounded (algebraMap A C t * ↑hs.unit⁻¹)) :
    ∃! g : B →ₐ[A] C, Continuous g := by
  let hden := P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
  obtain ⟨e, -, he'⟩ := id h
  obtain ⟨f, ⟨hf_cont, hf_eq⟩, -⟩ :=
    P.existsUnique_continuous_ringHom_completion_locTopology T s (Localization.Away s) hden
      hc hs hpow
  refine ⟨⟨f.comp e.symm.toRingHom, fun a ↦ ?_⟩, hf_cont.comp he', fun g hg ↦
    h.algHom_ext_of_continuous hg (hf_cont.comp he')⟩
  change f (e.symm (algebraMap A B a)) = algebraMap A C a
  rw [e.symm.commutes, algebraMap_ratLoc]
  exact congrArg (· a) hf_eq

/-- **Functoriality of models along refining rational presentations.** If `s' = s * r` and every
`t ∈ T` satisfies either `t = s` (so `t / s = 1`) or `t * r ∈ T'` (so `t / s = (t * r) / s'` is a
distinguished fraction of `A⟨T'/s'⟩`), then there is a unique continuous `A`-algebra homomorphism
`B →ₐ[A] B'` between any models of `A⟨T/s⟩` and `A⟨T'/s'⟩`. -/
theorem IsRationalCompletion.existsUnique_continuous_algHom_of_refines
    (h : IsRationalCompletion P T s hT B)
    {T' : Finset A} {s' r : A} {hT' : IsOpen (Ideal.span (T' : Set A) : Set A)}
    {B' : Type*} [CommRing B'] [TopologicalSpace B'] [Algebra A B']
    (h' : IsRationalCompletion P T' s' hT' B')
    (hs' : s' = s * r) (hTT' : ∀ t ∈ T, t = s ∨ t * r ∈ T') :
    ∃! ρ : B →ₐ[A] B', Continuous ρ := by
  let hden' := P.hasDenominatorPower_of_isOpen_span T' s' (Localization.Away s') hT'
  obtain ⟨e', he', -⟩ := id h'
  have hu₀ := P.isUnit_toCompletionLoc_of_dvd T' s' _ hden' ⟨r, hs'⟩
  have hu : IsUnit (algebraMap A (ratLoc P T' s' hden') s) := by rwa [algebraMap_ratLoc]
  have hpow : ∀ t ∈ T, IsPowerBounded (algebraMap A (ratLoc P T' s' hden') t * ↑hu.unit⁻¹) := by
    intro t ht
    rcases hTT' t ht with rfl | ht'
    · rw [IsUnit.mul_val_inv]; exact isPowerBounded_one
    · have hinv : (↑hu.unit⁻¹ : ratLoc P T' s' hden') = ↑hu₀.unit⁻¹ :=
        congrArg (fun u : (ratLoc P T' s' hden')ˣ ↦ (↑u⁻¹ : ratLoc P T' s' hden'))
          (Units.ext (by simp [algebraMap_ratLoc]))
      rw [hinv, algebraMap_ratLoc]
      exact P.isPowerBounded_toCompletionLoc_mul_unit_inv T' s' _ hden' hs' hu₀
        (Finset.mem_coe.mpr ht')
  obtain ⟨g, hg, -⟩ := h.existsUnique_continuous_algHom
    (continuous_algebraMap_ratLoc P T' s' hden').continuousAt hu hpow
  have _ : T2Space B' := h'.t2Space
  exact ⟨e'.toAlgHom.comp g, he'.comp hg, fun f hf ↦ h.algHom_ext_of_continuous hf (he'.comp hg)⟩

/-- Any ring homomorphism compatible with the `A`-algebra maps between two rational completions at
the *same* denominator `s` has dense range, because its range contains the canonical dense image of
`Localization.Away s`. -/
theorem IsRationalCompletion.denseRange_of_comp_algebraMap_eq
    (hB : IsRationalCompletion P T s hT B)
    {T' : Finset A} {hT' : IsOpen (Ideal.span (T' : Set A) : Set A)}
    {C : Type*} [CommRing C] [TopologicalSpace C] [Algebra A C]
    (hC : IsRationalCompletion P T' s hT' C)
    {φ : B →+* C} (hφ : φ.comp (algebraMap A B) = algebraMap A C) :
    DenseRange φ := by
  let S := Localization.Away s
  let hdenB := P.hasDenominatorPower_of_isOpen_span T s S hT
  let hdenC := P.hasDenominatorPower_of_isOpen_span T' s S hT'
  obtain ⟨eB, -, -⟩ := hB
  obtain ⟨eC, heC, -⟩ := hC
  let f₁ : S →+* C :=
    letI := P.locUniformSpace T s S hdenB
    letI := P.isUniformAddGroup_locUniformSpace T s S hdenB
    letI := P.isTopologicalRing_locUniformSpace T s S hdenB
    φ.comp (eB.toRingHom.comp Completion.coeRingHom)
  let f₂ : S →+* C :=
    letI := P.locUniformSpace T' s S hdenC
    letI := P.isUniformAddGroup_locUniformSpace T' s S hdenC
    letI := P.isTopologicalRing_locUniformSpace T' s S hdenC
    eC.toRingHom.comp Completion.coeRingHom
  have heqS : f₁ = f₂ := IsLocalization.ringHom_ext (Submonoid.powers s) <| RingHom.ext fun a ↦ by
    have hb : f₁ (algebraMap A S a) = φ (algebraMap A B a) := by
      let _ := P.locUniformSpace T s S hdenB
      have _ := P.isUniformAddGroup_locUniformSpace T s S hdenB
      have _ := P.isTopologicalRing_locUniformSpace T s S hdenB
      change φ (eB (algebraMap A S a : Completion S)) = φ (algebraMap A B a)
      rw [← P.toCompletionLoc_apply T s S hdenB a, ← algebraMap_ratLoc, eB.commutes]
    have hc : f₂ (algebraMap A S a) = algebraMap A C a := by
      let _ := P.locUniformSpace T' s S hdenC
      have _ := P.isUniformAddGroup_locUniformSpace T' s S hdenC
      have _ := P.isTopologicalRing_locUniformSpace T' s S hdenC
      change eC (algebraMap A S a : Completion S) = algebraMap A C a
      rw [← P.toCompletionLoc_apply T' s S hdenC a, ← algebraMap_ratLoc, eC.commutes]
    simpa only [RingHom.comp_apply, hb, hc] using congrArg (· a) hφ
  have hdense₂ : DenseRange f₂ := by
    let _ := P.locUniformSpace T' s S hdenC
    exact eC.surjective.denseRange.comp Completion.denseRange_coe heC
  exact hdense₂.mono fun _ h ↦ by rcases h with ⟨x, rfl⟩; rw [← heqS]; exact ⟨_, rfl⟩

end ModelProperties

section SpecialDenominators

/-- At denominator `0`, any model of `A⟨T/0⟩` is a subsingleton, since `Localization.Away (0 : A)`
is already trivial. -/
theorem IsRationalCompletion.subsingleton_of_denom_zero {P : PairOfDefinition A} {T : Finset A}
    {hT : IsOpen (Ideal.span (T : Set A) : Set A)}
    {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra A B]
    (h : IsRationalCompletion P T 0 hT B) : Subsingleton B := by
  obtain ⟨u, hu⟩ : IsUnit (0 : B) := by simpa using h.isUnit_algebraMap
  exact subsingleton_of_zero_eq_one (by rw [← u.mul_inv, hu, zero_mul])

/-- Conversely, every subsingleton `A`-algebra is a model of `A⟨T/0⟩`. -/
theorem isRationalCompletion_of_subsingleton_denom_zero (P : PairOfDefinition A) (T : Finset A)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (B : Type*) [CommRing B] [TopologicalSpace B] [Algebra A B] [Subsingleton B] :
    IsRationalCompletion P T 0 hT B := by
  have _ := (isRationalCompletion_ratLoc P T 0 hT).subsingleton_of_denom_zero
  exact ⟨{ toFun := fun _ ↦ 0, invFun := fun _ ↦ 0,
           left_inv := fun _ ↦ Subsingleton.elim _ _, right_inv := fun _ ↦ Subsingleton.elim _ _,
           map_mul' := fun _ _ ↦ Subsingleton.elim _ _, map_add' := fun _ _ ↦ Subsingleton.elim _ _,
           commutes' := fun _ ↦ Subsingleton.elim _ _ },
    continuous_const, continuous_const⟩

end SpecialDenominators

end Basic

section Uniform

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]

/-- At denominator `1`, a complete Hausdorff Huber ring `A` is itself a model of `A⟨T/1⟩` whenever
every numerator in `T` is power-bounded. -/
theorem isRationalCompletion_self_denom_one [CompleteSpace A] [T0Space A]
    (P : PairOfDefinition A) (T : Finset A)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (hTpb : ∀ t ∈ T, IsPowerBounded t) :
    IsRationalCompletion P T 1 hT A := by
  rw [isRationalCompletion_def]
  let S := Localization.Away (1 : A)
  let hden := P.hasDenominatorPower_of_isOpen_span T 1 S hT
  let _ := P.locUniformSpace T 1 S hden
  have _ := P.isUniformAddGroup_locUniformSpace T 1 S hden
  have _ := P.isTopologicalRing_locUniformSpace T 1 S hden
  let e := P.toCompletionLocEquivDenomOne T hTpb S
  have he : Continuous e := (P.continuous_toCompletionLoc T 1 S hden).congr fun a ↦
    (P.toCompletionLocEquivDenomOne_apply T hTpb S a).symm
  refine ⟨e.symm, P.continuous_toCompletionLocEquivDenomOne_symm T hTpb S, he,
    RingHom.ext fun a ↦ ?_⟩
  change e.symm (P.toCompletionLoc T 1 S hden a) = a
  rw [← P.toCompletionLocEquivDenomOne_apply T hTpb S a, e.symm_apply_apply]

/-! ### Surjectivity of the difference map on a simple Laurent cover -/

section SimpleLaurent

variable [CompleteSpace A] [T0Space A]

section ModelEval

variable (P : PairOfDefinition A) {T : Finset A} {s : A}
  (hT : IsOpen (Ideal.span (T : Set A) : Set A))
  {B : Type*} [CommRing B] [Algebra A B]
  (e : ratLoc P T s (P.hasDenominatorPower_of_isOpen_span T s _ hT) ≃ₐ[A] B)
  {k : ℕ} (t : Fin k → A) (ht : ∀ i, t i ∈ T)

/-- Evaluation `A⟨X₁, …, Xₖ⟩ → B` from the uncompleted restricted power series ring into a model
`B` of `A⟨T/s⟩`. -/
private noncomputable def modelEvalHom :
    letI := P.toNonarchimedeanRing
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →+* B :=
  letI := P.toNonarchimedeanRing
  e.toRingHom.comp ((P.rationalEvalHom T s (Localization.Away s)
    (P.hasDenominatorPower_of_isOpen_span T s _ hT) t ht).comp
      (restrictedMvPowerSeriesCompletionEquiv k A).symm.toRingHom)

private theorem continuous_modelEvalHom [TopologicalSpace B] (he : Continuous e) :
    letI := P.toNonarchimedeanRing
    Continuous (modelEvalHom P hT e t ht) :=
  letI := P.toNonarchimedeanRing
  he.comp ((P.continuous_rationalEvalHom T s _ _ t ht).comp
    uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm.continuous)

private theorem modelEvalHom_weightedC (a : A) :
    letI := P.toNonarchimedeanRing
    modelEvalHom P hT e t ht
      (weightedC (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight a) =
      algebraMap A B a := by
  let _ := P.toNonarchimedeanRing
  change e (P.rationalEvalHom T s _ _ t ht
    ((restrictedMvPowerSeriesCompletionEquiv k A).symm _)) = _
  rw [restrictedMvPowerSeriesCompletionEquiv_symm_apply, P.rationalEvalHom_coe_weightedC,
    ← algebraMap_ratLoc, e.commutes]

private theorem modelEvalHom_X_eq_algebraMap_of_mul (i : Fin k) {a : A} (hti : t i = s * a) :
    letI := P.toNonarchimedeanRing
    modelEvalHom P hT e t ht
      (weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i) =
      algebraMap A B a := by
  let _ := P.toNonarchimedeanRing
  change e (P.rationalEvalHom T s _ _ t ht
    ((restrictedMvPowerSeriesCompletionEquiv k A).symm _)) = _
  rw [restrictedMvPowerSeriesCompletionEquiv_symm_apply, P.rationalEvalHom_coe_weightedX, hti,
    divBy_mul_cancel_left a s, ← P.toCompletionLoc_apply, ← algebraMap_ratLoc, e.commutes]

private theorem modelEvalHom_X_mul_inv (i : Fin k) (hti : t i = 1) :
    letI := P.toNonarchimedeanRing
    algebraMap A B s * modelEvalHom P hT e t ht
      (weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i) = 1 := by
  let _ := P.toNonarchimedeanRing
  let S := Localization.Away s
  let hden := P.hasDenominatorPower_of_isOpen_span T s S hT
  let _ := P.locUniformSpace T s S hden
  have _ := P.isUniformAddGroup_locUniformSpace T s S hden
  have _ := P.isTopologicalRing_locUniformSpace T s S hden
  change algebraMap A B s * e (P.rationalEvalHom T s S hden t ht
    ((restrictedMvPowerSeriesCompletionEquiv k A).symm _)) = 1
  rw [restrictedMvPowerSeriesCompletionEquiv_symm_apply, P.rationalEvalHom_coe_weightedX,
    ← e.commutes s, ← map_mul, algebraMap_ratLoc, P.toCompletionLoc_apply]
  change e (((algebraMap A S s : S) : Completion S) * ((divBy (t i) s : S) : Completion S)) = 1
  rw [← Completion.coe_mul, hti, divBy_one, IsLocalization.Away.mul_invSelf]
  exact map_one e

end ModelEval

private theorem comp_modelEvalHom_eq_weightedRename (P : PairOfDefinition A)
    {T₁ T₂ : Finset A} {s₁ s₂ : A}
    (hT₁ : IsOpen (Ideal.span (T₁ : Set A) : Set A))
    (hT₂ : IsOpen (Ideal.span (T₂ : Set A) : Set A))
    {B B₁₂ : Type*} [CommRing B] [TopologicalSpace B] [Algebra A B]
    [CommRing B₁₂] [TopologicalSpace B₁₂] [T2Space B₁₂] [Algebra A B₁₂]
    (e : ratLoc P T₁ s₁ (P.hasDenominatorPower_of_isOpen_span T₁ s₁ _ hT₁) ≃ₐ[A] B)
    (he : Continuous e)
    (e₁₂ : ratLoc P T₂ s₂ (P.hasDenominatorPower_of_isOpen_span T₂ s₂ _ hT₂) ≃ₐ[A] B₁₂)
    (he₁₂ : Continuous e₁₂)
    (t : Fin 1 → A) (ht : ∀ i, t i ∈ T₁) (t₁₂ : Fin 2 → A) (ht₁₂ : ∀ i, t₁₂ i ∈ T₂)
    (ρ : B →ₐ[A] B₁₂) (hc : Continuous ρ) (emb : Fin 1 ↪ Fin 2)
    (hX :
      letI := P.toNonarchimedeanRing
      ρ (modelEvalHom P hT₁ e t ht (weightedX _ isWeightFamily_one_weight 0)) =
        modelEvalHom P hT₂ e₁₂ t₁₂ ht₁₂ (weightedX _ isWeightFamily_one_weight (emb 0))) :
    letI := P.toNonarchimedeanRing
    ρ.toRingHom.comp (modelEvalHom P hT₁ e t ht) =
      (modelEvalHom P hT₂ e₁₂ t₁₂ ht₁₂).comp
        (weightedRename emb isWeightFamily_one_weight isWeightFamily_one_weight
          fun _ ↦ subset_rfl) := by
  let _ := P.toNonarchimedeanRing
  refine weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    (hc.comp (continuous_modelEvalHom P hT₁ e t ht he))
    ((continuous_modelEvalHom P hT₂ e₁₂ t₁₂ ht₁₂ he₁₂).comp (continuous_weightedRename emb _ _ _))
    (fun a ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, weightedRename_weightedC,
        modelEvalHom_weightedC, modelEvalHom_weightedC, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, ρ.commutes])
    (fun i ↦ by
      rw [Subsingleton.elim i 0, RingHom.comp_apply, RingHom.comp_apply, weightedRename_weightedX,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hX])

variable [DecidableEq A]

private theorem modelEvalHom_surjective_overlap (P : PairOfDefinition A) (f : A)
    (hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset A) : Set A) : Set A))
    {B₁₂ : Type*} [CommRing B₁₂] [Algebra A B₁₂]
    (e₁₂ : ratLoc P {f * f, 1} f
      (P.hasDenominatorPower_of_isOpen_span ({f * f, 1} : Finset A) f _ hT₁₂) ≃ₐ[A] B₁₂) :
    letI := P.toNonarchimedeanRing
    Function.Surjective (modelEvalHom P hT₁₂ e₁₂ ![f * f, 1]
      (Fin.forall_fin_two.mpr ⟨by simp, by simp⟩)) := by
  let _ := P.toNonarchimedeanRing
  have _ : (nhds (0 : A)).IsCountablyGenerated := P.hasBasis_nhds_zero.isCountablyGenerated
  have hspan : Ideal.span (insert f (Set.range (![f * f, 1] : Fin 2 → A))) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range.mpr ⟨1, rfl⟩))) isUnit_one
  have hTt : Set.range (fun y : ↥({f * f, 1} : Finset A) ↦ (divBy (y : A) f : Localization.Away f))
      ⊆ Set.range fun i : Fin 2 ↦ (divBy (![f * f, 1] i) f : Localization.Away f) := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨0, rfl⟩
    · rcases Finset.mem_singleton.mp hy with rfl; exact ⟨1, rfl⟩
  exact e₁₂.surjective.comp ((P.rationalEvalHom_surjective {f * f, 1} f _ _ ![f * f, 1] _
    hspan hTt).comp (restrictedMvPowerSeriesCompletionEquiv 2 A).symm.surjective)

/-- **Kedlaya–Liu, Lemma 2.4.22.** For a complete Hausdorff Huber ring `A` and any `f : A`,
given models `B₁`, `B₂`, `B₁₂` of the simple Laurent pieces `A⟨f, 1/1⟩`, `A⟨1/f⟩`, and their
overlap `A⟨f², 1/f⟩`, together with continuous `A`-algebra maps `ρ₁ : B₁ →ₐ[A] B₁₂` and
`ρ₂ : B₂ →ₐ[A] B₁₂`, the difference map `(b₁, b₂) ↦ ρ₁ b₁ - ρ₂ b₂` is surjective. -/
theorem IsRationalCompletion.surjective_sub_laurent
    {P : PairOfDefinition A} {f : A}
    {B₁ B₂ B₁₂ : Type*} [CommRing B₁] [CommRing B₂] [CommRing B₁₂]
    [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace B₁₂]
    [Algebra A B₁] [Algebra A B₂] [Algebra A B₁₂]
    {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset A) : Set A) : Set A)}
    {hT₂ : IsOpen (Ideal.span (({1} : Finset A) : Set A) : Set A)}
    {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset A) : Set A) : Set A)}
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁)
    (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂)
    (ρ₁ : B₁ →ₐ[A] B₁₂) (ρ₂ : B₂ →ₐ[A] B₁₂)
    (hc₁ : Continuous ρ₁) (hc₂ : Continuous ρ₂) :
    Function.Surjective fun x : B₁ × B₂ ↦ ρ₁ x.1 - ρ₂ x.2 := by
  let _ := P.toNonarchimedeanRing
  have _ : T2Space B₁₂ := h₁₂.t2Space
  obtain ⟨e₁, he₁, -⟩ := h₁
  obtain ⟨e₂, he₂, -⟩ := h₂
  obtain ⟨e₁₂, he₁₂, -⟩ := h₁₂
  let π₁ := modelEvalHom P hT₁ e₁ ![f] (fun i ↦ by fin_cases i; simp)
  let π₂ := modelEvalHom P hT₂ e₂ ![1] (fun i ↦ by fin_cases i; simp)
  let π₁₂ := modelEvalHom P hT₁₂ e₁₂ ![f * f, 1] (Fin.forall_fin_two.mpr ⟨by simp, by simp⟩)
  have hX₀ : π₁₂ (weightedX _ isWeightFamily_one_weight 0) = algebraMap A B₁₂ f :=
    modelEvalHom_X_eq_algebraMap_of_mul P hT₁₂ e₁₂ ![f * f, 1] _ 0 rfl
  have hmul₁₂ : algebraMap A B₁₂ f * π₁₂ (weightedX _ isWeightFamily_one_weight 1) = 1 :=
    modelEvalHom_X_mul_inv P hT₁₂ e₁₂ ![f * f, 1] _ 1 rfl
  have hρ₁ := comp_modelEvalHom_eq_weightedRename P hT₁ hT₁₂ e₁ he₁ e₁₂ he₁₂
    ![f] _ ![f * f, 1] _ ρ₁ hc₁ Fin.castSuccEmb (by
      have hf₁ : π₁ (weightedX _ isWeightFamily_one_weight 0) = algebraMap A B₁ f :=
        modelEvalHom_X_eq_algebraMap_of_mul P hT₁ e₁ ![f] _ 0 (one_mul f).symm
      change ρ₁ (π₁ _) = π₁₂ _
      rw [Fin.castSuccEmb_apply, Fin.castSucc_zero', hf₁, hX₀, ρ₁.commutes])
  have hρ₂ := comp_modelEvalHom_eq_weightedRename P hT₂ hT₁₂ e₂ he₂ e₁₂ he₁₂
    ![1] _ ![f * f, 1] _ ρ₂ hc₂ (Fin.succEmb 1) (by
      have hunit₂ : algebraMap A B₂ f * π₂ (weightedX _ isWeightFamily_one_weight 0) = 1 :=
        modelEvalHom_X_mul_inv P hT₂ e₂ ![1] _ 0 rfl
      have hmul₂ : algebraMap A B₁₂ f * ρ₂ (π₂ (weightedX _ isWeightFamily_one_weight 0)) = 1 := by
        rw [← ρ₂.commutes f, ← map_mul, hunit₂, map_one]
      change ρ₂ (π₂ _) = π₁₂ _
      rw [Fin.coe_succEmb, Fin.succ_zero_eq_one']
      exact left_inv_eq_right_inv (by rw [mul_comm]; exact hmul₂) hmul₁₂)
  intro y
  obtain ⟨u, rfl⟩ := modelEvalHom_surjective_overlap P f hT₁₂ e₁₂ y
  obtain ⟨⟨g, h⟩, hgh⟩ := laurentDiff_surjective A (Ideal.Quotient.mk (laurentIdeal A) u)
  rw [laurentDiff_apply, Ideal.Quotient.eq, mem_laurentIdeal] at hgh
  obtain ⟨w, hw⟩ := hgh
  refine ⟨(π₁ g, π₂ h), ?_⟩
  have hrel : π₁₂ (1 - weightedX _ isWeightFamily_one_weight 0 *
      weightedX _ isWeightFamily_one_weight 1) = 0 := by
    rw [map_sub, map_one, map_mul, hX₀, hmul₁₂, sub_self]
  have hsub := congrArg π₁₂ hw
  rw [map_sub, map_sub, map_mul, hrel, zero_mul, sub_eq_zero] at hsub
  dsimp only at hsub ⊢
  rw [show ρ₁ (π₁ g) = _ from congrArg (· g) hρ₁, show ρ₂ (π₂ h) = _ from congrArg (· h) hρ₂]
  exact hsub

/-- Scalar-tower form of `IsRationalCompletion.surjective_sub_laurent`, for `B₁ → B₁₂` and
`B₂ → B₁₂` given as `[Algebra B₁ B₁₂]` and `[Algebra B₂ B₁₂]`. -/
theorem IsRationalCompletion.surjective_algebraMap_sub_laurent
    {P : PairOfDefinition A} {f : A}
    {B₁ B₂ B₁₂ : Type*} [CommRing B₁] [CommRing B₂] [CommRing B₁₂]
    [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace B₁₂]
    [Algebra A B₁] [Algebra A B₂] [Algebra A B₁₂]
    [Algebra B₁ B₁₂] [Algebra B₂ B₁₂] [IsScalarTower A B₁ B₁₂] [IsScalarTower A B₂ B₁₂]
    {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset A) : Set A) : Set A)}
    {hT₂ : IsOpen (Ideal.span (({1} : Finset A) : Set A) : Set A)}
    {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset A) : Set A) : Set A)}
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁)
    (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂)
    (hc₁ : Continuous (algebraMap B₁ B₁₂)) (hc₂ : Continuous (algebraMap B₂ B₁₂)) :
    Function.Surjective fun x : B₁ × B₂ ↦ algebraMap B₁ B₁₂ x.1 - algebraMap B₂ B₁₂ x.2 :=
  h₁.surjective_sub_laurent h₂ h₁₂ (IsScalarTower.toAlgHom A B₁ B₁₂)
    (IsScalarTower.toAlgHom A B₂ B₁₂) hc₁ hc₂

end SimpleLaurent

end Uniform

section LaurentTransition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [DecidableEq A]

/-- There is a unique continuous `A`-algebra transition map `B₁ →ₐ[A] B₁₂` from any model `B₁` of
`A⟨f, 1/1⟩` to any model `B₁₂` of `A⟨f², 1/f⟩`: in `B₁₂`, `f = f² / f` is a distinguished
fraction and `1 / 1 = 1`. -/
theorem IsRationalCompletion.existsUnique_laurentLeftAlgHom
    {P : PairOfDefinition A} {f : A}
    {B₁ B₁₂ : Type*} [CommRing B₁] [CommRing B₁₂] [TopologicalSpace B₁] [TopologicalSpace B₁₂]
    [Algebra A B₁] [Algebra A B₁₂]
    {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset A) : Set A) : Set A)}
    {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset A) : Set A) : Set A)}
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) :
    ∃! ρ₁ : B₁ →ₐ[A] B₁₂, Continuous ρ₁ :=
  h₁.existsUnique_continuous_algHom_of_refines h₁₂ (one_mul f).symm fun t ht ↦
    (Finset.mem_insert.mp ht).elim (fun h ↦ Or.inr (by simp [h]))
      (fun h ↦ Or.inl (Finset.mem_singleton.mp h))

/-- There is a unique continuous `A`-algebra transition map `B₂ →ₐ[A] B₁₂` from any model `B₂` of
`A⟨1/f⟩` to any model `B₁₂` of `A⟨f², 1/f⟩`. -/
theorem IsRationalCompletion.existsUnique_laurentRightAlgHom
    {P : PairOfDefinition A} {f : A}
    {B₂ B₁₂ : Type*} [CommRing B₂] [CommRing B₁₂] [TopologicalSpace B₂] [TopologicalSpace B₁₂]
    [Algebra A B₂] [Algebra A B₁₂]
    {hT₂ : IsOpen (Ideal.span (({1} : Finset A) : Set A) : Set A)}
    {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset A) : Set A) : Set A)}
    (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) :
    ∃! ρ₂ : B₂ →ₐ[A] B₁₂, Continuous ρ₂ :=
  h₂.existsUnique_continuous_algHom_of_refines h₁₂ (mul_one f).symm fun t ht ↦
    Or.inr (by rw [Finset.mem_singleton.mp ht]; simp)

end LaurentTransition

end TauCeti.Huber

end
