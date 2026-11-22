/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.RatLoc
import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction
import TauCeti.RingTheory.Huber.LocalizationTopology.Trivial
import TauCeti.Topology.Algebra.Ring.Basic

/-!
# Models of the completed rational localisation `A⟨T/s⟩`

`TauCeti.Huber.ratLoc` fixes one canonical carrier for the completed rational localisation
`A⟨T/s⟩`. In practice callers work with arbitrary topological `A`-algebras `B` (such as `A` itself
at denominator `1`, a Tate algebra `A⟨X⟩`, or a limit over presentations) that are *isomorphic as
topological `A`-algebras* to `A⟨T/s⟩`.

This file defines `TauCeti.Huber.IsRationalCompletion P T s hT B`, proves its invariance under
pair-of-definition changes and bicontinuous `A`-algebra equivalences, and transfers the structural
and universal properties of `ratLoc`.

## Main definitions

* `TauCeti.Huber.IsRationalCompletion P T s hT B`: `B` is isomorphic as a topological `A`-algebra
  to the completed rational localisation `A⟨T/s⟩`.

## Main results

* `TauCeti.Huber.isRationalCompletion_iff_ratLoc`, `TauCeti.Huber.isRationalCompletion_ratLoc`, and
  `TauCeti.Huber.IsRationalCompletion.congr_pairOfDefinition`: comparison with `ratLoc` and
  independence of the pair of definition `P`.
* `TauCeti.Huber.IsRationalCompletion.isTopologicalRing`,
  `TauCeti.Huber.IsRationalCompletion.completeSpace`,
  `TauCeti.Huber.IsRationalCompletion.t2Space`,
  `TauCeti.Huber.IsRationalCompletion.isHuberRing`, and
  `TauCeti.Huber.IsRationalCompletion.isTateRing`: topological ring, completeness, separation,
  Huber, and Tate properties of any model.
* `TauCeti.Huber.IsRationalCompletion.isPowerBounded_algebraMap_mul_unit_inv`: the distinguished
  fractions `t / s` (`t ∈ T`) are power-bounded in any model.
* `TauCeti.Huber.IsRationalCompletion.localizationAlgHom`,
  `TauCeti.Huber.IsRationalCompletion.localizationAlgHom_algebraMap`,
  `TauCeti.Huber.IsRationalCompletion.continuous_localizationAlgHom`, and
  `TauCeti.Huber.IsRationalCompletion.denseRange_localizationAlgHom`: canonical dense copy of
  `Localization.Away s` in any model and its continuity for the localisation topology.
* `TauCeti.Huber.IsRationalCompletion.ringHom_ext_of_continuous`,
  `TauCeti.Huber.IsRationalCompletion.existsUnique_continuous_algHom`,
  `TauCeti.Huber.IsRationalCompletion.existsUnique_continuous_algHom_of_refines`, and
  `TauCeti.Huber.IsRationalCompletion.denseRange_of_comp_algebraMap_eq`: uniqueness, universal
  property, functoriality along refinements, and density at a shared denominator.
* `TauCeti.Huber.isRationalCompletion_self_denom_one` and
  `TauCeti.Huber.IsRationalCompletion.subsingleton_of_denom_zero`: behaviour at denominators `1`
  and `0`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.4.
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

section ModelProperties

variable {P : PairOfDefinition A} {T : Finset A} {s : A}
  {hT : IsOpen (Ideal.span (T : Set A) : Set A)}
  {B : Type*} [CommRing B] [TopologicalSpace B] [Algebra A B]

/-- `IsRationalCompletion` is independent of the chosen pair of definition `P`. -/
theorem IsRationalCompletion.congr_pairOfDefinition (h : IsRationalCompletion P T s hT B)
    (P' : PairOfDefinition A) : IsRationalCompletion P' T s hT B := by
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
theorem IsRationalCompletion.of_algEquiv {B' : Type*} [CommRing B'] [TopologicalSpace B']
    [Algebra A B'] (h : IsRationalCompletion P T s hT B) (e : B ≃ₐ[A] B')
    (he : Continuous e) (he' : Continuous e.symm) :
    IsRationalCompletion P T s hT B' :=
  let ⟨f, hf, hf'⟩ := h
  ⟨f.trans e, he.comp hf, hf'.comp he'⟩

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

/-- Any model of `A⟨T/s⟩` is a topological ring. -/
theorem IsRationalCompletion.isTopologicalRing (h : IsRationalCompletion P T s hT B) :
    IsTopologicalRing B := by
  obtain ⟨e, he, he'⟩ := h
  exact _root_.Topology.IsInducing.isTopologicalRing e.symm.toRingHom
    (Homeomorph.mk e.toEquiv he he').symm.isInducing

/-- Any model of `A⟨T/s⟩` is a Huber ring. -/
theorem IsRationalCompletion.isHuberRing (h : IsRationalCompletion P T s hT B) :
    @IsHuberRing B _ _ h.isTopologicalRing := by
  have := h.isTopologicalRing
  obtain ⟨e, he, he'⟩ := h
  exact IsHuberRing.of_isOpenQuotientMap (f := e.toRingHom)
    (Homeomorph.mk e.toEquiv he he').isOpenQuotientMap

/-- Over a Tate ring `A`, any model of `A⟨T/s⟩` is a Tate ring. -/
theorem IsRationalCompletion.isTateRing [IsTateRing A] (h : IsRationalCompletion P T s hT B) :
    @IsTateRing B _ _ h.isTopologicalRing := by
  have := h.isTopologicalRing
  have := h.isHuberRing
  exact IsTateRing.of_continuous h.continuous_algebraMap

/-- Any model of `A⟨T/s⟩` equipped with a compatible `IsUniformAddGroup` uniform structure is
complete. -/
theorem IsRationalCompletion.completeSpace {B : Type*} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [Algebra A B] (h : IsRationalCompletion P T s hT B) :
    CompleteSpace B := by
  have := h.isTopologicalRing
  obtain ⟨e, he, he'⟩ := h
  let ue : ratLoc P T s (P.hasDenominatorPower_of_isOpen_span T s _ hT) ≃ᵤ B :=
    ⟨e.toEquiv, uniformContinuous_of_continuousAt_zero e.toAddMonoidHom he.continuousAt,
      uniformContinuous_of_continuousAt_zero e.symm.toAddMonoidHom he'.continuousAt⟩
  exact ue.completeSpace_iff.mp inferInstance

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
      simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        AlgEquiv.coe_toRingEquiv, ← algebraMap_ratLoc, e.commutes] using RingHom.congr_fun hfg a)
  exact RingHom.ext fun x ↦ by simpa using congrArg (· (e.symm x)) hfe

/-- Two continuous `A`-algebra homomorphisms out of a model of `A⟨T/s⟩` into a Hausdorff
`A`-algebra are equal. -/
theorem IsRationalCompletion.algHom_ext_of_continuous (h : IsRationalCompletion P T s hT B)
    {C : Type*} [CommSemiring C] [TopologicalSpace C] [T2Space C] [Algebra A C]
    {f g : B →ₐ[A] C} (hf : Continuous f) (hg : Continuous g) : f = g :=
  AlgHom.toRingHom_injective <| h.ringHom_ext_of_continuous hf hg
    (RingHom.ext fun a ↦ (f.commutes a).trans (g.commutes a).symm)

/-- For any numerator `t ∈ T`, the fraction `t / s` is power-bounded in any model `B` of
`A⟨T/s⟩`. -/
theorem IsRationalCompletion.isPowerBounded_algebraMap_mul_unit_inv
    (h : IsRationalCompletion P T s hT B) {t : A} (ht : t ∈ T) :
    IsPowerBounded (algebraMap A B t * ↑h.isUnit_algebraMap.unit⁻¹) := by
  let S := Localization.Away s
  let hden := P.hasDenominatorPower_of_isOpen_span T s S hT
  let _ := P.locUniformSpace T s S hden
  have _ := P.isUniformAddGroup_locUniformSpace T s S hden
  have _ := P.isTopologicalRing_locUniformSpace T s S hden
  obtain ⟨e, he, he'⟩ := id h
  have hu : IsUnit (P.toCompletionLoc T s S hden s) := by
    simpa [algebraMap_ratLoc] using isUnit_algebraMap_ratLoc P T s hden
  have hpow := P.isPowerBounded_toCompletionLoc_mul_unit_inv T s S hden (mul_one s).symm hu
    (by simpa using ht)
  rw [← isPowerBounded_ringEquiv_iff e.toRingEquiv he he'] at hpow
  have ht_eq : e (P.toCompletionLoc T s S hden t) = algebraMap A B t := by
    rw [← algebraMap_ratLoc]; exact e.commutes t
  have hmul : algebraMap A B s * e ↑hu.unit⁻¹ = 1 := by
    rw [← e.commutes s, algebraMap_ratLoc, ← map_mul, IsUnit.mul_val_inv, map_one]
  have hinv : e ↑hu.unit⁻¹ = (↑h.isUnit_algebraMap.unit⁻¹ : B) := by
    calc
      e ↑hu.unit⁻¹ = ↑h.isUnit_algebraMap.unit⁻¹ * (algebraMap A B s * e ↑hu.unit⁻¹) := by
        rw [← mul_assoc, h.isUnit_algebraMap.val_inv_mul, one_mul]
      _ = ↑h.isUnit_algebraMap.unit⁻¹ := by rw [hmul, mul_one]
  simpa only [RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv, map_mul, ht_eq, hinv] using hpow

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
  simpa only [RingHom.toFun_eq_coe, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, AlgEquiv.coe_toRingEquiv, e.symm.commutes, algebraMap_ratLoc] using
    RingHom.congr_fun hf_eq a

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

/-- The canonical `A`-algebra homomorphism from `Localization.Away s` into any model `B` of
`A⟨T/s⟩`. -/
noncomputable def IsRationalCompletion.localizationAlgHom
    (h : IsRationalCompletion P T s hT B) : Localization.Away s →ₐ[A] B where
  toRingHom := IsLocalization.Away.lift s h.isUnit_algebraMap
  commutes' := IsLocalization.Away.lift_eq s h.isUnit_algebraMap

/-- On the image of `A`, `IsRationalCompletion.localizationAlgHom` agrees with `algebraMap A B`
(also available to `simp` via `AlgHom.commutes`). -/
theorem IsRationalCompletion.localizationAlgHom_algebraMap
    (h : IsRationalCompletion P T s hT B) (a : A) :
    h.localizationAlgHom (algebraMap A (Localization.Away s) a) = algebraMap A B a :=
  h.localizationAlgHom.commutes a

private theorem IsRationalCompletion.localizationAlgHom_eq_comp_coeRingHom
    (h : IsRationalCompletion P T s hT B)
    (e : ratLoc P T s (P.hasDenominatorPower_of_isOpen_span T s _ hT) ≃ₐ[A] B) :
    let hden := P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
    letI := P.locUniformSpace T s (Localization.Away s) hden
    letI := P.isUniformAddGroup_locUniformSpace T s (Localization.Away s) hden
    letI := P.isTopologicalRing_locUniformSpace T s (Localization.Away s) hden
    h.localizationAlgHom.toRingHom = e.toRingHom.comp Completion.coeRingHom := by
  let hden := P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
  let _ := P.locUniformSpace T s (Localization.Away s) hden
  have _ := P.isUniformAddGroup_locUniformSpace T s (Localization.Away s) hden
  have _ := P.isTopologicalRing_locUniformSpace T s (Localization.Away s) hden
  refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun a ↦ ?_)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    localizationAlgHom_algebraMap, RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_toRingEquiv,
    Completion.coe_coeRingHom]
  rw [← P.toCompletionLoc_apply T s (Localization.Away s) hden a, ← algebraMap_ratLoc, e.commutes]

/-- The canonical map `Localization.Away s →ₐ[A] B` into any model `B` of `A⟨T/s⟩` is continuous
for the localisation topology on `Localization.Away s`. -/
theorem IsRationalCompletion.continuous_localizationAlgHom
    (h : IsRationalCompletion P T s hT B) :
    letI := P.locTopology T s (Localization.Away s)
      (P.hasDenominatorPower_of_isOpen_span T s _ hT)
    Continuous h.localizationAlgHom := by
  let hden := P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
  let _ := P.locUniformSpace T s (Localization.Away s) hden
  have _ := P.isUniformAddGroup_locUniformSpace T s (Localization.Away s) hden
  have _ := P.isTopologicalRing_locUniformSpace T s (Localization.Away s) hden
  obtain ⟨e, he, -⟩ := id h
  rw [← P.locUniformSpace_toTopologicalSpace T s (Localization.Away s) hden]
  have hcomp : (h.localizationAlgHom : Localization.Away s → B) =
      e ∘ (Completion.coe' : Localization.Away s → ratLoc P T s hden) :=
    funext fun x ↦ RingHom.congr_fun (h.localizationAlgHom_eq_comp_coeRingHom e) x
  rw [hcomp]
  exact he.comp (Completion.continuous_coe (Localization.Away s))

/-- The canonical map `Localization.Away s →ₐ[A] B` into any model `B` of `A⟨T/s⟩` has dense
range. -/
theorem IsRationalCompletion.denseRange_localizationAlgHom
    (h : IsRationalCompletion P T s hT B) :
    DenseRange h.localizationAlgHom := by
  let hden := P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT
  let _ := P.locUniformSpace T s (Localization.Away s) hden
  have _ := P.isUniformAddGroup_locUniformSpace T s (Localization.Away s) hden
  have _ := P.isTopologicalRing_locUniformSpace T s (Localization.Away s) hden
  obtain ⟨e, he, -⟩ := id h
  have hcomp : (h.localizationAlgHom : Localization.Away s → B) =
      e ∘ (Completion.coe' : Localization.Away s → ratLoc P T s hden) :=
    funext fun x ↦ RingHom.congr_fun (h.localizationAlgHom_eq_comp_coeRingHom e) x
  rw [hcomp]
  exact e.surjective.denseRange.comp Completion.denseRange_coe he

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
  have heq : φ.comp hB.localizationAlgHom.toRingHom = hC.localizationAlgHom.toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun a ↦ ?_)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      localizationAlgHom_algebraMap]
    exact RingHom.congr_fun hφ a
  exact hC.denseRange_localizationAlgHom.mono fun _ hy ↦ by
    rcases hy with ⟨x, rfl⟩
    exact ⟨hB.localizationAlgHom x, by simpa using RingHom.congr_fun heq x⟩

/-- At denominator `0`, any model of `A⟨T/0⟩` is a subsingleton, since `Localization.Away (0 : A)`
is already trivial. -/
theorem IsRationalCompletion.subsingleton_of_denom_zero
    (h : IsRationalCompletion P T 0 hT B) : Subsingleton B := by
  obtain ⟨u, hu⟩ : IsUnit (0 : B) := by simpa using h.isUnit_algebraMap
  exact subsingleton_of_zero_eq_one (by rw [← u.mul_inv, hu, zero_mul])

end ModelProperties

/-- Conversely, every subsingleton `A`-algebra is a model of `A⟨T/0⟩`. -/
theorem isRationalCompletion_of_subsingleton_denom_zero (P : PairOfDefinition A) (T : Finset A)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (B : Type*) [CommRing B] [TopologicalSpace B] [Algebra A B] [Subsingleton B] :
    IsRationalCompletion P T 0 hT B := by
  have _ := (isRationalCompletion_ratLoc P T 0 hT).subsingleton_of_denom_zero
  exact ⟨{ toFun := fun _ ↦ 0, invFun := fun _ ↦ 0,
           left_inv := fun _ ↦ Subsingleton.elim _ _, right_inv := fun _ ↦ Subsingleton.elim _ _,
           map_mul' := fun _ _ ↦ Subsingleton.elim _ _, map_add' := fun _ _ ↦ Subsingleton.elim _ _,
           commutes' := fun _ ↦ Subsingleton.elim _ _ }, continuous_const, continuous_const⟩

end Basic

section Uniform

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]

/-- At denominator `1`, a complete Hausdorff Huber ring `A` is itself a model of `A⟨T/1⟩` whenever
every numerator in `T` is power-bounded. -/
theorem isRationalCompletion_self_denom_one [CompleteSpace A] [T0Space A]
    (P : PairOfDefinition A) (T : Finset A) (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (hTpb : ∀ t ∈ T, IsPowerBounded t) : IsRationalCompletion P T 1 hT A := by
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
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.algebraMap_self, RingHom.id_apply]
  rw [← P.toCompletionLocEquivDenomOne_apply T hTpb S a, e.symm_apply_apply]

end Uniform

end TauCeti.Huber

end
