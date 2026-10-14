/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Pair
public import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction

/-!
# Base change of rational localisations along a ring homomorphism

Let `f : A → B` be a continuous homomorphism of topological rings with pairs of definition `P` and
`P'`, let `(T, s)` present a rational localisation `A⟨T/s⟩` of `A`, and let `(T', f(s))` present
one of `B` whose numerators contain `f(T)`. The universal property of `A⟨T/s⟩` (Wedhorn,
Proposition and Definition 5.51) extends `f` uniquely to a continuous ring homomorphism

```text
A⟨T/s⟩ → B⟨T'/f(s)⟩
```

compatible with the structure maps (`completionLocMap`). On the image of `A[1/s]` it is the map of
localisations `A[1/s] → B[1/f(s)]`, so it carries `A⁺[T/s]` into `B⁺[T'/f(s)]` whenever `f` carries
`A⁺` into `B⁺`. Passing to integral closures and closures, it carries the plus ring `A_U⁺` into
`B_V⁺`, which makes it a morphism of rational localisation pairs (`completionLocPairMap`).

The target is localised at any `s'` together with a proof of `f(s) = s'`, rather than at the term
`f(s)` itself. The identity and composition laws then hold as stated, without needing
`id(s)` or `(g ∘ f)(s)` to reduce definitionally to `s` or `g(f(s))`.

For `T'` with underlying set `f(T)`, the rational subset `R(T'/f(s))` of `Spa(B, B⁺)` is the
preimage of `R(T/s) ⊆ Spa(A, A⁺)` (Wedhorn, Lemma 7.46(3)), so this is the map between the
coordinate rings of a rational open and of its preimage. Over a Tate base it preserves topological
finite type: `TauCeti.Huber.PairOfDefinition.isTopologicallyFiniteType_completionLocPairMap` in
`TauCeti.RingTheory.Huber.LocalizationTopology.FiniteType`.

For the concrete localisations `Localization.Away s` of presentations, the universal property
here also underlies `TauCeti.Huber.PairOfDefinition.Presentation.mapHom`, the same map as a
morphism of complete separated topological rings, used for the structure presheaf. Here the
localisations `S` and `S'` are arbitrary, as for
`TauCeti.Huber.PairOfDefinition.rationalLocalizationPair`, and the map carries the plus rings.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.completionLocMap`: the base change `A⟨T/s⟩ →+* B⟨T'/f(s)⟩`.
* `TauCeti.Huber.PairOfDefinition.completionLocPairMap`: the base change as a morphism of rational
  localisation pairs `(A⟨T/s⟩, A_U⁺) → (B⟨T'/f(s)⟩, B_V⁺)`.

## Main results

* `TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_comp_toCompletionLoc_eq`: the
  universal property of `A⟨T/s⟩` applied to `A → B → B⟨T'/f(s)⟩`.
* `TauCeti.Huber.PairOfDefinition.completionLocMap_comp_toCompletionLoc` and
  `TauCeti.Huber.PairOfDefinition.eq_completionLocMap`: the base change is compatible with the
  structure maps, and continuity and this compatibility determine it.
* `TauCeti.Huber.PairOfDefinition.completionLocMap_coe`: on the image of `A[1/s]` it is the map of
  localisations.
* `TauCeti.Huber.PairOfDefinition.completionLocPairMap_comp_toCompletionLocHom`: the morphism of
  pairs is compatible with the structure morphisms.
* `TauCeti.Huber.PairOfDefinition.completionLocMap_id`,
  `TauCeti.Huber.PairOfDefinition.completionLocMap_comp_completionLocMap` and their analogues
  `completionLocPairMap_id`, `completionLocPairMap_comp_completionLocPairMap` for morphisms of
  pairs: the base change is functorial.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition and Definition 5.51,
  Lemma 7.46 and §8.1.
-/

public section

open UniformSpace TauCeti.Localization

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-! ### The base change of completed rational localisations -/

section RingHom

variable (P : PairOfDefinition A) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
  [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)
  (P' : PairOfDefinition B) (f : A →+* B) (hf : ContinuousAt f 0) (T' : Finset B) (s' : B)
  (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
  (hden' : HasDenominatorPower P' T' s' S') (hs : f s = s') (hT : ∀ t ∈ T, f t ∈ T')

include hf hs hT in
/-- **The universal property of `A⟨T/s⟩` applied to `A → B → B⟨T'/f(s)⟩`**: exactly one continuous
ring homomorphism `A⟨T/s⟩ → B⟨T'/f(s)⟩` carries the structure map of `A` to that of `B` after `f`.
Beyond continuity of `f` at `0`, only `f(T) ⊆ T'` is assumed: `f(s)` is a unit of `B⟨T'/f(s)⟩`, and
each `f(t)/f(s)`, for `t ∈ T`, is power-bounded there because `f(t)` is a numerator. -/
theorem existsUnique_continuous_ringHom_comp_toCompletionLoc_eq :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    ∃! g : Completion S →+* Completion S', Continuous g ∧
      g.comp (toCompletionLoc P T s S hden) = (toCompletionLoc P' T' s' S' hden').comp f := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  have hs₁ : s' = f s * 1 := by rw [mul_one, hs]
  have hu := isUnit_toCompletionLoc_of_dvd P' T' s' S' hden' ⟨1, hs₁⟩
  exact existsUnique_continuous_ringHom_completion_locTopology P T s S hden
    (φ := (toCompletionLoc P' T' s' S' hden').comp f)
    ((continuous_toCompletionLoc P' T' s' S' hden').comp
      (continuous_of_continuousAt_zero f hf)).continuousAt hu
    fun t ht ↦ isPowerBounded_toCompletionLoc_mul_unit_inv P' T' s' S' hden' hs₁ hu
      ((mul_one (f t)).symm ▸ hT t ht)

include hf hs hT in
/-- **The base change `A⟨T/s⟩ → B⟨T'/f(s)⟩` of `f`**: the unique continuous ring homomorphism
carrying the structure map of `A` to that of `B` after `f`.

Its two defining properties are `continuous_completionLocMap` and
`completionLocMap_comp_toCompletionLoc`, and `eq_completionLocMap` says they determine it. -/
noncomputable def completionLocMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    Completion S →+* Completion S' :=
  (existsUnique_continuous_ringHom_comp_toCompletionLoc_eq P T s S hden P' f hf T' s' S' hden'
    hs hT).choose

/-- The base change is continuous. -/
theorem continuous_completionLocMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    Continuous (completionLocMap P T s S hden P' f hf T' s' S' hden' hs hT) :=
  (existsUnique_continuous_ringHom_comp_toCompletionLoc_eq P T s S hden P' f hf T' s' S' hden'
    hs hT).choose_spec.1.1

/-- **The base change is compatible with the structure maps**: `A → A⟨T/s⟩` followed by it is
`A → B → B⟨T'/f(s)⟩`. -/
@[simp]
theorem completionLocMap_comp_toCompletionLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    (completionLocMap P T s S hden P' f hf T' s' S' hden' hs hT).comp
        (toCompletionLoc P T s S hden) =
      (toCompletionLoc P' T' s' S' hden').comp f :=
  (existsUnique_continuous_ringHom_comp_toCompletionLoc_eq P T s S hden P' f hf T' s' S' hden'
    hs hT).choose_spec.1.2

/-- **The two properties determine the base change**: a continuous ring homomorphism
`A⟨T/s⟩ → B⟨T'/f(s)⟩` carrying the structure map of `A` to that of `B` after `f` is
`completionLocMap`. -/
theorem eq_completionLocMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    ∀ g : Completion S →+* Completion S', Continuous g →
      g.comp (toCompletionLoc P T s S hden) = (toCompletionLoc P' T' s' S' hden').comp f →
      g = completionLocMap P T s S hden P' f hf T' s' S' hden' hs hT := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  exact fun g hgc hge ↦
    (existsUnique_continuous_ringHom_comp_toCompletionLoc_eq P T s S hden P' f hf T' s' S' hden'
      hs hT).choose_spec.2 g ⟨hgc, hge⟩

/-- **On the image of `A[1/s]`, the base change is the map of localisations**
`A[1/s] → B[1/f(s)]` induced by `f`, which sends `a/s` to `f(a)/f(s)`
(`RingHom.awayMap_divBy`). -/
@[simp]
theorem completionLocMap_coe (x : S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    completionLocMap P T s S hden P' f hf T' s' S' hden' hs hT (x : Completion S) =
      (IsLocalization.map (M := .powers s) (T := .powers s') S' f
          (Submonoid.powers_le.mpr (by rw [Submonoid.mem_comap, hs]; exact Submonoid.mem_powers s'))
          x : Completion S') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have h :
      (completionLocMap P T s S hden P' f hf T' s' S' hden' hs hT).comp Completion.coeRingHom =
      Completion.coeRingHom.comp
        (IsLocalization.map (M := .powers s) (T := .powers s') S' f (Submonoid.powers_le.mpr
          (by rw [Submonoid.mem_comap, hs]; exact Submonoid.mem_powers s'))) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun a ↦ ?_)
    -- both sides send `a` to the image of `f(a)` in `B⟨T'/f(s)⟩`
    simpa only [RingHom.coe_comp, Completion.coe_coeRingHom, Function.comp_apply,
      IsLocalization.map_eq, toCompletionLoc_apply] using
      RingHom.congr_fun
        (completionLocMap_comp_toCompletionLoc P T s S hden P' f hf T' s' S' hden' hs hT) a
  exact RingHom.congr_fun h x

/-! ### The plus rings -/

variable {Aplus : Subring A} {Bplus : Subring B}

/-- The base change carries the plus ring `A_U⁺` of `A⟨T/s⟩` built from `A⁺` into the plus ring
`B_V⁺` of `B⟨T'/f(s)⟩` built from `B⁺`, as soon as `f` carries `A⁺` into `B⁺`. The preimage of
`B_V⁺` is a closed subring, so it suffices that it contain the image of the integral closure of
`A⁺[T/s]`. -/
private theorem completionLocMap_mem_completedPlusSubring (hplus : ∀ a ∈ Aplus, f a ∈ Bplus) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    ∀ x ∈ completedPlusSubring P Aplus T s S hden,
      completionLocMap P T s S hden P' f hf T' s' S' hden' hs hT x ∈
        completedPlusSubring P' Bplus T' s' S' hden' := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have hclosed : IsClosed ((completedPlusSubring P' Bplus T' s' S' hden').comap
      (completionLocMap P T s S hden P' f hf T' s' S' hden' hs hT) : Set (Completion S)) :=
    (isClosed_completedPlusSubring P' Bplus T' s' S' hden').preimage
      (continuous_completionLocMap P T s S hden P' f hf T' s' S' hden' hs hT)
  intro x hx
  refine (completedPlusSubring_le_iff P Aplus T s S hden hclosed).mpr (fun c hc ↦ ?_) hx
  rw [Subring.mem_comap, completionLocMap_coe]
  subst hs
  exact coeRingHom_mem_completedPlusSubring P' Bplus T' _ S' hden'
    (map_integralClosure_adjoin_divBy_le (T : Set A) s f (T' : Set B) hT hplus ⟨c, hc, rfl⟩)

end RingHom

/-! ### Functoriality of the base change -/

section Functoriality

variable (P : PairOfDefinition A) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
  [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S)

/-- **The base change of the identity is the identity.** -/
@[simp]
theorem completionLocMap_id :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    completionLocMap P T s S hden P (RingHom.id A) continuous_id.continuousAt T s S hden rfl
      (fun _ ht ↦ ht) = RingHom.id _ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  exact (eq_completionLocMap P T s S hden P (RingHom.id A) continuous_id.continuousAt T s S hden
    rfl (fun _ ht ↦ ht) _ continuous_id (by rw [RingHom.id_comp, RingHom.comp_id])).symm

variable {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  (P' : PairOfDefinition B) (f : A →+* B) (hf : ContinuousAt f 0) (T' : Finset B) (s' : B)
  (S' : Type*) [CommRing S'] [Algebra B S'] [IsLocalization.Away s' S']
  (hden' : HasDenominatorPower P' T' s' S') (hs : f s = s') (hT : ∀ t ∈ T, f t ∈ T')
  (P'' : PairOfDefinition C) (g : B →+* C) (hg : ContinuousAt g 0) (T'' : Finset C) (s'' : C)
  (S'' : Type*) [CommRing S''] [Algebra C S''] [IsLocalization.Away s'' S'']
  (hden'' : HasDenominatorPower P'' T'' s'' S'') (hs' : g s' = s'') (hT' : ∀ t ∈ T', g t ∈ T'')

/-- **The base change of a composite is the composite of the base changes.** -/
@[simp]
theorem completionLocMap_comp_completionLocMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := locUniformSpace P'' T'' s'' S'' hden''
    letI := isUniformAddGroup_locUniformSpace P'' T'' s'' S'' hden''
    letI := isTopologicalRing_locUniformSpace P'' T'' s'' S'' hden''
    (completionLocMap P' T' s' S' hden' P'' g hg T'' s'' S'' hden'' hs' hT').comp
        (completionLocMap P T s S hden P' f hf T' s' S' hden' hs hT) =
      completionLocMap P T s S hden P'' (g.comp f) (hg.comp_of_eq hf (map_zero f)) T'' s'' S''
        hden'' (by rw [RingHom.comp_apply, hs, hs']) fun t ht ↦ hT' _ (hT t ht) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  let _ := locUniformSpace P'' T'' s'' S'' hden''
  have _ := isUniformAddGroup_locUniformSpace P'' T'' s'' S'' hden''
  have _ := isTopologicalRing_locUniformSpace P'' T'' s'' S'' hden''
  refine eq_completionLocMap P T s S hden P'' (g.comp f) (hg.comp_of_eq hf (map_zero f)) T'' s''
    S'' hden'' _ (fun t ht ↦ hT' _ (hT t ht)) _
    ((continuous_completionLocMap P' T' s' S' hden' P'' g hg T'' s'' S'' hden'' hs' hT').comp
      (continuous_completionLocMap P T s S hden P' f hf T' s' S' hden' hs hT)) ?_
  rw [RingHom.comp_assoc, completionLocMap_comp_toCompletionLoc, ← RingHom.comp_assoc,
    completionLocMap_comp_toCompletionLoc, RingHom.comp_assoc]

end Functoriality

/-! ### The base change as a morphism of Huber pairs -/

section Pair

variable [IsHuberRing A] [IsHuberRing B]
  (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus)
  (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)
  (P' : PairOfDefinition B) (U' : Pair B) (hP' : P'.ringOfDefinition ≤ U'.plus)
  (f : Pair.Hom U U') (T' : Finset B) (s' : B) (S' : Type*) [CommRing S'] [Algebra B S']
  [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P' T' s' S')
  (hs : f.toRingHom s = s') (hT : ∀ t ∈ T, f.toRingHom t ∈ T')

/-- **The base change as a morphism of Huber pairs**
`(A⟨T/s⟩, A_U⁺) → (B⟨T'/f(s)⟩, B_V⁺)`, between the rational localisation pairs of `(A, A⁺)` and of
`(B, B⁺)`, for a morphism of Huber pairs `f : (A, A⁺) → (B, B⁺)`. Its underlying ring
homomorphism is `completionLocMap`. -/
noncomputable def completionLocPairMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    Pair.Hom (rationalLocalizationPair P U hP T s S hden)
      (rationalLocalizationPair P' U' hP' T' s' S' hden') :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_completion_locTopology P T s S hden
  letI := locUniformSpace P' T' s' S' hden'
  letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  letI := isHuberRing_completion_locTopology P' T' s' S' hden'
  { toRingHom := completionLocMap P T s S hden P' f.toRingHom f.continuous_toRingHom.continuousAt
      T' s' S' hden' hs hT
    continuous_toRingHom := continuous_completionLocMap P T s S hden P' f.toRingHom
      f.continuous_toRingHom.continuousAt T' s' S' hden' hs hT
    map_mem_plus := by
      rw [rationalLocalizationPair_plus, rationalLocalizationPair_plus]
      exact completionLocMap_mem_completedPlusSubring P T s S hden P' f.toRingHom
        f.continuous_toRingHom.continuousAt T' s' S' hden' hs hT f.map_mem_plus }

/-- The underlying ring homomorphism of `completionLocPairMap` is `completionLocMap`. -/
@[simp]
theorem toRingHom_completionLocPairMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    (completionLocPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hs hT).toRingHom =
      completionLocMap P T s S hden P' f.toRingHom f.continuous_toRingHom.continuousAt
        T' s' S' hden' hs hT :=
  (rfl)

/-- **`completionLocPairMap` is compatible with the structure morphisms**: the structure morphism
`(A, A⁺) → (A⟨T/s⟩, A_U⁺)` followed by it is `f` followed by the structure morphism
`(B, B⁺) → (B⟨T'/f(s)⟩, B_V⁺)`. -/
@[simp]
theorem completionLocPairMap_comp_toCompletionLocHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    (completionLocPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hs hT).comp
        (toCompletionLocHom P U hP T s S hden) =
      (toCompletionLocHom P' U' hP' T' s' S' hden').comp f := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  apply Pair.Hom.ext
  rw [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_comp, toRingHom_completionLocPairMap,
    toRingHom_toCompletionLocHom, toRingHom_toCompletionLocHom]
  exact completionLocMap_comp_toCompletionLoc P T s S hden P' f.toRingHom
    f.continuous_toRingHom.continuousAt T' s' S' hden' hs hT

/-- **The base change of the identity morphism of Huber pairs is the identity.** -/
@[simp]
theorem completionLocPairMap_id :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    completionLocPairMap P U hP T s S hden P U hP (Pair.Hom.id U) T s S hden
      (by rw [Pair.Hom.toRingHom_id, RingHom.id_apply])
      (fun t ht ↦ by rwa [Pair.Hom.toRingHom_id, RingHom.id_apply]) = Pair.Hom.id _ := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  apply Pair.Hom.ext
  rw [toRingHom_completionLocPairMap]
  exact (eq_completionLocMap P T s S hden P (Pair.Hom.id U).toRingHom
    (Pair.Hom.id U).continuous_toRingHom.continuousAt T s S hden _ _ _
    (Pair.Hom.id _).continuous_toRingHom
    (by simp only [Pair.Hom.toRingHom_id, RingHom.id_comp, RingHom.comp_id])).symm

variable {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  (P'' : PairOfDefinition C) (U'' : Pair C) (hP'' : P''.ringOfDefinition ≤ U''.plus)
  (g : Pair.Hom U' U'') (T'' : Finset C) (s'' : C) (S'' : Type*) [CommRing S''] [Algebra C S'']
  [IsLocalization.Away s'' S''] (hden'' : HasDenominatorPower P'' T'' s'' S'')
  (hs' : g.toRingHom s' = s'') (hT' : ∀ t ∈ T', g.toRingHom t ∈ T'')

/-- **The base change of a composite morphism of Huber pairs is the composite of the base
changes.** -/
@[simp]
theorem completionLocPairMap_comp_completionLocPairMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' s' S' hden'
    letI := isHuberRing_completion_locTopology P' T' s' S' hden'
    letI := locUniformSpace P'' T'' s'' S'' hden''
    letI := isUniformAddGroup_locUniformSpace P'' T'' s'' S'' hden''
    letI := isTopologicalRing_locUniformSpace P'' T'' s'' S'' hden''
    letI := isHuberRing_completion_locTopology P'' T'' s'' S'' hden''
    (completionLocPairMap P' U' hP' T' s' S' hden' P'' U'' hP'' g T'' s'' S'' hden'' hs'
        hT').comp (completionLocPairMap P U hP T s S hden P' U' hP' f T' s' S' hden' hs hT) =
      completionLocPairMap P U hP T s S hden P'' U'' hP'' (g.comp f) T'' s'' S'' hden''
        (by rw [Pair.Hom.toRingHom_comp, RingHom.comp_apply, hs, hs'])
        fun t ht ↦ by rw [Pair.Hom.toRingHom_comp]; exact hT' _ (hT t ht) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P' T' s' S' hden'
  let _ := locUniformSpace P'' T'' s'' S'' hden''
  have _ := isUniformAddGroup_locUniformSpace P'' T'' s'' S'' hden''
  have _ := isTopologicalRing_locUniformSpace P'' T'' s'' S'' hden''
  have _ := isHuberRing_completion_locTopology P'' T'' s'' S'' hden''
  apply Pair.Hom.ext
  rw [Pair.Hom.toRingHom_comp, toRingHom_completionLocPairMap, toRingHom_completionLocPairMap,
    toRingHom_completionLocPairMap]
  refine eq_completionLocMap P T s S hden P'' (g.comp f).toRingHom
    (g.comp f).continuous_toRingHom.continuousAt T'' s'' S'' hden'' _ _ _
    ((continuous_completionLocMap P' T' s' S' hden' P'' g.toRingHom
      g.continuous_toRingHom.continuousAt T'' s'' S'' hden'' hs' hT').comp
      (continuous_completionLocMap P T s S hden P' f.toRingHom
        f.continuous_toRingHom.continuousAt T' s' S' hden' hs hT)) ?_
  rw [RingHom.comp_assoc, completionLocMap_comp_toCompletionLoc, ← RingHom.comp_assoc,
    completionLocMap_comp_toCompletionLoc, RingHom.comp_assoc, Pair.Hom.toRingHom_comp]

end Pair

end TauCeti.Huber.PairOfDefinition
