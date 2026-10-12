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
  (P' : PairOfDefinition B) (f : A →+* B) (hf : ContinuousAt f 0) (T' : Finset B) (S' : Type*)
  [CommRing S'] [Algebra B S'] [IsLocalization.Away (f s) S']
  (hden' : HasDenominatorPower P' T' (f s) S') (hT : ∀ t ∈ T, f t ∈ T')

include hf hT in
/-- **The universal property of `A⟨T/s⟩` applied to `A → B → B⟨T'/f(s)⟩`**: exactly one continuous
ring homomorphism `A⟨T/s⟩ → B⟨T'/f(s)⟩` carries the structure map of `A` to that of `B` after `f`.
Beyond continuity of `f` at `0`, only `f(T) ⊆ T'` is assumed: `f(s)` is a unit of `B⟨T'/f(s)⟩`, and
each `f(t)/f(s)`, for `t ∈ T`, is power-bounded there because `f(t)` is a numerator. -/
theorem existsUnique_continuous_ringHom_comp_toCompletionLoc_eq :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' (f s) S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' (f s) S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' (f s) S' hden'
    ∃! g : Completion S →+* Completion S', Continuous g ∧
      g.comp (toCompletionLoc P T s S hden) = (toCompletionLoc P' T' (f s) S' hden').comp f := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' (f s) S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' (f s) S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' (f s) S' hden'
  have _ := isHuberRing_completion_locTopology P' T' (f s) S' hden'
  have hs : f s = f s * 1 := (mul_one _).symm
  have hu := isUnit_toCompletionLoc_of_dvd P' T' (f s) S' hden' ⟨1, hs⟩
  exact existsUnique_continuous_ringHom_completion_locTopology P T s S hden
    (φ := (toCompletionLoc P' T' (f s) S' hden').comp f)
    ((continuous_toCompletionLoc P' T' (f s) S' hden').comp
      (continuous_of_continuousAt_zero f hf)).continuousAt hu
    fun t ht ↦ isPowerBounded_toCompletionLoc_mul_unit_inv P' T' (f s) S' hden' hs hu
      ((mul_one (f t)).symm ▸ hT t ht)

include hf hT in
/-- **The base change `A⟨T/s⟩ → B⟨T'/f(s)⟩` of `f`**: the unique continuous ring homomorphism
carrying the structure map of `A` to that of `B` after `f`.

Its two defining properties are `continuous_completionLocMap` and
`completionLocMap_comp_toCompletionLoc`, and `eq_completionLocMap` says they determine it. -/
noncomputable def completionLocMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' (f s) S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' (f s) S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' (f s) S' hden'
    Completion S →+* Completion S' :=
  (existsUnique_continuous_ringHom_comp_toCompletionLoc_eq P T s S hden P' f hf T' S' hden'
    hT).choose

/-- The base change is continuous. -/
theorem continuous_completionLocMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' (f s) S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' (f s) S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' (f s) S' hden'
    Continuous (completionLocMap P T s S hden P' f hf T' S' hden' hT) :=
  (existsUnique_continuous_ringHom_comp_toCompletionLoc_eq P T s S hden P' f hf T' S' hden'
    hT).choose_spec.1.1

/-- **The base change is compatible with the structure maps**: `A → A⟨T/s⟩` followed by it is
`A → B → B⟨T'/f(s)⟩`. -/
@[simp]
theorem completionLocMap_comp_toCompletionLoc :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' (f s) S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' (f s) S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' (f s) S' hden'
    (completionLocMap P T s S hden P' f hf T' S' hden' hT).comp (toCompletionLoc P T s S hden) =
      (toCompletionLoc P' T' (f s) S' hden').comp f :=
  (existsUnique_continuous_ringHom_comp_toCompletionLoc_eq P T s S hden P' f hf T' S' hden'
    hT).choose_spec.1.2

/-- **The two properties determine the base change**: a continuous ring homomorphism
`A⟨T/s⟩ → B⟨T'/f(s)⟩` carrying the structure map of `A` to that of `B` after `f` is
`completionLocMap`. -/
theorem eq_completionLocMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' (f s) S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' (f s) S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' (f s) S' hden'
    ∀ g : Completion S →+* Completion S', Continuous g →
      g.comp (toCompletionLoc P T s S hden) = (toCompletionLoc P' T' (f s) S' hden').comp f →
      g = completionLocMap P T s S hden P' f hf T' S' hden' hT := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' (f s) S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' (f s) S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' (f s) S' hden'
  exact fun g hgc hge ↦
    (existsUnique_continuous_ringHom_comp_toCompletionLoc_eq P T s S hden P' f hf T' S' hden'
      hT).choose_spec.2 g ⟨hgc, hge⟩

/-- **On the image of `A[1/s]`, the base change is the map of localisations**
`A[1/s] → B[1/f(s)]` induced by `f`, which sends `a/s` to `f(a)/f(s)`
(`RingHom.awayMap_divBy`). -/
@[simp]
theorem completionLocMap_coe (x : S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' (f s) S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' (f s) S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' (f s) S' hden'
    completionLocMap P T s S hden P' f hf T' S' hden' hT (x : Completion S) =
      (IsLocalization.Away.map S S' f s x : Completion S') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' (f s) S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' (f s) S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' (f s) S' hden'
  have h : (completionLocMap P T s S hden P' f hf T' S' hden' hT).comp Completion.coeRingHom =
      Completion.coeRingHom.comp (IsLocalization.Away.map S S' f s) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun a ↦ ?_)
    -- both sides send `a` to the image of `f(a)` in `B⟨T'/f(s)⟩`
    simpa only [RingHom.coe_comp, Completion.coe_coeRingHom, Function.comp_apply,
      IsLocalization.Away.map, IsLocalization.map_eq, toCompletionLoc_apply] using
      RingHom.congr_fun
        (completionLocMap_comp_toCompletionLoc P T s S hden P' f hf T' S' hden' hT) a
  exact RingHom.congr_fun h x

/-! ### The plus rings -/

variable {Aplus : Subring A} {Bplus : Subring B}

omit [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B] in
include hT in
/-- The map of localisations carries `A⁺[T/s]` into `B⁺[T'/f(s)]` as soon as `f` carries `A⁺` into
`B⁺`. -/
private theorem adjoin_plus_map_awayMap_le (hplus : ∀ a ∈ Aplus, f a ∈ Bplus) :
    (Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S))).toSubring.map
        (IsLocalization.Away.map S S' f s) ≤
      (Algebra.adjoin Bplus (Set.range fun t : T' ↦ (divBy (t : B) (f s) : S'))).toSubring := by
  rw [Subring.map_le_iff_le_comap, Algebra.adjoin_eq_ring_closure, Subring.closure_le]
  rintro _ (⟨a, rfl⟩ | ⟨t, rfl⟩)
  · rw [SetLike.mem_coe, Subring.mem_comap, IsScalarTower.algebraMap_apply Aplus A S,
      Algebra.algebraMap_ofSubsemiring_apply, IsLocalization.Away.map, IsLocalization.map_eq]
    exact Subalgebra.algebraMap_mem _ (⟨_, hplus a a.2⟩ : Bplus)
  · rw [SetLike.mem_coe, Subring.mem_comap, RingHom.awayMap_divBy]
    exact Algebra.subset_adjoin ⟨⟨_, hT t t.2⟩, rfl⟩

omit [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B] in
include hT in
/-- The map of localisations carries the integral closure of `A⁺[T/s]` in `A[1/s]` into the
integral closure of `B⁺[T'/f(s)]` in `B[1/f(s)]`. -/
private theorem integralClosure_adjoin_plus_map_awayMap_le (hplus : ∀ a ∈ Aplus, f a ∈ Bplus) :
    (integralClosure ↥(Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S)))
        S).toSubring.map (IsLocalization.Away.map S S' f s) ≤
      (integralClosure ↥(Algebra.adjoin Bplus (Set.range fun t : T' ↦
        (divBy (t : B) (f s) : S'))) S').toSubring := by
  rintro _ ⟨x, hx, rfl⟩
  have hle := adjoin_plus_map_awayMap_le T s S f T' S' hT hplus
  let φ := (IsLocalization.Away.map S S' f s).restrict
    (Algebra.adjoin Aplus (Set.range fun t : T ↦ (divBy (t : A) s : S)))
    (Algebra.adjoin Bplus (Set.range fun t : T' ↦ (divBy (t : B) (f s) : S')))
    fun y hy ↦ hle ⟨y, hy, rfl⟩
  exact IsIntegral.map_of_comp_eq φ _ (by ext; rfl) hx

/-- The base change carries the plus ring `A_U⁺` of `A⟨T/s⟩` built from `A⁺` into the plus ring
`B_V⁺` of `B⟨T'/f(s)⟩` built from `B⁺`, as soon as `f` carries `A⁺` into `B⁺`. The preimage of
`B_V⁺` is a closed subring, so it suffices that it contain the image of the integral closure of
`A⁺[T/s]`. -/
private theorem completionLocMap_mem_completedPlusSubring (hplus : ∀ a ∈ Aplus, f a ∈ Bplus) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P' T' (f s) S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' (f s) S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' (f s) S' hden'
    ∀ x ∈ completedPlusSubring P Aplus T s S hden,
      completionLocMap P T s S hden P' f hf T' S' hden' hT x ∈
        completedPlusSubring P' Bplus T' (f s) S' hden' := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P' T' (f s) S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' (f s) S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' (f s) S' hden'
  have hclosed : IsClosed ((completedPlusSubring P' Bplus T' (f s) S' hden').comap
      (completionLocMap P T s S hden P' f hf T' S' hden' hT) : Set (Completion S)) :=
    (isClosed_completedPlusSubring P' Bplus T' (f s) S' hden').preimage
      (continuous_completionLocMap P T s S hden P' f hf T' S' hden' hT)
  intro x hx
  refine (completedPlusSubring_le_iff P Aplus T s S hden hclosed).mpr (fun c hc ↦ ?_) hx
  rw [Subring.mem_comap, completionLocMap_coe]
  exact coeRingHom_mem_completedPlusSubring P' Bplus T' (f s) S' hden'
    (integralClosure_adjoin_plus_map_awayMap_le T s S f T' S' hT hplus ⟨c, hc, rfl⟩)

end RingHom

/-! ### The base change as a morphism of Huber pairs -/

section Pair

variable [IsHuberRing A] [IsHuberRing B]
  (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus)
  (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)
  (P' : PairOfDefinition B) (U' : Pair B) (hP' : P'.ringOfDefinition ≤ U'.plus)
  (f : Pair.Hom U U') (T' : Finset B) (S' : Type*) [CommRing S'] [Algebra B S']
  [IsLocalization.Away (f.toRingHom s) S'] (hden' : HasDenominatorPower P' T' (f.toRingHom s) S')
  (hT : ∀ t ∈ T, f.toRingHom t ∈ T')

/-- **The base change as a morphism of Huber pairs**
`(A⟨T/s⟩, A_U⁺) → (B⟨T'/f(s)⟩, B_V⁺)`, between the rational localisation pairs of `(A, A⁺)` and of
`(B, B⁺)`, for a morphism of Huber pairs `f : (A, A⁺) → (B, B⁺)`. Its underlying ring
homomorphism is `completionLocMap`. -/
noncomputable def completionLocPairMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' (f.toRingHom s) S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' (f.toRingHom s) S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' (f.toRingHom s) S' hden'
    letI := isHuberRing_completion_locTopology P' T' (f.toRingHom s) S' hden'
    Pair.Hom (rationalLocalizationPair P U hP T s S hden)
      (rationalLocalizationPair P' U' hP' T' (f.toRingHom s) S' hden') :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_completion_locTopology P T s S hden
  letI := locUniformSpace P' T' (f.toRingHom s) S' hden'
  letI := isUniformAddGroup_locUniformSpace P' T' (f.toRingHom s) S' hden'
  letI := isTopologicalRing_locUniformSpace P' T' (f.toRingHom s) S' hden'
  letI := isHuberRing_completion_locTopology P' T' (f.toRingHom s) S' hden'
  { toRingHom := completionLocMap P T s S hden P' f.toRingHom f.continuous_toRingHom.continuousAt
      T' S' hden' hT
    continuous_toRingHom := continuous_completionLocMap P T s S hden P' f.toRingHom
      f.continuous_toRingHom.continuousAt T' S' hden' hT
    map_mem_plus := by
      rw [rationalLocalizationPair_plus, rationalLocalizationPair_plus]
      exact completionLocMap_mem_completedPlusSubring P T s S hden P' f.toRingHom
        f.continuous_toRingHom.continuousAt T' S' hden' hT f.map_mem_plus }

/-- The underlying ring homomorphism of `completionLocPairMap` is `completionLocMap`. -/
@[simp]
theorem toRingHom_completionLocPairMap :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_completion_locTopology P T s S hden
    letI := locUniformSpace P' T' (f.toRingHom s) S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' (f.toRingHom s) S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' (f.toRingHom s) S' hden'
    letI := isHuberRing_completion_locTopology P' T' (f.toRingHom s) S' hden'
    (completionLocPairMap P U hP T s S hden P' U' hP' f T' S' hden' hT).toRingHom =
      completionLocMap P T s S hden P' f.toRingHom f.continuous_toRingHom.continuousAt
        T' S' hden' hT :=
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
    letI := locUniformSpace P' T' (f.toRingHom s) S' hden'
    letI := isUniformAddGroup_locUniformSpace P' T' (f.toRingHom s) S' hden'
    letI := isTopologicalRing_locUniformSpace P' T' (f.toRingHom s) S' hden'
    letI := isHuberRing_completion_locTopology P' T' (f.toRingHom s) S' hden'
    (completionLocPairMap P U hP T s S hden P' U' hP' f T' S' hden' hT).comp
        (toCompletionLocHom P U hP T s S hden) =
      (toCompletionLocHom P' U' hP' T' (f.toRingHom s) S' hden').comp f := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  let _ := locUniformSpace P' T' (f.toRingHom s) S' hden'
  have _ := isUniformAddGroup_locUniformSpace P' T' (f.toRingHom s) S' hden'
  have _ := isTopologicalRing_locUniformSpace P' T' (f.toRingHom s) S' hden'
  have _ := isHuberRing_completion_locTopology P' T' (f.toRingHom s) S' hden'
  apply Pair.Hom.ext
  rw [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_comp, toRingHom_completionLocPairMap,
    toRingHom_toCompletionLocHom, toRingHom_toCompletionLocHom]
  exact completionLocMap_comp_toCompletionLoc P T s S hden P' f.toRingHom
    f.continuous_toRingHom.continuousAt T' S' hden' hT

end Pair

end TauCeti.Huber.PairOfDefinition
