/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.UniversalProperty
public import TauCeti.RingTheory.Huber.LocalizationTopology.CompleteSeparated.RefinementCategory

/-!
# Comparison maps from a containment of rational subsets

`TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_of_refines` compares two coordinate
rings when the second presentation *refines* the first syntactically — `s'' = s * r` with every
`t * r` a numerator. Wedhorn's Proposition 8.2(1) asks for the comparison under the weaker,
geometric hypothesis that the rational subsets are *contained* in one another, and this file
instantiates Lemma 8.1 at a coordinate ring to get it.

> (1) If `U' ⊆ U`, then there exists a unique continuous homomorphism `σ : A⟨T/s⟩ → A⟨T'/s'⟩`
> such that `σ ∘ ρ = ρ'`.

Wedhorn's proof is "follows immediately from Lemma 8.1", and so is the one here: `Spa` of the
structure map `A → A⟨T'/s'⟩` lands in `R(T'/s')` (`spaComapLoc_mem_rationalSubset`), so a
containment `R(T'/s') ⊆ R(T/s)` is exactly the geometric hypothesis of Lemma 8.1.

Applying that in both directions to two presentations of the *same* rational subset gives
presentation independence: each composite fixes the structure map from `A`, hence is the identity,
so the two coordinate rings are canonically isomorphic. That is the shape
`TauCeti.Huber.PairOfDefinition.presentationRingEquiv` has been waiting for — it produces the
isomorphism *given* comparison maps both ways, and this file supplies them from an equality of
rational subsets.

Both results assume only that `A⁺` consists of power-bounded elements, as every ring of integral
elements of `A` does.

## Main definitions

* `TauCeti.ValuationSpectrum.ringHomOfRationalSubsetSubset` and
  `TauCeti.ValuationSpectrum.homOfRationalSubsetSubset` : the comparison map of Proposition
  8.2(1), respectively as a ring homomorphism and as a morphism of complete separated topological
  rings.
* `TauCeti.ValuationSpectrum.presentationRingEquivOfEq` : **presentation independence** — two
  presentations of the same rational subset have canonically isomorphic coordinate rings, by the
  comparison maps in both directions.

## Main results

* `TauCeti.ValuationSpectrum.existsUnique_continuous_ringHom_of_rationalSubset_subset` :
  **Wedhorn's Proposition 8.2(1)** — a containment of rational subsets induces a unique continuous
  comparison map compatible with the structure maps.
* `TauCeti.ValuationSpectrum.restrictionHom_eq_homOfRationalSubsetSubset` : the restriction
  morphism of a refinement is the comparison morphism of the induced containment.

`presentationRingEquivOfEq` is a `def`, so it comes with the lemmas that pin down what it is
without unfolding the proof term: `continuous_presentationRingEquivOfEq` and
`continuous_presentationRingEquivOfEq_symm`, which make it an isomorphism of *topological*
rings, and `presentationRingEquivOfEq_coe_comp_toCompletionLoc` together with its `symm`
counterpart, which say the isomorphism and its inverse commute with the structure maps from `A`.
By the uniqueness in Proposition 8.2(1), that compatibility characterises the isomorphism among
continuous ring homomorphisms, so a consumer needs nothing else.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.2(1),
  Lemma 8.1 and Proposition 7.52(2).

## Provenance

Developed here; nothing is ported. AINTLIB reaches presentation independence through a
height-one reduction resting on unproved bodies, which is not followed.
-/

public section

namespace TauCeti.ValuationSpectrum

open CategoryTheory TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Wedhorn's Proposition 8.2(1).** If the rational subset presented by `T'` over `s'` is
contained in the one presented by `T` over `s`, then exactly one continuous ring homomorphism
`A⟨T/s⟩ → A⟨T'/s'⟩` is compatible with the structure maps from `A`.

This is the containment form of
`TauCeti.Huber.PairOfDefinition.existsUnique_continuous_ringHom_of_refines`, which asks instead that
the second presentation refine the first syntactically. The hypothesis `hAplus` holds whenever
`A⁺` is a ring of integral elements of `A`. -/
theorem existsUnique_continuous_ringHom_of_rationalSubset_subset (P : PairOfDefinition A)
    (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (T' : Finset A) (s' : A) (S' : Type*) [CommRing S']
    [Algebra A S'] [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∃! σ : UniformSpace.Completion S →+* UniformSpace.Completion S',
      Continuous σ ∧ σ.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden' := by
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  have _ := isHuberRing_completion_locTopology P T' s' S' hden'
  -- Wedhorn's proof: Lemma 8.1 for `ρ' : A → A⟨T'/s'⟩` with plus ring `(A⟨T'/s'⟩)°`, a ring of
  -- integral elements of any Huber ring; its hypothesis is that `Spa ρ'` factors through `R(T/s)`
  refine existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset
    P Aplus T s S hden (powerBoundedSubring (UniformSpace.Completion S'))
    ⟨isOpen_powerBoundedSubring _, inferInstance, le_rfl⟩
    (continuous_toCompletionLoc P T' s' S' hden').continuousAt fun w hw ↦ hsub ?_
  -- `A_U⁺ ⊆ (A⟨T'/s'⟩)°`, so `w` is also a point for the plus ring `A_U⁺`; `Spa ρ'` lands in
  -- `R(T'/s')`, and the containment carries it into `R(T/s)`
  have hle := completedPlusSubring_le_powerBoundedSubring P Aplus hAplus T' s' S' hden'
  simpa only [spaComapLoc_val] using
    spaComapLoc_mem_rationalSubset P Aplus T' s' S' hden' ⟨w, spa_antitone hle hw⟩

/-- **The comparison map of Wedhorn's Proposition 8.2(1)**: for a containment `R(T'/s') ⊆ R(T/s)`
of rational subsets, the continuous ring homomorphism `A⟨T/s⟩ → A⟨T'/s'⟩` compatible with the
structure maps from `A`, which is unique by
`existsUnique_continuous_ringHom_of_rationalSubset_subset`.

The body is not exported: consumers use `continuous_ringHomOfRationalSubsetSubset` and
`ringHomOfRationalSubsetSubset_comp_toCompletionLoc`. -/
noncomputable def ringHomOfRationalSubsetSubset (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    UniformSpace.Completion S →+* UniformSpace.Completion S' :=
  -- the map is data, so it is extracted with `Exists.choose`; `obtain` would be eliminating an
  -- `ExistsUnique` (a `Prop`) into `Type`
  (existsUnique_continuous_ringHom_of_rationalSubset_subset P Aplus hAplus T s S hden T' s' S' hden'
    hsub).choose

/-- The comparison map of Wedhorn's Proposition 8.2(1) is continuous. -/
theorem continuous_ringHomOfRationalSubsetSubset (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    Continuous (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub) :=
  (existsUnique_continuous_ringHom_of_rationalSubset_subset P Aplus hAplus T s S hden T' s' S' hden'
    hsub).choose_spec.1.1

/-- The comparison map of Wedhorn's Proposition 8.2(1) is compatible with the structure maps
from `A`. -/
@[simp]
theorem ringHomOfRationalSubsetSubset_comp_toCompletionLoc (P : PairOfDefinition A)
    (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (T' : Finset A) (s' : A) (S' : Type*) [CommRing S']
    [Algebra A S'] [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub).comp
      (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden' :=
  (existsUnique_continuous_ringHom_of_rationalSubset_subset P Aplus hAplus T s S hden T' s' S' hden'
    hsub).choose_spec.1.2

/-- **Uniqueness of the comparison map**: `ringHomOfRationalSubsetSubset` is the only continuous
ring homomorphism `A⟨T/s⟩ → A⟨T'/s'⟩` compatible with the structure maps from `A`. -/
theorem eq_ringHomOfRationalSubsetSubset (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (hsub : rationalSubset Aplus T' s' ⊆ rationalSubset Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ g : UniformSpace.Completion S →+* UniformSpace.Completion S',
      Continuous g → g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden' →
      g = ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' hsub :=
  fun g hgc hge ↦ (existsUnique_continuous_ringHom_of_rationalSubset_subset P Aplus hAplus
    T s S hden T' s' S' hden' hsub).choose_spec.2 g ⟨hgc, hge⟩

/-! ### Comparison morphisms between completed rational localizations -/

/-- **The comparison morphism of a containment** `R(q) ⊆ R(p)`: Wedhorn's Proposition 8.2(1) map
`A⟨p⟩ → A⟨q⟩`, the unique continuous ring homomorphism compatible with the structure maps from `A`,
as a morphism of `CompleteSeparatedTopCommRingCat`. -/
noncomputable def homOfRationalSubsetSubset (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) {P : PairOfDefinition A}
    {p q : Presentation P}
    (h : rationalSubset Aplus q.num q.den ⊆ rationalSubset Aplus p.num p.den) :
    p.completionLocObj ⟶ q.completionLocObj :=
  completionLocObjHom P p.num p.den _ p.hasDenominatorPower q.num q.den _ q.hasDenominatorPower
    (ringHomOfRationalSubsetSubset P Aplus hAplus p.num p.den _ p.hasDenominatorPower q.num q.den _
      q.hasDenominatorPower h)
    (continuous_ringHomOfRationalSubsetSubset P Aplus hAplus p.num p.den _ p.hasDenominatorPower
      q.num q.den _ q.hasDenominatorPower h)

/-- The comparison morphism of `R(p) ⊆ R(p)` is the identity. -/
@[simp]
theorem homOfRationalSubsetSubset_self (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) {P : PairOfDefinition A}
    {p : Presentation P}
    (h : rationalSubset Aplus p.num p.den ⊆ rationalSubset Aplus p.num p.den) :
    homOfRationalSubsetSubset Aplus hAplus h = 𝟙 p.completionLocObj :=
  completionLocObjHom_eq_id P p.num p.den _ p.hasDenominatorPower _ _
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus p.num p.den _
      p.hasDenominatorPower p.num p.den _ p.hasDenominatorPower h)

/-- Comparison morphisms compose along a chain of containments. -/
@[reassoc (attr := simp)]
theorem homOfRationalSubsetSubset_comp (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) {P : PairOfDefinition A}
    {p q w : Presentation P}
    (h₁ : rationalSubset Aplus q.num q.den ⊆ rationalSubset Aplus p.num p.den)
    (h₂ : rationalSubset Aplus w.num w.den ⊆ rationalSubset Aplus q.num q.den) :
    homOfRationalSubsetSubset Aplus hAplus h₁ ≫ homOfRationalSubsetSubset Aplus hAplus h₂ =
      homOfRationalSubsetSubset Aplus hAplus (h₂.trans h₁) :=
  (completionLocObjHom_eq_comp P p.num p.den _ p.hasDenominatorPower q.num q.den _
    q.hasDenominatorPower w.num w.den _ w.hasDenominatorPower _ _ _ _ _ _
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus _ _ _ _ _ _ _ _ h₁)
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus _ _ _ _ _ _ _ _ h₂)
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus _ _ _ _ _ _ _ _
      (h₂.trans h₁))).symm

/-- **The restriction morphism of a refinement is a comparison morphism**: both are continuous
and compatible with the structure maps from `A`, which determines the map. -/
theorem restrictionHom_eq_homOfRationalSubsetSubset (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) {P : PairOfDefinition A}
    {p q : Presentation P} (h : p ≤ q) :
    Presentation.restrictionHom h =
      homOfRationalSubsetSubset Aplus hAplus
        (rationalSubset_subset_rationalSubset_of_le Aplus h) := by
  obtain ⟨r, hr, hT⟩ := Presentation.le_def.mp h
  rw [Presentation.restrictionHom_eq h r hr hT, restrictionObjHom_eq_completionLocObjHom]
  -- both are `completionLocObjHom` of a ring homomorphism; the two ring homomorphisms agree by
  -- the uniqueness in Proposition 8.2(1)
  unfold homOfRationalSubsetSubset
  congr 1
  exact eq_ringHomOfRationalSubsetSubset P Aplus hAplus _ _ _ _ _ _ _ _ _ _
    (continuous_restrictionRingHom P _ _ _ _ _ _ _ _ r hr hT)
    (restrictionRingHom_comp_toCompletionLoc P _ _ _ _ _ _ _ _ r hr hT)

/-- **Presentation independence**: two presentations of the *same* rational subset have
canonically isomorphic coordinate rings.

It is `TauCeti.Huber.PairOfDefinition.presentationRingEquiv` at the comparison maps that
`existsUnique_continuous_ringHom_of_rationalSubset_subset` gives for the two containments, so it
needs only the equality `heq` of rational subsets. The body is not exported: consumers use
`presentationRingEquivOfEq_coe_comp_toCompletionLoc`, `continuous_presentationRingEquivOfEq` and
their `symm` counterparts. -/
noncomputable def presentationRingEquivOfEq (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (heq : rationalSubset Aplus T s = rationalSubset Aplus T' s') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    UniformSpace.Completion S ≃+* UniformSpace.Completion S' :=
  -- Wedhorn's Proposition 8.2(1) in both directions gives the comparison maps, and
  -- `presentationRingEquiv` turns them into an isomorphism: each composite is compatible with the
  -- structure map from `A`, hence is the identity
  presentationRingEquiv P T s S hden T' s' S' hden'
    (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' heq.ge)
    (ringHomOfRationalSubsetSubset P Aplus hAplus T' s' S' hden' T s S hden heq.le)
    (continuous_ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' heq.ge)
    (continuous_ringHomOfRationalSubsetSubset P Aplus hAplus T' s' S' hden' T s S hden heq.le)
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus T s S hden T' s' S' hden'
      heq.ge)
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus T' s' S' hden' T s S hden
      heq.le)

/-- The presentation-independence isomorphism is continuous. -/
theorem continuous_presentationRingEquivOfEq (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (heq : rationalSubset Aplus T s = rationalSubset Aplus T' s') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    Continuous (presentationRingEquivOfEq P Aplus hAplus T s S hden T' s' S' hden' heq) :=
  continuous_presentationRingEquiv P T s S hden T' s' S' hden'
    (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' heq.ge)
    (ringHomOfRationalSubsetSubset P Aplus hAplus T' s' S' hden' T s S hden heq.le)
    (continuous_ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' heq.ge)
    (continuous_ringHomOfRationalSubsetSubset P Aplus hAplus T' s' S' hden' T s S hden heq.le)
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus T s S hden T' s' S' hden'
      heq.ge)
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus T' s' S' hden' T s S hden
      heq.le)

/-- The presentation-independence isomorphism is compatible with the structure maps from `A`;
among continuous ring homomorphisms `A⟨T/s⟩ → A⟨T'/s'⟩` this compatibility characterises it
(`existsUnique_continuous_ringHom_of_rationalSubset_subset`). -/
theorem presentationRingEquivOfEq_coe_comp_toCompletionLoc (P : PairOfDefinition A)
    (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (T' : Finset A) (s' : A) (S' : Type*) [CommRing S']
    [Algebra A S'] [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (heq : rationalSubset Aplus T s = rationalSubset Aplus T' s') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    (presentationRingEquivOfEq P Aplus hAplus T s S hden T' s' S' hden' heq : _ →+* _).comp
      (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden' :=
  presentationRingEquiv_coe_comp_toCompletionLoc P T s S hden T' s' S' hden'
    (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' heq.ge)
    (ringHomOfRationalSubsetSubset P Aplus hAplus T' s' S' hden' T s S hden heq.le)
    (continuous_ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' heq.ge)
    (continuous_ringHomOfRationalSubsetSubset P Aplus hAplus T' s' S' hden' T s S hden heq.le)
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus T s S hden T' s' S' hden'
      heq.ge)
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus T' s' S' hden' T s S hden
      heq.le)

/-- The inverse of the presentation-independence isomorphism is compatible with the structure maps
from `A`: the `symm` counterpart of `presentationRingEquivOfEq_coe_comp_toCompletionLoc`. -/
theorem presentationRingEquivOfEq_symm_coe_comp_toCompletionLoc (P : PairOfDefinition A)
    (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (T' : Finset A) (s' : A) (S' : Type*) [CommRing S']
    [Algebra A S'] [IsLocalization.Away s' S'] (hden' : HasDenominatorPower P T' s' S')
    (heq : rationalSubset Aplus T s = rationalSubset Aplus T' s') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ((presentationRingEquivOfEq P Aplus hAplus T s S hden T' s' S' hden' heq).symm : _ →+* _).comp
      (toCompletionLoc P T' s' S' hden') = toCompletionLoc P T s S hden := by
  -- the forward compatibility, rewritten backwards, leaves the isomorphism composed with its
  -- inverse, which cancels
  simp [← presentationRingEquivOfEq_coe_comp_toCompletionLoc P Aplus hAplus T s S hden T' s' S'
    hden' heq, ← RingHom.comp_assoc]

/-- The inverse of the presentation-independence isomorphism is continuous, so together with
`continuous_presentationRingEquivOfEq` the isomorphism is one of topological rings. -/
theorem continuous_presentationRingEquivOfEq_symm (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (T : Finset A) (s : A) (S : Type*) [CommRing S]
    [Algebra A S] [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) (T' : Finset A)
    (s' : A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (heq : rationalSubset Aplus T s = rationalSubset Aplus T' s') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    Continuous (presentationRingEquivOfEq P Aplus hAplus T s S hden T' s' S' hden' heq).symm :=
  continuous_presentationRingEquiv_symm P T s S hden T' s' S' hden'
    (ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' heq.ge)
    (ringHomOfRationalSubsetSubset P Aplus hAplus T' s' S' hden' T s S hden heq.le)
    (continuous_ringHomOfRationalSubsetSubset P Aplus hAplus T s S hden T' s' S' hden' heq.ge)
    (continuous_ringHomOfRationalSubsetSubset P Aplus hAplus T' s' S' hden' T s S hden heq.le)
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus T s S hden T' s' S' hden'
      heq.ge)
    (ringHomOfRationalSubsetSubset_comp_toCompletionLoc P Aplus hAplus T' s' S' hden' T s S hden
      heq.le)

end TauCeti.ValuationSpectrum
