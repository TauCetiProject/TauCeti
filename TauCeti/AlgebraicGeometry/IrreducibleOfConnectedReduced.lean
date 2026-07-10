/-
Copyright (c) 2026 daouid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib

/-!
# Irreducible components of a connected reduced scheme

This file provides the topological results needed to show that a connected scheme
whose stalks are integral domains is an irreducible space. It deconstructs the
bijection between minimal primes of the stalks and the irreducible components,
and proves that such irreducible components are open and disjoint.

This advances the roadmap at TauCetiRoadmap/JacobianChallenge/README.md.
-/

public section

open TopologicalSpace Set AlgebraicGeometry Topology CategoryTheory PrimeSpectrum

universe u

namespace TauCeti

namespace AlgebraicGeometry

/-- Auxiliary declaration. -/
private lemma image_mem_irreducibleComponents {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : IsOpenEmbedding f) {c : Set α}
    (hc : c ∈ irreducibleComponents α) :
    closure (f '' c) ∈ irreducibleComponents β := by
  have hIrred : IsIrreducible (closure (f '' c)) :=
    isIrreducible_iff_closure.mpr (hc.1.image f hf.continuous.continuousOn)
  refine ⟨hIrred, fun u hu hSub => ?_⟩
  have hClIrred : IsIrreducible (closure u) := isIrreducible_iff_closure.mpr hu
  have ⟨x, hx⟩ := hc.1.nonempty
  have hClNonempty : ((closure u) ∩ range f).Nonempty :=
    ⟨f x, subset_closure (hSub (subset_closure (mem_image_of_mem f hx))), ⟨x, rfl⟩⟩
  have hPreIrred : IsIrreducible (f ⁻¹' (closure u)) :=
    IsIrreducible.preimage hClIrred hf hClNonempty
  have hSubPre : c ⊆ f ⁻¹' (closure u) :=
    image_subset_iff.mp (subset_closure.trans (hSub.trans subset_closure))
  have hEq : c = f ⁻¹' (closure u) := hSubPre.antisymm (hc.2 hPreIrred hSubPre)
  rw [hEq, closure_image_preimage_of_isPreirreducible f hf.isOpenMap (closure u)
    (nonempty_preimage_iff.mpr hClNonempty) hClIrred.2 isClosed_closure]
  exact subset_closure

/-- Auxiliary declaration. -/
private def irreducibleComponents_containing_equiv_of_isOpenEmbedding
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : IsOpenEmbedding f) (x : α) :
    { c : irreducibleComponents α // x ∈ (c : Set α) } ≃
    { c : irreducibleComponents β // f x ∈ (c : Set β) } where
  toFun c := ⟨⟨closure (f '' c.val.val), image_mem_irreducibleComponents hf c.val.property⟩, by
    dsimp
    exact subset_closure (mem_image_of_mem f c.property)⟩
  invFun c' :=
    have hNonempty : (c'.val.val ∩ range f).Nonempty := ⟨f x, c'.property, ⟨x, rfl⟩⟩
    ⟨⟨f ⁻¹' c'.val.val, preimage_mem_irreducibleComponents c'.val.property hf hNonempty⟩,
      c'.property⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    exact hf.isOpenMap.preimage_closure_image hf.injective hf.continuous c.val.val
      (isClosed_of_mem_irreducibleComponents c.val.val c.val.property)
  right_inv c' := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    exact closure_image_preimage_of_isPreirreducible f hf.isOpenMap c'.val.val
      ⟨x, c'.property⟩ c'.val.property.1.2
      (isClosed_of_mem_irreducibleComponents c'.val.val c'.val.property)

/-- Auxiliary declaration. -/
private lemma minimalPrimes_map_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (hI : I ∈ minimalPrimes A) :
    Ideal.map e I ∈ minimalPrimes B := by
  change IsMinimalPrime I at hI
  haveI : I.IsPrime := hI.1.1
  haveI : (Ideal.map e I).IsPrime := Ideal.map_isPrime_of_equiv e
  refine ⟨⟨‹_›, bot_le⟩, fun q hq hle ↦ ?_⟩
  haveI : q.IsPrime := hq.1
  have h_le : Ideal.comap e q ≤ I := by
    have := Ideal.comap_mono (f := e) hle
    rw [Ideal.comap_map_of_bijective e e.bijective] at this
    exact this
  haveI : (Ideal.comap e q).IsPrime := inferInstance
  have h_eq := hI.eq_of_le ⟨‹_›, bot_le⟩ h_le
  rw [← Ideal.map_comap_of_surjective e e.surjective q, h_eq]

/-- Auxiliary declaration. -/
private lemma minimalPrimes_map_iff {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) :
    Ideal.map e I ∈ minimalPrimes B ↔ I ∈ minimalPrimes A := by
  refine ⟨fun h ↦ ?_, minimalPrimes_map_of_ringEquiv e I⟩
  have := minimalPrimes_map_of_ringEquiv e.symm (Ideal.map e I) h
  rw [Ideal.map_symm, Ideal.comap_map_of_bijective e e.bijective] at this
  exact this

/-- Ring isomorphism preserves minimal primes. -/
private def minimalPrimes_equiv_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : minimalPrimes A ≃ minimalPrimes B where
  toFun p := ⟨Ideal.map e p.val, (minimalPrimes_map_iff e p.val).mpr p.property⟩
  invFun q := ⟨Ideal.map e.symm q.val, (minimalPrimes_map_iff e.symm q.val).mpr q.property⟩
  left_inv p := Subtype.ext
    (by dsimp; rw [Ideal.map_symm, Ideal.comap_map_of_bijective e e.bijective])
  right_inv q := Subtype.ext
    (by dsimp; rw [Ideal.map_symm, Ideal.map_comap_of_surjective e e.surjective])

/-- Auxiliary declaration. -/
private lemma disjoint_primeCompl_iff {R : Type*} [CommRing R] {I J : Ideal R} [I.IsPrime] :
    Disjoint (I.primeCompl : Set R) (J : Set R) ↔ J ≤ I :=
  Set.disjoint_compl_left_iff_subset

/-- Auxiliary declaration. -/
private lemma comap_le_p_of_mem_minimalPrimes {R : Type*} [CommRing R] (p : PrimeSpectrum R)
    (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    (hS : S = p.asIdeal.primeCompl) (q' : minimalPrimes A) :
    q'.val.comap (algebraMap R A) ≤ p.asIdeal := by
  haveI : q'.val.IsPrime := q'.property.1.1
  have hDisj := (IsLocalization.isPrime_iff_isPrime_disjoint S A q'.val).mp ‹_› |>.2
  rwa [hS, disjoint_primeCompl_iff] at hDisj

/-- Auxiliary declaration. -/
private def minimalPrimesEquivMinimalPrimesLe {R : Type*} [CommRing R] (p : PrimeSpectrum R)
    (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    (hS : S = p.asIdeal.primeCompl) :
    minimalPrimes A ≃ { q : minimalPrimes R // q.val ≤ p.asIdeal } where
  toFun q' := ⟨⟨q'.val.comap (algebraMap R A), by
    change q'.val ∈ Ideal.under R ⁻¹' (⊥ : Ideal R).minimalPrimes
    rw [← IsLocalization.minimalPrimes_map S A ⊥, Ideal.map_bot]
    exact q'.property⟩, comap_le_p_of_mem_minimalPrimes p S A hS q'⟩
  invFun q := ⟨q.val.val.map (algebraMap R A), by
    have hMap := IsLocalization.minimalPrimes_map S A (⊥ : Ideal R)
    rw [Ideal.map_bot] at hMap
    change q.val.val.map (algebraMap R A) ∈ (⊥ : Ideal A).minimalPrimes
    rw [hMap]
    have hI' : Disjoint (S : Set R) (q.val.val : Set R) := by
      rw [hS, disjoint_primeCompl_iff]
      exact q.property
    haveI : q.val.val.IsPrime := q.val.property.1.1
    have hEq := IsLocalization.under_map_of_isPrime_disjoint S A ‹_› hI'
    change Ideal.under R (Ideal.map (algebraMap R A) q.val.val) ∈ minimalPrimes R
    rw [hEq]
    exact q.val.property⟩
  left_inv q' := Subtype.ext (IsLocalization.map_under S A q'.val)
  right_inv q := Subtype.ext <| Subtype.ext <| by
    have hI' : Disjoint (S : Set R) (q.val.val : Set R) := by
      rw [hS, disjoint_primeCompl_iff]
      exact q.property
    haveI : q.val.val.IsPrime := q.val.property.1.1
    exact IsLocalization.under_map_of_isPrime_disjoint S A ‹_› hI'



/-- Equivalence between minimal primes and irreducible components. -/
private noncomputable def equiv_clean (R : Type*) [CommRing R] :
    minimalPrimes R ≃ irreducibleComponents (PrimeSpectrum R) where
  toFun q := ⟨zeroLocus q.val, by
    rw [zeroLocus_ideal_mem_irreducibleComponents, q.property.1.1.radical]
    exact q.property⟩
  invFun c := ⟨vanishingIdeal c.val, by
    have hcClosed : IsClosed c.val :=
      isClosed_of_mem_irreducibleComponents c.val c.property
    have hcIrred : IsIrreducible c.val := c.property.1
    rw [isIrreducible_iff_vanishingIdeal_isPrime] at hcIrred
    refine ⟨⟨hcIrred, bot_le⟩, fun I hI hIsub ↦ ?_⟩
    haveI : I.IsPrime := hI.left
    have h2 : IsIrreducible (zeroLocus (I : Set R)) := by
      rw [isIrreducible_iff_vanishingIdeal_isPrime, vanishingIdeal_zeroLocus_eq_radical,
        Ideal.IsPrime.radical hI.left]
      exact hI.left
    have hSub' : c.val ⊆ zeroLocus (I : Set R) := by
      rw [← closure_eq_iff_isClosed.mpr hcClosed]
      rw [← zeroLocus_vanishingIdeal_eq_closure]
      exact zeroLocus_anti_mono_ideal hIsub
    have hEq := c.property.2 h2 hSub'
    have hEq_val : c.val = zeroLocus (I : Set R) := hSub'.antisymm hEq
    rw [hEq_val, vanishingIdeal_zeroLocus_eq_radical, Ideal.IsPrime.radical hI.left]⟩
  left_inv q := Subtype.ext (by
    dsimp
    rw [vanishingIdeal_zeroLocus_eq_radical]
    exact q.property.1.1.radical)
  right_inv c := Subtype.ext (by
    dsimp
    have hcClosed : IsClosed c.val :=
      isClosed_of_mem_irreducibleComponents c.val c.property
    rw [zeroLocus_vanishingIdeal_eq_closure, closure_eq_iff_isClosed.mpr hcClosed])

private lemma equiv_clean_val {R : Type*} [CommRing R] (q : minimalPrimes R) :
    ((equiv_clean R q : irreducibleComponents (PrimeSpectrum R)) :
      Set (PrimeSpectrum R)) = zeroLocus q.val :=
  rfl

/-- Auxiliary declaration. -/
private noncomputable def irreducibleComponentsContainingEquivMinimalPrimesLe (R : Type*)
    [CommRing R] (p : PrimeSpectrum R) :
    { c : irreducibleComponents (PrimeSpectrum R) // p ∈ (c : Set (PrimeSpectrum R)) } ≃
      { q : minimalPrimes R // q.val ≤ p.asIdeal } :=
  Equiv.subtypeEquiv (equiv_clean R).symm (fun c ↦ by
    obtain ⟨q, rfl⟩ := (equiv_clean R).surjective c
    rw [Equiv.symm_apply_apply]
    rw [equiv_clean_val, mem_zeroLocus, SetLike.coe_subset_coe]
  )

/-- For an affine scheme Spec R, the minimal prime ideals of the local ring (stalk)
at a point p (which is a prime ideal of R) are in bijection with the irreducible components
of Spec R containing p.
This is the affine case of the bijection between minimal primes of stalks and irreducible
components containing the point. -/
private noncomputable def equiv_minimalPrimes_irreducibleComponents_spec
    (R : Type*) [CommRing R] (p : PrimeSpectrum R) :
    minimalPrimes (Localization.AtPrime p.asIdeal) ≃
      { c : irreducibleComponents (PrimeSpectrum R) // p ∈ (c : Set (PrimeSpectrum R)) } :=
  (minimalPrimesEquivMinimalPrimesLe p p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) rfl).trans
    (irreducibleComponentsContainingEquivMinimalPrimesLe R p).symm

/-- The minimal prime ideals of the stalk of a scheme at a point x are in bijection
with the irreducible components of the scheme containing x.
We construct this by deconstructing the global scheme-theoretic bijection into:
1. The topological bijection under open embeddings
   (`irreducibleComponents_containing_equiv_of_isOpenEmbedding`).
2. The affine spectrum case (`equiv_minimalPrimes_irreducibleComponents_spec`).
3. Stalk isomorphism and ring isomorphism preservation of minimal primes. -/
noncomputable def equiv_minimalPrimes_irreducibleComponents {X : Scheme} (x : X.carrier) :
    minimalPrimes (X.presheaf.stalk x) ≃
      { c : irreducibleComponents X.carrier // x ∈ (c : Set X.carrier) } := by
  let i := X.affineCover.idx x
  let f := X.affineCover.f i
  have hf : IsOpenEmbedding f.1.base := f.isOpenEmbedding
  have hCov := X.affineCover.covers x
  let y := Classical.choose hCov
  have hy : f.1.base y = x := Classical.choose_spec hCov
  have eStalk := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  let U := X.affineCover.X i
  have eStalkX : X.presheaf.stalk x ≃+* U.presheaf.stalk y := by
    rw [← hy]
    exact eStalk
  let hEq1 := minimalPrimes_equiv_of_ringEquiv eStalkX
  let R := Γ(U, ⊤)
  let g := U.isoSpec
  let eHomeo := Scheme.homeoOfIso g
  let y_spec : PrimeSpectrum R := g.hom.1.1.base y
  have eStalkSpecG := (asIso (g.hom.stalkMap y)).commRingCatIsoToRingEquiv.symm
  let eStalk2 := (Spec.stalkIso R y_spec).commRingCatIsoToRingEquiv
  let eStalkSpec := eStalkSpecG.trans eStalk2
  let hEq2 := minimalPrimes_equiv_of_ringEquiv eStalkSpec
  let hEq3 := equiv_minimalPrimes_irreducibleComponents_spec R y_spec
  have hYspec : eHomeo.symm y_spec = y := by
    dsimp [y_spec, eHomeo, g]
    simp
  have hEq4 : { c : irreducibleComponents (PrimeSpectrum R) //
      y_spec ∈ (c : Set (PrimeSpectrum R)) } ≃
      { c : irreducibleComponents U.carrier // y ∈ (c : Set U.carrier) } := by
    have := irreducibleComponents_containing_equiv_of_isOpenEmbedding
      eHomeo.symm.isOpenEmbedding y_spec
    rwa [hYspec] at this
  have hEq5 : { c : irreducibleComponents U.carrier // y ∈ (c : Set U.carrier) } ≃
      { c : irreducibleComponents X.carrier // x ∈ (c : Set X.carrier) } := by
    have := irreducibleComponents_containing_equiv_of_isOpenEmbedding hf y
    rwa [hy] at this
  exact hEq1.trans (hEq2.trans (hEq3.trans (hEq4.trans hEq5)))

/-- Ring equivalence preserves the property of being an integral domain. -/
private lemma isDomain_of_ringEquiv {A B : Type*} [CommRing A] [IsDomain A]
    [CommRing B] (e : A ≃+* B) :
    IsDomain B :=
  e.symm.injective.isDomain (e.symm : B →+* A)

/-- Auxiliary declaration. -/
private lemma isOpen_of_open_cover {α : Type*} [TopologicalSpace α] {ι : Type*}
    (U : ι → Set α) (hUCov : (⋃ i, U i) = univ)
    (s : Set α) (hs : ∀ i, IsOpen (s ∩ U i)) : IsOpen s := by
  have hEq : s = ⋃ i, s ∩ U i := by
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      have hIn : x ∈ ⋃ i, U i := by rw [hUCov]; exact mem_univ x
      rcases mem_iUnion.mp hIn with ⟨i, hi⟩
      exact ⟨i, hx, hi⟩
    · rintro ⟨i, hx, _⟩
      exact hx
  rw [hEq]
  exact isOpen_iUnion hs

/-- A point in a scheme whose stalk is a domain belongs to a unique irreducible component. -/
lemma unique_irreducible_component_of_stalk_domain {X : Scheme} (x : X.carrier)
  (hStalks : IsDomain (X.presheaf.stalk x)) :
  ∃! c : irreducibleComponents X.carrier, x ∈ (c : Set X.carrier) := by
  have e := equiv_minimalPrimes_irreducibleComponents x
  haveI : Unique (minimalPrimes (X.presheaf.stalk x)) := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot (X.presheaf.stalk x)]
    exact Set.uniqueSingleton ⊥
  haveI hUniqSub : Unique { c : irreducibleComponents X.carrier // x ∈ (c : Set X.carrier) } :=
    Equiv.unique e.symm
  exact ⟨hUniqSub.default.1, hUniqSub.default.2,
    fun c hc => congrArg Subtype.val (hUniqSub.uniq ⟨c, hc⟩)⟩

/-- In a scheme whose stalks are domains, the irreducible components are disjoint. -/
lemma disjoint_irreducible_components_of_reduced_no_embedded {Z : Scheme}
  (hStalks : ∀ x : Z.carrier, IsDomain (Z.presheaf.stalk x)) :
  ∀ c1 c2 : irreducibleComponents Z.carrier, c1 ≠ c2 →
    Disjoint (c1 : Set Z.carrier) (c2 : Set Z.carrier) := by
  intro c1 c2 hneq
  rw [Set.disjoint_iff]
  intro x hx
  have hx1 : x ∈ (c1 : Set Z.carrier) := hx.1
  have hx2 : x ∈ (c2 : Set Z.carrier) := hx.2
  have h_unique := unique_irreducible_component_of_stalk_domain x (hStalks x)
  obtain ⟨c, _, hcUniq⟩ := h_unique
  have hEq1 : c1 = c := hcUniq c1 hx1
  have hEq2 : c2 = c := hcUniq c2 hx2
  rw [hEq1, hEq2] at hneq
  exact hneq rfl

/-- Auxiliary declaration. -/
lemma isOpen_irreducibleComponents_of_pairwise_disjoint {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] (hDisj : ∀ c1 c2 : irreducibleComponents α, c1 ≠ c2 →
      Disjoint (c1 : Set α) (c2 : Set α))
    (c : irreducibleComponents α) : IsOpen (c : Set α) := by
  have hX : (irreducibleComponents α).Finite := NoetherianSpace.finite_irreducibleComponents
  have hEq : (c : Set α) = (⋃ c' ∈ (irreducibleComponents α \ {c.val}), c')ᶜ := by
    ext x
    simp only [mem_compl_iff, mem_iUnion, mem_sdiff, mem_singleton_iff]
    constructor
    · intro hx
      rintro ⟨c', ⟨hc', hneq⟩, hxc'⟩
      have hDisj' := hDisj c ⟨c', hc'⟩ (fun heq => hneq (congrArg Subtype.val heq).symm)
      exact hDisj'.le_bot ⟨hx, hxc'⟩
    · intro hx
      have hUniv : x ∈ ⋃₀ (irreducibleComponents α) := by
        rw [sUnion_irreducibleComponents]
        exact mem_univ x
      rcases hUniv with ⟨c', hc'S, hxc'⟩
      by_contra hc
      apply hx
      refine ⟨c', ⟨hc'S, ?_⟩, hxc'⟩
      intro heq
      exact hc (heq ▸ hxc')
  rw [hEq]
  rw [isOpen_compl_iff]
  exact Set.Finite.isClosed_biUnion hX.sdiff
    (fun t ht => isClosed_of_mem_irreducibleComponents t ht.1)

/-- In an affine scheme whose stalks are domains, every irreducible component is open. -/
theorem isOpen_irreducibleComponents_of_affine_stalks_domain {X : Scheme.{u}} [IsAffine X]
    [IsLocallyNoetherian X] (hStalks : ∀ x : X.carrier, IsDomain (X.presheaf.stalk x))
    (c : irreducibleComponents X.carrier) : IsOpen (c : Set X.carrier) := by
  haveI : NoetherianSpace X.carrier :=
    @noetherianSpace_of_isAffine X _
      (IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩)
  apply isOpen_irreducibleComponents_of_pairwise_disjoint
  exact disjoint_irreducible_components_of_reduced_no_embedded hStalks

/-- In a scheme whose stalks are domains, every irreducible component is open.
We prove this by gluing the local result for affine schemes. -/
theorem isOpen_irreducibleComponents_of_stalks_domain {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (hStalks : ∀ x : Z.carrier, IsDomain (Z.presheaf.stalk x))
    (c : irreducibleComponents Z.carrier) :
    IsOpen (c : Set Z.carrier) := by
  apply isOpen_of_open_cover (fun j => Set.range (Z.affineCover.f j).1.base)
    Z.affineCover.iUnion_range
  intro j
  let f := Z.affineCover.f j
  have hf : IsOpenEmbedding f.1.base := f.isOpenEmbedding
  rw [← image_preimage_eq_inter_range]
  apply hf.isOpenMap
  let Y := Z.affineCover.X j
  have hStalksY : ∀ y : Y.carrier, IsDomain (Y.presheaf.stalk y) := by
    intro y
    haveI : IsDomain (Z.presheaf.stalk (f.1.base y)) := hStalks (f.1.base y)
    exact isDomain_of_ringEquiv (asIso <| f.stalkMap y).commRingCatIsoToRingEquiv
  by_cases hEmpty : (f.1.base ⁻¹' (c : Set Z.carrier)).Nonempty
  · have hNonempty : ((c : Set Z.carrier) ∩ Set.range f.1.base).Nonempty := by
      obtain ⟨x, hx⟩ := hEmpty
      exact ⟨f.1.base x, hx, ⟨x, rfl⟩⟩
    have hComp : f.1.base ⁻¹' (c : Set Z.carrier) ∈ irreducibleComponents Y.carrier :=
      preimage_mem_irreducibleComponents c.property hf hNonempty
    have hOpen := isOpen_irreducibleComponents_of_affine_stalks_domain hStalksY ⟨_, hComp⟩
    exact hOpen
  · rw [Set.not_nonempty_iff_eq_empty] at hEmpty
    rw [hEmpty]
    exact isOpen_empty

/-- Auxiliary declaration. -/
private lemma compl_sUnion_eq_sUnion_diff {α : Type*} {S : Set (Set α)}
    (hDisj : PairwiseDisjoint S id) (hCov : ⋃₀ S = univ)
    (T : Set (Set α)) (hT : T ⊆ S) :
    (⋃₀ T)ᶜ = ⋃₀ (S \ T) := by
  ext x
  simp only [mem_compl_iff, mem_sUnion, mem_sdiff]
  constructor
  · intro hx
    have hIn : x ∈ ⋃₀ S := by
      rw [hCov]
      exact mem_univ x
    rcases hIn with ⟨s, hsS, hxs⟩
    use s
    refine ⟨⟨hsS, ?_⟩, hxs⟩
    intro hsT
    exact hx ⟨s, hsT, hxs⟩
  · rintro ⟨s, ⟨hsS, hsT⟩, hxs⟩ ⟨t, htT, hxt⟩
    have htS := hT htT
    have hEq : s = t := by
      by_contra hc
      have hDisj' := hDisj hsS htS hc
      exact hDisj'.le_bot ⟨hxs, hxt⟩
    subst hEq
    exact hsT htT

/-- Auxiliary declaration. -/
private lemma isClosed_sUnion_of_disjoint_isOpen {α : Type*} [TopologicalSpace α]
    {S : Set (Set α)} (hDisj : PairwiseDisjoint S id) (hOpen : ∀ s ∈ S, IsOpen s)
    (hCov : ⋃₀ S = univ) (T : Set (Set α)) (hT : T ⊆ S) :
    IsClosed (⋃₀ T) := by
  rw [← isOpen_compl_iff]
  rw [compl_sUnion_eq_sUnion_diff hDisj hCov T hT]
  apply isOpen_sUnion
  rintro s ⟨hsS, _⟩
  exact hOpen s hsS

/-- Auxiliary declaration. -/
private lemma sUnion_other_eq_iUnion_other {α : Type*} (S : Set (Set α)) (c : { x // x ∈ S }) :
    (⋃ c' ∈ {c' : { x // x ∈ S } | c' ≠ c}, (c' : Set α)) = ⋃₀ (S \ {c.val}) := by
  ext x
  simp only [mem_iUnion, mem_setOf_eq, mem_sUnion, mem_sdiff, mem_singleton_iff]
  constructor
  · rintro ⟨c', hneq, hx⟩
    refine ⟨c'.val, ⟨c'.property, ?_⟩, hx⟩
    intro heq
    apply hneq
    exact Subtype.ext heq
  · rintro ⟨s, ⟨hsS, hs_ne⟩, hx⟩
    use ⟨s, hsS⟩
    refine ⟨?_, hx⟩
    intro heq
    apply hs_ne
    exact congrArg Subtype.val heq

/-- In a scheme whose stalks are domains, the union of all irreducible components
other than a given one is closed. -/
lemma isClosed_sUnion_other_irreducible_components {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (hStalks : ∀ x : Z.carrier, IsDomain (Z.presheaf.stalk x))
    (c : irreducibleComponents Z.carrier) :
    IsClosed (⋃ c' ∈ {c' : irreducibleComponents Z.carrier | c' ≠ c}, (c' : Set Z.carrier)) := by
  rw [sUnion_other_eq_iUnion_other (irreducibleComponents Z.carrier) c]
  apply isClosed_sUnion_of_disjoint_isOpen
  · intro c1 hc1 c2 hc2 hneq
    exact disjoint_irreducible_components_of_reduced_no_embedded hStalks ⟨c1, hc1⟩ ⟨c2, hc2⟩
      (fun heq => hneq (congrArg Subtype.val heq))
  · intro s hs
    exact isOpen_irreducibleComponents_of_stalks_domain hStalks ⟨s, hs⟩
  · exact sUnion_irreducibleComponents
  · exact sdiff_subset

/-- A topological space is irreducible if its irreducible components are disjoint
and it is connected. Note: `hDisj` is mathematically redundant because clopen components
in a connected space force uniqueness without needing explicit disjointness. -/
lemma irreducible_of_connected_of_disjoint_components {α : Type*} [TopologicalSpace α]
    [ConnectedSpace α]
    (_hDisj : ∀ c1 c2 : irreducibleComponents α, c1 ≠ c2 →
      Disjoint (c1:Set α) (c2:Set α))
    (hOpen : ∀ c : irreducibleComponents α, IsOpen (c:Set α)) :
    IrreducibleSpace α := by
  have hNonempty : Nonempty (irreducibleComponents α) := by
    have h_ne : Nonempty α := inferInstance
    obtain ⟨x⟩ := h_ne
    have hSU : x ∈ ⋃₀ irreducibleComponents α := by
      rw [sUnion_irreducibleComponents]
      exact mem_univ x
    obtain ⟨c, hc_in, hx⟩ := hSU
    exact ⟨⟨c, hc_in⟩⟩
  obtain ⟨c⟩ := hNonempty
  have hcClopen : IsClopen (c : Set α) :=
    ⟨isClosed_of_mem_irreducibleComponents (c:Set α) c.2, hOpen c⟩
  have hcNonempty : (c:Set α).Nonempty := c.2.1.1
  have hcEqUniv : (c : Set α) = univ := IsClopen.eq_univ hcClopen hcNonempty
  have hIrredUniv : IsIrreducible (univ : Set α) := by
    rw [← hcEqUniv]
    exact c.2.1
  haveI : PreirreducibleSpace α := ⟨hIrredUniv.2⟩
  exact ⟨inferInstance⟩

/-- Auxiliary declaration. -/
theorem irreducibleSpace_of_connected_reduced_no_embedded (Z : Scheme.{u}) [IsLocallyNoetherian Z]
    [ConnectedSpace Z] (hStalks : ∀ x : Z.carrier, IsDomain (Z.presheaf.stalk x)) :
    IrreducibleSpace Z := by
  apply irreducible_of_connected_of_disjoint_components
  · exact disjoint_irreducible_components_of_reduced_no_embedded hStalks
  · intro c
    exact isOpen_irreducibleComponents_of_stalks_domain hStalks c

end AlgebraicGeometry

end TauCeti
