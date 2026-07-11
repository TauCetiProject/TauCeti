/-
Copyright (c) 2026 daouid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module


public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Irreducibility of connected schemes with domain stalks

We prove that a locally noetherian connected scheme whose stalks are
integral domains is irreducible (`irreducibleSpace_of_connected_of_isDomain_stalk`).

The proof proceeds by showing that the irreducible components of such
a scheme are pairwise disjoint and open (hence clopen), so
connectedness forces a unique component.

Along the way we construct the bijection between minimal primes of
the stalk at a point and the irreducible components containing that
point (`stalkMinimalPrimesEquivIrreducibleComponentsContaining`).
-/

public section

open TopologicalSpace Set AlgebraicGeometry Topology CategoryTheory PrimeSpectrum

universe u

namespace TauCeti

namespace AlgebraicGeometry

/-- The closure of the image of an irreducible component under an open
embedding is an irreducible component. -/
private lemma closure_image_mem_irreducibleComponents {α β : Type*}
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

/-- Given an open embedding, irreducible components containing a point `x` are
in bijection with irreducible components containing `f x`. -/
private def irreducibleComponents_containing_equiv_of_isOpenEmbedding
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : IsOpenEmbedding f) (x : α) :
    { c : irreducibleComponents α // x ∈ (c : Set α) } ≃
    { c : irreducibleComponents β // f x ∈ (c : Set β) } where
  toFun c := ⟨⟨closure (f '' c.val.val),
    closure_image_mem_irreducibleComponents hf c.val.property⟩, by
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

/-- Ring isomorphism preserves minimal primes,
via `Ideal.minimalPrimes_map_of_surjective`. -/
private noncomputable def minimalPrimes_equiv_of_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : minimalPrimes A ≃ minimalPrimes B := by
  have hker : RingHom.ker e.toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp e.injective
  have himg : Ideal.map e.toRingHom '' minimalPrimes A =
      minimalPrimes B := by
    have h := Ideal.minimalPrimes_map_of_surjective
      (f := e.toRingHom) e.surjective (⊥ : Ideal A)
    rw [Ideal.map_bot, hker, bot_sup_eq] at h
    exact h.symm
  have hinj : Function.Injective (Ideal.map e.toRingHom) :=
    fun I J h => by
      rw [← Ideal.comap_map_of_bijective e.toRingHom
            e.bijective (I := I),
         ← Ideal.comap_map_of_bijective e.toRingHom
            e.bijective (I := J), h]
  exact (Equiv.Set.image _ _ hinj).trans
    (Equiv.setCongr himg)

/-- An ideal is disjoint from the prime complement of a prime ideal `I`
if and only if it is contained in `I`. -/
private lemma disjoint_primeCompl_iff {R : Type*} [CommRing R] {I J : Ideal R} [I.IsPrime] :
    Disjoint (I.primeCompl : Set R) (J : Set R) ↔ J ≤ I :=
  Set.disjoint_compl_left_iff_subset

/-- The pullback of a minimal prime of a localization at `p`
is contained in `p`. -/
private lemma comap_le_p_of_mem_minimalPrimes {R : Type*} [CommRing R] (p : PrimeSpectrum R)
    (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    (hS : S = p.asIdeal.primeCompl) (q' : minimalPrimes A) :
    q'.val.comap (algebraMap R A) ≤ p.asIdeal := by
  haveI : q'.val.IsPrime := q'.property.1.1
  have hDisj := (IsLocalization.isPrime_iff_isPrime_disjoint S A q'.val).mp ‹_› |>.2
  rwa [hS, disjoint_primeCompl_iff] at hDisj

/-- The minimal primes of the localization `A` of a ring `R` at the prime complement of `p`
are in bijection with the minimal primes of `R` contained in `p`. -/
private def minimalPrimesEquivMinimalPrimesLe {R : Type*} [CommRing R] (p : PrimeSpectrum R)
    (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    (hS : S = p.asIdeal.primeCompl) :
    minimalPrimes A ≃ { q : minimalPrimes R // q.val ≤ p.asIdeal } where
  toFun q' := ⟨⟨q'.val.comap (algebraMap R A), by
    have hMap := IsLocalization.minimalPrimes_map S A (⊥ : Ideal R)
    rw [Ideal.map_bot] at hMap
    exact (Set.ext_iff.mp hMap q'.val).mp q'.property⟩, comap_le_p_of_mem_minimalPrimes p S A hS q'⟩
  invFun q := ⟨q.val.val.map (algebraMap R A), by
    have hMap := IsLocalization.minimalPrimes_map S A (⊥ : Ideal R)
    rw [Ideal.map_bot] at hMap
    have hI' : Disjoint (S : Set R) (q.val.val : Set R) := by
      rw [hS, disjoint_primeCompl_iff]
      exact q.property
    haveI : q.val.val.IsPrime := q.val.property.1.1
    have hEq := IsLocalization.under_map_of_isPrime_disjoint S A ‹_› hI'
    have h_in : Ideal.under R (Ideal.map (algebraMap R A) q.val.val) ∈ minimalPrimes R :=
      hEq.symm ▸ q.val.property
    exact (Set.ext_iff.mp hMap (Ideal.map (algebraMap R A) q.val.val)).mpr h_in⟩
  left_inv q' := Subtype.ext (IsLocalization.map_under S A q'.val)
  right_inv q := Subtype.ext <| Subtype.ext <| by
    have hI' : Disjoint (S : Set R) (q.val.val : Set R) := by
      rw [hS, disjoint_primeCompl_iff]
      exact q.property
    haveI : q.val.val.IsPrime := q.val.property.1.1
    exact IsLocalization.under_map_of_isPrime_disjoint S A ‹_› hI'

/-- Mathlib's `minimalPrimes.equivIrreducibleComponents` is defined via a tactic block (`by rw ...`)
which inserts `Eq.ndrec` making definitional equality evaluation fail with an
`Application type mismatch` in the kernel (due to `x.2.1` on a `Set`).
Because Mathlib provides no API lemmas for it, we must construct the equivalence manually
using `vanishingIdeal` and `zeroLocus`. -/
private noncomputable def vanishingIdealEquiv (R : Type*) [CommRing R] :
    irreducibleComponents (PrimeSpectrum R) ≃ minimalPrimes R := by
  let f : irreducibleComponents (PrimeSpectrum R) → minimalPrimes R := fun c ↦
    ⟨vanishingIdeal c.val, by
      have hc : IsClosed (c.val : Set (PrimeSpectrum R)) :=
        isClosed_of_mem_irreducibleComponents c.val c.property
      have h : closure (c.val : Set (PrimeSpectrum R)) ∈
          irreducibleComponents (PrimeSpectrum R) := by
        rw [hc.closure_eq]
        exact c.property
      exact PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mpr h⟩
  have h_inj : Function.Injective f := fun c1 c2 h => Subtype.ext (by
    have h1 := congrArg Subtype.val h
    have hc1 : IsClosed (c1.val : Set (PrimeSpectrum R)) :=
      isClosed_of_mem_irreducibleComponents c1.val c1.property
    have hc2 : IsClosed (c2.val : Set (PrimeSpectrum R)) :=
      isClosed_of_mem_irreducibleComponents c2.val c2.property
    have h2 := congrArg (fun (I : Ideal R) => PrimeSpectrum.zeroLocus (I : Set R)) h1
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure c1.val,
        PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure c2.val] at h2
    rw [hc1.closure_eq, hc2.closure_eq] at h2
    exact h2
  )
  have h_surj : Function.Surjective f := fun q => by
    have h_eq := Set.ext_iff.mp
      (PrimeSpectrum.vanishingIdeal_irreducibleComponents (R := R)) (q.val : Ideal R)
    have hq : q.val ∈ vanishingIdeal '' irreducibleComponents (PrimeSpectrum R) :=
      h_eq.mpr q.property
    rcases hq with ⟨c, hc, hc_eq⟩
    exact ⟨⟨c, hc⟩, Subtype.ext hc_eq⟩
  exact Equiv.ofBijective f ⟨h_inj, h_surj⟩

/-- Irreducible components of `Spec R` containing a point `p`
correspond to minimal primes below `p`, via the
`zeroLocus`/`vanishingIdeal` Galois correspondence. -/
private noncomputable def
    irreducibleComponentsContainingEquivMinimalPrimesLe
    (R : Type*) [CommRing R] (p : PrimeSpectrum R) :
    { c : irreducibleComponents (PrimeSpectrum R) //
      p ∈ (c : Set (PrimeSpectrum R)) } ≃
    { q : minimalPrimes R // q.val ≤ p.asIdeal } := by
  let e := (vanishingIdealEquiv R)
  refine Equiv.subtypeEquiv e (fun c => ?_)
  have hc : IsClosed (c.val : Set (PrimeSpectrum R)) :=
    isClosed_of_mem_irreducibleComponents c.val c.property
  have h1 : p ∈ (c.val : Set (PrimeSpectrum R)) ↔
      vanishingIdeal (c.val : Set (PrimeSpectrum R)) ≤ p.asIdeal :=
    calc p ∈ (c.val : Set (PrimeSpectrum R))
      _ ↔ p ∈ PrimeSpectrum.zeroLocus (vanishingIdeal c.val : Set R) := by
        have h_eq : (c.val : Set (PrimeSpectrum R)) = zeroLocus (vanishingIdeal c.val) :=
          hc.closure_eq.symm.trans
            (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure c.val).symm
        exact Iff.of_eq (congrArg (fun s => p ∈ s) h_eq)
      _ ↔ (vanishingIdeal (c.val : Set (PrimeSpectrum R)) : Set R) ⊆ p.asIdeal :=
        PrimeSpectrum.mem_zeroLocus (x := p) (s := (vanishingIdeal c.val : Set R))
      _ ↔ vanishingIdeal (c.val : Set (PrimeSpectrum R)) ≤ p.asIdeal := Iff.rfl
  exact h1

/-- For an affine scheme Spec R, the minimal prime ideals of the local ring (stalk)
at a point p (which is a prime ideal of R) are in bijection with the irreducible components
of Spec R containing p. -/
private noncomputable def stalkMinimalPrimesEquivIrreducibleComponentsContainingSpec
    (R : Type*) [CommRing R] (p : PrimeSpectrum R) :
    minimalPrimes (Localization.AtPrime p.asIdeal) ≃
      { c : irreducibleComponents (PrimeSpectrum R) // p ∈ (c : Set (PrimeSpectrum R)) } :=
  (minimalPrimesEquivMinimalPrimesLe p p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) rfl).trans
    (irreducibleComponentsContainingEquivMinimalPrimesLe R p).symm

/-- The minimal primes of the stalk of a scheme at a point `x`
are in bijection with the irreducible components containing `x`. -/
private lemma
    nonempty_stalkMinimalPrimesEquivIrreducibleComponentsContaining
    {X : Scheme} (x : X.carrier) :
    Nonempty (minimalPrimes (X.presheaf.stalk x) ≃
      { c : irreducibleComponents X.carrier // x ∈ (c : Set X.carrier) }) := by
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
  let hEq3 := stalkMinimalPrimesEquivIrreducibleComponentsContainingSpec R y_spec
  have hYspec : eHomeo.symm y_spec = y := by
    -- `y_spec = eHomeo y` by `Scheme.homeoOfIso_apply`.
    have : eHomeo y = y_spec :=
      Scheme.homeoOfIso_apply g y
    exact eHomeo.symm_apply_eq.mpr this.symm
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
  exact ⟨hEq1.trans (hEq2.trans (hEq3.trans (hEq4.trans hEq5)))⟩

/-- If the stalk at `x` has a unique minimal prime, then
`x` belongs to a unique irreducible component. -/
lemma existsUnique_irreducibleComponent_of_unique_minimalPrime
    {X : Scheme} (x : X.carrier)
    [Unique (minimalPrimes (X.presheaf.stalk x))] :
    ∃! c : irreducibleComponents X.carrier,
      x ∈ (c : Set X.carrier) := by
  have e_nonempty :=
    nonempty_stalkMinimalPrimesEquivIrreducibleComponentsContaining x
  exact e_nonempty.elim fun e => by
    haveI hU : Unique { c : irreducibleComponents X.carrier //
        x ∈ (c : Set X.carrier) } :=
      Equiv.unique e.symm
    exact ⟨hU.default.1, hU.default.2,
      fun c hc ↦ congrArg Subtype.val (hU.uniq ⟨c, hc⟩)⟩



/-- In a scheme whose stalks have unique minimal primes, the irreducible
components are pairwise disjoint. -/
lemma disjoint_irreducibleComponents_of_unique_minimalPrime {Z : Scheme}
  (hStalks : ∀ x : Z.carrier, Unique (minimalPrimes (Z.presheaf.stalk x))) :
  ∀ c1 c2 : irreducibleComponents Z.carrier, c1 ≠ c2 →
    Disjoint (c1 : Set Z.carrier) (c2 : Set Z.carrier) := by
  intro c1 c2 hneq
  rw [Set.disjoint_iff]
  intro x hx
  have hx1 : x ∈ (c1 : Set Z.carrier) := hx.1
  have hx2 : x ∈ (c2 : Set Z.carrier) := hx.2
  have h_unique := existsUnique_irreducibleComponent_of_unique_minimalPrime x
  obtain ⟨c, _, hcUniq⟩ := h_unique
  have hEq1 : c1 = c := hcUniq c1 hx1
  have hEq2 : c2 = c := hcUniq c2 hx2
  rw [hEq1, hEq2] at hneq
  exact hneq rfl



/-- In a topological space with finitely many irreducible components, pairwise-disjoint
components are open. -/
private lemma isOpen_irreducibleComponents_of_pairwise_disjoint {α : Type*} [TopologicalSpace α]
    (hFinite : (irreducibleComponents α).Finite)
    (hDisj : ∀ c1 c2 : irreducibleComponents α, c1 ≠ c2 →
      Disjoint (c1 : Set α) (c2 : Set α))
    (c : irreducibleComponents α) : IsOpen (c : Set α) := by
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
  exact Set.Finite.isClosed_biUnion hFinite.sdiff
    (fun t ht => isClosed_of_mem_irreducibleComponents t ht.1)

/-- In an affine locally noetherian scheme whose stalks have unique minimal
primes, every irreducible component is open. -/
private theorem isOpen_irreducibleComponents_of_affine_unique_minimalPrime {X : Scheme.{u}}
    [IsAffine X]
    [IsLocallyNoetherian X] (hStalks : ∀ x : X.carrier, Unique (minimalPrimes (X.presheaf.stalk x)))
    (c : irreducibleComponents X.carrier) : IsOpen (c : Set X.carrier) := by
  haveI : NoetherianSpace X.carrier :=
    @noetherianSpace_of_isAffine X _
      (IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩)
  apply isOpen_irreducibleComponents_of_pairwise_disjoint
    (NoetherianSpace.finite_irreducibleComponents (α := X.carrier))
  exact disjoint_irreducibleComponents_of_unique_minimalPrime hStalks



/-- In a locally noetherian scheme whose stalks have unique minimal primes,
every irreducible component is open. -/
theorem isOpen_irreducibleComponents_of_unique_minimalPrime {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (hStalks : ∀ x : Z.carrier, Unique (minimalPrimes (Z.presheaf.stalk x)))
    (c : irreducibleComponents Z.carrier) :
    IsOpen (c : Set Z.carrier) := by
  rw [isOpen_iff_of_cover (fun j ↦ (Z.affineCover.f j).isOpenEmbedding.isOpen_range)
    Z.affineCover.iUnion_range]
  intro j
  rw [inter_comm]
  let f := Z.affineCover.f j
  have hf : IsOpenEmbedding f.1.base := f.isOpenEmbedding
  rw [← image_preimage_eq_inter_range]
  apply hf.isOpenMap
  let Y := Z.affineCover.X j
  have hStalksY : ∀ y : Y.carrier, Unique (minimalPrimes (Y.presheaf.stalk y)) := by
    intro y
    haveI hU : Unique (minimalPrimes (Z.presheaf.stalk (f.1.base y))) := hStalks (f.1.base y)
    exact Equiv.unique (minimalPrimes_equiv_of_ringEquiv
      (asIso <| f.stalkMap y).commRingCatIsoToRingEquiv.symm)
  by_cases hEmpty : (f.1.base ⁻¹' (c : Set Z.carrier)).Nonempty
  · have hNonempty : ((c : Set Z.carrier) ∩ Set.range f.1.base).Nonempty := by
      obtain ⟨x, hx⟩ := hEmpty
      exact ⟨f.1.base x, hx, ⟨x, rfl⟩⟩
    have hComp : f.1.base ⁻¹' (c : Set Z.carrier) ∈ irreducibleComponents Y.carrier :=
      preimage_mem_irreducibleComponents c.property hf hNonempty
    have hOpen := isOpen_irreducibleComponents_of_affine_unique_minimalPrime hStalksY ⟨_, hComp⟩
    exact hOpen
  · rw [Set.not_nonempty_iff_eq_empty] at hEmpty
    rw [hEmpty]
    exact isOpen_empty





/-- A connected topological space with open irreducible components is irreducible. -/
private lemma irreducibleSpace_of_connected_of_open_components {α : Type*} [TopologicalSpace α]
    [ConnectedSpace α] (hOpen : ∀ c : irreducibleComponents α, IsOpen (c : Set α)) :
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
    ⟨isClosed_of_mem_irreducibleComponents (c : Set α) c.2, hOpen c⟩
  have hcNonempty : (c : Set α).Nonempty := c.2.1.1
  have hcEqUniv : (c : Set α) = univ := IsClopen.eq_univ hcClopen hcNonempty
  have hIrredUniv : IsIrreducible (univ : Set α) := by
    rw [← hcEqUniv]
    exact c.2.1
  haveI : PreirreducibleSpace α := ⟨hIrredUniv.2⟩
  exact ⟨inferInstance⟩

/-- A locally noetherian connected scheme whose stalks have unique minimal
primes is irreducible. -/
theorem irreducibleSpace_of_connected_of_unique_minimalPrime (Z : Scheme.{u})
    [IsLocallyNoetherian Z]
    [ConnectedSpace Z] (hStalks : ∀ x : Z.carrier, Unique (minimalPrimes (Z.presheaf.stalk x))) :
    IrreducibleSpace Z := by
  apply irreducibleSpace_of_connected_of_open_components
  intro c
  exact isOpen_irreducibleComponents_of_unique_minimalPrime hStalks c

/-- A locally noetherian connected scheme whose stalks are integral domains
is irreducible. -/
theorem irreducibleSpace_of_connected_of_isDomain_stalk (Z : Scheme.{u}) [IsLocallyNoetherian Z]
    [ConnectedSpace Z] (hStalks : ∀ x : Z.carrier, IsDomain (Z.presheaf.stalk x)) :
    IrreducibleSpace Z := by
  haveI hU : ∀ x, Unique (minimalPrimes (Z.presheaf.stalk x)) := fun x => by
    haveI := hStalks x
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    exact Set.uniqueSingleton ⊥
  exact irreducibleSpace_of_connected_of_unique_minimalPrime Z hU

end AlgebraicGeometry

end TauCeti
