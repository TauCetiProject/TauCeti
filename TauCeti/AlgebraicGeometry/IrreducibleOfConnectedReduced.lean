/-
Copyright (c) 2026 daouid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Irreducible components of a connected reduced scheme

This file provides the topological results needed to show that a connected scheme
whose stalks are integral domains is an irreducible space. It deconstructs the
bijection between minimal primes of the stalks and the irreducible components,
and proves that such irreducible components are open and disjoint.

This advances the roadmap at TauCetiRoadmap/JacobianChallenge/README.md,
heading Standing hypotheses, specifically the geometrically integral curve
prerequisite and the substep regular + connected ⇒ irreducible.
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
  toFun c := ⟨⟨closure (f '' c.val.val),
    image_mem_irreducibleComponents hf c.val.property⟩, by
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

/-- Ring isomorphism preserves minimal primes. -/
private def minimalPrimes_equiv_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : minimalPrimes A ≃ minimalPrimes B where
  toFun p := ⟨Ideal.map e p.val, by
    -- Unfold `minimalPrimes` to its definition as `(⊥ : Ideal B).minimalPrimes`.
    change _ ∈ (⊥ : Ideal B).minimalPrimes
    have h1 := Ideal.minimalPrimes_map_of_surjective (f := e.toRingHom) e.surjective ⊥
    have hker : RingHom.ker e.toRingHom = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective
    rw [Ideal.map_bot, hker, bot_sup_eq] at h1
    rw [h1]
    exact Set.mem_image_of_mem _ p.property⟩
  invFun q := ⟨Ideal.comap e q.val, by
    -- Unfold `minimalPrimes` to its definition as `(⊥ : Ideal A).minimalPrimes`.
    change _ ∈ (⊥ : Ideal A).minimalPrimes
    have h1 := Ideal.comap_minimalPrimes_eq_of_surjective (f := e.toRingHom) e.surjective ⊥
    have hker : Ideal.comap e.toRingHom ⊥ = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective
    rw [hker] at h1
    rw [h1]
    exact Set.mem_image_of_mem _ q.property⟩
  left_inv p := Subtype.ext (by
    dsimp
    rw [Ideal.comap_map_of_bijective e e.bijective])
  right_inv q := Subtype.ext (by
    dsimp
    rw [Ideal.map_comap_of_surjective e e.surjective])

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
    -- Unfold the definition of `minimalPrimes` to express it as the preimage under `Ideal.under`.
    change q'.val ∈ Ideal.under R ⁻¹' (⊥ : Ideal R).minimalPrimes
    rw [← IsLocalization.minimalPrimes_map S A ⊥, Ideal.map_bot]
    exact q'.property⟩, comap_le_p_of_mem_minimalPrimes p S A hS q'⟩
  invFun q := ⟨q.val.val.map (algebraMap R A), by
    have hMap := IsLocalization.minimalPrimes_map S A (⊥ : Ideal R)
    rw [Ideal.map_bot] at hMap
    -- Unfold the definition of `minimalPrimes` to express the membership directly.
    change q.val.val.map (algebraMap R A) ∈ (⊥ : Ideal A).minimalPrimes
    rw [hMap]
    have hI' : Disjoint (S : Set R) (q.val.val : Set R) := by
      rw [hS, disjoint_primeCompl_iff]
      exact q.property
    haveI : q.val.val.IsPrime := q.val.property.1.1
    have hEq := IsLocalization.under_map_of_isPrime_disjoint S A ‹_› hI'
    -- Unfold `minimalPrimes R` to its expression in terms of `Ideal.under` membership.
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



/-- Equivalence between minimal primes and irreducible components, obtained by composing
Mathlib's `minimalPrimes.equivIrreducibleComponents` (an `OrderIso` into the order-dual
subtype) with `OrderDual.ofDual` to land in `irreducibleComponents` directly. -/
private noncomputable def minimalPrimesEquiv (R : Type*)
    [CommRing R] :
    minimalPrimes R ≃
      irreducibleComponents (PrimeSpectrum R) :=
  (minimalPrimes.equivIrreducibleComponents R).toEquiv.trans
    OrderDual.ofDual

/-- Auxiliary definition to extract the underlying set from an order-dual subtype element.
Used to normalize through the `OrderDual` coercion in `equivIrreducibleComponents`. -/
private def equivIrreducibleComponentsVal {R : Type*} [CommRing R]
    (S : Set (Set (PrimeSpectrum R))) (y : (S : Type _)ᵒᵈ) :
    Set (PrimeSpectrum R) := (OrderDual.ofDual y).val

/-- The value of `equivIrreducibleComponents` at a minimal prime `q` is `zeroLocus q.val`.
This requires manually unfolding the definition of `equivIrreducibleComponents`, because
Mathlib defines it via `irreducibleComponents_eq_maximals_closed`, introducing a type-level
`cast` that blocks direct `simp`/`rfl` evaluation. The `rcases h_S with rfl` trick
eliminates the cast, reducing the goal to `closure {⟨q.val, _⟩} = zeroLocus q.val`,
which is `PrimeSpectrum.closure_singleton`. -/
private lemma equivIrreducibleComponents_val {R : Type*} [CommRing R]
    (q : minimalPrimes R) :
    equivIrreducibleComponentsVal
      (irreducibleComponents (PrimeSpectrum R))
      ((minimalPrimes.equivIrreducibleComponents R) q) =
      zeroLocus q.val := by
  -- Unfold `equivIrreducibleComponents` to expose the cast over
  -- `irreducibleComponents_eq_maximals_closed`, then eliminate it.
  have H : ∀ (S2 : Set (Set (PrimeSpectrum R)))
    (h_S : {s | Maximal (fun x ↦ IsClosed x ∧ IsIrreducible x) s}
      = S2),
      equivIrreducibleComponentsVal S2 ((cast (congrArg
        (f := fun (S : Set (Set (PrimeSpectrum R))) ↦
          minimalPrimes R ≃o (S : Type _)ᵒᵈ) h_S)
        (OrderIso.setOfMinimalIsoSetOfMaximal
          ((show {p : Ideal R | p.IsPrime ∧ ⊥ ≤ p} ≃o
              PrimeSpectrum R from
            ⟨⟨fun x ↦ ⟨x.1, x.2.1⟩,
              fun x ↦ ⟨x.1, x.2, bot_le⟩,
              fun _ ↦ rfl, fun _ ↦ rfl⟩, Iff.rfl⟩).trans
            ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).trans
              (IrreducibleCloseds.orderIsoSubtype'
                (PrimeSpectrum R)).dual)))) q) =
        zeroLocus q.val := by
    intro S2 h_S
    -- Eliminating the cast reduces to the concrete order isomorphism.
    rcases h_S with rfl
    -- The underlying set is `closure {⟨q.val, _⟩}`, which equals `zeroLocus q.val`
    -- by `PrimeSpectrum.closure_singleton`.
    change closure { (⟨q.val, _⟩ : PrimeSpectrum R) } =
      zeroLocus q.val
    exact PrimeSpectrum.closure_singleton
      (x := ⟨q.val, _⟩)
  exact H _ (irreducibleComponents_eq_maximals_closed
    (PrimeSpectrum R)).symm

private lemma minimalPrimesEquiv_val {R : Type*} [CommRing R]
    (q : minimalPrimes R) :
    ((minimalPrimesEquiv R q :
      irreducibleComponents (PrimeSpectrum R)) :
      Set (PrimeSpectrum R)) = zeroLocus q.val := by
  -- Reduce to `equivIrreducibleComponents_val` by definitional unfolding.
  have h_val : ((minimalPrimesEquiv R q :
      irreducibleComponents (PrimeSpectrum R)) :
      Set (PrimeSpectrum R)) =
      equivIrreducibleComponentsVal
        (irreducibleComponents (PrimeSpectrum R))
        ((minimalPrimes.equivIrreducibleComponents R) q) :=
    rfl
  rw [h_val]
  exact equivIrreducibleComponents_val q
/-- Auxiliary declaration. -/
private noncomputable def irreducibleComponentsContainingEquivMinimalPrimesLe (R : Type*)
    [CommRing R] (p : PrimeSpectrum R) :
    { c : irreducibleComponents (PrimeSpectrum R) // p ∈ (c : Set (PrimeSpectrum R)) } ≃
      { q : minimalPrimes R // q.val ≤ p.asIdeal } :=
  Equiv.subtypeEquiv (minimalPrimesEquiv R).symm (fun c ↦ by
    obtain ⟨q, rfl⟩ := (minimalPrimesEquiv R).surjective c
    rw [Equiv.symm_apply_apply]
    rw [minimalPrimesEquiv_val, mem_zeroLocus, SetLike.coe_subset_coe]
  )

/-- For an affine scheme Spec R, the minimal prime ideals of the local ring (stalk)
at a point p (which is a prime ideal of R) are in bijection with the irreducible components
of Spec R containing p.
This is the affine case of the bijection between minimal primes of stalks and irreducible
components containing the point. -/
private noncomputable def stalkMinimalPrimesEquivIrreducibleComponentsContainingSpec
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
2. The affine spectrum case (`stalkMinimalPrimesEquivIrreducibleComponentsContainingSpec`).
3. Stalk isomorphism and ring isomorphism preservation of minimal primes. -/
private noncomputable def stalkMinimalPrimesEquivIrreducibleComponentsContaining
    {X : Scheme} (x : X.carrier) :
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
  let hEq3 := stalkMinimalPrimesEquivIrreducibleComponentsContainingSpec R y_spec
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

/-- A point in a scheme whose stalk is a domain belongs to a unique irreducible component. -/
lemma unique_irreducibleComponent_of_isDomain_stalk {X : Scheme} (x : X.carrier)
  (hStalks : IsDomain (X.presheaf.stalk x)) :
  ∃! c : irreducibleComponents X.carrier, x ∈ (c : Set X.carrier) := by
  have e := stalkMinimalPrimesEquivIrreducibleComponentsContaining x
  haveI : Unique (minimalPrimes (X.presheaf.stalk x)) := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot (X.presheaf.stalk x)]
    exact Set.uniqueSingleton ⊥
  haveI hUniqSub : Unique { c : irreducibleComponents X.carrier // x ∈ (c : Set X.carrier) } :=
    Equiv.unique e.symm
  exact ⟨hUniqSub.default.1, hUniqSub.default.2,
    fun c hc => congrArg Subtype.val (hUniqSub.uniq ⟨c, hc⟩)⟩

/-- In a scheme whose stalks are domains, the irreducible components are pairwise disjoint. -/
lemma disjoint_irreducibleComponents_of_isDomain_stalk {Z : Scheme}
  (hStalks : ∀ x : Z.carrier, IsDomain (Z.presheaf.stalk x)) :
  ∀ c1 c2 : irreducibleComponents Z.carrier, c1 ≠ c2 →
    Disjoint (c1 : Set Z.carrier) (c2 : Set Z.carrier) := by
  intro c1 c2 hneq
  rw [Set.disjoint_iff]
  intro x hx
  have hx1 : x ∈ (c1 : Set Z.carrier) := hx.1
  have hx2 : x ∈ (c2 : Set Z.carrier) := hx.2
  have h_unique := unique_irreducibleComponent_of_isDomain_stalk x (hStalks x)
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

/-- In an affine locally noetherian scheme whose stalks are domains,
every irreducible component is open. -/
private theorem isOpen_irreducibleComponents_of_affine_isDomain_stalk {X : Scheme.{u}} [IsAffine X]
    [IsLocallyNoetherian X] (hStalks : ∀ x : X.carrier, IsDomain (X.presheaf.stalk x))
    (c : irreducibleComponents X.carrier) : IsOpen (c : Set X.carrier) := by
  haveI : NoetherianSpace X.carrier :=
    @noetherianSpace_of_isAffine X _
      (IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩)
  apply isOpen_irreducibleComponents_of_pairwise_disjoint
    (NoetherianSpace.finite_irreducibleComponents (α := X.carrier))
  exact disjoint_irreducibleComponents_of_isDomain_stalk hStalks

/-- In a locally noetherian scheme whose stalks are domains, every irreducible component is open. -/
theorem isOpen_irreducibleComponents_of_isDomain_stalk {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (hStalks : ∀ x : Z.carrier, IsDomain (Z.presheaf.stalk x))
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
  have hStalksY : ∀ y : Y.carrier, IsDomain (Y.presheaf.stalk y) := by
    intro y
    haveI : IsDomain (Z.presheaf.stalk (f.1.base y)) := hStalks (f.1.base y)
    exact (asIso <| f.stalkMap y).commRingCatIsoToRingEquiv.isDomain_iff.mp inferInstance
  by_cases hEmpty : (f.1.base ⁻¹' (c : Set Z.carrier)).Nonempty
  · have hNonempty : ((c : Set Z.carrier) ∩ Set.range f.1.base).Nonempty := by
      obtain ⟨x, hx⟩ := hEmpty
      exact ⟨f.1.base x, hx, ⟨x, rfl⟩⟩
    have hComp : f.1.base ⁻¹' (c : Set Z.carrier) ∈ irreducibleComponents Y.carrier :=
      preimage_mem_irreducibleComponents c.property hf hNonempty
    have hOpen := isOpen_irreducibleComponents_of_affine_isDomain_stalk hStalksY ⟨_, hComp⟩
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
private lemma biUnion_ne_eq_sUnion_sdiff {α : Type*} (S : Set (Set α)) (c : { x // x ∈ S }) :
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

/-- In a locally noetherian scheme whose stalks are domains, the union of all
irreducible components other than a given one is closed. -/
private lemma isClosed_biUnion_other_irreducibleComponents_of_isDomain_stalk
    {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (hStalks : ∀ x : Z.carrier, IsDomain (Z.presheaf.stalk x))
    (c : irreducibleComponents Z.carrier) :
    IsClosed (⋃ c' ∈
      {c' : irreducibleComponents Z.carrier | c' ≠ c},
      (c' : Set Z.carrier)) := by
  rw [biUnion_ne_eq_sUnion_sdiff (irreducibleComponents Z.carrier) c]
  apply isClosed_sUnion_of_disjoint_isOpen
  · intro c1 hc1 c2 hc2 hneq
    exact disjoint_irreducibleComponents_of_isDomain_stalk hStalks ⟨c1, hc1⟩ ⟨c2, hc2⟩
      (fun heq => hneq (congrArg Subtype.val heq))
  · intro s hs
    exact isOpen_irreducibleComponents_of_isDomain_stalk hStalks ⟨s, hs⟩
  · exact sUnion_irreducibleComponents
  · exact sdiff_subset

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

/-- A locally noetherian connected scheme whose stalks are integral domains is irreducible. -/
theorem irreducibleSpace_of_connected_of_isDomain_stalk (Z : Scheme.{u}) [IsLocallyNoetherian Z]
    [ConnectedSpace Z] (hStalks : ∀ x : Z.carrier, IsDomain (Z.presheaf.stalk x)) :
    IrreducibleSpace Z := by
  apply irreducibleSpace_of_connected_of_open_components
  intro c
  exact isOpen_irreducibleComponents_of_isDomain_stalk hStalks c

end AlgebraicGeometry

end TauCeti
