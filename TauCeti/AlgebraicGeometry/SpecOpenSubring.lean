/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import TauCeti.RingTheory.Huber.OpenIdeal
public import TauCeti.RingTheory.Localization.OpenSubring
public import TauCeti.Topology.Algebra.Ring.Subring

/-!
# The spectrum of an open subring of a Huber ring

Let `A` be a Huber ring and `B ⊆ A` an open subring, with the subspace topology, and let
`f : Spec A → Spec B` be the morphism induced by the inclusion. Write `T ⊆ Spec B` for the set of
open prime ideals of `B`. Away from `T` the two spectra agree:

* `T` is Zariski closed: it is the zero locus of the elements of `B` that are topologically
  nilpotent in `A`;
* `f⁻¹(T)` is the set of open prime ideals of `A`;
* `f` restricts to an isomorphism of schemes from `f⁻¹(Spec B ∖ T)` onto `Spec B ∖ T`.

The complement `Spec B ∖ T` is covered by the basic opens `D(s)` for `s ∈ B` topologically
nilpotent in `A`, and over `D(s)` the morphism `f` is `Spec` of the map `B_s → A_s`, which is an
isomorphism because `s` absorbs every element of `A` into the open subring `B`
(`TauCeti.Localization.awayRingEquivOfIsTopologicallyNilpotent`). Being an isomorphism is local on
the target, so `f` is an isomorphism over the union of these basic opens.

No completeness, separatedness or noetherian hypothesis enters. The main case is a ring of
definition `B = A₀` with ideal of definition `I`, where Huber's sheafiness argument for rings with a
noetherian ring of definition uses this comparison to pass between `Spec A₀` and `Spec A` away
from the primes containing `I`.

## Main results

* `Subring.setOf_isOpen_eq_zeroLocus`: the open primes of `B` are the zero locus of the
  elements of `B` topologically nilpotent in `A`.
* `Subring.isClosed_setOf_isOpen`: in particular they form a Zariski closed set.
* `Subring.nonOpenPrimes`: the non-open primes of `B`, as an open subset of `Spec B`.
* `Subring.nonOpenPrimes_eq_iSup_basicOpen`: it is covered by the basic opens `D(s)` for
  `s ∈ B` topologically nilpotent in `A`.
* `Subring.preimage_setOf_isOpen`: the preimage in `Spec A` of the open primes of `B` is the
  set of open primes of `A`.
* `Subring.isIso_morphismRestrict_nonOpenPrimes`: `Spec A → Spec B` restricts to an
  isomorphism over the non-open primes of `B`.

## References

* R. Huber, *Continuous valuations*, Math. Z. 212 (1993), Lemma 3.7 and its proof.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §2, proof of (1.3.1)(i).
* [Wedhorn, *Adic Spaces*][wedhorn_adic], Lemma 7.44(1).
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.Huber

namespace Subring

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-- **The open primes of a subring of a Huber ring are a zero locus**: they are the primes
containing every element of the subring that is topologically nilpotent in the ambient ring. -/
theorem setOf_isOpen_eq_zeroLocus (B : Subring A) :
    {q : PrimeSpectrum B | IsOpen (q.asIdeal : Set B)} =
      PrimeSpectrum.zeroLocus {s : B | IsTopologicallyNilpotent (s : A)} := by
  ext q
  exact isOpen_iff_setOf_isTopologicallyNilpotent_coe_subset_of_isPrime

/-- **Huber, *Continuous valuations*, Lemma 3.7: the open primes of a subring of a Huber ring form
a Zariski closed subset of its spectrum.** -/
theorem isClosed_setOf_isOpen (B : Subring A) :
    IsClosed {q : PrimeSpectrum B | IsOpen (q.asIdeal : Set B)} :=
  setOf_isOpen_eq_zeroLocus B ▸ PrimeSpectrum.isClosed_zeroLocus _

/-- The prime ideals of a subring `B` of a Huber ring that are not open for the subspace topology,
as an open subset of `Spec B`: the complement of the closed set of open primes
(`Subring.isClosed_setOf_isOpen`). -/
def nonOpenPrimes (B : Subring A) : (Spec (CommRingCat.of B)).Opens where
  carrier := {q : PrimeSpectrum B | ¬IsOpen (q.asIdeal : Set B)}
  is_open' := (isClosed_setOf_isOpen B).isOpen_compl

/-- A prime of `B` lies in `Subring.nonOpenPrimes B` exactly when it is not open. -/
@[simp]
theorem mem_nonOpenPrimes (B : Subring A) {q : PrimeSpectrum B} :
    q ∈ nonOpenPrimes B ↔ ¬IsOpen (q.asIdeal : Set B) :=
  Iff.rfl

/-- **The non-open primes are covered by basic opens**: the non-open primes of `B` are the union of
the basic opens `D(s)` for `s ∈ B` topologically nilpotent in the ambient ring. -/
theorem nonOpenPrimes_eq_iSup_basicOpen (B : Subring A) :
    nonOpenPrimes B =
      ⨆ s : {s : B // IsTopologicallyNilpotent (s : A)}, PrimeSpectrum.basicOpen s.1 := by
  refine SetLike.ext fun q ↦
    ((B.mem_nonOpenPrimes).trans ?_).trans TopologicalSpace.Opens.mem_iSup.symm
  rw [isOpen_iff_setOf_isTopologicallyNilpotent_coe_subset_of_isPrime, Set.not_subset]
  simp

omit [IsHuberRing A] in
/-- **Huber, *Continuous valuations*, Lemma 3.7: open primes pull back to open primes.** For an
open subring `B` of a topological ring `A`, a prime of `A` is open exactly when its image in
`Spec B` is an open prime of `B`. -/
theorem preimage_setOf_isOpen (B : Subring A) (hB : IsOpen (B : Set A)) :
    Spec.map (CommRingCat.ofHom B.subtype) ⁻¹' {q : PrimeSpectrum B | IsOpen (q.asIdeal : Set B)} =
      {p : PrimeSpectrum A | IsOpen (p.asIdeal : Set A)} := by
  ext p
  exact p.asIdeal.isOpen_comap_subtype_iff hB

/-- The preimage of the non-open primes of an open subring `B` of a Huber ring `A` is the set of
non-open primes of `A`: this is the source of the isomorphism
`Subring.isIso_morphismRestrict_nonOpenPrimes`. -/
theorem mem_preimage_nonOpenPrimes (B : Subring A) (hB : IsOpen (B : Set A))
    {p : PrimeSpectrum A} :
    p ∈ Spec.map (CommRingCat.ofHom B.subtype) ⁻¹ᵁ nonOpenPrimes B ↔
      ¬IsOpen (p.asIdeal : Set A) := (p.asIdeal.isOpen_comap_subtype_iff hB).not

/-- **Huber, *Continuous valuations*, Lemma 3.7: away from the open primes, an open subring has
the same spectrum.** For an open subring `B` of a Huber ring `A`, the morphism
`Spec A → Spec B` restricts to an isomorphism over the non-open primes of `B`. -/
theorem isIso_morphismRestrict_nonOpenPrimes (B : Subring A) (hB : IsOpen (B : Set A)) :
    IsIso (Spec.map (CommRingCat.ofHom B.subtype) ∣_ nonOpenPrimes B) := by
  -- cover the non-open primes, as a scheme, by the preimages of the basic opens `D(s)`
  let V (s : {s : B // IsTopologicallyNilpotent (s : A)}) : (nonOpenPrimes B).toScheme.Opens :=
    (nonOpenPrimes B).ι ⁻¹ᵁ PrimeSpectrum.basicOpen s.1
  have hV : ⨆ s, V s = ⊤ := by
    refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨s, hs⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((nonOpenPrimes_eq_iSup_basicOpen B).le x.2)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hs⟩
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) V hV]
  intro s
  have hle : (PrimeSpectrum.basicOpen s.1 : (Spec (CommRingCat.of B)).Opens) ≤ nonOpenPrimes B :=
    (le_iSup (fun s : {s : B // IsTopologicallyNilpotent (s : A)} ↦
      (PrimeSpectrum.basicOpen s.1 : (Spec (CommRingCat.of B)).Opens)) s).trans
      (nonOpenPrimes_eq_iSup_basicOpen B).ge
  have himage : (nonOpenPrimes B).ι ''ᵁ V s = PrimeSpectrum.basicOpen s.1 :=
    ((nonOpenPrimes B).ι.image_preimage_eq_opensRange_inf _).trans <| by
      rw [Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr hle
  -- over `D(s)` the morphism is `Spec` of the isomorphism `B_s ≃+* A_s`
  refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict (Spec.map (CommRingCat.ofHom B.subtype)) _ (V s) ≪≫
      morphismRestrictEq (Spec.map (CommRingCat.ofHom B.subtype)) himage ≪≫
        SpecMapRestrictBasicOpenIso (CommRingCat.ofHom B.subtype) s.1)).mpr ?_
  have hbij : Function.Bijective (Localization.awayMap B.subtype s.1) := by
    have := (TauCeti.Localization.awayRingEquivOfIsTopologicallyNilpotent (Localization.Away s.1)
      (Localization.Away (B.subtype s.1)) hB s.2).bijective
    rwa [TauCeti.Localization.coe_awayRingEquivOfIsTopologicallyNilpotent] at this
  have : IsIso (CommRingCat.ofHom (Localization.awayMap B.subtype s.1)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact (MorphismProperty.isomorphisms.iff _).mpr (inferInstanceAs (IsIso (Spec.map _)))

end Subring
