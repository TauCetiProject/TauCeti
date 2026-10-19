/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# The regular locus of a commutative ring

The *regular locus* of a commutative ring `R` is the set of primes `p` of `R` whose localization
`R_p` is a regular local ring (Stacks, Section 15.48, opening paragraph). It is defined for every
commutative ring, with no Noetherian hypothesis, and it need not be open: openness for all
finite type algebras is the J-2 condition of Stacks, Definition 15.48.1 (07P7).

## Main definitions and results

* `TauCeti.Excellence.regularLocus R`: the primes `p` of `R` with `R_p` a regular local ring.
* `TauCeti.Excellence.mem_regularLocus_iff_of_isLocalization`: membership can be tested on any
  localization of `R` at the prime, not only on `Localization.AtPrime`.
* `TauCeti.Excellence.regularLocus_eq_univ`: a regular ring is regular at every prime, and
  `TauCeti.Excellence.regularLocus_eq_univ_iff`: conversely, a Noetherian ring regular at every
  prime is a regular ring.
* `TauCeti.Excellence.algebraMap_eq_zero_of_mem_regularLocus_of_isNilpotent`: a nilpotent element
  of `R` vanishes in every localization at a prime of the regular locus.
* `TauCeti.Excellence.regularLocus_ringEquiv`: a ring isomorphism `R ≃+* S` identifies the regular
  loci through the induced homeomorphism of prime spectra.
* `TauCeti.Excellence.regularLocus_eq_empty_of_subsingleton`: the zero ring has empty regular
  locus, as its spectrum is empty.
* `TauCeti.Excellence.regularLocus_trivSqZeroExt_eq_empty`: the dual numbers `k[ε]/(ε²)` over a
  commutative ring `k` have empty regular locus, since a regular local ring is a domain.

## References

* [Stacks Project, Section 15.48](https://stacks.math.columbia.edu/tag/07P6).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `a39c3781b9850b9f3d5cbc9920322a3b8e365ef2` (Apache-2.0),
  `lean/Pcf/Bounding/FiniteTypeRegularLocus.lean`: `regularLocus` and `regularLocus_eq_univ` are
  its `Pcf.primeRegularLocus` and `Pcf.primeRegularLocus_eq_univ`, and `regularLocus_ringEquiv`
  follows the comap-preimage form of its `Pcf.preimage_primeRegularLocus_of_isLocalization`
  together with its `Pcf.isRegularLocalRing_iff_of_ringEquiv`. New here, with no source in that
  project: `mem_regularLocus_iff_of_isLocalization`, `regularLocus_eq_univ_iff`,
  `algebraMap_eq_zero_of_mem_regularLocus_of_isNilpotent`, the empty-locus results and the
  examples.
-/

public section

namespace TauCeti.Excellence

variable (R : Type*) [CommRing R]

/-- The *regular locus* of `R`: the primes `p` such that `R_p` is a regular local ring. It need not
be open. Stacks, Section 15.48. -/
def regularLocus : Set (PrimeSpectrum R) :=
  {p | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}

variable {R}

@[simp]
theorem mem_regularLocus {p : PrimeSpectrum R} :
    p ∈ regularLocus R ↔ IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
  Iff.rfl

/-- A prime `p` lies in the regular locus exactly when some, equivalently every, localization `S`
of `R` at `p` is a regular local ring. -/
theorem mem_regularLocus_iff_of_isLocalization {p : PrimeSpectrum R} (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization.AtPrime S p.asIdeal] :
    p ∈ regularLocus R ↔ IsRegularLocalRing S := by
  let e : Localization.AtPrime p.asIdeal ≃+* S :=
    (IsLocalization.algEquiv p.asIdeal.primeCompl _ S).toRingEquiv
  rw [mem_regularLocus]
  exact ⟨fun _ ↦ .of_ringEquiv e, fun _ ↦ .of_ringEquiv e.symm⟩

variable (R) in
/-- Every prime of a regular ring lies in its regular locus. -/
theorem regularLocus_eq_univ [IsRegularRing R] : regularLocus R = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ mem_regularLocus.mpr inferInstance

variable (R) in
/-- A Noetherian ring is a regular ring exactly when its regular locus is everything. -/
theorem regularLocus_eq_univ_iff [IsNoetherianRing R] :
    regularLocus R = Set.univ ↔ IsRegularRing R :=
  ⟨fun h ↦ isRegularRing_iff.mpr fun q hq ↦
    mem_regularLocus.mp (Set.eq_univ_iff_forall.mp h ⟨q, hq⟩), fun _ ↦ regularLocus_eq_univ R⟩

/-- A ring isomorphism `e : R ≃+* S` identifies the regular loci: a prime `p` of `S` is in the
regular locus of `S` exactly when its contraction to `R` is in the regular locus of `R`. -/
theorem regularLocus_ringEquiv {S : Type*} [CommRing S] (e : R ≃+* S) :
    PrimeSpectrum.comap (e : R →+* S) ⁻¹' regularLocus R = regularLocus S := by
  ext p
  -- The prime of `R` below `p` is `p.asIdeal.comap e` by `PrimeSpectrum.comap_asIdeal`, a `rfl`
  -- lemma, so `e.map_primeCompl_comap_eq` applies to its complement as stated.
  let q := PrimeSpectrum.comap (e : R →+* S) p
  let f : Localization.AtPrime q.asIdeal ≃+* Localization.AtPrime p.asIdeal :=
    IsLocalization.ringEquivOfRingEquiv (M := q.asIdeal.primeCompl) _ _ e
      (e.map_primeCompl_comap_eq p.asIdeal)
  rw [Set.mem_preimage, mem_regularLocus, mem_regularLocus]
  exact ⟨fun _ ↦ .of_ringEquiv f, fun _ ↦ .of_ringEquiv f.symm⟩

/-- A nilpotent element of `R` vanishes in every localization `S` of `R` at a prime of the regular
locus, since a regular local ring is a domain. -/
theorem algebraMap_eq_zero_of_mem_regularLocus_of_isNilpotent {p : PrimeSpectrum R}
    (hp : p ∈ regularLocus R) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S p.asIdeal] {a : R} (ha : IsNilpotent a) : algebraMap R S a = 0 :=
  have := (mem_regularLocus_iff_of_isLocalization S).mp hp
  (ha.map _).eq_zero

variable (R) in
/-- The zero ring has empty regular locus, as it has no primes. -/
theorem regularLocus_eq_empty_of_subsingleton [Subsingleton R] : regularLocus R = ∅ :=
  Set.eq_empty_of_isEmpty _

variable (k : Type*) [CommRing k]

/-- The dual numbers `k[ε]/(ε²)` over a commutative ring `k` have empty regular locus: in every
localization at a prime, `ε` is a nonzero element with `ε² = 0`, whereas nilpotents vanish in the
localizations at primes of the regular locus. -/
theorem regularLocus_trivSqZeroExt_eq_empty : regularLocus (TrivSqZeroExt k k) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p hp ↦ ?_
  set ε : TrivSqZeroExt k k := TrivSqZeroExt.inr 1
  have hεsq : ε * ε = 0 := by simp [ε]
  have hε := algebraMap_eq_zero_of_mem_regularLocus_of_isNilpotent hp
    (Localization.AtPrime p.asIdeal) (a := ε) ⟨2, by rw [pow_two, hεsq]⟩
  -- Some `s ∉ p` kills `ε`; comparing second components forces `s.fst = 0`, so `s ^ 2 = 0 ∈ p`.
  obtain ⟨⟨s, hs⟩, hsε⟩ := (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl _ ε).mp hε
  have hfst : s.fst = 0 := by
    simpa [ε] using congrArg TrivSqZeroExt.snd hsε
  have hss : s * s = 0 := by
    ext <;> simp [hfst]
  exact hs (p.isPrime.mem_of_pow_mem 2 (by simp [pow_two, hss]))

section Field

variable (k : Type*) [Field k]

/-- The dual numbers over a field have empty regular locus. -/
example : regularLocus (TrivSqZeroExt k k) = ∅ := regularLocus_trivSqZeroExt_eq_empty k

/-- A field is regular at its unique prime. -/
example : regularLocus k = Set.univ := regularLocus_eq_univ k

/-- The zero ring `k ⧸ ⊤` has empty regular locus. -/
example : regularLocus (k ⧸ (⊤ : Ideal k)) = ∅ :=
  have : Subsingleton (k ⧸ (⊤ : Ideal k)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  regularLocus_eq_empty_of_subsingleton _

end Field

end TauCeti.Excellence
