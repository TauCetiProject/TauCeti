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
* `TauCeti.Excellence.regularLocus_eq_univ`: a regular ring is regular at every prime.
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
  together with its `Pcf.isRegularLocalRing_iff_of_ringEquiv`. The empty-locus results and the
  examples are new here.
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

variable (R) in
/-- Every prime of a regular ring lies in its regular locus. -/
theorem regularLocus_eq_univ [IsRegularRing R] : regularLocus R = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ mem_regularLocus.mpr inferInstance

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

variable (R) in
/-- The zero ring has empty regular locus, as it has no primes. -/
theorem regularLocus_eq_empty_of_subsingleton [Subsingleton R] : regularLocus R = ∅ :=
  Set.eq_empty_of_isEmpty _

variable (k : Type*) [CommRing k]

/-- The dual numbers `k[ε]/(ε²)` over a commutative ring `k` have empty regular locus: in every
localization at a prime, `ε` is a nonzero element with `ε² = 0`, so no such localization is a
domain, whereas a regular local ring is a domain. -/
theorem regularLocus_trivSqZeroExt_eq_empty : regularLocus (TrivSqZeroExt k k) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p hp ↦ ?_
  rw [mem_regularLocus] at hp
  -- Argue for an abstract localization `S`: on `Localization.AtPrime` itself the domain instance
  -- of a regular local ring does not unify with the localization's own semiring structure.
  suffices ∀ (S : Type _) [CommRing S] [Algebra (TrivSqZeroExt k k) S]
      [IsLocalization.AtPrime S p.asIdeal] [IsRegularLocalRing S], False from
    this (Localization.AtPrime p.asIdeal)
  intro S _ _ _ _
  set ε : TrivSqZeroExt k k := TrivSqZeroExt.inr 1
  have hεsq : ε * ε = 0 := by simp [ε]
  have hε : algebraMap (TrivSqZeroExt k k) S ε = 0 :=
    mul_self_eq_zero.mp (by rw [← map_mul, hεsq, map_zero])
  -- Some `s ∉ p` kills `ε`; comparing second components forces `s.fst = 0`, so `s ^ 2 = 0 ∈ p`.
  obtain ⟨⟨s, hs⟩, hsε⟩ := (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl S ε).mp hε
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
