/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import TauCeti.RingTheory.CohenMacaulay.Basic
public import TauCeti.RingTheory.RegularLocalRing.Locus

/-!
# Serre's conditions `(S_n)` and `(R_n)`

Let `R` be a Noetherian ring. A finite `R`-module `M` satisfies *Serre's condition* `(S_n)` if
`depth M_p ≥ min (n, dim Supp M_p)` for every prime `p` of `R`, and `R` satisfies `(R_n)` if the
local ring `R_p` is regular for every prime `p` of height at most `n` (Stacks, Definition 10.157.1
(031P)). These are the two halves of Serre's criterion for normality, `(R_1) + (S_2)`, and the
depth condition `(S_2)` is what lets sections of a module extend across closed subsets of
codimension at least two.

Depth is Mathlib's `IsLocalRing.depth` and the dimension of the support is Mathlib's
`Module.supportDim`. The zero module has depth `⊤` and support dimension `⊥`, so a prime outside
the support of `M` imposes no condition.

## Main definitions

* `Module.SatisfiesSerreS n R M`: the `R`-module `M` satisfies `(S_n)`.
* `Ring.SatisfiesSerreR n R`: every prime of `R` of height at most `n` lies in the regular locus
  `TauCeti.Excellence.regularLocus R`.

## Main results

* `Module.satisfiesSerreS_zero` and `Module.SatisfiesSerreS.mono`: every module satisfies `(S_0)`,
  and `(S_n)` implies `(S_m)` for `m ≤ n`; likewise `Ring.SatisfiesSerreR.mono`, and a regular
  ring satisfies `(R_n)` for every `n` (`IsRegularRing.satisfiesSerreR`).
* `Module.forall_satisfiesSerreS_iff_forall_isCohenMacaulay`: a finite module satisfies `(S_n)`
  for every `n` if and only if all of its localizations at primes are Cohen–Macaulay.
* `Module.satisfiesSerreS_one_iff`: a finite module satisfies `(S_1)` if and only if it has no
  embedded primes, that is, its associated primes are the minimal primes of its support (Stacks,
  Lemma 10.157.2 (031Q)).
* `isReduced_iff_satisfiesSerreR_zero_and_satisfiesSerreS_one`: a Noetherian ring is reduced if and
  only if it satisfies `(R_0)` and `(S_1)` (Stacks, Lemma 10.157.3 (031R)); the forward half of
  `(R_0)` is `IsReduced.satisfiesSerreR_zero`, which needs no Noetherian hypothesis.
* `Module.supportDim_localizedModule_nonpos_iff`: the dimension input, that `M_p` has
  zero-dimensional support exactly when `p` is a minimal prime of the support of `M`.

## References

* [Stacks Project, Section 10.157](https://stacks.math.columbia.edu/tag/031O)
-/

public section

universe u v

open IsLocalRing

namespace Module

variable (n : ℕ) (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- An `R`-module `M` satisfies *Serre's condition* `(S_n)` if for every prime `p` of `R` the depth
of `M_p` over `R_p` is at least `min (n, dim Supp M_p)`. This is meant for finite modules over a
Noetherian ring. Since the zero module has depth `⊤`, primes outside the support impose nothing.
Stacks, Definition 10.157.1 (031P). -/
@[stacks 031P]
def SatisfiesSerreS : Prop :=
  ∀ (p : Ideal R) [p.IsPrime],
    min (n : WithBot ℕ∞) (supportDim (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) ≤
      (depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) :
        WithBot ℕ∞)

variable {n R M}

/-- Unfolds `Module.SatisfiesSerreS`. -/
theorem satisfiesSerreS_iff : SatisfiesSerreS n R M ↔ ∀ (p : Ideal R) [p.IsPrime],
    min (n : WithBot ℕ∞) (supportDim (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) ≤
      (depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) :
        WithBot ℕ∞) :=
  Iff.rfl

/-- Every module satisfies `(S_0)`. -/
theorem satisfiesSerreS_zero : SatisfiesSerreS 0 R M := fun _ _ ↦
  (min_le_left _ _).trans (by exact_mod_cast zero_le)

/-- The zero module satisfies `(S_n)` for every `n`. -/
theorem satisfiesSerreS_of_subsingleton [Subsingleton M] : SatisfiesSerreS n R M := fun _ _ ↦ by
  rw [depth_eq_top_of_subsingleton]
  exact le_top

/-- Serre's condition `(S_n)` implies `(S_m)` for `m ≤ n`. -/
theorem SatisfiesSerreS.mono {m : ℕ} (h : SatisfiesSerreS n R M) (hmn : m ≤ n) :
    SatisfiesSerreS m R M := fun p _ ↦
  (min_le_min_right _ (by exact_mod_cast hmn)).trans (h p)

/-- A finite module over a Noetherian ring satisfies `(S_n)` for every `n` if and only if its
localization at every prime is Cohen–Macaulay. -/
theorem forall_satisfiesSerreS_iff_forall_isCohenMacaulay [IsNoetherianRing R]
    [Module.Finite R M] :
    (∀ n, SatisfiesSerreS n R M) ↔ ∀ (p : Ideal R) [p.IsPrime],
      IsCohenMacaulay (Localization.AtPrime p) (LocalizedModule p.primeCompl M) := by
  refine ⟨fun h p _ ↦ ?_, fun h n p _ ↦ ?_⟩ <;>
    rcases subsingleton_or_nontrivial (LocalizedModule p.primeCompl M) with _ | _
  · exact isCohenMacaulay_of_subsingleton
  · -- The support of `M_p` has finite dimension, bounded by that of the Noetherian local `R_p`.
    obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.1
      (supportDim_ne_bot_of_nontrivial (Localization.AtPrime p) (LocalizedModule p.primeCompl M))
    have hd_top : d ≠ ⊤ := fun hd_top ↦ by
      have := (supportDim_le_ringKrullDim _ (LocalizedModule p.primeCompl M)).trans_lt
        (ringKrullDim_lt_top (R := Localization.AtPrime p))
      rw [← hd, hd_top] at this
      exact this.ne rfl
    obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.1 hd_top
    rw [isCohenMacaulay_iff_supportDim_le_depth, ← hd]
    simpa [← hd] using h k p
  · rw [depth_eq_top_of_subsingleton]
    exact le_top
  · exact (min_le_right _ _).trans (h p).depth_eq.ge

/-- Let `M` be a finite module over a Noetherian ring and `p` a prime containing the annihilator
of `M`. The support of `M_p` has dimension zero exactly when `p` is a minimal prime of the support
of `M`. -/
theorem supportDim_localizedModule_nonpos_iff [IsNoetherianRing R] [Module.Finite R M]
    {p : Ideal R} [p.IsPrime] (hp : annihilator R M ≤ p) :
    supportDim (Localization.AtPrime p) (LocalizedModule p.primeCompl M) ≤ 0 ↔
      p ∈ (annihilator R M).minimalPrimes := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- A minimal prime `q ⊊ p` of the support is associated to `M`, so `q R_p` is an associated
    -- prime of `M_p` strictly below the maximal ideal, and `1 ≤ dim (R_p ⧸ q R_p) ≤ dim Supp M_p`.
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hp
    refine by_contra fun hpmin ↦ ?_
    have hqp : q < p := lt_of_le_of_ne hqp fun h ↦ hpmin (h ▸ hq)
    have := hq.isPrime
    have hdisj : Disjoint (p.primeCompl : Set R) q :=
      Set.disjoint_left.2 fun _ hx hxq ↦ hx (hqp.le hxq)
    set Q := q.map (algebraMap R (Localization.AtPrime p))
    have hQ : Q.under R = q := IsLocalization.under_map_of_isPrime_disjoint _ _ ‹_› hdisj
    have hQass : IsAssociatedPrime Q (LocalizedModule p.primeCompl M) :=
      associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
        p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) Q
        (by rw [← Ideal.under_def, hQ]
            exact associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hq)
    have := hQass.isPrime
    have hQlt : Q < maximalIdeal (Localization.AtPrime p) :=
      lt_of_le_of_ne (le_maximalIdeal this.ne_top) fun h ↦
        hqp.ne (hQ.symm.trans (Localization.AtPrime.eq_maximalIdeal_iff_under_eq.2 h))
    have hdim := (TauCeti.ringKrullDim_quotient_add_one_le_of_lt hQlt).trans
      hQass.ringKrullDim_quotient_le_supportDim
    rw [ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance), zero_add] at hdim
    exact absurd (hdim.trans h) (by decide)
  · -- Every prime `Q` of the support of `M_p` contracts to a prime between the annihilator of `M`
    -- and `p`, hence to `p`, so `Q` is the maximal ideal and the support is a single point.
    refine Order.krullDim_nonpos_iff_forall_isMax.2 fun Q Q' _ ↦ ?_
    suffices key : ∀ Q ∈ support (Localization.AtPrime p) (LocalizedModule p.primeCompl M),
        Q.asIdeal = maximalIdeal (Localization.AtPrime p) by
      exact (Subtype.ext (PrimeSpectrum.ext ((key _ Q'.2).trans (key _ Q.2).symm))).le
    intro Q hQ
    have hQp : Q.asIdeal.under R ≤ p :=
      (Ideal.comap_mono (le_maximalIdeal Q.isPrime.ne_top)).trans_eq
        Localization.AtPrime.under_maximalIdeal
    -- `R` acts on `M_p` through `M`, so the annihilator of `M` kills `M_p`.
    have hann : annihilator R M ≤ Q.asIdeal.under R := fun r hr ↦
      annihilator_le_of_mem_support
        (support_subset_preimage_comap (R := R) (A := Localization.AtPrime p) hQ) <|
        mem_annihilator.2 fun x ↦ LocalizedModule.induction_on (fun m s ↦ by
          rw [LocalizedModule.smul'_mk, mem_annihilator.1 hr, LocalizedModule.zero_mk]) x
    exact Localization.AtPrime.eq_maximalIdeal_iff_under_eq.1
      (le_antisymm hQp (h.2 ⟨Ideal.IsPrime.under R Q.asIdeal, hann⟩ hQp))

/-- A finite module over a Noetherian ring satisfies `(S_1)` if and only if it has no embedded
primes: its associated primes are exactly the minimal primes of its support. Stacks,
Lemma 10.157.2 (031Q). -/
@[stacks 031Q]
theorem satisfiesSerreS_one_iff [IsNoetherianRing R] [Module.Finite R M] :
    SatisfiesSerreS 1 R M ↔ associatedPrimes R M = (annihilator R M).minimalPrimes := by
  refine ⟨fun h ↦ Set.Subset.antisymm (fun p hp ↦ ?_)
    (associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M), fun h p _ ↦ ?_⟩
  · -- At an associated prime the depth of `M_p` is zero, so `(S_1)` forces `dim Supp M_p ≤ 0`.
    have := hp.isPrime
    have hann : annihilator R M ≤ p :=
      Submodule.annihilator_top (R := R) (M := M) ▸ hp.annihilator_le
    refine (supportDim_localizedModule_nonpos_iff hann).1 ?_
    have h1 := h p
    rw [TauCeti.depth_localizedModule_eq_zero_iff.2 hp, min_le_iff] at h1
    exact h1.resolve_left (by decide)
  · by_cases hp : p ∈ associatedPrimes R M
    · rw [h] at hp
      exact (min_le_right _ _).trans <|
        ((supportDim_localizedModule_nonpos_iff hp.1.2).2 hp).trans (by exact_mod_cast zero_le)
    · refine (min_le_left _ _).trans ?_
      exact_mod_cast Order.one_le_iff_ne_zero.2 (mt TauCeti.depth_localizedModule_eq_zero_iff.1 hp)

end Module

namespace Ring

variable (n : ℕ) (R : Type u) [CommRing R]

/-- A ring `R` satisfies *Serre's condition* `(R_n)` if every prime of height at most `n` lies in
the regular locus, that is, `R_p` is a regular local ring whenever `ht p ≤ n`. Stacks,
Definition 10.157.1 (031P). -/
@[stacks 031P]
def SatisfiesSerreR : Prop :=
  ∀ p : PrimeSpectrum R, p.asIdeal.height ≤ n → p ∈ TauCeti.Excellence.regularLocus R

variable {n R}

/-- Restates `Ring.SatisfiesSerreR` in terms of the localizations at primes. -/
theorem satisfiesSerreR_iff : SatisfiesSerreR n R ↔
    ∀ (p : Ideal R) [p.IsPrime], p.height ≤ n → IsRegularLocalRing (Localization.AtPrime p) :=
  ⟨fun h p _ hp ↦ TauCeti.Excellence.mem_regularLocus.1 (h ⟨p, ‹_›⟩ hp),
    fun h p hp ↦ TauCeti.Excellence.mem_regularLocus.2 (h p.asIdeal hp)⟩

/-- Serre's condition `(R_n)` implies `(R_m)` for `m ≤ n`. -/
theorem SatisfiesSerreR.mono {m : ℕ} (h : SatisfiesSerreR n R) (hmn : m ≤ n) :
    SatisfiesSerreR m R := fun p hp ↦
  h p (hp.trans (by exact_mod_cast hmn))

end Ring

/-- A regular ring satisfies `(R_n)` for every `n`. -/
theorem IsRegularRing.satisfiesSerreR {R : Type u} [CommRing R] [IsRegularRing R] (n : ℕ) :
    Ring.SatisfiesSerreR n R := fun p _ ↦
  TauCeti.Excellence.regularLocus_eq_univ R ▸ Set.mem_univ p

/-- A reduced ring satisfies `(R_0)`: its localizations at minimal primes are fields. -/
theorem IsReduced.satisfiesSerreR_zero {R : Type u} [CommRing R] [IsReduced R] :
    Ring.SatisfiesSerreR 0 R := fun p hp ↦ by
  have : Ring.KrullDimLE 0 (Localization.AtPrime p.asIdeal) := Ring.krullDimLE_iff.2 <| by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal]
    exact_mod_cast hp
  have hfield := Ring.KrullDimLE.isField_of_isReduced (R := Localization.AtPrime p.asIdeal)
  have := hfield.isDomain
  have := hfield.isPrincipalIdealRing
  exact TauCeti.Excellence.mem_regularLocus.2 inferInstance

/-- A Noetherian ring is reduced if and only if it satisfies `(R_0)` and `(S_1)`: its localizations
at minimal primes are fields and it has no embedded primes. Stacks, Lemma 10.157.3 (031R). -/
@[stacks 031R]
theorem isReduced_iff_satisfiesSerreR_zero_and_satisfiesSerreS_one {R : Type u} [CommRing R]
    [IsNoetherianRing R] :
    IsReduced R ↔ Ring.SatisfiesSerreR 0 R ∧ Module.SatisfiesSerreS 1 R R := by
  have hann : Module.annihilator R R = ⊥ := Module.annihilator_eq_bot.2 inferInstance
  rw [Module.satisfiesSerreS_one_iff, hann]
  constructor
  · intro _
    refine ⟨IsReduced.satisfiesSerreR_zero, Set.Subset.antisymm (fun p hp ↦ ?_) (by simpa [hann]
      using Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R R)⟩
    -- An associated prime `p = ann x` lies in a minimal prime `q` not containing `x ≠ 0`.
    obtain ⟨hp, x, rfl⟩ := isAssociatedPrime_iff.1 (AssociatedPrimes.mem_iff.1 hp)
    have hx0 : x ≠ 0 := fun h ↦ hp.ne_top (by simp [h])
    obtain ⟨q, hq, hxq⟩ : ∃ q ∈ minimalPrimes R, x ∉ q := by
      by_contra! h
      have hx : x ∈ nilradical R := by
        rw [nilradical, ← Ideal.sInf_minimalPrimes]
        exact Submodule.mem_sInf.2 h
      simp [nilradical_eq_zero, hx0] at hx
    have hle : (⊥ : Submodule R R).colon {x} ≤ q := fun r hr ↦ by
      refine (hq.1.1.mem_or_mem ?_).resolve_right hxq
      rw [← smul_eq_mul, (Submodule.mem_bot R).1 (Submodule.mem_colon_singleton.1 hr)]
      exact q.zero_mem
    rw [le_antisymm hle (hq.2 ⟨hp, bot_le⟩ hle)]
    exact hq
  · -- An associated prime `P ⊇ ann x` is minimal by `(S_1)`, so `R_P` is regular by `(R_0)` and
    -- the nilpotent `x` dies in `R_P`: some `s ∉ P` kills `x`, contradicting `ann x ⊆ P`.
    rintro ⟨hR, hS⟩
    refine ⟨fun x hx ↦ by_contra fun hx0 ↦ ?_⟩
    obtain ⟨P, hP, hxP⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x hx0
    have hPmin : P ∈ (⊥ : Ideal R).minimalPrimes := hS ▸ hP
    have := hP.isPrime
    have hreg := hR ⟨P, ‹_›⟩ (Ideal.height_eq_zero_iff.2 hPmin).le
    obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ x).1 <|
      TauCeti.Excellence.algebraMap_eq_zero_of_mem_regularLocus_of_isNilpotent hreg
        (Localization.AtPrime P) hx
    exact hs (hxP (Submodule.mem_colon_singleton.2 (by simpa using hsx)))

/-- A Noetherian domain, such as `ℤ` or a polynomial ring over a field, has no embedded primes. -/
example {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] :
    Module.SatisfiesSerreS 1 R R :=
  (isReduced_iff_satisfiesSerreR_zero_and_satisfiesSerreS_one.1 inferInstance).2

/-- A Dedekind domain is regular, so it satisfies `(R_n)` for every `n`. -/
example {R : Type u} [CommRing R] [IsDedekindDomain R] (n : ℕ) : Ring.SatisfiesSerreR n R :=
  IsRegularRing.satisfiesSerreR n
