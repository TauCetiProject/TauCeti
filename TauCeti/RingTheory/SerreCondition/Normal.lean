/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.SerreCondition.Basic
public import TauCeti.RingTheory.CohenMacaulay.Normal
public import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
public import TauCeti.RingTheory.IntegralClosure.LocalRing
public import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.Ideal.Quotient.Colon

/-!
# Serre's criterion for normality

A Noetherian ring `R` is *normal* when every localization `R_p` at a prime is an integrally closed
domain (Stacks, Definition 10.37.11 (00GV)). *Serre's criterion* says that this holds exactly when
`R` satisfies `(R_1)` and `(S_2)`: the local rings at primes of height at most one are regular, and
`depth R_p ≥ min (2, dim R_p)` for every prime `p` (Stacks, Lemma 10.157.4 (031S)).

The forward direction is local: an integrally closed Noetherian local domain of dimension at most
one is a field or a discrete valuation ring, hence regular, and one of dimension at least two has
depth at least two (`IsLocalRing.two_le_depth_of_isIntegrallyClosed`).

For the converse, `(S_2)` forces every associated prime of `R ⧸ (b)`, for a nonzerodivisor `b`, to
have height one, and `(R_1)` makes the localization at such a prime a discrete valuation ring.
If `a / b` is integral over `R`, it therefore lies in every such localization, so `a ∈ (b)`: `R` is
integrally closed in its total ring of fractions. Both conditions pass to the local rings `R_p`,
which are reduced by `(R_0)` and `(S_1)` and hence domains
(`IsLocalRing.isDomain_of_isIntegrallyClosed`).

## Main results

* `Module.SatisfiesSerreS.height_eq_one_of_isAssociatedPrime_quotient_span_singleton`: in a
  Noetherian ring satisfying `(S_2)`, the associated primes of `R ⧸ (b)` for a nonzerodivisor `b`
  have height one.
* `TauCeti.isIntegrallyClosed_of_satisfiesSerreR_one_of_satisfiesSerreS_two`: a Noetherian ring
  satisfying `(R_1)` and `(S_2)` is integrally closed in its total ring of fractions.
* `TauCeti.satisfiesSerreR_one_of_forall_isIntegrallyClosed` and
  `TauCeti.satisfiesSerreS_two_of_forall_isIntegrallyClosed`: a Noetherian normal ring satisfies
  `(R_1)` and `(S_2)`.
* `TauCeti.forall_isDomain_and_isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two`:
  **Serre's criterion**, a Noetherian ring is normal if and only if it satisfies `(R_1)` and
  `(S_2)`.

## References

* [Stacks Project, Lemma 10.157.4](https://stacks.math.columbia.edu/tag/031S)
* The proofs of `Module.SatisfiesSerreS.height_eq_one_of_isAssociatedPrime_quotient_span_singleton`
  and `TauCeti.isIntegrallyClosed_of_satisfiesSerreR_one_of_satisfiesSerreS_two` follow those of
  `TauCeti.IsRegularRing.height_eq_one_of_isAssociatedPrime_quotient_span_singleton` and
  `TauCeti.IsRegularRing.isIntegrallyClosed` in `TauCeti.RingTheory.RegularLocalRing.Normal`
  (ported there from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization)), with depth at least two
  in place of regularity and `(R_1)` in place of regularity in codimension one.
-/

public section

universe u

open IsLocalRing Ideal

open scoped nonZeroDivisors

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

namespace Module.SatisfiesSerreS

/-- **Associated primes of a principal ideal under `(S_2)`.** In a Noetherian ring satisfying
`(S_2)`, every associated prime of `R ⧸ (b)`, for a nonzerodivisor `b`, has height one. -/
theorem height_eq_one_of_isAssociatedPrime_quotient_span_singleton (h : SatisfiesSerreS 2 R R)
    {b : R} (hb : b ∈ R⁰) {P : Ideal R} (hP : IsAssociatedPrime P (R ⧸ span {b})) :
    P.height = 1 := by
  obtain ⟨_, y, hPy⟩ := isAssociatedPrime_iff.mp hP
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  -- `P = ((b) : c)`
  have hPc : ∀ r, r ∈ P ↔ r * c ∈ span {b} := fun r ↦ by
    rw [hPy, TauCeti.Ideal.Quotient.mem_colon_singleton_mk]
  have hPb : b ∈ P := (hPc b).mpr (mem_span_singleton'.mpr ⟨c, mul_comm _ _⟩)
  let A := Localization.AtPrime P
  -- `height P ≥ 1`, since `P` contains the nonzerodivisor `b`
  have hP1 : 1 ≤ P.height := (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hb).trans
    (Ideal.height_mono ((span_singleton_le_iff_mem _).mpr hPb))
  have hbA : IsSMulRegular A (algebraMap R A b) := fun u v huv ↦ sub_eq_zero.1 <|
    mem_nonZeroDivisors_iff_left.1 (IsLocalization.nonZeroDivisors_le_comap P.primeCompl A hb) _
      (by rw [mul_sub, sub_eq_zero]; exact huv)
  -- `dim A < 2`: otherwise `A` has depth at least two by `(S_2)`, which puts `c` in `(b) A`, so
  -- some `s ∉ P` has `s c ∈ (b)`, contradicting `P = ((b) : c)`
  have hlt2 : ¬ 2 ≤ ringKrullDim A := fun h2 ↦ by
    have hdepth : 2 ≤ depth (ModuleCat.of A A) := by
      have hP := satisfiesSerreS_self_iff.1 h P
      rw [min_eq_left (by exact_mod_cast h2), ← WithBot.coe_natCast, WithBot.coe_le_coe] at hP
      exact_mod_cast hP
    have hspan : (span {b}).map (algebraMap R A) = span {algebraMap R A b} := by
      rw [Ideal.map_span, Set.image_singleton]
    have hPc' : P * span {c} ≤ span {b} := Ideal.mul_le.mpr fun r hr d hd ↦ by
      obtain ⟨t, rfl⟩ := mem_span_singleton'.mp hd
      rw [mul_left_comm]
      exact (span {b}).mul_mem_left t ((hPc r).mp hr)
    have hmem : algebraMap R A c ∈ span {algebraMap R A b} := by
      refine mem_span_singleton_of_forall_mul_mem_of_two_le_depth hdepth hbA fun z hz ↦ ?_
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P A] at hz
      rw [← hspan]
      refine Ideal.map_mono hPc' ?_
      rw [Ideal.map_mul]
      exact Ideal.mul_mem_mul hz (Ideal.mem_map_of_mem _ (mem_span_singleton_self c))
    rw [← hspan, IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl] at hmem
    obtain ⟨s, hs, hsc⟩ := hmem
    exact hs ((hPc s).mpr hsc)
  -- `dim A = height P`, so `height P < 2`
  have hP2 : P.height < 2 := not_le.mp fun h ↦ hlt2 <| by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P A]
    exact WithBot.coe_le_coe.mpr h
  exact le_antisymm (ENat.lt_two_iff.mp hP2) hP1

end Module.SatisfiesSerreS

namespace TauCeti

/-- A Noetherian ring satisfying `(R_1)` and `(S_2)` is integrally closed in its total ring of
fractions. Stacks, Lemma 10.157.4 (031S). -/
@[stacks 031S "integral closedness in the total ring of fractions"]
theorem isIntegrallyClosed_of_satisfiesSerreR_one_of_satisfiesSerreS_two
    (hR : Ring.SatisfiesSerreR 1 R) (hS : Module.SatisfiesSerreS 2 R R) : IsIntegrallyClosed R := by
  let K := FractionRing R
  refine (isIntegrallyClosed_iff K).2 fun {z} hz ↦ ?_
  -- write the integral element as `a / b` and show `a ∈ (b)`
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ z
  by_cases hab : a ∈ span {b}
  · obtain ⟨r, hr⟩ := mem_span_singleton'.mp hab
    exact ⟨r, by rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, hr]⟩
  exfalso
  -- an associated prime `P = ((b) : c)` of `R ⧸ (b)` containing `((b) : a)`
  obtain ⟨P, hPass, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (Ideal.Quotient.mk (span {b}) a) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have := hPass.isPrime
  have hcolon : ∀ r, r * a ∈ span {b} → r ∈ P := fun r hr ↦
    hle (Ideal.Quotient.mem_colon_singleton_mk.mpr hr)
  -- `P` has height one, so `R_P` is a regular local ring of dimension one, a DVR
  let A := Localization.AtPrime P
  have hP := hS.height_eq_one_of_isAssociatedPrime_quotient_span_singleton hb hPass
  have : IsRegularLocalRing A := Ring.satisfiesSerreR_iff.1 hR P hP.le
  have : IsDiscreteValuationRing A :=
    IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr <| by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height P, hP, WithBot.coe_one]
  -- the image of `a / b` in the fraction field of `R_P` is integral, hence lies in `R_P`
  let L := FractionRing A
  have hle' : R⁰ ≤ A⁰.comap (algebraMap R A) :=
    IsLocalization.nonZeroDivisors_le_comap P.primeCompl A
  have hint := hz.map_of_comp_eq (algebraMap R A) (IsLocalization.map L (algebraMap R A) hle')
    (IsLocalization.map_comp hle').symm
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff L).1 inferInstance hint
  rw [IsLocalization.map_mk', IsLocalization.eq_mk'_iff_mul_eq, ← map_mul] at hy
  -- so `a ∈ (b) R_P`, that is `s a ∈ (b)` for some `s ∉ P`
  have hmem : algebraMap R A a ∈ (span {b}).map (algebraMap R A) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact mem_span_singleton'.mpr ⟨y, IsFractionRing.injective A L hy⟩
  obtain ⟨s, hs, hsa⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl A _ _).1 hmem
  exact hs (hcolon s hsa)

/-- **The `(R_1)` half of Serre's criterion.** A Noetherian ring whose local rings are integrally
closed domains satisfies `(R_1)`. Stacks, Lemma 10.157.4 (031S). -/
@[stacks 031S "normal implies (R₁)"]
theorem satisfiesSerreR_one_of_forall_isIntegrallyClosed
    (h : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    Ring.SatisfiesSerreR 1 R := by
  refine Ring.satisfiesSerreR_iff.2 fun p _ hp ↦ ?_
  obtain ⟨_, _⟩ := h p
  -- `R_p` has dimension at most one, so it is a field or a discrete valuation ring
  have hdim : ringKrullDim (Localization.AtPrime p) ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
    exact_mod_cast hp
  -- a principal ideal local domain is regular
  suffices IsPrincipalIdealRing (Localization.AtPrime p) from inferInstance
  rcases hdim.lt_or_eq with hlt | heq
  · have : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
      Ring.krullDimLE_iff.2 (ENat.WithBot.lt_add_one_iff.mp (by simpa using hlt))
    have hfield := Ring.KrullDimLE.isField_of_isReduced (R := Localization.AtPrime p)
    exact hfield.isPrincipalIdealRing
  · have := IsDiscreteValuationRing.of_ringKrullDim_eq_one heq
    infer_instance

/-- **The `(S_2)` half of Serre's criterion.** A Noetherian ring whose local rings are integrally
closed domains satisfies `(S_2)`. Stacks, Lemma 10.157.4 (031S). -/
@[stacks 031S "normal implies (S₂)"]
theorem satisfiesSerreS_two_of_forall_isIntegrallyClosed
    (h : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    Module.SatisfiesSerreS 2 R R := by
  refine Module.satisfiesSerreS_self_iff.2 fun p _ ↦ ?_
  obtain ⟨_, _⟩ := h p
  -- in dimension at least two the depth is at least two; otherwise `R_p` is Cohen–Macaulay
  by_cases h2 : 2 ≤ ringKrullDim (Localization.AtPrime p)
  · refine (min_le_left _ _).trans ?_
    rw [← WithBot.coe_natCast, WithBot.coe_le_coe]
    exact_mod_cast IsLocalRing.two_le_depth_of_isIntegrallyClosed h2
  have : Ring.KrullDimLE 1 (Localization.AtPrime p) := Ring.krullDimLE_iff.mpr
    (ENat.WithBot.lt_add_one_iff.mp (by simpa [one_add_one_eq_two] using not_le.mp h2))
  refine (min_le_right _ _).trans ?_
  rw [← Module.supportDim_self_eq_ringKrullDim]
  exact (Module.isCohenMacaulay_self_of_isDomain_of_krullDimLE_one).depth_eq.ge

/-- **Serre's criterion for normality.** A Noetherian ring is normal, that is, every localization
at a prime is an integrally closed domain, if and only if it satisfies `(R_1)` and `(S_2)`.
Stacks, Lemma 10.157.4 (031S). -/
@[stacks 031S]
theorem forall_isDomain_and_isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two :
    (∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ↔
      Ring.SatisfiesSerreR 1 R ∧ Module.SatisfiesSerreS 2 R R := by
  refine ⟨fun h ↦ ⟨satisfiesSerreR_one_of_forall_isIntegrallyClosed h,
    satisfiesSerreS_two_of_forall_isIntegrallyClosed h⟩, fun ⟨hR, hS⟩ p _ ↦ ?_⟩
  -- `(R_1)` and `(S_2)` pass to `R_p`, which is then integrally closed and, by `(R_0)` and
  -- `(S_1)`, reduced; a reduced integrally closed Noetherian local ring is a domain
  have hR' := hR.localization p.primeCompl (Localization.AtPrime p)
  have hS' := hS.localization_self p.primeCompl (Localization.AtPrime p)
  have := isIntegrallyClosed_of_satisfiesSerreR_one_of_satisfiesSerreS_two hR' hS'
  have : IsReduced (Localization.AtPrime p) :=
    isReduced_iff_satisfiesSerreR_zero_and_satisfiesSerreS_one.2
      ⟨hR'.mono zero_le_one, hS'.mono one_le_two⟩
  exact ⟨IsLocalRing.isDomain_of_isIntegrallyClosed, ‹_›⟩

end TauCeti

/-- A Noetherian integrally closed domain, such as `ℤ` or a polynomial ring over a field, satisfies
`(R_1)` and `(S_2)`. -/
example [IsDomain R] [IsIntegrallyClosed R] :
    Ring.SatisfiesSerreR 1 R ∧ Module.SatisfiesSerreS 2 R R :=
  TauCeti.forall_isDomain_and_isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two.1
    fun p _ ↦ ⟨inferInstance,
      isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors⟩
