/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import TauCeti.RingTheory.RegularLocalRing.Basic
public import TauCeti.RingTheory.Ideal.Quotient.Colon

/-!
# Regular rings are normal

A Noetherian domain all of whose localizations at primes are regular local rings is integrally
closed (Stacks, Lemma 10.157.5 (0567), whose "normal" means that every localization at a prime is
an integrally closed domain). Consequently every localization of a regular ring at a prime is an
integrally closed domain. This is the ring-level step of the statement that regular schemes are
normal.

## Proof

Stacks deduces 0567 from Serre's criterion `(R₁) + (S₂)`. The proof here avoids Serre's criterion
and the depth API. Its inputs are that regular local rings are domains
(`TauCeti.IsRegularLocalRing.isDomain`, Stacks 00NP), that `A ⧸ (x)` is regular for `x ∉ 𝔪²`
(`TauCeti.IsRegularLocalRing.quotient_span_singleton`), that a regular local ring of dimension
one is a discrete valuation ring
(`TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one`), and Mathlib's
associated primes of Noetherian modules.

1. A regular local ring `A` of dimension at least two contains `x, y` in its maximal ideal with
   `x ≠ 0` and `y` a nonzerodivisor on `A ⧸ (x)`: take `x ∉ 𝔪²`, so that `A ⧸ (x)` is a regular
   local ring, hence a domain, and take `y ∈ 𝔪 \ (x)`, which exists because `𝔪` needs at least
   two generators.
2. Hence, for `b ≠ 0` in such an `A`, the maximal ideal is not an associated prime of `A ⧸ (b)`:
   if `𝔪 c ⊆ (b)` then `c ∈ (b)`
   (`TauCeti.IsRegularLocalRing.mem_span_singleton_of_forall_mul_mem`).
3. Let `R` be a regular Noetherian domain and let `a / b` lie in `R_𝔭` for every prime `𝔭` with
   `R_𝔭` integrally closed. If `a ∉ (b)`, an associated prime `𝔭` of `R ⧸ (b)` containing
   `((b) : a)` has `R_𝔭` regular local of dimension one by step 2, hence a discrete valuation
   ring, and `a / b ∈ R_𝔭` contradicts `𝔭 ⊇ ((b) : a)`. Mathlib's
   `IsIntegrallyClosed.of_localization` then shows that `R` is integrally closed.

The same statement for a regular *local* ring needs that its localizations at primes are again
regular (Stacks 0AFS), which is not used here.

## Main results

* `TauCeti.IsRegularLocalRing.mem_span_singleton_of_forall_mul_mem`: in a regular local ring of
  dimension at least two, `𝔪 c ⊆ (b)` with `b ≠ 0` forces `c ∈ (b)`.
* `TauCeti.IsRegularRing.height_eq_one_of_isAssociatedPrime_quotient_span_singleton`: for
  a nonzerodivisor `b` of a regular ring, every associated prime of `R ⧸ (b)` has height one.
* `TauCeti.IsRegularRing.isIntegrallyClosed`: a regular ring that is a domain is integrally
  closed. It is a low-priority instance, so with
  `TauCeti.IsRegularRing.isRegularRing_localization` and `TauCeti.IsRegularLocalRing.isDomain`
  every localization of a regular ring at a prime is found to be an integrally closed domain.

## References

* [Stacks Project, Lemma 10.157.5](https://stacks.math.columbia.edu/tag/0567).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `a39c3781b9850b9f3d5cbc9920322a3b8e365ef2` (Apache-2.0),
  `lean/Pcf/Stacks/Common/RegularNormal.lean`: `mem_span_singleton_of_forall_mul_mem` is its
  `Pcf.Stacks.mem_span_singleton_of_maximalIdeal_mul_le` (with the private step
  `exists_regular_pair` from its `exists_regular_pair_of_two_le_ringKrullDim`), and
  `IsRegularRing.isIntegrallyClosed` is its `Pcf.Stacks.isIntegrallyClosed_of_isRegularRing`.
-/

public section

namespace TauCeti

open _root_.IsLocalRing _root_.IsRegularLocalRing _root_.Ideal

open scoped nonZeroDivisors

namespace IsRegularLocalRing

variable {A : Type*} [CommRing A]

variable [IsRegularLocalRing A]

/-- A regular local ring of dimension at least two has elements `x, y` of its maximal ideal with
`x ≠ 0` and `y` a nonzerodivisor on `A ⧸ (x)`. -/
private theorem exists_regular_pair (hdim : 2 ≤ ringKrullDim A) :
    ∃ x ∈ maximalIdeal A, ∃ y ∈ maximalIdeal A, x ≠ 0 ∧
      ∀ u, y * u ∈ span {x} → u ∈ span {x} := by
  have hspan : 2 ≤ (maximalIdeal A).spanFinrank := by
    rw [← spanFinrank_maximalIdeal (R := A)] at hdim
    exact_mod_cast hdim
  obtain ⟨x, hxm, hx2, -⟩ :=
    TauCeti.IsLocalRing.exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes (R := A)
      (lt_of_lt_of_le (by norm_num) hdim)
  have hx0 : x ≠ 0 := by rintro rfl; exact hx2 (zero_mem _)
  -- `𝔪 ≠ (x)`, since `𝔪` needs at least two generators
  have hne : ¬ maximalIdeal A ≤ span {x} := fun h ↦ by
    have hle : (span {x} : Ideal A).spanFinrank ≤ 1 := by
      simpa using Submodule.spanFinrank_span_le_ncard_of_finite (R := A) (Set.finite_singleton x)
    rw [← le_antisymm h ((span_singleton_le_iff_mem _).mpr hxm)] at hle
    omega
  obtain ⟨y, hym, hyx⟩ := IsConcreteLE.not_le_iff_exists.mp hne
  have : IsRegularLocalRing (A ⧸ span {x}) := quotient_span_singleton hxm hx2
  refine ⟨x, hxm, y, hym, hx0, fun u hu ↦ ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hu hyx ⊢
  rw [map_mul] at hu
  exact (mul_eq_zero.mp hu).resolve_left hyx

/-- **The depth-two property of a regular local ring.** In a regular local ring of dimension at
least two, the maximal ideal is not an associated prime of `A ⧸ (b)` for `b ≠ 0`: if `z c ∈ (b)`
for every `z` in the maximal ideal, then `c ∈ (b)`. -/
theorem mem_span_singleton_of_forall_mul_mem (hdim : 2 ≤ ringKrullDim A) {b c : A} (hb : b ≠ 0)
    (hc : ∀ z ∈ maximalIdeal A, z * c ∈ span {b}) : c ∈ span {b} := by
  obtain ⟨x, hx, y, hy, hx0, hreg⟩ := exists_regular_pair hdim
  obtain ⟨u, hu⟩ := mem_span_singleton'.mp (hc x hx)
  obtain ⟨v, hv⟩ := mem_span_singleton'.mp (hc y hy)
  -- `b (y u) = y x c = b (v x)`, so `y u = v x ∈ (x)`, so `u = w x`, so `c = w b`
  have hyu : y * u = v * x := mul_left_cancel₀ hb (by linear_combination y * hu - x * hv)
  obtain ⟨w, hw⟩ := mem_span_singleton'.mp (hreg u (mem_span_singleton'.mpr ⟨v, hyu.symm⟩))
  exact mem_span_singleton'.mpr ⟨w, mul_left_cancel₀ hx0 (by linear_combination b * hw + hu)⟩

end IsRegularLocalRing

namespace IsRegularRing

variable (R : Type*) [CommRing R] [IsRegularRing R]

variable {R} in
/-- **Associated primes of a principal ideal in a regular ring have height one.** For a
nonzerodivisor `b` of a regular ring, every associated prime of `R ⧸ (b)` has height one: by the
depth-two property of regular local rings, the localization at an associated prime cannot have
dimension two or more. -/
theorem height_eq_one_of_isAssociatedPrime_quotient_span_singleton {b : R} (hb : b ∈ R⁰)
    {P : Ideal R} (hP : IsAssociatedPrime P (R ⧸ span {b})) : P.height = 1 := by
  obtain ⟨_, y, hPy⟩ := isAssociatedPrime_iff.mp hP
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  -- `P = ((b) : c)`
  have hPc : ∀ r, r ∈ P ↔ r * c ∈ span {b} := fun r ↦ by
    rw [hPy, Ideal.Quotient.mem_colon_singleton_mk]
  have hPb : b ∈ P := (hPc b).mpr (mem_span_singleton'.mpr ⟨c, mul_comm _ _⟩)
  let A := Localization.AtPrime P
  -- `height P ≥ 1`, since `P` contains the nonzerodivisor `b`
  have hP1 : 1 ≤ P.height := (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hb).trans
    (Ideal.height_mono ((span_singleton_le_iff_mem _).mpr hPb))
  have hbA : algebraMap R A b ≠ 0 :=
    nonZeroDivisors.ne_zero (IsLocalization.nonZeroDivisors_le_comap P.primeCompl A hb)
  -- `dim A < 2`: otherwise the depth-two property puts `c` in `(b) R_P`, so some `s ∉ P` has
  -- `s c ∈ (b)`, contradicting `P = ((b) : c)`
  have hlt2 : ¬ 2 ≤ ringKrullDim A := fun h2 ↦ by
    have hspan : (span {b}).map (algebraMap R A) = span {algebraMap R A b} := by
      rw [Ideal.map_span, Set.image_singleton]
    have hPc' : P * span {c} ≤ span {b} := Ideal.mul_le.mpr fun r hr d hd ↦ by
      obtain ⟨t, rfl⟩ := mem_span_singleton'.mp hd
      rw [mul_left_comm]
      exact (span {b}).mul_mem_left t ((hPc r).mp hr)
    have hmem : algebraMap R A c ∈ span {algebraMap R A b} := by
      refine IsRegularLocalRing.mem_span_singleton_of_forall_mul_mem h2 hbA fun z hz ↦ ?_
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

section Domain

variable [IsDomain R]

/-- **A regular ring that is a domain is integrally closed** (Stacks, Lemma 10.157.5 (0567), for
a domain). -/
@[stacks 0567 "for a domain, in the form `IsIntegrallyClosed`"]
instance (priority := low) isIntegrallyClosed : IsIntegrallyClosed R := by
  classical
  let K := FractionRing R
  -- localize at the primes where `R_p` is integrally closed, so that the side condition of
  -- `IsIntegrallyClosed.of_localization` is exactly the defining condition of this set
  apply IsIntegrallyClosed.of_localization
    {p : PrimeSpectrum R | IsIntegrallyClosed (Localization.AtPrime p.asIdeal)}
    fun _ hp ↦ by simpa using hp
  rw [eq_bot_iff]
  intro z hz
  simp only [Algebra.mem_iInf, Set.mem_ofPred_eq] at hz
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) (K := K) z
  have hbK : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  by_cases hab : a ∈ span {b}
  · obtain ⟨r, hr⟩ := mem_span_singleton'.mp hab
    exact Algebra.mem_bot.mpr ⟨r, by rw [← hr, map_mul, mul_div_cancel_right₀ _ hbK]⟩
  exfalso
  -- an associated prime `P = ((b) : c)` of `R ⧸ (b)` containing `((b) : a)`
  obtain ⟨P, hPass, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (Ideal.Quotient.mk (span {b}) a) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have := hPass.isPrime
  have hcolon : ∀ r, r * a ∈ span {b} → r ∈ P := fun r hr ↦
    hle (Ideal.Quotient.mem_colon_singleton_mk.mpr hr)
  -- `R_P` is a regular local ring of dimension one, hence a discrete valuation ring
  have : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr <| by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height P,
        height_eq_one_of_isAssociatedPrime_quotient_span_singleton hb hPass, WithBot.coe_one]
  -- `a / b = r / s` with `s ∉ P` gives `s a ∈ (b)`, so `s ∈ P`
  have hzP := hz ⟨P, inferInstance⟩ inferInstance
  rw [← Localization.subalgebra.ofField_eq K P.primeCompl P.primeCompl_le_nonZeroDivisors] at hzP
  obtain ⟨r, s, hs, hrs⟩ := hzP
  have hsK : algebraMap R K s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (P.primeCompl_le_nonZeroDivisors hs)
  rw [← div_eq_mul_inv, div_eq_div_iff hbK hsK, ← map_mul, ← map_mul] at hrs
  exact hs (hcolon s (mem_span_singleton'.mpr ⟨r, by
    rw [mul_comm s, IsFractionRing.injective R K hrs]⟩))

end Domain

/-- Every localization of a regular ring at a prime is an integrally closed domain, so a regular
ring is normal in the sense of Stacks, Definition 10.37.11 (00GV). -/
example (p : Ideal R) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) :=
  ⟨inferInstance, inferInstance⟩

end IsRegularRing

end TauCeti
