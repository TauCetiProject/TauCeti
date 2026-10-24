/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Regular.LinearMap
public import TauCeti.RingTheory.CohenMacaulay.Basic
public import TauCeti.RingTheory.LocalRing.MaximalIdeal.Generator
import TauCeti.RingTheory.Ideal.Quotient.Colon

/-!
# Depth of normal local domains

A Noetherian local domain `R` which is integrally closed and has dimension at least two has depth
at least two. This is the local form of the `(S₂)` half of Serre's normality criterion (Stacks,
Lemma 10.157.4 (031S)): a normal Noetherian ring satisfies `(S₂)`. Consequently a Noetherian
integrally closed local domain of dimension at most two is Cohen–Macaulay, which is the
hypothesis miracle flatness asks of a two-dimensional normal local domain finite over a regular
local ring.

## Proof

The depth statement rests on the following property of the maximal ideal `𝔪`: for `b ≠ 0`, it is
not an associated prime of `R ⧸ (b)`, unless `𝔪` is principal. Indeed, let `𝔪 c ⊆ (b)` and put
`t = c / b` in the fraction field, so that `t 𝔪 ⊆ R`. If `t 𝔪 ⊆ 𝔪`, then `t` is integral over `R`
(Mathlib's `isIntegral_of_smul_mem_submodule`), hence lies in `R`, and `c ∈ (b)`. Otherwise
`t u` is a unit for some `u ∈ 𝔪`, and then `𝔪 = (u)`. A principal maximal ideal forces dimension
at most one, so in dimension at least two, any nonzero `x ∈ 𝔪` is followed by an element of `𝔪`
regular on `R ⧸ (x)` (Mathlib's `IsSMulRegular.subsingleton_linearMap_iff`).

## Main results

* `TauCeti.IsIntegrallyClosed.mem_span_singleton_of_forall_mul_mem`: in a Noetherian integrally
  closed local domain whose maximal ideal is not principal, `𝔪 c ⊆ (b)` with `b ≠ 0` forces
  `c ∈ (b)`.
* `TauCeti.IsIntegrallyClosed.isSMulRegular_quotient_span_singleton_of_radical_span_pair`:
  if `(x, y)` has maximal radical, `x ≠ 0` and the maximal ideal is nonprincipal, then `y` is
  regular on `R ⧸ (x)`.
* `IsLocalRing.two_le_depth_of_isIntegrallyClosed`: a Noetherian integrally closed local domain of
  dimension at least two has depth at least two.
* `Module.isCohenMacaulay_self_of_isIntegrallyClosed_of_krullDimLE_two`: a Noetherian integrally
  closed local domain of dimension at most two is Cohen–Macaulay over itself.

## References

* [Stacks Project, Lemma 10.157.4](https://stacks.math.columbia.edu/tag/031S), Serre's criterion
  for normality.
* H. Matsumura, *Commutative Ring Theory*, Theorem 23.8.
-/

public section

open IsLocalRing Ideal Pointwise

namespace TauCeti.IsIntegrallyClosed

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
  [IsIntegrallyClosed R]

/-- In a Noetherian integrally closed local domain whose maximal ideal is not principal, the
maximal ideal is not an associated prime of `R ⧸ (b)` for `b ≠ 0`: if `z c ∈ (b)` for every `z` in
the maximal ideal, then `c ∈ (b)`. -/
theorem mem_span_singleton_of_forall_mul_mem (hm : ¬ (maximalIdeal R).IsPrincipal) {b c : R}
    (hb : b ≠ 0) (hc : ∀ z ∈ maximalIdeal R, z * c ∈ span {b}) : c ∈ span {b} := by
  have hc' : ∀ z ∈ maximalIdeal R, ∃ w, z * c = b * w := fun z hz ↦ by
    obtain ⟨w, hw⟩ := mem_span_singleton'.mp (hc z hz)
    exact ⟨w, by rw [← hw, mul_comm]⟩
  by_cases hall : ∀ z ∈ maximalIdeal R, ∀ w, z * c = b * w → w ∈ maximalIdeal R
  · -- `t = c / b` maps the maximal ideal into itself, so it is integral over `R`.
    let K := FractionRing R
    have hb' : algebraMap R K b ≠ 0 := by simpa using (IsFractionRing.injective R K).ne hb
    let N : Submodule R K := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
    have hN : N ≠ ⊥ := fun h ↦ hm <| by
      rw [Submodule.map_injective_of_injective (IsFractionRing.injective R K)
        (h.trans (Submodule.map_bot _).symm)]
      exact bot_isPrincipal
    have hint : IsIntegral R (algebraMap R K c / algebraMap R K b) := by
      refine isIntegral_of_smul_mem_submodule N hN
        ((IsNoetherian.noetherian (maximalIdeal R)).map _) _ ?_
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨w, hw⟩ := hc' z hz
      refine ⟨w, hall z hz w hw, ?_⟩
      have hw' := congrArg (algebraMap R K) hw
      simp only [map_mul] at hw'
      simp only [Algebra.linearMap_apply, smul_eq_mul]
      field_simp
      linear_combination -hw'
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).mp hint
    refine mem_span_singleton'.mpr ⟨a, IsFractionRing.injective R K ?_⟩
    rw [map_mul, ha, div_mul_cancel₀ _ hb']
  · -- Otherwise `u c = b v` with `v` a unit for some `u` in the maximal ideal, which is then `(u)`.
    push Not at hall
    obtain ⟨u, hu, v, huv, hv⟩ := hall
    have hv : IsUnit v := notMem_maximalIdeal.mp hv
    refine absurd ⟨⟨u, le_antisymm (fun z hz ↦ ?_) ((span_singleton_le_iff_mem _).mpr hu)⟩⟩ hm
    obtain ⟨w, hw⟩ := hc' z hz
    have : v * z = u * w := mul_left_cancel₀ hb (by linear_combination u * hw - z * huv)
    rw [Submodule.mem_span_singleton]
    exact ⟨↑hv.unit⁻¹ * w, by
      rw [smul_eq_mul]
      linear_combination -(↑hv.unit⁻¹ : R) * this + z * hv.val_inv_mul⟩

/-- In a Noetherian normal local domain with nonprincipal maximal ideal, if `(x, y)` has maximal
radical and `x ≠ 0`, then `y` is a nonzerodivisor on `R ⧸ (x)`. -/
theorem isSMulRegular_quotient_span_singleton_of_radical_span_pair
    (hm : ¬ (maximalIdeal R).IsPrincipal) {x y : R} (hx : x ≠ 0)
    (hxy : (span {x, y}).radical = maximalIdeal R) :
    IsSMulRegular (R ⧸ span {x}) y := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro c hc
  by_contra hcx
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (Ideal.Quotient.mk (span {x}) c) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hprime := hP.isPrime
  have hxP : x ∈ P := hle (Ideal.Quotient.mem_colon_singleton_mk.mpr
    (mem_span_singleton'.mpr ⟨c, mul_comm _ _⟩))
  have hyP : y ∈ P := hle (Ideal.Quotient.mem_colon_singleton_mk.mpr hc)
  have hPm : P = maximalIdeal R := by
    refine le_antisymm (le_maximalIdeal hprime.ne_top) ?_
    rw [← hxy]
    exact hprime.radical_le_iff.mpr (span_le.mpr (by rintro z (rfl | rfl) <;> assumption))
  obtain ⟨_, u, hu⟩ := isAssociatedPrime_iff.mp hP
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective u
  have hd : d ∈ span {x} := mem_span_singleton_of_forall_mul_mem hm hx fun z hz ↦
    Ideal.Quotient.mem_colon_singleton_mk.mp (hu ▸ hPm.symm ▸ hz)
  have hone : (1 : R) ∈ P := by
    rw [hu]
    exact Ideal.Quotient.mem_colon_singleton_mk.mpr (by simpa using hd)
  exact hprime.one_notMem hone

end TauCeti.IsIntegrallyClosed

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- **The `(S₂)` property of normal local domains.** A Noetherian integrally closed local domain of
dimension at least two has depth at least two. The local form of the `(S₂)` half of Serre's
criterion, Stacks, Lemma 10.157.4 (031S). -/
@[stacks 031S "the local form of normal implies (S₂)"]
theorem two_le_depth_of_isIntegrallyClosed [IsDomain R] [IsIntegrallyClosed R]
    (hdim : 2 ≤ ringKrullDim R) : 2 ≤ depth (ModuleCat.of R R) := by
  have hm : ¬ (maximalIdeal R).IsPrincipal := fun h ↦
    absurd (hdim.trans (ringKrullDim_le_one_of_isPrincipal_maximalIdeal h)) (by decide)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := maximalIdeal R)
    fun h ↦ hm (h ▸ bot_isPrincipal)
  -- Every linear map `R ⧸ 𝔪 → R ⧸ (x)` vanishes, so some `y ∈ 𝔪` is regular on `R ⧸ (x)`.
  have : Subsingleton (R ⧸ maximalIdeal R →ₗ[R] QuotSMulTop x R) := by
    refine subsingleton_of_forall_eq 0 fun f ↦ ?_
    have hmk (r : R) : Ideal.Quotient.mk (maximalIdeal R) r = r • Ideal.Quotient.mk _ 1 := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_one, mul_one]
    have key : f (Ideal.Quotient.mk _ 1) = 0 := by
      -- The maximal ideal kills `f 1`, so a lift `c` of `f 1` has `𝔪 c ⊆ (x)`.
      have hkill (z : R) (hz : z ∈ maximalIdeal R) : z • f (Ideal.Quotient.mk _ 1) = 0 := by
        rw [← map_smul, ← hmk, Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]
      obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (f (Ideal.Quotient.mk _ 1))
      simp only [← hc, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        ← Submodule.ideal_span_singleton_smul, smul_eq_mul, mul_top] at hkill ⊢
      exact TauCeti.IsIntegrallyClosed.mem_span_singleton_of_forall_mul_mem hm hx0 hkill
    refine LinearMap.ext fun q ↦ ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [hmk, map_smul, key, smul_zero, LinearMap.zero_apply]
  obtain ⟨y, hy, hreg⟩ := IsSMulRegular.subsingleton_linearMap_iff.mp this
  rw [annihilator_quotient] at hy
  rw [← depth_quotSMulTop_succ_eq_depth (IsSMulRegular.of_ne_zero hx0) hx,
    ← depth_quotSMulTop_succ_eq_depth hreg hy, add_assoc]
  exact le_add_self

end IsLocalRing

namespace Module

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
  [IsIntegrallyClosed R]

/-- A Noetherian integrally closed local domain of dimension at most two is Cohen–Macaulay over
itself. -/
theorem isCohenMacaulay_self_of_isIntegrallyClosed_of_krullDimLE_two [Ring.KrullDimLE 2 R] :
    IsCohenMacaulay R R := by
  by_cases hdim : 2 ≤ ringKrullDim R
  · rw [isCohenMacaulay_iff_supportDim_le_depth, supportDim_self_eq_ringKrullDim]
    refine (Ring.krullDimLE_iff.1 ‹_›).trans ?_
    rw [← WithBot.coe_natCast, WithBot.coe_le_coe]
    exact_mod_cast IsLocalRing.two_le_depth_of_isIntegrallyClosed hdim
  -- In dimension at most one, a Noetherian local domain is Cohen–Macaulay.
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr
    (ENat.WithBot.lt_add_one_iff.mp (by simpa [one_add_one_eq_two] using not_le.mp hdim))
  exact isCohenMacaulay_self_of_isDomain_of_krullDimLE_one

end Module
