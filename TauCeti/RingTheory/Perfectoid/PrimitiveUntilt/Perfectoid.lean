/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Integral.Tilt
public import TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Map
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Tate

import Mathlib.Algebra.CharP.Subring
import Mathlib.LinearAlgebra.SModEq.Pow
import Mathlib.RingTheory.AdicCompletion.Functoriality
import TauCeti.RingTheory.Huber.Pair.Complete
import TauCeti.RingTheory.Huber.Perfect
import TauCeti.RingTheory.Ideal.Quotient.Frobenius
import TauCeti.RingTheory.Perfectoid.Away

/-!
# Primitive untilts are perfectoid Tate rings with tilt `R`

Let `(R, R⁺)` be a perfect complete Hausdorff Tate Huber pair of characteristic `p`, and let
`ξ ∈ 𝕎 R⁺` be a primitive element. This file proves that the untilt `A = untilt p P (span {ξ})`
constructed in `TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Basic` is a perfectoid Tate ring whose
tilt `A♭` is topologically isomorphic to `R`:

* Choosing a pseudouniformiser `ϖ ∈ R⁺` with `ϖ ^ p ∣ ξ₀`, the isomorphism
  `A⁺ ⧸ (sharp ϖ) ≃+* R⁺ ⧸ (ϖ)` and its `p`-th-power counterpart show that relative Frobenius
  `A₀ ⧸ (π) → A₀ ⧸ (π ^ p)` is bijective on `A₀ = 𝕎 R⁺ ⧸ (ξ)`. Consequently `A₀` and `A⁺` are
  integral perfectoid (`untilt.isIntegralPerfectoid_quotient`,
  `untilt.isIntegralPerfectoid_untiltPlus`), `A` is uniform (`untilt.isUniform`), and `A` is a
  perfectoid Tate ring (`untilt.isPerfectoidTateRing`) via
  `TauCeti.Perfectoid.isPerfectoidTateRing_of_bijective_frobeniusModPow`.
* An elementary induction using `quotientTeichmullerEquiv` proves that `sharp x ∈ A⁺ ↔ x ∈ R⁺`
  (`untilt.sharp_mem_untiltPlus_iff`).
* The tilt `A♭` is a Tate ring (`untilt.isTateRing_uniformTilt`), and the map
  `x ↦ (sharp (x ^ (1 / p ^ n)))_n` is a topological ring isomorphism `R ≃+* A♭`, whose inverse
  is `untilt.tiltEquiv` (`untilt.isHomeomorph_tiltEquiv`).

For the Huber pair structure `(A, A⁺)`, the identification of `A♭⁺` and `PreTilt A⁺ p` with `R⁺`,
Fontaine's `ker θ = (ξ)`, and the almost vanishing of `A° ⧸ A⁺`, see
`TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Pair`.

## Main definitions

* `TauCeti.Perfectoid.untilt.tiltEquiv`: the ring isomorphism `A♭ ≃+* R`.

## Main results

* `TauCeti.Perfectoid.untilt.isIntegralPerfectoid_quotient`,
  `TauCeti.Perfectoid.untilt.isIntegralPerfectoid_untiltPlus`: `𝕎 R⁺ ⧸ (ξ)` and `A⁺` are integral
  perfectoid rings.
* `TauCeti.Perfectoid.untilt.isUniform`, `TauCeti.Perfectoid.untilt.isPerfectoidTateRing`:
  the untilt `A` is a uniform perfectoid Tate ring.
* `TauCeti.Perfectoid.untilt.sharp_mem_untiltPlus_iff`: `sharp x ∈ A⁺ ↔ x ∈ R⁺`.
* `TauCeti.Perfectoid.untilt.isTateRing_uniformTilt`,
  `TauCeti.Perfectoid.untilt.isHomeomorph_tiltEquiv`: `A♭` is Tate and `tiltEquiv : A♭ ≃+* R` is a
  homeomorphism.

## References

* P. Scholze, *Étale cohomology of diamonds*, Theorem 3.17.
* P. Scholze and J. Weinstein, *Berkeley lectures on `p`-adic geometry*, Theorem 6.2.11.
* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*,
  Arizona Winter School 2017, Lemmas 2.6.14, 2.7.9, and Theorem 2.3.9.
* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.21.
-/

public section

open Filter Ideal Topology TauCeti.Huber WittVector
open scoped nonZeroDivisors Pointwise

namespace TauCeti.Perfectoid.untilt

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

private theorem iterateFrobeniusEquiv_symm_pow {S : Type*} [CommRing S] [CharP S p]
    [PerfectRing S p] (n : ℕ) (x : S) :
    (iterateFrobeniusEquiv S p n).symm x ^ p ^ n = x := by
  rw [← iterateFrobeniusEquiv_def]
  exact (iterateFrobeniusEquiv S p n).apply_symm_apply x

private theorem iterateFrobeniusEquiv_zero_symm {S : Type*} [CommRing S] [CharP S p]
    [PerfectRing S p] (x : S) : (iterateFrobeniusEquiv S p 0).symm x = x := by
  have := iterateFrobeniusEquiv_symm_pow (p := p) 0 x
  simpa only [pow_zero, pow_one] using this

/-! ### Divisibility and relative Frobenius on `𝕎 R⁺ ⧸ (ξ)` -/

section Algebraic

variable [TopologicalSpace R] [IsTopologicalRing R] [IsTateRing R] [CharP R p] [PerfectRing R p]
  {P : Pair R} {ξ : WittVector p P.plus}

private theorem coe_iterateFrobeniusEquiv_plus_symm (c : P.plus) (n : ℕ) :
    ((iterateFrobeniusEquiv P.plus p n).symm c : R) =
      (iterateFrobeniusEquiv R p n).symm (c : R) := by
  apply (iterateFrobeniusEquiv R p n).injective
  rw [(iterateFrobeniusEquiv R p n).apply_symm_apply, iterateFrobeniusEquiv_def,
    ← Subring.coe_pow, iterateFrobeniusEquiv_symm_pow]

/-- For any topologically nilpotent element `a ∈ P.plus` of a perfect Tate ring of characteristic
`p`, there exists a pseudouniformiser `ϖ ∈ P.plus` such that `ϖ ^ p ∣ a` in `P.plus`. -/
private theorem exists_isPseudoUniformizer_pow_dvd (a : P.plus)
    (ha : IsTopologicallyNilpotent (a : R)) :
    ∃ ϖ : P.plus, IsPseudoUniformizer (ϖ : R) ∧ ϖ ^ p ∣ a := by
  obtain ⟨ϖ₀, hϖ₀⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  obtain ⟨N, c, hc⟩ := P.plus.exists_dvd_pow_of_isTopologicallyNilpotent
    P.isRingOfIntegralElements.isOpen hϖ₀.isUnit ha
  let ϖ : P.plus := (iterateFrobeniusEquiv P.plus p (N + 1)).symm ϖ₀
  have hpow : ϖ ^ p ^ (N + 1) = ϖ₀ := iterateFrobeniusEquiv_symm_pow (N + 1) ϖ₀
  have hϖ : IsPseudoUniformizer (ϖ : R) := by
    have hpowR : (ϖ : R) ^ p ^ (N + 1) = (ϖ₀ : R) := by
      exact_mod_cast hpow
    refine isPseudoUniformizer_iff.mpr ⟨?_, ?_⟩
    · exact (isUnit_pow_iff (pow_ne_zero _ hp.out.ne_zero)).mp (hpowR.symm ▸ hϖ₀.isUnit)
    · exact IsTopologicallyNilpotent.of_pow (pow_ne_zero _ hp.out.ne_zero)
        (hpowR.symm ▸ hϖ₀.isTopologicallyNilpotent)
  have hle : N ≤ p ^ N := (Nat.lt_pow_self hp.out.one_lt).le
  have hdiv : (ϖ ^ p) ^ p ^ N ∣ a ^ p ^ N := by
    rw [← pow_mul, ← pow_succ', hpow]
    exact ⟨c * a ^ (p ^ N - N), by
      rw [← mul_assoc, ← hc, ← pow_add, Nat.add_sub_of_le hle]⟩
  change iterateFrobeniusEquiv P.plus p N (ϖ ^ p) ∣ iterateFrobeniusEquiv P.plus p N a at hdiv
  exact ⟨ϖ, hϖ, (map_dvd_iff (iterateFrobeniusEquiv P.plus p N)).mp hdiv⟩

/-- For a primitive element `ξ` and `ϖ ∈ P.plus` with `ϖ ^ p ∣ ξ.coeff 0`, we have
`(mk [ϖ]) ^ p ∣ p` in `𝕎 P.plus ⧸ (ξ)`. -/
private theorem mk_teichmuller_pow_dvd_natCast (hξ : ξ.IsPrimitive) {ϖ : P.plus}
    (hξ₀p : ϖ ^ p ∣ ξ.coeff 0) :
    Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p ϖ) ^ p ∣
      (p : WittVector p P.plus ⧸ Ideal.span {ξ}) := by
  obtain ⟨u, hu⟩ := isDistinguished_iff_exists_unit.mp hξ.isDistinguished
  obtain ⟨c, hc⟩ := hξ₀p
  set J := Ideal.span {ξ}
  refine ⟨Ideal.Quotient.mk J (teichmuller p c) * (-Ideal.Quotient.mk J ↑u⁻¹), ?_⟩
  have hu' : Ideal.Quotient.mk J ↑u * Ideal.Quotient.mk J ↑u⁻¹ = 1 := by
    rw [← map_mul, u.mul_inv, map_one]
  have hξ' : Ideal.Quotient.mk J (teichmuller p (ξ.coeff 0)) +
      (p : WittVector p P.plus ⧸ J) * Ideal.Quotient.mk J ↑u = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk J), ← map_mul, ← map_add, ← hu,
      Ideal.Quotient.mk_singleton_self]
  have hteich : Ideal.Quotient.mk J (teichmuller p ϖ) ^ p *
      Ideal.Quotient.mk J (teichmuller p c) =
      Ideal.Quotient.mk J (teichmuller p (ξ.coeff 0)) := by
    rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, ← hc]
  rw [← mul_assoc, hteich]
  linear_combination -(p : WittVector p P.plus ⧸ J) * hu' + Ideal.Quotient.mk J ↑u⁻¹ * hξ'

/-- Relative Frobenius `A₀ ⧸ (π) → A₀ ⧸ (π ^ p)` is bijective on `A₀ = 𝕎 R⁺ ⧸ (ξ)` for any
`ϖ ∈ P.plus` with `ϖ ^ p ∣ ξ.coeff 0`. -/
private theorem bijective_frobeniusModPow_quotient (hξ : ξ.IsPrimitive) {ϖ : P.plus}
    (hξ₀p : ϖ ^ p ∣ ξ.coeff 0) :
    Function.Bijective (frobeniusModPow p (mk_teichmuller_pow_dvd_natCast hξ hξ₀p)) := by
  set J := Ideal.span {ξ}
  set π : WittVector p P.plus ⧸ J := Ideal.Quotient.mk J (teichmuller p ϖ)
  have hξ₀ : ϖ ∣ ξ.coeff 0 := (dvd_pow_self ϖ hp.out.ne_zero).trans hξ₀p
  have hπp : Ideal.Quotient.mk J (teichmuller p (ϖ ^ p)) = π ^ p := by
    rw [map_pow, map_pow]
  let e1 := hξ.isDistinguished.quotientTeichmullerEquiv hξ₀
  let ep := hξ.isDistinguished.quotientTeichmullerEquiv hξ₀p
  constructor
  · rw [frobeniusModPow_injective_iff]
    intro x hx
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : Ideal.Quotient.mk (span {Ideal.Quotient.mk J (teichmuller p (ϖ ^ p))})
        (Ideal.Quotient.mk J w ^ p) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton, hπp]
      exact hx
    have hcoeff : ϖ ^ p ∣ w.coeff 0 ^ p := by
      have h0 := congrArg ep hx'
      rw [map_zero ep, map_pow (Ideal.Quotient.mk _), map_pow ep,
        IsDistinguished.quotientTeichmullerEquiv_mk_mk, ← map_pow] at h0
      exact mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    have hcoeff1 : ϖ ∣ w.coeff 0 := by
      change frobeniusEquiv P.plus p ϖ ∣ frobeniusEquiv P.plus p (w.coeff 0) at hcoeff
      exact (map_dvd_iff (frobeniusEquiv P.plus p)).mp hcoeff
    have h1 : e1 (Ideal.Quotient.mk (span {π}) (Ideal.Quotient.mk J w)) = 0 := by
      rw [IsDistinguished.quotientTeichmullerEquiv_mk_mk, Ideal.Quotient.eq_zero_iff_mem,
        mem_span_singleton]
      exact hcoeff1
    exact mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (e1.injective (h1.trans
      (map_zero e1).symm)))
  · rw [frobeniusModPow_surjective_iff]
    intro x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    let a : P.plus := (frobeniusEquiv P.plus p).symm (w.coeff 0)
    refine ⟨Ideal.Quotient.mk J (teichmuller p a), ?_⟩
    rw [← hπp, ← mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    apply ep.injective
    rw [map_zero ep, map_sub (Ideal.Quotient.mk _), map_sub ep, map_pow (Ideal.Quotient.mk _),
      map_pow ep, IsDistinguished.quotientTeichmullerEquiv_mk_mk,
      IsDistinguished.quotientTeichmullerEquiv_mk_mk, teichmuller_coeff_zero, ← map_pow,
      frobeniusEquiv_symm_pow_p, sub_self]

/-- **The sharp-membership criterion**: for a primitive element `ξ`, `sharp x ∈ A⁺` if and
only if `x ∈ R⁺`. -/
theorem sharp_mem_untiltPlus_iff (hξ : ξ.IsPrimitive) {x : R} :
    sharp p P (Ideal.span {ξ}) x ∈ untiltPlus p P (Ideal.span {ξ}) ↔ x ∈ P.plus := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ by
    change sharp p P (Ideal.span {ξ}) ((⟨x, hx⟩ : P.plus) : R) ∈ _
    exact sharp_mem_untiltPlus _⟩
  obtain ⟨ϖ, hϖ, hξ₀p⟩ := exists_isPseudoUniformizer_pow_dvd (ξ.coeff 0)
    (hξ.isTopologicallyNilpotent_coeff_zero.map (φ := P.plus.subtype) continuous_subtypeVal)
  have hξ₀ : ϖ ∣ ξ.coeff 0 := (dvd_pow_self ϖ hp.out.ne_zero).trans hξ₀p
  set J := Ideal.span {ξ}
  obtain ⟨m, hm⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent
    hϖ.isTopologicallyNilpotent P.isRingOfIntegralElements.isOpen x
  suffices ∀ (k : ℕ) (y : R), sharp p P J y ∈ untiltPlus p P J → y * (ϖ : R) ^ k ∈ P.plus →
      y ∈ P.plus from this m x hx hm
  intro k
  induction k with
  | zero => intro y _ hy; simpa using hy
  | succ k ih =>
    intro y hy hyk
    let a : P.plus := ⟨y * (ϖ : R) ^ (k + 1), hyk⟩
    obtain ⟨b, hb⟩ := mem_untiltPlus.mp hy
    have heqA : algebraMap (WittVector p P.plus ⧸ J) (untilt p P J)
        (Ideal.Quotient.mk J (teichmuller p a)) =
        algebraMap (WittVector p P.plus ⧸ J) (untilt p P J)
          (b * Ideal.Quotient.mk J (teichmuller p ϖ) ^ (k + 1)) := by
      have ha' : algebraMap (WittVector p P.plus ⧸ J) (untilt p P J)
          (Ideal.Quotient.mk J (teichmuller p a)) = sharp p P J (a : R) :=
        (sharp_apply a).symm
      have hϖ' : algebraMap (WittVector p P.plus ⧸ J) (untilt p P J)
          (Ideal.Quotient.mk J (teichmuller p ϖ)) = sharp p P J (ϖ : R) :=
        (sharp_apply ϖ).symm
      rw [map_mul, map_pow, hb, ha', hϖ']
      change sharp p P J (y * (ϖ : R) ^ (k + 1)) = _
      rw [map_mul, map_pow]
    have heqQ : Ideal.Quotient.mk J (teichmuller p a) =
        Ideal.Quotient.mk J (teichmuller p ϖ) *
          (b * Ideal.Quotient.mk J (teichmuller p ϖ) ^ k) := by
      have h1 := algebraMap_injective hξ heqA
      rw [h1, pow_succ]
      ring
    have h0 : hξ.isDistinguished.quotientTeichmullerEquiv hξ₀
        (Ideal.Quotient.mk (span {Ideal.Quotient.mk J (teichmuller p ϖ)})
          (Ideal.Quotient.mk J (teichmuller p a))) = 0 := by
      have hmk : Ideal.Quotient.mk (span {Ideal.Quotient.mk J (teichmuller p ϖ)})
          (Ideal.Quotient.mk J (teichmuller p a)) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton]
        exact ⟨b * Ideal.Quotient.mk J (teichmuller p ϖ) ^ k, heqQ⟩
      rw [hmk, map_zero]
    rw [IsDistinguished.quotientTeichmullerEquiv_mk_mk, teichmuller_coeff_zero,
      Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton] at h0
    obtain ⟨c, hc⟩ := h0
    have hyc : y * (ϖ : R) ^ k = (c : R) := by
      apply hϖ.isUnit.mul_right_cancel
      have hca : (a : R) = (ϖ : R) * (c : R) := congrArg Subtype.val hc
      change y * (ϖ : R) ^ (k + 1) = (ϖ : R) * (c : R) at hca
      rw [pow_succ] at hca
      rw [mul_assoc, hca, mul_comm]
    exact ih y hy (hyc.symm ▸ c.property)

/-- The untilt along a primitive element is uniform. -/
theorem isUniform (hξ : ξ.IsPrimitive) : IsUniform (untilt p P (Ideal.span {ξ})) := by
  obtain ⟨ϖ, hϖ, hξ₀p⟩ := exists_isPseudoUniformizer_pow_dvd (ξ.coeff 0)
    (hξ.isTopologicallyNilpotent_coeff_zero.map (φ := P.plus.subtype) continuous_subtypeVal)
  set J := Ideal.span {ξ}
  have := isLocalizationAway (J := J) hϖ
  have hrad : ξ.coeff 0 ∈ (span {ϖ}).radical :=
    ⟨1, by rw [pow_one, mem_span_singleton]; exact (dvd_pow_self ϖ hp.out.ne_zero).trans hξ₀p⟩
  have hreg : Ideal.Quotient.mk J (teichmuller p ϖ) ∈ (WittVector p P.plus ⧸ J)⁰ :=
    hξ.isDistinguished.mk_teichmuller_mem_nonZeroDivisors hrad
      (comap_nonZeroDivisors_le_of_injective (f := P.plus.subtype) Subtype.val_injective
        hϖ.isUnit.mem_nonZeroDivisors)
  have hroot : ∀ a : WittVector p P.plus ⧸ J,
      Ideal.Quotient.mk J (teichmuller p ϖ) ^ p ∣ a ^ p →
        Ideal.Quotient.mk J (teichmuller p ϖ) ∣ a :=
    (frobeniusModPow_injective_iff (mk_teichmuller_pow_dvd_natCast hξ hξ₀p)).mp
      (bijective_frobeniusModPow_quotient hξ hξ₀p).1
  exact isUniform_of_hasBasis hp.out.one_lt (hasBasis_nhds_zero hϖ) hreg hroot

end Algebraic

/-! ### Perfectoidness, tilt identification, and the untilt Huber pair -/

section Perfectoid

variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R]
  [CompleteSpace R] [T2Space R] [CharP R p] [PerfectRing R p] {P : Pair R}
  {ξ : WittVector p P.plus}

/-- **`𝕎 R⁺ ⧸ (ξ)` is an integral perfectoid ring** for a primitive element `ξ`. -/
theorem isIntegralPerfectoid_quotient (hξ : ξ.IsPrimitive) :
    IsIntegralPerfectoid p (WittVector p P.plus ⧸ Ideal.span {ξ}) := by
  obtain ⟨ϖ, hϖ, hξ₀p⟩ := exists_isPseudoUniformizer_pow_dvd (ξ.coeff 0)
    (hξ.isTopologicallyNilpotent_coeff_zero.map (φ := P.plus.subtype) continuous_subtypeVal)
  set J := Ideal.span {ξ}
  have hrad : ξ.coeff 0 ∈ (span {ϖ}).radical :=
    ⟨1, by rw [pow_one, mem_span_singleton]; exact (dvd_pow_self ϖ hp.out.ne_zero).trans hξ₀p⟩
  have := IsUniform.of_perfectRing (R := R) p
  have := P.isRingOfIntegralElements.isAdicComplete_span_singleton ϖ hϖ
  have := hξ.isDistinguished.isAdicComplete_quotient hrad
  have hreg : Ideal.Quotient.mk J (teichmuller p ϖ) ∈ (WittVector p P.plus ⧸ J)⁰ :=
    hξ.isDistinguished.mk_teichmuller_mem_nonZeroDivisors hrad
      (comap_nonZeroDivisors_le_of_injective (f := P.plus.subtype) Subtype.val_injective
        hϖ.isUnit.mem_nonZeroDivisors)
  exact IsIntegralPerfectoid.of_bijective_frobeniusModPow hreg
    (bijective_frobeniusModPow_quotient hξ hξ₀p)

/-- **`A⁺` is an integral perfectoid ring** for the untilt along a primitive element `ξ`. -/
theorem isIntegralPerfectoid_untiltPlus (hξ : ξ.IsPrimitive) :
    IsIntegralPerfectoid p (untiltPlus p P (Ideal.span {ξ})) := by
  obtain ⟨ϖ, hϖ, hξ₀p⟩ := exists_isPseudoUniformizer_pow_dvd (ξ.coeff 0)
    (hξ.isTopologicallyNilpotent_coeff_zero.map (φ := P.plus.subtype) continuous_subtypeVal)
  set J := Ideal.span {ξ}
  set e := quotientEquivUntiltPlus hξ
  set π₀ : WittVector p P.plus ⧸ J := Ideal.Quotient.mk J (teichmuller p ϖ)
  set π : untiltPlus p P J := e π₀
  have hrad : ξ.coeff 0 ∈ (span {ϖ}).radical :=
    ⟨1, by rw [pow_one, mem_span_singleton]; exact (dvd_pow_self ϖ hp.out.ne_zero).trans hξ₀p⟩
  have := IsUniform.of_perfectRing (R := R) p
  have := P.isRingOfIntegralElements.isAdicComplete_span_singleton ϖ hϖ
  have := hξ.isDistinguished.isAdicComplete_quotient hrad
  have hmap : (span {π₀}).map e = span {π} := by
    rw [Ideal.map_span, Set.image_singleton]
  have : IsAdicComplete (span {π}) (untiltPlus p P J) := by
    rw [← hmap]
    exact (IsAdicComplete.congr_ringEquiv (span {π₀}) e).mpr inferInstance
  have hreg₀ : π₀ ∈ (WittVector p P.plus ⧸ J)⁰ :=
    hξ.isDistinguished.mk_teichmuller_mem_nonZeroDivisors hrad
      (comap_nonZeroDivisors_le_of_injective (f := P.plus.subtype) Subtype.val_injective
        hϖ.isUnit.mem_nonZeroDivisors)
  have hreg : π ∈ (untiltPlus p P J)⁰ := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    apply e.symm.injective
    rw [map_zero]
    exact (mem_nonZeroDivisors_iff_right.mp hreg₀) (e.symm x) (by
      have := congrArg e.symm hx
      simpa [π] using this)
  have hdvd₀ := mk_teichmuller_pow_dvd_natCast hξ hξ₀p
  have hdvd : π ^ p ∣ (p : untiltPlus p P J) := by
    obtain ⟨c, hc⟩ := hdvd₀
    exact ⟨e c, by simpa [π] using congrArg e hc⟩
  have hbij₀ := bijective_frobeniusModPow_quotient hξ hξ₀p
  have hbij : Function.Bijective (frobeniusModPow p hdvd) := by
    refine ⟨(frobeniusModPow_injective_iff hdvd).mpr fun x hx ↦ ?_,
      (frobeniusModPow_surjective_iff hdvd).mpr fun x ↦ ?_⟩
    · obtain ⟨c, hc⟩ := hx
      have h0 : π₀ ^ p ∣ (e.symm x) ^ p :=
        ⟨e.symm c, by simpa [π] using congrArg e.symm hc⟩
      obtain ⟨d, hd⟩ := (frobeniusModPow_injective_iff hdvd₀).mp hbij₀.1 (e.symm x) h0
      exact ⟨e d, by simpa [π] using congrArg e hd⟩
    · obtain ⟨y, c, hc⟩ := (frobeniusModPow_surjective_iff hdvd₀).mp hbij₀.2 (e.symm x)
      exact ⟨e y, e c, by simpa [π] using congrArg e hc⟩
  exact IsIntegralPerfectoid.of_bijective_frobeniusModPow hreg hbij

/-- **The untilt along a primitive element is a perfectoid Tate ring** (Scholze, *Étale cohomology
of diamonds*, Theorem 3.17; Bhatt–Morrow–Scholze, Lemma 3.21). -/
theorem isPerfectoidTateRing (hξ : ξ.IsPrimitive) :
    letI := t2Space hξ
    letI := completeSpace hξ
    IsPerfectoidTateRing p (untilt p P (Ideal.span {ξ})) := by
  obtain ⟨ϖ, hϖ, hξ₀p⟩ := exists_isPseudoUniformizer_pow_dvd (ξ.coeff 0)
    (hξ.isTopologicallyNilpotent_coeff_zero.map (φ := P.plus.subtype) continuous_subtypeVal)
  set J := Ideal.span {ξ}
  have := isLocalizationAway (J := J) hϖ
  have := t2Space hξ
  have := completeSpace hξ
  have := IsUniform.of_perfectRing (R := R) p
  have := P.isRingOfIntegralElements.isAdicComplete_span_singleton ϖ hϖ
  have hrad : ξ.coeff 0 ∈ (span {ϖ}).radical :=
    ⟨1, by rw [pow_one, mem_span_singleton]; exact (dvd_pow_self ϖ hp.out.ne_zero).trans hξ₀p⟩
  have := hξ.isDistinguished.isAdicComplete_quotient hrad
  have hreg : Ideal.Quotient.mk J (teichmuller p ϖ) ∈ (WittVector p P.plus ⧸ J)⁰ :=
    hξ.isDistinguished.mk_teichmuller_mem_nonZeroDivisors hrad
      (comap_nonZeroDivisors_le_of_injective (f := P.plus.subtype) Subtype.val_injective
        hϖ.isUnit.mem_nonZeroDivisors)
  exact isPerfectoidTateRing_of_bijective_frobeniusModPow (hasBasis_nhds_zero hϖ) hreg
    (bijective_frobeniusModPow_quotient hξ hξ₀p)

/-- The `p ^ n`-th root map `(iterateFrobeniusEquiv R p n).symm` is continuous on a perfect
complete Hausdorff Tate ring of characteristic `p`. -/
private theorem continuous_iterateFrobeniusEquiv_symm (n : ℕ) :
    Continuous (iterateFrobeniusEquiv R p n).symm := by
  have h1 : Continuous (frobeniusEquiv R p).symm := by
    rw [continuous_def]
    intro U hU
    have heq : (frobeniusEquiv R p).symm ⁻¹' U = frobenius R p '' U := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      exact ⟨fun h ↦ ⟨(frobeniusEquiv R p).symm x, h, by
        change frobeniusEquiv R p ((frobeniusEquiv R p).symm x) = x
        exact (frobeniusEquiv R p).apply_symm_apply x⟩,
        by rintro ⟨y, hy, rfl⟩; simpa using hy⟩
    rw [heq]
    exact isOpenMap_frobenius p U hU
  induction n with
  | zero =>
    have heq : ⇑(iterateFrobeniusEquiv R p 0).symm = id := funext iterateFrobeniusEquiv_zero_symm
    rw [heq]
    exact continuous_id
  | succ n ih =>
    have heq : ⇑(iterateFrobeniusEquiv R p (n + 1)).symm =
        ⇑(frobeniusEquiv R p).symm ∘ ⇑(iterateFrobeniusEquiv R p n).symm := by
      ext x
      apply (iterateFrobeniusEquiv R p (n + 1)).injective
      rw [(iterateFrobeniusEquiv R p (n + 1)).apply_symm_apply, Function.comp_apply,
        iterateFrobeniusEquiv_def, pow_succ', pow_mul, frobeniusEquiv_symm_pow_p,
        iterateFrobeniusEquiv_symm_pow]
    rw [heq]
    exact h1.comp ih

/-- The canonical map `R → uniformTilt p (untilt p P (Ideal.span {ξ}))`,
`x ↦ (sharp (x ^ (1 / p ^ n)))_n`. -/
private noncomputable def toTiltFun (ξ : WittVector p P.plus) (x : R) :
    uniformTilt p (untilt p P (Ideal.span {ξ})) :=
  uniformTilt.mk (fun n ↦ sharp p P (Ideal.span {ξ}) ((iterateFrobeniusEquiv R p n).symm x))
    fun n ↦ by
      rw [← map_pow]
      congr 1
      apply (iterateFrobeniusEquiv R p n).injective
      rw [iterateFrobeniusEquiv_def, ← pow_mul, ← pow_succ',
        iterateFrobeniusEquiv_symm_pow (n + 1) x, (iterateFrobeniusEquiv R p n).apply_symm_apply]

private theorem coeff_toTiltFun (hξ : ξ.IsPrimitive) (x : R) (n : ℕ) :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n (toTiltFun ξ x) =
      sharp p P (Ideal.span {ξ}) ((iterateFrobeniusEquiv R p n).symm x) := by
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  exact uniformTilt.coeff_mk _ _ n

/-- **The tilt of the untilt is Tate**, via `toTiltFun ϖ` for any pseudouniformiser `ϖ` of `R`. -/
theorem isTateRing_uniformTilt (hξ : ξ.IsPrimitive) :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    IsTateRing (uniformTilt p (untilt p P (Ideal.span {ξ}))) := by
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  refine uniformTilt.isTateRing_of_sharp (ϖ := toTiltFun ξ ϖ) ?_
  rw [coeff_toTiltFun hξ, iterateFrobeniusEquiv_zero_symm]
  exact isPseudoUniformizer_sharp hϖ

/-- `toTiltFun` is a ring homomorphism `R →+* uniformTilt p (untilt p P (Ideal.span {ξ}))`. -/
private noncomputable def toTiltHom (hξ : ξ.IsPrimitive) :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    R →+* uniformTilt p (untilt p P (Ideal.span {ξ})) :=
  letI := t2Space hξ
  letI := completeSpace hξ
  letI := isUniform hξ
  letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  have hmul : ∀ x y : R, toTiltFun ξ (x * y) = toTiltFun ξ x * toTiltFun ξ y := fun x y ↦ by
    apply uniformTilt.ext
    intro n
    rw [map_mul, coeff_toTiltFun hξ, coeff_toTiltFun hξ, coeff_toTiltFun hξ, map_mul, map_mul]
  have hadd_plus : ∀ a b : P.plus, toTiltFun ξ (a + b) = toTiltFun ξ a + toTiltFun ξ b := by
    intro a b
    set J := Ideal.span {ξ}
    set A := untilt p P J
    apply uniformTilt.ext
    intro i
    have hlim := uniformTilt.coeff_add (toTiltFun ξ a) (toTiltFun ξ b) i
    refine (tendsto_nhds_unique hlim ?_).symm
    rw [← tendsto_sub_nhds_zero_iff]
    have hdiff (m : ℕ) :
        (uniformTilt.coeff p A (i + m) (toTiltFun ξ a) +
            uniformTilt.coeff p A (i + m) (toTiltFun ξ b)) ^ p ^ m -
          uniformTilt.coeff p A i (toTiltFun ξ (a + b)) ∈
          ((p : A) ^ (m + 1)) • (untiltPlus p P J : Set A) := by
      let ai : P.plus := (iterateFrobeniusEquiv P.plus p (i + m)).symm a
      let bi : P.plus := (iterateFrobeniusEquiv P.plus p (i + m)).symm b
      have hconst : constantCoeff (teichmuller p ai + teichmuller p bi -
          teichmuller p (ai + bi)) = 0 := by
        rw [map_sub, map_add, constantCoeff_apply, constantCoeff_apply, constantCoeff_apply,
          teichmuller_coeff_zero, teichmuller_coeff_zero, teichmuller_coeff_zero, sub_self]
      have hmemp : teichmuller p ai + teichmuller p bi - teichmuller p (ai + bi) ∈
          span {(p : WittVector p P.plus)} := by
        rw [← WittVector.ker_constantCoeff]
        exact hconst
      have hsmod : teichmuller p ai + teichmuller p bi ≡ teichmuller p (ai + bi)
          [SMOD span {(p : WittVector p P.plus)}] :=
        SModEq.sub_mem.mpr hmemp
      have hpow_smod := hsmod.pow_pow_add_one
        (mem_span_singleton_self (p : WittVector p P.plus)) m
      rw [SModEq.sub_mem, span_singleton_pow, mem_span_singleton] at hpow_smod
      obtain ⟨d, hd⟩ := hpow_smod
      have hsum_pow : (ai + bi) ^ p ^ m = (iterateFrobeniusEquiv P.plus p i).symm (a + b) := by
        rw [add_pow_char_pow]
        apply (iterateFrobeniusEquiv P.plus p i).injective
        rw [(iterateFrobeniusEquiv P.plus p i).apply_symm_apply, map_add,
          iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def, ← pow_mul, ← pow_mul, ← pow_add,
          add_comm m i, iterateFrobeniusEquiv_symm_pow, iterateFrobeniusEquiv_symm_pow]
      refine ⟨algebraMap (WittVector p P.plus ⧸ J) A (Ideal.Quotient.mk J d),
        mem_untiltPlus.mpr ⟨_, rfl⟩, ?_⟩
      change (p : A) ^ (m + 1) *
          algebraMap (WittVector p P.plus ⧸ J) A (Ideal.Quotient.mk J d) = _
      rw [coeff_toTiltFun hξ, coeff_toTiltFun hξ, coeff_toTiltFun hξ,
        ← coe_iterateFrobeniusEquiv_plus_symm a (i + m),
        ← coe_iterateFrobeniusEquiv_plus_symm b (i + m), ← Subring.coe_add,
        ← coe_iterateFrobeniusEquiv_plus_symm (a + b) i,
        sharp_apply ai, sharp_apply bi, sharp_apply, ← map_add, ← map_add, ← map_pow, ← map_pow,
        ← hsum_pow, map_pow (teichmuller p) (ai + bi), ← map_sub, ← map_sub, hd, map_mul,
        map_pow, map_natCast, map_mul, map_pow, map_natCast]
    rw [Filter.tendsto_def]
    intro U hU
    obtain ⟨V, hV, hVU⟩ := isBounded_iff.mp isBounded_untiltPlus U hU
    have hev : ∀ᶠ m in atTop, (p : A) ^ (m + 1) ∈ V :=
      ((isTopologicallyNilpotent_natCast hξ).comp (tendsto_add_atTop_nat 1)).eventually_mem hV
    exact hev.mono fun m hm ↦ by
      obtain ⟨b, hb, hbm⟩ := hdiff m
      dsimp only
      rw [← hbm]
      exact hVU (Set.mul_mem_mul hm hb)
  { toFun := toTiltFun ξ
    map_one' := by
      apply uniformTilt.ext
      intro n
      rw [map_one, coeff_toTiltFun hξ, map_one, map_one]
    map_mul' := hmul
    map_zero' := by
      apply uniformTilt.ext
      intro n
      rw [uniformTilt.coeff_zero, coeff_toTiltFun hξ, map_zero, map_zero]
    map_add' := fun x y ↦ by
      obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
      obtain ⟨kx, hkx⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent
        hϖ.isTopologicallyNilpotent P.isRingOfIntegralElements.isOpen x
      obtain ⟨ky, hky⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent
        hϖ.isTopologicallyNilpotent P.isRingOfIntegralElements.isOpen y
      set k := max kx ky
      have hxk : x * (ϖ : R) ^ k ∈ P.plus := by
        have h1 : x * (ϖ : R) ^ k = (x * (ϖ : R) ^ kx) * (ϖ : R) ^ (k - kx) := by
          rw [mul_assoc, ← pow_add, Nat.add_sub_of_le (le_max_left _ _)]
        rw [h1]
        exact P.plus.mul_mem hkx (P.plus.pow_mem ϖ.property _)
      have hyk : y * (ϖ : R) ^ k ∈ P.plus := by
        have h1 : y * (ϖ : R) ^ k = (y * (ϖ : R) ^ ky) * (ϖ : R) ^ (k - ky) := by
          rw [mul_assoc, ← pow_add, Nat.add_sub_of_le (le_max_right _ _)]
        rw [h1]
        exact P.plus.mul_mem hky (P.plus.pow_mem ϖ.property _)
      have hu : IsUnit (toTiltFun ξ ((ϖ : R) ^ k)) := by
        rw [uniformTilt.isUnit_iff_coeff_zero, coeff_toTiltFun hξ, iterateFrobeniusEquiv_zero_symm,
          map_pow]
        exact (isPseudoUniformizer_sharp hϖ).isUnit.pow k
      refine hu.mul_right_cancel ?_
      rw [← hmul, add_mul, add_mul, ← hmul, ← hmul]
      exact hadd_plus ⟨x * (ϖ : R) ^ k, hxk⟩ ⟨y * (ϖ : R) ^ k, hyk⟩ }

private theorem coeff_toTiltHom (hξ : ξ.IsPrimitive) (x : R) (n : ℕ) :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n (toTiltHom hξ x) =
      sharp p P (Ideal.span {ξ}) ((iterateFrobeniusEquiv R p n).symm x) :=
  coeff_toTiltFun hξ x n

/-- `toTiltHom` is injective. -/
private theorem toTiltHom_injective (hξ : ξ.IsPrimitive) :
    Function.Injective (toTiltHom hξ) := by
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx0 : sharp p P (Ideal.span {ξ}) x = 0 := by
    have h0 := congrArg (uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) 0) hx
    rw [uniformTilt.coeff_zero, coeff_toTiltHom hξ, iterateFrobeniusEquiv_zero_symm] at h0
    exact h0
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  have := IsUniform.of_perfectRing (R := R) p
  let D : PairOfDefinition R := PairOfDefinition.ofIsPseudoUniformizer P.plus
    P.isRingOfIntegralElements.isOpen P.isRingOfIntegralElements.isBounded hϖ ϖ.property
  have hmem (n : ℕ) : x ∈ ((ϖ : R) ^ n) • (D.ringOfDefinition : Set R) := by
    let u := (hϖ.isUnit.pow n).unit
    have hsharp : sharp p P (Ideal.span {ξ}) (↑u⁻¹ * x) ∈ untiltPlus p P (Ideal.span {ξ}) := by
      rw [map_mul, hx0, mul_zero]
      exact zero_mem _
    have hplus : ↑u⁻¹ * x ∈ P.plus := (sharp_mem_untiltPlus_iff hξ).mp hsharp
    refine ⟨↑u⁻¹ * x, ?_, ?_⟩
    · rw [PairOfDefinition.ofIsPseudoUniformizer_ringOfDefinition]
      exact hplus
    · change (u : R) * (↑u⁻¹ * x) = x
      rw [← mul_assoc, Units.mul_inv, one_mul]
  have htend : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 (0 : R)) :=
    (hϖ.hasBasis_nhds_zero D).tendsto_right_iff.mpr fun n _ ↦ Eventually.of_forall fun _ ↦ hmem n
  exact tendsto_nhds_unique tendsto_const_nhds htend

/-- For a primitive element `ξ` and a pseudouniformiser `ϖ ∈ R⁺` with `ϖ ^ p ∣ ξ₀`, there is a
surjective ring homomorphism `g : R⁺ →+* PreTilt (𝕎 R⁺ ⧸ (ξ)) p` lifting Teichmüller
representatives (`(g a).untilt = mk [a]`). -/
private theorem exists_surjective_toPreTilt_quotient (hξ : ξ.IsPrimitive) {ϖ : P.plus}
    (hϖ : IsPseudoUniformizer (ϖ : R)) (hξ₀p : ϖ ^ p ∣ ξ.coeff 0)
    [IsAdicComplete (span {(p : WittVector p P.plus ⧸ Ideal.span {ξ})})
      (WittVector p P.plus ⧸ Ideal.span {ξ})]
    [Fact ¬IsUnit (p : WittVector p P.plus ⧸ Ideal.span {ξ})] :
    ∃ g : P.plus →+* PreTilt (WittVector p P.plus ⧸ Ideal.span {ξ}) p,
      Function.Surjective g ∧
      ∀ a : P.plus, (g a).untilt = Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p a) := by
  set J := Ideal.span {ξ}
  set A₀ := WittVector p P.plus ⧸ J
  have hξ₀ : ϖ ∣ ξ.coeff 0 := (dvd_pow_self ϖ hp.out.ne_zero).trans hξ₀p
  set π : A₀ := Ideal.Quotient.mk J (teichmuller p ϖ)
  have hrad : ξ.coeff 0 ∈ (span {ϖ}).radical := ⟨1, by rwa [pow_one, mem_span_singleton]⟩
  have := IsUniform.of_perfectRing (R := R) p
  have := P.isRingOfIntegralElements.isAdicComplete_span_singleton ϖ hϖ
  have := hξ.isDistinguished.isAdicComplete_quotient hrad
  let mkP : A₀ →+* ModP A₀ p := Ideal.Quotient.mk (span {(p : A₀)})
  have hmkP_teich_add (a b : P.plus) :
      mkP (Ideal.Quotient.mk J (teichmuller p (a + b))) =
        mkP (Ideal.Quotient.mk J (teichmuller p a)) +
          mkP (Ideal.Quotient.mk J (teichmuller p b)) := by
    have hconst : constantCoeff (teichmuller p a + teichmuller p b -
        teichmuller p (a + b)) = 0 := by
      rw [map_sub, map_add, constantCoeff_apply, constantCoeff_apply, constantCoeff_apply,
        teichmuller_coeff_zero, teichmuller_coeff_zero, teichmuller_coeff_zero, sub_self]
    have hmemp : teichmuller p a + teichmuller p b - teichmuller p (a + b) ∈
        span {(p : WittVector p P.plus)} := by
      rw [← WittVector.ker_constantCoeff]
      exact hconst
    obtain ⟨d, hd⟩ := mem_span_singleton.mp hmemp
    symm
    rw [← sub_eq_zero, ← map_add mkP, ← map_add (Ideal.Quotient.mk J), ← map_sub mkP,
      ← map_sub (Ideal.Quotient.mk J), hd, map_mul, map_natCast, map_mul]
    have hp0 : mkP (p : A₀) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (mem_span_singleton_self _)
    rw [hp0, zero_mul]
  let gPerf (a : P.plus) : Perfection (ModP A₀ p) p :=
    ⟨fun n ↦ mkP (Ideal.Quotient.mk J
        (teichmuller p ((iterateFrobeniusEquiv P.plus p n).symm a))),
      fun n ↦ by
        rw [← map_pow, ← map_pow, ← map_pow]
        congr 3
        apply (iterateFrobeniusEquiv P.plus p n).injective
        rw [iterateFrobeniusEquiv_def, ← pow_mul, ← pow_succ',
          iterateFrobeniusEquiv_symm_pow (n + 1) a,
          (iterateFrobeniusEquiv P.plus p n).apply_symm_apply]⟩
  let gFun (a : P.plus) : PreTilt A₀ p := PreTilt.equivPerfection.symm (gPerf a)
  have hcoeff_gFun (a : P.plus) (n : ℕ) :
      PreTilt.coeff n (gFun a) =
        mkP (Ideal.Quotient.mk J (teichmuller p ((iterateFrobeniusEquiv P.plus p n).symm a))) := by
    dsimp only [gFun]
    rw [PreTilt.coeff_equivPerfection_symm]
    rfl
  let g : P.plus →+* PreTilt A₀ p :=
    { toFun := gFun
      map_one' := PreTilt.ext fun n ↦ by simp [hcoeff_gFun]
      map_mul' := fun a b ↦ PreTilt.ext fun n ↦ by simp [hcoeff_gFun, map_mul]
      map_zero' := PreTilt.ext fun n ↦ by simp [hcoeff_gFun]
      map_add' := fun a b ↦ PreTilt.ext fun n ↦ by
        rw [map_add, hcoeff_gFun, hcoeff_gFun, hcoeff_gFun, map_add, hmkP_teich_add] }
  have hg_untilt (a : P.plus) : (g a).untilt = Ideal.Quotient.mk J (teichmuller p a) := by
    dsimp only [g, gFun, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [PreTilt.untilt_equivPerfection_symm]
    refine Perfection.teichmuller₀_spec fun n ↦
      ⟨Ideal.Quotient.mk J (teichmuller p ((iterateFrobeniusEquiv P.plus p n).symm a)), rfl, ?_⟩
    rw [← map_pow, ← map_pow]
    congr 2
    exact congrArg (teichmuller p) (iterateFrobeniusEquiv_symm_pow n a)
  have hg_varpi : (g ϖ).untilt = π := hg_untilt ϖ
  have hhaus : IsHausdorff ((span {ϖ}).map g) (PreTilt A₀ p) := by
    rw [Ideal.map_span, Set.image_singleton]
    refine ⟨fun z hz ↦ PreTilt.ext fun n ↦ ?_⟩
    rw [map_zero, PreTilt.coeff_eq_mk_untilt_iterate]
    suffices h0 : (((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) z).untilt = 0 by
      rw [h0, map_zero]
    refine IsHausdorff.haus' (I := span {π}) _ fun k ↦ ?_
    rw [Ideal.smul_eq_mul, Ideal.mul_top, SModEq.zero, span_singleton_pow, mem_span_singleton]
    have hzk : g ϖ ^ (k * p ^ n) ∣ z := by
      have hmem := hz (k * p ^ n)
      rw [Ideal.smul_eq_mul, Ideal.mul_top, SModEq.zero, span_singleton_pow,
        mem_span_singleton] at hmem
      exact hmem
    have hpow_dvd :
        (g ϖ ^ k) ^ p ^ n ∣ (((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) z) ^ p ^ n := by
      rw [← pow_mul, iterate_frobeniusEquiv_symm_pow_p_pow]
      exact hzk
    have hdvd_n : g ϖ ^ k ∣ ((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) z := by
      change iterateFrobeniusEquiv (PreTilt A₀ p) p n (g ϖ ^ k) ∣
        iterateFrobeniusEquiv (PreTilt A₀ p) p n (((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) z)
        at hpow_dvd
      exact (map_dvd_iff (iterateFrobeniusEquiv (PreTilt A₀ p) p n)).mp hpow_dvd
    obtain ⟨c, hc⟩ := hdvd_n
    refine ⟨c.untilt, ?_⟩
    rw [← hg_varpi, ← map_pow, ← map_mul, ← hc]
  refine ⟨g, ?_, hg_untilt⟩
  refine surjective_of_mk_map_comp_surjective (I := span {ϖ}) (f := g) fun qz ↦ ?_
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective qz
  have : IsIntegralPerfectoid p A₀ := isIntegralPerfectoid_quotient hξ
  have hdvd' : (g ϖ).untilt ∣ (p : A₀) :=
    (dvd_pow_self _ hp.out.ne_zero).trans (by
      rw [hg_varpi]
      exact mk_teichmuller_pow_dvd_natCast hξ hξ₀p)
  let eQ := PreTilt.quotientSpanEquiv (t := g ϖ) hdvd'
  let eR := hξ.isDistinguished.quotientTeichmullerEquiv hξ₀
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (eR (Ideal.Quotient.mk (span {π}) z.untilt))
  refine ⟨a, ?_⟩
  rw [RingHom.comp_apply, Ideal.map_span, Set.image_singleton]
  apply eQ.injective
  dsimp only [eQ]
  rw [PreTilt.quotientSpanEquiv_mk, PreTilt.quotientSpanEquiv_mk]
  have heq_pi : Ideal.Quotient.mk (span {π}) (g a).untilt =
      Ideal.Quotient.mk (span {π}) z.untilt := by
    apply eR.injective
    rw [hg_untilt, IsDistinguished.quotientTeichmullerEquiv_mk_mk, teichmuller_coeff_zero, ha]
  have hdiff_pi : π ∣ (g a).untilt - z.untilt :=
    mem_span_singleton.mp (Ideal.Quotient.eq.mp heq_pi)
  exact Ideal.Quotient.eq.mpr (mem_span_singleton.mpr (by rwa [hg_varpi]))

/-- `toTiltHom` is surjective. -/
private theorem toTiltHom_surjective (hξ : ξ.IsPrimitive) :
    Function.Surjective (toTiltHom hξ) := by
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  set J := Ideal.span {ξ}
  set A := untilt p P J
  set A₀ := WittVector p P.plus ⧸ J
  rcases subsingleton_or_nontrivial A with hA | hA
  · intro y
    refine ⟨0, uniformTilt.ext fun n ↦ Subsingleton.elim _ _⟩
  obtain ⟨ϖ, hϖ, hξ₀p⟩ := exists_isPseudoUniformizer_pow_dvd (ξ.coeff 0)
    (hξ.isTopologicallyNilpotent_coeff_zero.map (φ := P.plus.subtype) continuous_subtypeVal)
  set π : A₀ := Ideal.Quotient.mk J (teichmuller p ϖ)
  have hdvd : π ^ p ∣ (p : A₀) := mk_teichmuller_pow_dvd_natCast hξ hξ₀p
  have hbij := bijective_frobeniusModPow_quotient hξ hξ₀p
  have hrad : ξ.coeff 0 ∈ (span {ϖ}).radical := ⟨1, by
    rw [pow_one, mem_span_singleton]
    exact (dvd_pow_self ϖ hp.out.ne_zero).trans hξ₀p⟩
  have := IsUniform.of_perfectRing (R := R) p
  have := P.isRingOfIntegralElements.isAdicComplete_span_singleton ϖ hϖ
  have := hξ.isDistinguished.isAdicComplete_quotient hrad
  have hπp : π ∣ (p : A₀) := (dvd_pow_self π hp.out.ne_zero).trans hdvd
  have : IsAdicComplete (span {(p : A₀)}) A₀ := .span_singleton_of_dvd hπp
  have : Nontrivial A₀ := by
    by_contra hnot
    rw [not_nontrivial_iff_subsingleton] at hnot
    exact not_subsingleton A (algebraMap A₀ A).codomain_trivial
  have : Fact ¬IsUnit (p : A₀) :=
    ⟨IsAdicComplete.not_isUnit_of_mem (I := span {π}) (mem_span_singleton.mpr hπp)⟩
  have hreg : π ∈ A₀⁰ :=
    hξ.isDistinguished.mk_teichmuller_mem_nonZeroDivisors hrad
      (comap_nonZeroDivisors_le_of_injective (f := P.plus.subtype) Subtype.val_injective
        hϖ.isUnit.mem_nonZeroDivisors)
  obtain ⟨g, hg_surj, hg_untilt⟩ := exists_surjective_toPreTilt_quotient hξ hϖ hξ₀p
  have hg_iter (a : P.plus) (n : ℕ) :
      ((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) (g a) =
        g ((iterateFrobeniusEquiv P.plus p n).symm a) := by
    apply (iterateFrobeniusEquiv (PreTilt A₀ p) p n).injective
    rw [iterateFrobeniusEquiv_def, iterate_frobeniusEquiv_symm_pow_p_pow, iterateFrobeniusEquiv_def,
      ← map_pow, iterateFrobeniusEquiv_symm_pow]
  -- Surjectivity on elements whose coordinates all lie in `untiltPlus`.
  have hsurj_plus : ∀ y : uniformTilt p A, (∀ n, uniformTilt.coeff p A n y ∈ untiltPlus p P J) →
      ∃ a : P.plus, toTiltHom hξ a = y := by
    intro y hy
    let u : ℕ → A₀ := fun n ↦ (quotientEquivUntiltPlus hξ).symm ⟨uniformTilt.coeff p A n y, hy n⟩
    have hu_map (n : ℕ) : algebraMap A₀ A (u n) = uniformTilt.coeff p A n y := by
      rw [← coe_quotientEquivUntiltPlus_apply hξ (u n),
        (quotientEquivUntiltPlus hξ).apply_symm_apply]
    have hu_pow (n : ℕ) : u (n + 1) ^ p = u n := by
      apply algebraMap_injective hξ
      rw [map_pow, hu_map, hu_map, uniformTilt.coeff_pow_p]
    let zPerf : Perfection (ModP A₀ p) p :=
      ⟨fun n ↦ Ideal.Quotient.mk (span {(p : A₀)}) (u n), fun n ↦ by
        rw [← map_pow, hu_pow]⟩
    let z : PreTilt A₀ p := PreTilt.equivPerfection.symm zPerf
    obtain ⟨a, ha⟩ := hg_surj z
    refine ⟨a, uniformTilt.ext fun n ↦ ?_⟩
    have hzn_untilt : (((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) z).untilt = u n := by
      rw [← PreTilt.teichmuller₀_equivPerfection]
      refine Perfection.teichmuller₀_spec fun m ↦ ⟨u (n + m), ?_, ?_⟩
      · have h1 : PreTilt.coeff m (((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) z) =
            PreTilt.coeff (n + m) z := by
          rw [PreTilt.coeff_iterate_frobeniusEquiv_symm, add_comm]
        rw [PreTilt.coeff_equivPerfection, h1]
        dsimp only [z]
        rw [PreTilt.coeff_equivPerfection_symm]
        rfl
      · have hpow : ∀ m, u (n + m) ^ p ^ m = u n := fun m ↦ by
          induction m with
          | zero => simp
          | succ m ihm =>
            rw [pow_succ', pow_mul, ← add_assoc, hu_pow, ihm]
        rw [hpow m]
        exact SModEq.rfl
    have hu_eq : Ideal.Quotient.mk J (teichmuller p ((iterateFrobeniusEquiv P.plus p n).symm a)) =
        u n := by
      rw [← hg_untilt, ← hg_iter, ha, hzn_untilt]
    rw [coeff_toTiltHom hξ, ← coe_iterateFrobeniusEquiv_plus_symm, sharp_apply, hu_eq, hu_map]
  -- Arbitrary `y : uniformTilt p A`: clear denominators using `ϖ ^ (k + 1)` and `Away.lean`.
  intro y
  have := isLocalizationAway (J := J) hϖ
  have hroot : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a := (frobeniusModPow_injective_iff hdvd).mp hbij.1
  obtain ⟨k, hk⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent
    (isPseudoUniformizer_sharp (J := J) hϖ).isTopologicallyNilpotent isOpen_untiltPlus
    (uniformTilt.coeff p A 0 y)
  have hz_pb (n : ℕ) :
      IsPowerBounded (uniformTilt.coeff p A n (toTiltHom hξ ((ϖ : R) ^ k) * y)) := by
    refine IsPowerBounded.of_pow (pow_ne_zero n hp.out.ne_zero) ?_
    have h0 := uniformTilt.coeff_pow_p_pow (toTiltHom hξ ((ϖ : R) ^ k) * y) 0 n
    rw [zero_add] at h0
    rw [h0, map_mul, coeff_toTiltHom hξ, iterateFrobeniusEquiv_zero_symm, map_pow, mul_comm]
    exact isBounded_untiltPlus.isPowerBounded_of_mem hk
  have hy'_plus (n : ℕ) :
      uniformTilt.coeff p A n (toTiltHom hξ ((ϖ : R) ^ (k + 1)) * y) ∈ untiltPlus p P J := by
    have hsplit : toTiltHom hξ ((ϖ : R) ^ (k + 1)) * y =
        toTiltHom hξ ϖ * (toTiltHom hξ ((ϖ : R) ^ k) * y) := by
      rw [pow_succ', map_mul, mul_assoc]
    rw [hsplit, map_mul]
    have hcoeff_ϖ : uniformTilt.coeff p A n (toTiltHom hξ ϖ) =
        algebraMap A₀ A ((((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) (g ϖ)).untilt) := by
      rw [hg_iter, hg_untilt, coeff_toTiltHom hξ, ← coe_iterateFrobeniusEquiv_plus_symm,
        sharp_apply]
    rw [hcoeff_ϖ]
    have hmem := (isPowerBounded_iff_forall_untilt_mul_mem_range (hasBasis_nhds_zero hϖ) hreg
      hroot (Associated.of_eq (hg_untilt ϖ).symm)).mp (hz_pb n) n
    obtain ⟨b, hb⟩ := hmem
    exact mem_untiltPlus.mpr ⟨b, hb⟩
  obtain ⟨a, ha⟩ := hsurj_plus _ hy'_plus
  let u := (hϖ.isUnit.pow (k + 1)).unit
  refine ⟨↑u⁻¹ * (a : R), ?_⟩
  have hu_tilt : IsUnit (toTiltHom hξ (u : R)) := (u.isUnit.map (toTiltHom hξ))
  refine hu_tilt.mul_left_cancel ?_
  rw [← map_mul, ← mul_assoc, Units.mul_inv, one_mul]
  exact ha

/-- **The tilt of a primitive untilt is `R`** (Scholze, *Étale cohomology of diamonds*,
Theorem 3.17): `uniformTilt p (untilt p P (Ideal.span {ξ})) ≃+* R`, with inverse
`x ↦ (sharp (x ^ (1 / p ^ n)))_n`. -/
noncomputable def tiltEquiv (hξ : ξ.IsPrimitive) :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    uniformTilt p (untilt p P (Ideal.span {ξ})) ≃+* R :=
  letI := t2Space hξ
  letI := completeSpace hξ
  letI := isUniform hξ
  letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  (RingEquiv.ofBijective (toTiltHom hξ) ⟨toTiltHom_injective hξ, toTiltHom_surjective hξ⟩).symm

/-- The `n`-th coordinate of `(tiltEquiv hξ).symm x` is `sharp (x ^ (1 / p ^ n))`. -/
@[simp]
theorem coeff_tiltEquiv_symm (hξ : ξ.IsPrimitive) (x : R) (n : ℕ) :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n ((tiltEquiv hξ).symm x) =
      sharp p P (Ideal.span {ξ}) ((iterateFrobeniusEquiv R p n).symm x) :=
  coeff_toTiltFun hξ x n

/-- Under `tiltEquiv`, `untilt.sharp` agrees with the zeroth coordinate of `uniformTilt`. -/
@[simp]
theorem sharp_tiltEquiv (hξ : ξ.IsPrimitive)
    (y : uniformTilt p (untilt p P (Ideal.span {ξ}))) :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    sharp p P (Ideal.span {ξ}) (tiltEquiv hξ y) =
      uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) 0 y := by
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  have h := coeff_tiltEquiv_symm hξ (tiltEquiv hξ y) 0
  rw [(tiltEquiv hξ).symm_apply_apply, iterateFrobeniusEquiv_zero_symm] at h
  exact h.symm

/-- **`tiltEquiv` is a homeomorphism** `A♭ ≃ₜ R`. -/
theorem isHomeomorph_tiltEquiv (hξ : ξ.IsPrimitive) :
    letI := t2Space hξ
    letI := completeSpace hξ
    letI := isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
      ⟨isTopologicallyNilpotent_natCast hξ⟩
    IsHomeomorph (tiltEquiv hξ) := by
  have := t2Space hξ
  have := completeSpace hξ
  have := isUniform hξ
  have : Fact (IsTopologicallyNilpotent (p : untilt p P (Ideal.span {ξ}))) :=
    ⟨isTopologicallyNilpotent_natCast hξ⟩
  set J := Ideal.span {ξ}
  set A := untilt p P J
  have hcont_symm : Continuous (tiltEquiv hξ).symm := by
    rw [uniformTilt.continuous_iff]
    intro n
    have heq : (fun x : R ↦ uniformTilt.coeff p A n ((tiltEquiv hξ).symm x)) =
        ⇑(sharp p P J) ∘ ⇑(iterateFrobeniusEquiv R p n).symm :=
      funext fun x ↦ coeff_tiltEquiv_symm hξ x n
    rw [heq]
    exact (continuous_sharp hξ).comp (continuous_iterateFrobeniusEquiv_symm n)
  have hcont : Continuous (tiltEquiv hξ) := by
    refine continuous_of_continuousAt_zero (tiltEquiv hξ).toAddMonoidHom ?_
    obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
    have := IsUniform.of_perfectRing (R := R) p
    let D : PairOfDefinition R := PairOfDefinition.ofIsPseudoUniformizer P.plus
      P.isRingOfIntegralElements.isOpen P.isRingOfIntegralElements.isBounded hϖ ϖ.property
    rw [ContinuousAt, map_zero, (hϖ.hasBasis_nhds_zero D).tendsto_right_iff]
    intro n _
    have hV : uniformTilt.coeff p A 0 ⁻¹'
        (awayNhd (Ideal.Quotient.mk J (teichmuller p ϖ)) A n : Set A) ∈
        𝓝 (0 : uniformTilt p A) := by
      have h0 : uniformTilt.coeff p A 0 0 = 0 := uniformTilt.coeff_zero 0
      exact (uniformTilt.continuous_coeff 0).continuousAt.preimage_mem_nhds
        (h0.symm ▸ (hasBasis_nhds_zero (J := J) hϖ).mem_of_mem (i := n) trivial)
    refine Filter.mem_of_superset hV fun y hy ↦ ?_
    obtain ⟨b, hb⟩ := mem_awayNhd.mp hy
    let u := (hϖ.isUnit.pow n).unit
    have hsharp : sharp p P J (↑u⁻¹ * tiltEquiv hξ y) ∈ untiltPlus p P J := by
      rw [map_mul, sharp_tiltEquiv hξ y, ← hb, map_mul, map_pow,
        ← sharp_apply ϖ, ← map_pow, ← mul_assoc, ← map_mul]
      have hu1 : (↑u⁻¹ : R) * (ϖ : R) ^ n = 1 := Units.inv_mul u
      rw [hu1, map_one, one_mul]
      exact mem_untiltPlus.mpr ⟨b, rfl⟩
    refine ⟨↑u⁻¹ * tiltEquiv hξ y, ?_, ?_⟩
    · rw [PairOfDefinition.ofIsPseudoUniformizer_ringOfDefinition]
      exact (sharp_mem_untiltPlus_iff hξ).mp hsharp
    · change (u : R) * (↑u⁻¹ * tiltEquiv hξ y) = tiltEquiv hξ y
      rw [← mul_assoc, Units.mul_inv, one_mul]
  exact (Homeomorph.mk (tiltEquiv hξ).toEquiv hcont hcont_symm).isHomeomorph

end Perfectoid

end TauCeti.Perfectoid.untilt
