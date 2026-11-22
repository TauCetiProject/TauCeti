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
import TauCeti.RingTheory.Perfect.Basic
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
  Arizona Winter School 2017, Lemmas 2.6.14 and 2.7.9.
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, Theorem 2.3.9.
* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Lemma 3.21.
-/

public section

open Filter Ideal Topology TauCeti.Huber WittVector
open scoped nonZeroDivisors Pointwise

namespace TauCeti.Perfectoid.untilt

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

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

/-- A pseudouniformiser `ϖ ∈ R⁺` with `ϖ ^ p ∣ ξ₀` together with the derived radical and
regularity witnesses in `𝕎 R⁺ ⧸ (ξ)`. -/
private structure PrimitiveWitness (ξ : WittVector p P.plus) where
  varpi : P.plus
  isPseudoUniformizer : IsPseudoUniformizer (varpi : R)
  pow_dvd : varpi ^ p ∣ ξ.coeff 0
  radical : ξ.coeff 0 ∈ (span {varpi}).radical
  nonZeroDivisor : Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p varpi) ∈
    (WittVector p P.plus ⧸ Ideal.span {ξ})⁰

private noncomputable def primitiveWitness (hξ : ξ.IsPrimitive) : PrimitiveWitness ξ :=
  have h := P.isRingOfIntegralElements.exists_isPseudoUniformizer_pow_dvd hp.out.one_lt
    (ξ.coeff 0)
    (hξ.isTopologicallyNilpotent_coeff_zero.map (φ := P.plus.subtype) continuous_subtypeVal)
  let ϖ := h.choose
  have hϖ := h.choose_spec.1
  have hξ₀p := h.choose_spec.2
  have hrad : ξ.coeff 0 ∈ (span {ϖ}).radical :=
    ⟨1, by rw [pow_one, mem_span_singleton]; exact (dvd_pow_self ϖ hp.out.ne_zero).trans hξ₀p⟩
  have hreg : Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p ϖ) ∈
      (WittVector p P.plus ⧸ Ideal.span {ξ})⁰ :=
    hξ.isDistinguished.mk_teichmuller_mem_nonZeroDivisors hrad
      (comap_nonZeroDivisors_le_of_injective (f := P.plus.subtype) Subtype.val_injective
        hϖ.isUnit.mem_nonZeroDivisors)
  ⟨ϖ, hϖ, hξ₀p, hrad, hreg⟩

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
      have hpow : ∀ x : P.plus, frobeniusEquiv P.plus p x = x ^ p := fun x ↦ by
        rw [coe_frobeniusEquiv, frobenius_def]
      rw [← hpow ϖ, ← hpow (w.coeff 0)] at hcoeff
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
  refine ⟨fun hx ↦ ?_, fun hx ↦ (sharp_coe (J := Ideal.span {ξ}) ⟨x, hx⟩).symm ▸
    sharpPlus_mem_untiltPlus (J := Ideal.span {ξ}) ⟨x, hx⟩⟩
  obtain ⟨ϖ, hϖ, hξ₀p, _, _⟩ := primitiveWitness hξ
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
      dsimp only [a]
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
      dsimp only [a] at hca
      rw [pow_succ] at hca
      rw [mul_assoc, hca, mul_comm]
    exact ih y hy (hyc.symm ▸ c.property)

/-- The untilt along a primitive element is uniform. -/
theorem isUniform (hξ : ξ.IsPrimitive) : IsUniform (untilt p P (Ideal.span {ξ})) := by
  obtain ⟨ϖ, hϖ, hξ₀p, _, hreg⟩ := primitiveWitness hξ
  have := isLocalizationAway (J := Ideal.span {ξ}) hϖ
  have hroot : ∀ a : WittVector p P.plus ⧸ Ideal.span {ξ},
      Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p ϖ) ^ p ∣ a ^ p →
        Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p ϖ) ∣ a :=
    (frobeniusModPow_injective_iff (mk_teichmuller_pow_dvd_natCast hξ hξ₀p)).mp
      (bijective_frobeniusModPow_quotient hξ hξ₀p).1
  exact isUniform_of_dvd_of_pow_dvd_pow hp.out.one_lt (hasBasis_nhds_zero hϖ) hreg hroot

/-- `IsUniform` instance on `untilt p P (Ideal.span {ξ})` when `[Fact ξ.IsPrimitive]`. -/
instance instIsUniform [hξ : Fact ξ.IsPrimitive] :
    IsUniform (untilt p P (Ideal.span {ξ})) :=
  isUniform hξ.out

end Algebraic

/-! ### Perfectoidness, tilt identification, and the untilt Huber pair -/

section Perfectoid

variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R]
  [CompleteSpace R] [T2Space R] [CharP R p] [PerfectRing R p] {P : Pair R}
  {ξ : WittVector p P.plus}

private theorem PrimitiveWitness.isAdicComplete_quotient {hξ : ξ.IsPrimitive}
    (w : PrimitiveWitness ξ) :
    IsAdicComplete (span {Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p w.varpi)})
      (WittVector p P.plus ⧸ Ideal.span {ξ}) := by
  have := IsUniform.of_perfectRing (R := R) p
  have := P.isRingOfIntegralElements.isAdicComplete_span_singleton w.varpi w.isPseudoUniformizer
  exact hξ.isDistinguished.isAdicComplete_quotient w.radical

/-- **`𝕎 R⁺ ⧸ (ξ)` is an integral perfectoid ring** for a primitive element `ξ`. -/
theorem isIntegralPerfectoid_quotient (hξ : ξ.IsPrimitive) :
    IsIntegralPerfectoid p (WittVector p P.plus ⧸ Ideal.span {ξ}) := by
  let w := primitiveWitness hξ
  have := w.isAdicComplete_quotient (hξ := hξ)
  exact IsIntegralPerfectoid.of_bijective_frobeniusModPow w.nonZeroDivisor
    (bijective_frobeniusModPow_quotient hξ w.pow_dvd)

/-- **`A⁺` is an integral perfectoid ring** for the untilt along a primitive element `ξ`. -/
theorem isIntegralPerfectoid_untiltPlus (hξ : ξ.IsPrimitive) :
    IsIntegralPerfectoid p (untiltPlus p P (Ideal.span {ξ})) := by
  let w := primitiveWitness hξ
  have := w.isAdicComplete_quotient (hξ := hξ)
  set J := Ideal.span {ξ}
  set e := quotientEquivUntiltPlus hξ
  set π₀ : WittVector p P.plus ⧸ J := Ideal.Quotient.mk J (teichmuller p w.varpi)
  set π : untiltPlus p P J := e π₀
  have hmap : (span {π₀}).map e = span {π} := by
    rw [Ideal.map_span, Set.image_singleton]
  have : IsAdicComplete (span {π}) (untiltPlus p P J) := by
    rw [← hmap]
    exact (IsAdicComplete.congr_ringEquiv (span {π₀}) e).mpr inferInstance
  have hreg : π ∈ (untiltPlus p P J)⁰ := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    apply e.symm.injective
    rw [map_zero]
    exact (mem_nonZeroDivisors_iff_right.mp w.nonZeroDivisor) (e.symm x) (by
      have := congrArg e.symm hx
      simpa [π] using this)
  have hdvd₀ := mk_teichmuller_pow_dvd_natCast hξ w.pow_dvd
  have hdvd : π ^ p ∣ (p : untiltPlus p P J) := by
    obtain ⟨c, hc⟩ := hdvd₀
    exact ⟨e c, by simpa [π] using congrArg e hc⟩
  have hbij₀ := bijective_frobeniusModPow_quotient hξ w.pow_dvd
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
theorem isPerfectoidTateRing [hξ : Fact ξ.IsPrimitive] :
    IsPerfectoidTateRing p (untilt p P (Ideal.span {ξ})) := by
  let w := primitiveWitness hξ.out
  have := isLocalizationAway (J := Ideal.span {ξ}) w.isPseudoUniformizer
  have := w.isAdicComplete_quotient (hξ := hξ.out)
  exact isPerfectoidTateRing_of_bijective_frobeniusModPow
    (hasBasis_nhds_zero w.isPseudoUniformizer) w.nonZeroDivisor
    (bijective_frobeniusModPow_quotient hξ.out w.pow_dvd)

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
        iterateFrobeniusEquiv_symm_pow x (n + 1), (iterateFrobeniusEquiv R p n).apply_symm_apply]

private theorem coeff_toTiltFun [Fact ξ.IsPrimitive] (x : R) (n : ℕ) :
    uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n (toTiltFun ξ x) =
      sharp p P (Ideal.span {ξ}) ((iterateFrobeniusEquiv R p n).symm x) :=
  uniformTilt.coeff_mk _ _ n

/-- `IsTateRing` instance on the tilt `uniformTilt p (untilt p P (Ideal.span {ξ}))` when
`[Fact ξ.IsPrimitive]`. -/
instance instIsTateRingUniformTilt [Fact ξ.IsPrimitive] :
    IsTateRing (uniformTilt p (untilt p P (Ideal.span {ξ}))) := by
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  refine uniformTilt.isTateRing_of_sharp (ϖ := toTiltFun ξ ϖ) ?_
  rw [coeff_toTiltFun, iterateFrobeniusEquiv_zero, RingEquiv.symm_refl, RingEquiv.refl_apply]
  exact isPseudoUniformizer_sharp hϖ

/-- **The tilt of the untilt is Tate**: the tilt `A♭` of the untilt along a primitive `ξ` is a
Tate ring. -/
theorem isTateRing_uniformTilt [Fact ξ.IsPrimitive] :
    IsTateRing (uniformTilt p (untilt p P (Ideal.span {ξ}))) :=
  inferInstance

private theorem teichmuller_add_sub_teichmuller_mem_span_p {S : Type*} [CommRing S] [CharP S p]
    [PerfectRing S p] (a b : S) :
    teichmuller p a + teichmuller p b - teichmuller p (a + b) ∈ span {(p : WittVector p S)} := by
  rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_add,
    constantCoeff_apply, constantCoeff_apply, constantCoeff_apply,
    teichmuller_coeff_zero, teichmuller_coeff_zero, teichmuller_coeff_zero, sub_self]

private theorem toTiltFun_add_plus_diff [Fact ξ.IsPrimitive] (a b : P.plus) (i m : ℕ) :
    (uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) (i + m) (toTiltFun ξ a) +
        uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) (i + m) (toTiltFun ξ b)) ^ p ^ m -
      uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) i (toTiltFun ξ (a + b)) ∈
      ((p : untilt p P (Ideal.span {ξ})) ^ (m + 1)) •
        (untiltPlus p P (Ideal.span {ξ}) : Set (untilt p P (Ideal.span {ξ}))) := by
  set J := Ideal.span {ξ}
  set A := untilt p P J
  let ai : P.plus := (iterateFrobeniusEquiv P.plus p (i + m)).symm a
  let bi : P.plus := (iterateFrobeniusEquiv P.plus p (i + m)).symm b
  have hsmod : teichmuller p ai + teichmuller p bi ≡ teichmuller p (ai + bi)
      [SMOD span {(p : WittVector p P.plus)}] :=
    SModEq.sub_mem.mpr (teichmuller_add_sub_teichmuller_mem_span_p ai bi)
  have hpow_smod := hsmod.pow_pow_add_one (mem_span_singleton_self (p : WittVector p P.plus)) m
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
  dsimp only
  rw [smul_eq_mul, coeff_toTiltFun, coeff_toTiltFun, coeff_toTiltFun,
    ← coe_iterateFrobeniusEquiv_plus_symm a (i + m),
    ← coe_iterateFrobeniusEquiv_plus_symm b (i + m), ← Subring.coe_add,
    ← coe_iterateFrobeniusEquiv_plus_symm (a + b) i,
    sharp_apply ai, sharp_apply bi, sharp_apply, ← map_add, ← map_add, ← map_pow, ← map_pow,
    ← hsum_pow, map_pow (teichmuller p) (ai + bi), ← map_sub, ← map_sub, hd, map_mul,
    map_pow, map_natCast, map_mul, map_pow, map_natCast]

private theorem toTiltFun_add_plus [hξ : Fact ξ.IsPrimitive] (a b : P.plus) :
    toTiltFun ξ (a + b) = toTiltFun ξ a + toTiltFun ξ b := by
  set J := Ideal.span {ξ}
  set A := untilt p P J
  apply uniformTilt.ext
  intro i
  have hlim := uniformTilt.coeff_add (toTiltFun ξ a) (toTiltFun ξ b) i
  refine (tendsto_nhds_unique hlim ?_).symm
  rw [← tendsto_sub_nhds_zero_iff, Filter.tendsto_def]
  intro U hU
  obtain ⟨V, hV, hVU⟩ := isBounded_iff.mp isBounded_untiltPlus U hU
  have hev : ∀ᶠ m in atTop, (p : A) ^ (m + 1) ∈ V :=
    ((isTopologicallyNilpotent_natCast hξ.out).comp (tendsto_add_atTop_nat 1)).eventually_mem hV
  exact hev.mono fun m hm ↦ by
    obtain ⟨c, hc, hcm⟩ := toTiltFun_add_plus_diff (ξ := ξ) a b i m
    dsimp only
    rw [← hcm]
    exact hVU (Set.mul_mem_mul hm hc)

/-- `toTiltFun` is a ring homomorphism `R →+* uniformTilt p (untilt p P (Ideal.span {ξ}))`. -/
private noncomputable def toTiltHom [Fact ξ.IsPrimitive] :
    R →+* uniformTilt p (untilt p P (Ideal.span {ξ})) :=
  have hmul : ∀ x y : R, toTiltFun ξ (x * y) = toTiltFun ξ x * toTiltFun ξ y := fun x y ↦ by
    apply uniformTilt.ext
    intro n
    rw [map_mul, coeff_toTiltFun, coeff_toTiltFun, coeff_toTiltFun, map_mul, map_mul]
  { toFun := toTiltFun ξ
    map_one' := uniformTilt.ext fun n ↦ by rw [map_one, coeff_toTiltFun, map_one, map_one]
    map_mul' := hmul
    map_zero' := uniformTilt.ext fun n ↦ by
      rw [uniformTilt.coeff_zero, coeff_toTiltFun, map_zero, map_zero]
    map_add' := fun x y ↦ by
      -- Clear denominators with a power of a pseudouniformiser `ϖ` and reduce to `P.plus`.
      obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
      obtain ⟨kx, hkx⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent
        hϖ.isTopologicallyNilpotent P.isRingOfIntegralElements.isOpen x
      obtain ⟨ky, hky⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent
        hϖ.isTopologicallyNilpotent P.isRingOfIntegralElements.isOpen y
      set k := max kx ky
      have hpow_mem (z : R) (k₀ : ℕ) (hk₀ : z * (ϖ : R) ^ k₀ ∈ P.plus) (hle : k₀ ≤ k) :
          z * (ϖ : R) ^ k ∈ P.plus := by
        rw [show z * (ϖ : R) ^ k = (z * (ϖ : R) ^ k₀) * (ϖ : R) ^ (k - k₀) by
          rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hle]]
        exact P.plus.mul_mem hk₀ (P.plus.pow_mem ϖ.property _)
      have hu : IsUnit (toTiltFun ξ ((ϖ : R) ^ k)) := by
        rw [uniformTilt.isUnit_iff_coeff_zero, coeff_toTiltFun, iterateFrobeniusEquiv_zero,
          RingEquiv.symm_refl, RingEquiv.refl_apply, map_pow]
        exact (isPseudoUniformizer_sharp hϖ).isUnit.pow k
      refine hu.mul_right_cancel ?_
      rw [← hmul, add_mul, add_mul, ← hmul, ← hmul]
      exact toTiltFun_add_plus ⟨x * (ϖ : R) ^ k, hpow_mem x kx hkx (le_max_left _ _)⟩
        ⟨y * (ϖ : R) ^ k, hpow_mem y ky hky (le_max_right _ _)⟩ }

private theorem coeff_toTiltHom [Fact ξ.IsPrimitive] (x : R) (n : ℕ) :
    uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n (toTiltHom x) =
      sharp p P (Ideal.span {ξ}) ((iterateFrobeniusEquiv R p n).symm x) :=
  coeff_toTiltFun x n

/-- `toTiltHom` is injective. -/
private theorem toTiltHom_injective [hξ : Fact ξ.IsPrimitive] :
    Function.Injective (toTiltHom (p := p) (P := P) (ξ := ξ)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx0 : sharp p P (Ideal.span {ξ}) x = 0 := by
    have h0 := congrArg (uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) 0) hx
    rw [uniformTilt.coeff_zero, coeff_toTiltHom, iterateFrobeniusEquiv_zero,
      RingEquiv.symm_refl, RingEquiv.refl_apply] at h0
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
    have hplus : ↑u⁻¹ * x ∈ P.plus := (sharp_mem_untiltPlus_iff hξ.out).mp hsharp
    refine ⟨↑u⁻¹ * x, ?_, ?_⟩
    · rw [PairOfDefinition.ofIsPseudoUniformizer_ringOfDefinition]
      exact hplus
    · dsimp only
      rw [smul_eq_mul, ← (hϖ.isUnit.pow n).unit_spec, Units.mul_inv_cancel_left]
  have htend : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 (0 : R)) :=
    (hϖ.hasBasis_nhds_zero D).tendsto_right_iff.mpr fun n _ ↦ Eventually.of_forall fun _ ↦ hmem n
  exact tendsto_nhds_unique tendsto_const_nhds htend

private theorem isHausdorff_preTilt_map_span (hξ : ξ.IsPrimitive)
    (w : PrimitiveWitness ξ)
    [IsAdicComplete (span {(p : WittVector p P.plus ⧸ Ideal.span {ξ})})
      (WittVector p P.plus ⧸ Ideal.span {ξ})]
    [Fact ¬IsUnit (p : WittVector p P.plus ⧸ Ideal.span {ξ})]
    (g : P.plus →+* PreTilt (WittVector p P.plus ⧸ Ideal.span {ξ}) p)
    (hg_untilt : ∀ a : P.plus, (g a).untilt =
      Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p a)) :
    IsHausdorff ((span {w.varpi}).map g)
      (PreTilt (WittVector p P.plus ⧸ Ideal.span {ξ}) p) := by
  set J := Ideal.span {ξ}
  set A₀ := WittVector p P.plus ⧸ J
  set ϖ := w.varpi
  set π : A₀ := Ideal.Quotient.mk J (teichmuller p ϖ)
  have := w.isAdicComplete_quotient (hξ := hξ)
  rw [Ideal.map_span, Set.image_singleton]
  refine ⟨fun z hz ↦ PreTilt.ext fun n ↦ ?_⟩
  rw [map_zero, PreTilt.coeff_eq_mk_untilt_iterate]
  suffices h0 : (((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) z).untilt = 0 by
    rw [h0, map_zero]
  refine IsHausdorff.haus' (I := span {π}) _ fun k ↦ ?_
  rw [Ideal.smul_eq_mul, Ideal.mul_top, SModEq.zero, span_singleton_pow, mem_span_singleton]
  have hzk : g ϖ ^ (k * p ^ n) ∣ z := by
    have hmem := hz (k * p ^ n)
    rwa [Ideal.smul_eq_mul, Ideal.mul_top, SModEq.zero, span_singleton_pow,
      mem_span_singleton] at hmem
  have hpow_dvd :
      (g ϖ ^ k) ^ p ^ n ∣ (((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) z) ^ p ^ n := by
    rw [← pow_mul, iterate_frobeniusEquiv_symm_pow_p_pow]
    exact hzk
  have hdvd_n : g ϖ ^ k ∣ ((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) z := by
    rw [← iterateFrobeniusEquiv_def (PreTilt A₀ p) p n,
      ← iterateFrobeniusEquiv_def (PreTilt A₀ p) p n] at hpow_dvd
    exact (map_dvd_iff (iterateFrobeniusEquiv (PreTilt A₀ p) p n)).mp hpow_dvd
  obtain ⟨c, hc⟩ := hdvd_n
  have hpi : (g ϖ).untilt = π := hg_untilt ϖ
  refine ⟨c.untilt, ?_⟩
  rw [← hpi, ← map_pow, ← map_mul, ← hc]

/-- For a primitive element `ξ` and a witness `w : PrimitiveWitness ξ`, there is a surjective
ring homomorphism `g : R⁺ →+* PreTilt (𝕎 R⁺ ⧸ (ξ)) p` lifting Teichmüller representatives
(`(g a).untilt = mk [a]`). -/
private theorem exists_surjective_toPreTilt_quotient (hξ : ξ.IsPrimitive)
    (w : PrimitiveWitness ξ)
    [IsAdicComplete (span {(p : WittVector p P.plus ⧸ Ideal.span {ξ})})
      (WittVector p P.plus ⧸ Ideal.span {ξ})]
    [Fact ¬IsUnit (p : WittVector p P.plus ⧸ Ideal.span {ξ})] :
    ∃ g : P.plus →+* PreTilt (WittVector p P.plus ⧸ Ideal.span {ξ}) p,
      Function.Surjective g ∧
      ∀ a : P.plus, (g a).untilt = Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p a) := by
  -- Construct `g : R⁺ →+* PreTilt A₀ p` coordinatewise via `a ↦ (mkP [a ^ (1 / p ^ n)])_n`, check
  -- additivity using `[a] + [b] - [a + b] ∈ (p)`, and prove surjectivity mod `ϖ` then `ϖ`-adically.
  set J := Ideal.span {ξ}
  set A₀ := WittVector p P.plus ⧸ J
  set ϖ := w.varpi
  have hξ₀ : ϖ ∣ ξ.coeff 0 := (dvd_pow_self ϖ hp.out.ne_zero).trans w.pow_dvd
  set π : A₀ := Ideal.Quotient.mk J (teichmuller p ϖ)
  have := IsUniform.of_perfectRing (R := R) p
  have := P.isRingOfIntegralElements.isAdicComplete_span_singleton ϖ w.isPseudoUniformizer
  have := w.isAdicComplete_quotient (hξ := hξ)
  let mkP : A₀ →+* ModP A₀ p := Ideal.Quotient.mk (span {(p : A₀)})
  have hmkP_teich_add (a b : P.plus) :
      mkP (Ideal.Quotient.mk J (teichmuller p (a + b))) =
        mkP (Ideal.Quotient.mk J (teichmuller p a)) +
          mkP (Ideal.Quotient.mk J (teichmuller p b)) := by
    obtain ⟨d, hd⟩ := mem_span_singleton.mp (teichmuller_add_sub_teichmuller_mem_span_p a b)
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
          iterateFrobeniusEquiv_symm_pow a (n + 1),
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
    exact congrArg (teichmuller p) (iterateFrobeniusEquiv_symm_pow a n)
  have : IsHausdorff ((span {w.varpi}).map g) (PreTilt A₀ p) :=
    isHausdorff_preTilt_map_span hξ w g hg_untilt
  refine ⟨g, ?_, hg_untilt⟩
  refine surjective_of_mk_map_comp_surjective (I := span {ϖ}) (f := g) fun qz ↦ ?_
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective qz
  have : IsIntegralPerfectoid p A₀ := isIntegralPerfectoid_quotient hξ
  have hdvd' : (g ϖ).untilt ∣ (p : A₀) :=
    (dvd_pow_self _ hp.out.ne_zero).trans (by
      rw [hg_untilt]
      exact mk_teichmuller_pow_dvd_natCast hξ w.pow_dvd)
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
  exact Ideal.Quotient.eq.mpr (mem_span_singleton.mpr (by rwa [hg_untilt ϖ]))

private theorem iterate_frobeniusEquiv_symm_preTilt_map {S A₀ : Type*} [CommRing S] [CharP S p]
    [PerfectRing S p] [CommRing A₀] [Fact ¬IsUnit (p : A₀)]
    (g : S →+* PreTilt A₀ p) (a : S) (n : ℕ) :
    ((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) (g a) =
      g ((iterateFrobeniusEquiv S p n).symm a) := by
  apply (iterateFrobeniusEquiv (PreTilt A₀ p) p n).injective
  rw [iterateFrobeniusEquiv_def, iterate_frobeniusEquiv_symm_pow_p_pow, iterateFrobeniusEquiv_def,
    ← map_pow, iterateFrobeniusEquiv_symm_pow]

private theorem mem_range_toTiltHom_of_forall_mem_untiltPlus [hξ : Fact ξ.IsPrimitive]
    [IsAdicComplete (span {(p : WittVector p P.plus ⧸ Ideal.span {ξ})})
      (WittVector p P.plus ⧸ Ideal.span {ξ})]
    [Fact ¬IsUnit (p : WittVector p P.plus ⧸ Ideal.span {ξ})]
    {g : P.plus →+* PreTilt (WittVector p P.plus ⧸ Ideal.span {ξ}) p}
    (hg_surj : Function.Surjective g)
    (hg_untilt : ∀ a : P.plus, (g a).untilt =
      Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p a))
    (y : uniformTilt p (untilt p P (Ideal.span {ξ})))
    (hy : ∀ n, uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n y ∈
      untiltPlus p P (Ideal.span {ξ})) :
    ∃ a : P.plus, toTiltHom (a : R) = y := by
  let J := Ideal.span {ξ}
  let A := untilt p P J
  let A₀ := WittVector p P.plus ⧸ J
  let u : ℕ → A₀ := fun n ↦ (quotientEquivUntiltPlus hξ.out).symm
    ⟨uniformTilt.coeff p A n y, hy n⟩
  have hu_map (n : ℕ) : algebraMap A₀ A (u n) = uniformTilt.coeff p A n y := by
    rw [← coe_quotientEquivUntiltPlus_apply hξ.out (u n),
      (quotientEquivUntiltPlus hξ.out).apply_symm_apply]
  have hu_pow (n : ℕ) : u (n + 1) ^ p = u n := by
    apply algebraMap_injective hξ.out
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
    · rw [PreTilt.coeff_equivPerfection, PreTilt.coeff_iterate_frobeniusEquiv_symm, add_comm]
      exact (PreTilt.coeff_equivPerfection_symm zPerf (m + n)).symm
    · have hpow : ∀ m, u (n + m) ^ p ^ m = u n := fun m ↦ by
        induction m with
        | zero => simp
        | succ m ihm => rw [pow_succ', pow_mul, ← add_assoc, hu_pow, ihm]
      rw [hpow m]
      exact SModEq.rfl
  have hu_eq : Ideal.Quotient.mk J (teichmuller p ((iterateFrobeniusEquiv P.plus p n).symm a)) =
      u n := by
    rw [← hg_untilt, ← iterate_frobeniusEquiv_symm_preTilt_map g a n, ha, hzn_untilt]
  rw [coeff_toTiltHom, ← coe_iterateFrobeniusEquiv_plus_symm, sharp_apply, hu_eq, hu_map]

/-- `toTiltHom` is surjective. -/
private theorem toTiltHom_surjective [hξ : Fact ξ.IsPrimitive] :
    Function.Surjective (toTiltHom (p := p) (P := P) (ξ := ξ)) := by
  -- Lift elements with `untiltPlus` coordinates via `exists_surjective_toPreTilt_quotient`, then
  -- scale an arbitrary `y` by a power of a pseudouniformiser `ϖ` into that integral regime.
  set J := Ideal.span {ξ}
  set A := untilt p P J
  set A₀ := WittVector p P.plus ⧸ J
  rcases subsingleton_or_nontrivial A with hA | hA
  · intro y
    refine ⟨0, uniformTilt.ext fun n ↦ Subsingleton.elim _ _⟩
  let w := primitiveWitness hξ.out
  set ϖ := w.varpi
  set π : A₀ := Ideal.Quotient.mk J (teichmuller p ϖ)
  have hdvd : π ^ p ∣ (p : A₀) := mk_teichmuller_pow_dvd_natCast hξ.out w.pow_dvd
  have hbij := bijective_frobeniusModPow_quotient hξ.out w.pow_dvd
  have := w.isAdicComplete_quotient (hξ := hξ.out)
  have hπp : π ∣ (p : A₀) := (dvd_pow_self π hp.out.ne_zero).trans hdvd
  have : IsAdicComplete (span {(p : A₀)}) A₀ := .span_singleton_of_dvd hπp
  have : Nontrivial A₀ := by
    by_contra hnot
    rw [not_nontrivial_iff_subsingleton] at hnot
    exact not_subsingleton A (algebraMap A₀ A).codomain_trivial
  have : Fact ¬IsUnit (p : A₀) :=
    ⟨IsAdicComplete.not_isUnit_of_mem (I := span {π}) (mem_span_singleton.mpr hπp)⟩
  obtain ⟨g, hg_surj, hg_untilt⟩ := exists_surjective_toPreTilt_quotient hξ.out w
  intro y
  have := isLocalizationAway (J := J) w.isPseudoUniformizer
  have hroot : ∀ a : A₀, π ^ p ∣ a ^ p → π ∣ a := (frobeniusModPow_injective_iff hdvd).mp hbij.1
  obtain ⟨k, hk⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent
    (isPseudoUniformizer_sharp (J := J) w.isPseudoUniformizer).isTopologicallyNilpotent
    isOpen_untiltPlus (uniformTilt.coeff p A 0 y)
  have hz_pb (n : ℕ) :
      IsPowerBounded (uniformTilt.coeff p A n (toTiltHom ((ϖ : R) ^ k) * y)) := by
    refine IsPowerBounded.of_pow (pow_ne_zero n hp.out.ne_zero) ?_
    have h0 := uniformTilt.coeff_pow_p_pow (toTiltHom ((ϖ : R) ^ k) * y) 0 n
    rw [zero_add] at h0
    rw [h0, map_mul, coeff_toTiltHom, iterateFrobeniusEquiv_zero, RingEquiv.symm_refl,
      RingEquiv.refl_apply, map_pow, mul_comm]
    exact isBounded_untiltPlus.isPowerBounded_of_mem hk
  have hy'_plus (n : ℕ) :
      uniformTilt.coeff p A n (toTiltHom ((ϖ : R) ^ (k + 1)) * y) ∈ untiltPlus p P J := by
    have hsplit : toTiltHom ((ϖ : R) ^ (k + 1)) * y =
        toTiltHom (ϖ : R) * (toTiltHom ((ϖ : R) ^ k) * y) := by
      rw [pow_succ', map_mul, mul_assoc]
    rw [hsplit, map_mul]
    have hcoeff_ϖ : uniformTilt.coeff p A n (toTiltHom (ϖ : R)) =
        algebraMap A₀ A ((((frobeniusEquiv (PreTilt A₀ p) p).symm^[n]) (g ϖ)).untilt) := by
      rw [iterate_frobeniusEquiv_symm_preTilt_map, hg_untilt, coeff_toTiltHom,
        ← coe_iterateFrobeniusEquiv_plus_symm, sharp_apply]
    rw [hcoeff_ϖ]
    have hmem := (isPowerBounded_iff_forall_untilt_mul_mem_range
      (hasBasis_nhds_zero w.isPseudoUniformizer) w.nonZeroDivisor
      hroot (Associated.of_eq (hg_untilt ϖ).symm)).mp (hz_pb n) n
    obtain ⟨b, hb⟩ := hmem
    exact mem_untiltPlus.mpr ⟨b, hb⟩
  obtain ⟨a, ha⟩ := mem_range_toTiltHom_of_forall_mem_untiltPlus hg_surj hg_untilt _ hy'_plus
  let u := (w.isPseudoUniformizer.isUnit.pow (k + 1)).unit
  refine ⟨↑u⁻¹ * (a : R), ?_⟩
  have hu_tilt : IsUnit (toTiltHom (p := p) (P := P) (ξ := ξ) (u : R)) :=
    u.isUnit.map toTiltHom
  refine hu_tilt.mul_left_cancel ?_
  rw [← map_mul, ← mul_assoc, Units.mul_inv, one_mul]
  exact ha

/-- **The tilt of a primitive untilt is `R`** (Scholze, *Étale cohomology of diamonds*,
Theorem 3.17): `uniformTilt p (untilt p P (Ideal.span {ξ})) ≃+* R`, with inverse
`x ↦ (sharp (x ^ (1 / p ^ n)))_n`. -/
noncomputable def tiltEquiv [Fact ξ.IsPrimitive] :
    uniformTilt p (untilt p P (Ideal.span {ξ})) ≃+* R :=
  (RingEquiv.ofBijective (toTiltHom (p := p) (P := P) (ξ := ξ))
    ⟨toTiltHom_injective, toTiltHom_surjective⟩).symm

/-- The `n`-th coordinate of `tiltEquiv.symm x` is `sharp (x ^ (1 / p ^ n))`. -/
@[simp]
theorem coeff_tiltEquiv_symm [Fact ξ.IsPrimitive] (x : R) (n : ℕ) :
    uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) n
        ((tiltEquiv (p := p) (P := P) (ξ := ξ)).symm x) =
      sharp p P (Ideal.span {ξ}) ((iterateFrobeniusEquiv R p n).symm x) :=
  coeff_toTiltFun x n

/-- Under `tiltEquiv`, `untilt.sharp` agrees with the zeroth coordinate of `uniformTilt`. -/
@[simp]
theorem sharp_tiltEquiv [Fact ξ.IsPrimitive]
    (y : uniformTilt p (untilt p P (Ideal.span {ξ}))) :
    sharp p P (Ideal.span {ξ}) (tiltEquiv y) =
      uniformTilt.coeff p (untilt p P (Ideal.span {ξ})) 0 y := by
  have h := coeff_tiltEquiv_symm (P := P) (ξ := ξ) (tiltEquiv y) 0
  rw [(tiltEquiv).symm_apply_apply, iterateFrobeniusEquiv_zero, RingEquiv.symm_refl,
    RingEquiv.refl_apply] at h
  exact h.symm

/-- **`tiltEquiv` is a homeomorphism** `A♭ ≃ₜ R`. -/
theorem isHomeomorph_tiltEquiv [hξ : Fact ξ.IsPrimitive] :
    IsHomeomorph (tiltEquiv (p := p) (P := P) (ξ := ξ)) := by
  set J := Ideal.span {ξ}
  set A := untilt p P J
  have hcont_symm : Continuous (tiltEquiv (p := p) (P := P) (ξ := ξ)).symm := by
    rw [uniformTilt.continuous_iff]
    intro n
    have heq :
        (fun x : R ↦ uniformTilt.coeff p A n ((tiltEquiv (p := p) (P := P) (ξ := ξ)).symm x)) =
          ⇑(sharp p P J) ∘ ⇑(iterateFrobeniusEquiv R p n).symm :=
      funext fun x ↦ coeff_tiltEquiv_symm x n
    rw [heq]
    exact (continuous_sharp hξ.out).comp (TauCeti.Huber.continuous_iterateFrobeniusEquiv_symm p n)
  have hcont : Continuous (tiltEquiv (p := p) (P := P) (ξ := ξ)) := by
    refine continuous_of_continuousAt_zero
      (tiltEquiv (p := p) (P := P) (ξ := ξ) : uniformTilt p A →+ R) ?_
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
    have hsharp : sharp p P J (↑u⁻¹ * tiltEquiv y) ∈ untiltPlus p P J := by
      rw [map_mul, sharp_tiltEquiv y, ← hb, map_mul, map_pow,
        ← sharp_apply ϖ, ← map_pow, ← mul_assoc, ← map_mul]
      have hu1 : (↑u⁻¹ : R) * (ϖ : R) ^ n = 1 := Units.inv_mul u
      rw [hu1, map_one, one_mul]
      exact mem_untiltPlus.mpr ⟨b, rfl⟩
    refine ⟨↑u⁻¹ * tiltEquiv y, ?_, ?_⟩
    · rw [PairOfDefinition.ofIsPseudoUniformizer_ringOfDefinition]
      exact (sharp_mem_untiltPlus_iff hξ.out).mp hsharp
    · dsimp only
      rw [AddMonoidHom.coe_ofClass, smul_eq_mul, ← (hϖ.isUnit.pow n).unit_spec,
        Units.mul_inv_cancel_left]
  exact (Homeomorph.mk (tiltEquiv (p := p) (P := P) (ξ := ξ)).toEquiv hcont hcont_symm).isHomeomorph

end Perfectoid

end TauCeti.Perfectoid.untilt
