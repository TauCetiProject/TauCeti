/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Perfectoid.Padic
import TauCeti.RingTheory.Perfectoid.Pair

/-!
# Checks for Fontaine's map on perfectoid Huber pairs

* Every Huber pair `P` on `ℂ_p` has an integral perfectoid plus ring `P.plus`, so `(p)`-adic
  completeness is synthesized automatically when forming `WittVector.fontaineTheta P.plus p`, its
  surjectivity, and its regular distinguished kernel generator.
* On `(Pair.powerBounded ℂ_p).plus = ℂ_p°`, extracting compatible `p`-power roots `ϖ` of `p` yields
  the explicit classical formula `ker θ = (p - [ϖ])` for all primes `p` (including `p = 2`), while
  the nonzero element `ξ ^ 2 ∈ ker θ` is not distinguished and does not generate `ker θ`.
* No domain assumption is needed: `Pair.powerBounded (ℂ_p × ℂ_p)` has nontrivial zero divisors, yet
  `ker θ` still admits a distinguished nonzerodivisor generator.
* On the zero Tate ring, `P.plus` is integral perfectoid and `frobenius_surjective_plus` holds.
-/

open Ideal TauCeti.Huber TauCeti.Perfectoid
open scoped nonZeroDivisors

namespace TauCeti.Examples

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Arbitrary Huber pairs on `ℂ_p` -/

-- Every plus ring of `ℂ_p` is integral perfectoid; `(p)`-adic completeness is automatic.
example (P : Pair ℂ_[p]) : IsIntegralPerfectoid p P.plus := inferInstance

example (P : Pair ℂ_[p]) : IsAdicComplete (span {(p : P.plus)}) P.plus := inferInstance

-- Surjectivity and regular distinguished kernel generator of `θ` on any plus ring of `ℂ_p`,
-- with no manual completeness argument.
example (P : Pair ℂ_[p]) :
    letI : Fact ¬IsUnit (p : P.plus) := ⟨P.isRingOfIntegralElements.not_isUnit_natCast⟩
    Function.Surjective (WittVector.fontaineTheta P.plus p) ∧
      ∃ ξ : WittVector p (PreTilt P.plus p),
        ξ.IsDistinguished ∧ ξ ∈ (WittVector p (PreTilt P.plus p))⁰ ∧
          RingHom.ker (WittVector.fontaineTheta P.plus p) = span {ξ} := by
  let : Fact ¬IsUnit (p : P.plus) := ⟨P.isRingOfIntegralElements.not_isUnit_natCast⟩
  exact ⟨surjective_fontaineTheta_of_isPerfectoidTateRing P,
    exists_regular_generator_ker_fontaineTheta P⟩

/-! ### Explicit formula `ker θ = (p - [p♭])` on `ℂ_p°` (for all primes `p`, including `p = 2`) -/

-- Extracting compatible `p`-power roots `ϖ` of `p` in `ℂ_p°` gives `ϖ.untilt = p` and
-- `ker θ = (p - [ϖ])` for every prime `p` (including `p = 2`).
example :
    letI : Fact ¬IsUnit (p : (Pair.powerBounded ℂ_[p]).plus) :=
      ⟨(Pair.powerBounded ℂ_[p]).isRingOfIntegralElements.not_isUnit_natCast⟩
    ∃ ϖ : PreTilt (Pair.powerBounded ℂ_[p]).plus p,
      ϖ.untilt = p ∧
        RingHom.ker (WittVector.fontaineTheta (Pair.powerBounded ℂ_[p]).plus p) =
          span {(p : WittVector p _) - WittVector.teichmuller p ϖ} := by
  let : Fact ¬IsUnit (p : (Pair.powerBounded ℂ_[p]).plus) :=
    ⟨(Pair.powerBounded ℂ_[p]).isRingOfIntegralElements.not_isUnit_natCast⟩
  have hroot : Function.Surjective fun x : (Pair.powerBounded ℂ_[p]).plus ↦ x ^ p := fun x ↦ by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ_[p]) hp.out.pos
    exact ⟨⟨y, (Pair.powerBounded ℂ_[p]).isRingOfIntegralElements.mem_of_pow_mem hp.out.pos
      (hy.symm ▸ x.2)⟩, Subtype.ext hy⟩
  obtain ⟨roots, hroots⟩ :=
    Perfection.coeffMonoidHom_surjective hroot 0 (p : (Pair.powerBounded ℂ_[p]).plus)
  let I : Ideal (Pair.powerBounded ℂ_[p]).plus := span {(p : (Pair.powerBounded ℂ_[p]).plus)}
  let ϖ : PreTilt (Pair.powerBounded ℂ_[p]).plus p :=
    PreTilt.equivPerfection.symm (Perfection.quotientMulEquiv p I roots)
  have hϖ : ϖ.untilt = p := by
    -- `PreTilt.untilt` is `Perfection.teichmuller₀` on `ModP`, and `equivPerfection.symm` is the
    -- identity on the underlying `Perfection` sequence.
    change Perfection.teichmuller₀ p I (Perfection.quotientMulEquiv p I roots) = p
    rw [← Perfection.coeff_zero_symm_quotientMulEquiv, MulEquiv.symm_apply_apply]
    exact hroots
  have : IsAdicComplete (span {ϖ.untilt}) (Pair.powerBounded ℂ_[p]).plus := hϖ.symm ▸ inferInstance
  have : IsAdicComplete (span {ϖ}) (PreTilt (Pair.powerBounded ℂ_[p]).plus p) :=
    PreTilt.isAdicComplete_span_singleton (hϖ.symm ▸ dvd_rfl)
  have hker : (p : WittVector p _) - WittVector.teichmuller p ϖ ∈
      RingHom.ker (WittVector.fontaineTheta (Pair.powerBounded ℂ_[p]).plus p) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, WittVector.fontaineTheta_teichmuller, hϖ, sub_self]
  refine ⟨ϖ, hϖ, ?_⟩
  rw [ker_fontaineTheta_eq_span_iff_isDistinguished (Pair.powerBounded ℂ_[p]) hker]
  have heq : (p : WittVector p _) - WittVector.teichmuller p ϖ =
      (p : WittVector p _) + WittVector.teichmuller p ϖ * (-1) := by ring
  rw [heq]
  exact WittVector.isDistinguished_p_add_teichmuller_mul_of_isAdicComplete ϖ (-1)

-- A nonzero element of `ker θ` need not generate `ker θ`: for any regular generator `ξ`, `ξ ^ 2` is
-- a nonzero element of `ker θ` which is neither distinguished nor a generator.
example :
    letI : Fact ¬IsUnit (p : (Pair.powerBounded ℂ_[p]).plus) :=
      ⟨(Pair.powerBounded ℂ_[p]).isRingOfIntegralElements.not_isUnit_natCast⟩
    ∃ η : WittVector p (PreTilt (Pair.powerBounded ℂ_[p]).plus p),
      η ≠ 0 ∧ η ∈ RingHom.ker (WittVector.fontaineTheta (Pair.powerBounded ℂ_[p]).plus p) ∧
        ¬η.IsDistinguished ∧
        RingHom.ker (WittVector.fontaineTheta (Pair.powerBounded ℂ_[p]).plus p) ≠ span {η} := by
  let : Fact ¬IsUnit (p : (Pair.powerBounded ℂ_[p]).plus) :=
    ⟨(Pair.powerBounded ℂ_[p]).isRingOfIntegralElements.not_isUnit_natCast⟩
  have : Nontrivial (WittVector p (PreTilt (Pair.powerBounded ℂ_[p]).plus p)) :=
    (WittVector.fontaineTheta (Pair.powerBounded ℂ_[p]).plus p).domain_nontrivial
  obtain ⟨ξ, -, hreg, hker⟩ :=
    exists_regular_generator_ker_fontaineTheta (p := p) (Pair.powerBounded ℂ_[p])
  have hξ_ker : ξ ∈ RingHom.ker (WittVector.fontaineTheta (Pair.powerBounded ℂ_[p]).plus p) := by
    rw [hker]
    exact mem_span_singleton_self ξ
  have hsq_ker :
      ξ ^ 2 ∈ RingHom.ker (WittVector.fontaineTheta (Pair.powerBounded ℂ_[p]).plus p) := by
    rw [sq]
    exact Ideal.mul_mem_right ξ _ hξ_ker
  have hnot_span :
      RingHom.ker (WittVector.fontaineTheta (Pair.powerBounded ℂ_[p]).plus p) ≠ span {ξ ^ 2} := by
    intro hspan
    have hmem : ξ ∈ span {ξ ^ 2} := by
      rw [← hspan, hker]
      exact mem_span_singleton_self ξ
    obtain ⟨y, hy⟩ := mem_span_singleton.mp hmem
    have h1 : ξ * (ξ * y) = ξ * 1 := by linear_combination -hy
    have hθ := congrArg (WittVector.fontaineTheta (Pair.powerBounded ℂ_[p]).plus p)
      ((mul_cancel_left_mem_nonZeroDivisors hreg).mp h1)
    simp [RingHom.mem_ker.mp hξ_ker] at hθ
  refine ⟨ξ ^ 2, nonZeroDivisors.ne_zero (pow_mem hreg 2), hsq_ker, ?_, hnot_span⟩
  rwa [← ker_fontaineTheta_eq_span_iff_isDistinguished (Pair.powerBounded ℂ_[p]) hsq_ker]

/-! ### Non-domain product `ℂ_p × ℂ_p` and the zero Tate ring -/

-- `ℂ_p × ℂ_p` has zero divisors, yet `ker θ` still has a regular distinguished generator.
example :
    letI : Fact ¬IsUnit (p : (Pair.powerBounded (ℂ_[p] × ℂ_[p])).plus) :=
      ⟨(Pair.powerBounded (ℂ_[p] × ℂ_[p])).isRingOfIntegralElements.not_isUnit_natCast⟩
    ∃ ξ : WittVector p (PreTilt (Pair.powerBounded (ℂ_[p] × ℂ_[p])).plus p),
      ξ.IsDistinguished ∧ ξ ∈ (WittVector p (PreTilt (Pair.powerBounded (ℂ_[p] × ℂ_[p])).plus p))⁰ ∧
        RingHom.ker (WittVector.fontaineTheta (Pair.powerBounded (ℂ_[p] × ℂ_[p])).plus p) =
          span {ξ} := by
  let : Fact ¬IsUnit (p : (Pair.powerBounded (ℂ_[p] × ℂ_[p])).plus) :=
    ⟨(Pair.powerBounded (ℂ_[p] × ℂ_[p])).isRingOfIntegralElements.not_isUnit_natCast⟩
  exact exists_regular_generator_ker_fontaineTheta (Pair.powerBounded (ℂ_[p] × ℂ_[p]))

-- On the zero Tate ring, `P.plus` is integral perfectoid and Frobenius modulo `p` is surjective.
example {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
    [IsTateRing R] [CompleteSpace R] [T2Space R] [Subsingleton R] (P : Pair R) :
    haveI := isPerfectoidTateRing_of_subsingleton p R
    IsIntegralPerfectoid p P.plus ∧ Function.Surjective fun x : ModP P.plus p ↦ x ^ p := by
  have := isPerfectoidTateRing_of_subsingleton p R
  exact ⟨inferInstance, frobenius_surjective_plus P⟩

end TauCeti.Examples
