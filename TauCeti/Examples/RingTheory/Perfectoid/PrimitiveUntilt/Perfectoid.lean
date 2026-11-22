/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Subring
public import TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Pair
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Gauge
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.RingTheory.Huber.Perfect
public import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Checks for the perfectoid pair structure and tilting isomorphism of primitive untilts

These checks exercise `TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Perfectoid` and
`TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Pair` on:

* a zero characteristic-`p` base, where the tilt of any primitive untilt is zero and `tiltEquiv`
  vanishes identically;
* the perfectoid pair `(ℂ_p♭, ℂ_p♭°)` and the mixed-characteristic primitive element `ξ = p - [ϖ]`,
  checking:
  - the untilt `(A, A⁺)` is a genuine mixed-characteristic perfectoid Huber pair (`p` is a unit in
    `A`, so `p ≠ 0`, in contrast to the characteristic-`p` untilt along `(p)`);
  - `tiltEquiv : A♭ ≃+* ℂ_p♭` is a homeomorphism whose inverse sends compatible pseudouniformiser
    roots `(ϖ_n)` and `(ϖ_{n+1})` so that their sum maps to `ϖ_0 + ϖ_1`, while `(ϖ_n)` does NOT
    map to `ϖ_0 ^ p` (distinguishing `tiltEquiv` from `φ ∘ tiltEquiv`);
  - `ker_theta_eq` and `ker_fontaineTheta_eq` recover `Ideal.span {ξ}` as the kernel of Fontaine's
    `θ` on `A⁺`;
  - `isAlmostZero_powerBounded_quotient` verifies that `A° ⧸ A⁺` is almost zero for `(A⁺, A°°)`.
-/

public section

open Filter Ideal Topology TauCeti.Huber TauCeti.Perfectoid
open WittVector (teichmuller)

namespace TauCeti.Examples.PrimitiveUntiltPerfectoid

variable (p : ℕ) [hp : Fact p.Prime]

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

private noncomputable def parameter : PseudoUniformizerRoots p ℂ_[p] :=
  Classical.choice (nonempty_pseudoUniformizerRoots_of_isAlgClosed (PadicComplex.norm_p_lt_one p))

local instance : IsTateRing (uniformTilt p ℂ_[p]) :=
  uniformTilt.isTateRing_of_sharp (ϖ := (parameter p).toTilt)
    (by simpa using (parameter p).isPseudoUniformizer_root_zero)

local instance : IsUniform (uniformTilt p ℂ_[p]) := IsUniform.of_perfectRing p

private noncomputable abbrev pair : Pair (uniformTilt p ℂ_[p]) := Pair.powerBounded _

/-- The integral pseudouniformiser `ϖ = (parameter p).toTilt ∈ ℂ_p♭°`. -/
private noncomputable def varpi : (pair p).plus :=
  ⟨(parameter p).toTilt, by
    rw [Pair.powerBounded_plus, mem_powerBoundedSubring]
    exact IsPowerBounded.of_isTopologicallyNilpotent <|
      (uniformTilt.isTopologicallyNilpotent_iff_coeff_zero (p := p) (B := ℂ_[p])
        (x := (parameter p).toTilt)).mpr <| by
        simpa using (parameter p).isPseudoUniformizer_root_zero.isTopologicallyNilpotent⟩

private theorem isPseudoUniformizer_varpi :
    IsPseudoUniformizer (varpi p : uniformTilt p ℂ_[p]) := by
  rw [isPseudoUniformizer_iff, uniformTilt.isUnit_iff_coeff_zero,
    uniformTilt.isTopologicallyNilpotent_iff_coeff_zero]
  exact isPseudoUniformizer_iff.mp (by simpa [varpi] using
    (parameter p).isPseudoUniformizer_root_zero)

/-- The mixed-characteristic primitive element `ξ = p - [ϖ] ∈ 𝕎(ℂ_p♭°)`. -/
private noncomputable def xi : WittVector p (pair p).plus :=
  (p : WittVector p (pair p).plus) - teichmuller p (varpi p)

private theorem isPrimitive_xi : (xi p).IsPrimitive := by
  have hϖ := isPseudoUniformizer_varpi p
  have hAdic : IsAdic (span {varpi p}) :=
    (pair p).plus.isAdic_span_singleton_of_isOpen_of_isBounded
      (pair p).isRingOfIntegralElements.isOpen (pair p).isRingOfIntegralElements.isBounded
      hϖ (varpi p).property
  have := (pair p).isRingOfIntegralElements.isAdicComplete_span_singleton (varpi p) hϖ
  have hξ : xi p = (p : WittVector p (pair p).plus) + teichmuller p (varpi p) * (-1) := by
    simp [xi, sub_eq_add_neg]
  rw [hξ]
  exact WittVector.isPrimitive_p_add_teichmuller_mul_of_isAdic hAdic
    (mem_span_singleton_self (varpi p)) (-1)

private theorem nontrivial_untilt_xi :
    Nontrivial (untilt p (pair p) (span {xi p})) := by
  rw [nontrivial_iff]
  refine ⟨1, 0, fun h10 ↦ ?_⟩
  have hq : (1 : WittVector p (pair p).plus ⧸ span {xi p}) = 0 :=
    untilt.algebraMap_injective (isPrimitive_xi p) (by simpa using h10)
  have hmem : (1 : WittVector p (pair p).plus) ∈ span {xi p} := by
    rwa [← Ideal.Quotient.eq_zero_iff_mem, map_one]
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hmem
  have h0 := congrArg (WittVector.constantCoeff (p := p) (R := (pair p).plus)) hc
  simp only [map_one, map_mul, WittVector.constantCoeff_apply, xi,
    WittVector.sub_coeff_zero, WittVector.coeff_p_zero, WittVector.teichmuller_coeff_zero,
    zero_sub] at h0
  have hmul : ((-(c.coeff 0) : (pair p).plus) : uniformTilt p ℂ_[p]) *
      (varpi p : uniformTilt p ℂ_[p]) = 1 := by
    have hsub := congrArg Subtype.val h0
    simp only [OneMemClass.coe_one, Subring.coe_mul, Subring.coe_neg] at hsub
    rw [Subring.coe_neg]
    linear_combination -hsub
  have hnil : IsTopologicallyNilpotent (1 : uniformTilt p ℂ_[p]) := by
    rw [← hmul]
    exact ((pair p).isRingOfIntegralElements.isPowerBounded_of_mem
      (-(c.coeff 0)).property).isTopologicallyNilpotent_mul
      (isPseudoUniformizer_varpi p).isTopologicallyNilpotent
  obtain ⟨n, hn⟩ := hnil.exists_pow_mem_of_mem_nhds (isOpen_ne.mem_nhds zero_ne_one)
  exact hn (one_pow n)

/-! ### Zero characteristic-`p` base -/

-- Over a zero characteristic-`p` base, the tilt of any primitive untilt is zero and `tiltEquiv`
-- sends every element to `0`.
example {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
    [IsTateRing R] [CompleteSpace R] [T2Space R] [CharP R p] [PerfectRing R p] [Subsingleton R]
    (P : Pair R) {ξ : WittVector p P.plus} (hξ : ξ.IsPrimitive) :
    letI := untilt.t2Space hξ
    letI := untilt.completeSpace hξ
    letI := untilt.isUniform hξ
    letI : Fact (IsTopologicallyNilpotent (p : untilt p P (span {ξ}))) :=
      ⟨untilt.isTopologicallyNilpotent_natCast hξ⟩
    letI := untilt.isTateRing_uniformTilt hξ
    ∀ x, untilt.tiltEquiv hξ x = 0 := fun _ ↦ Subsingleton.elim _ _

/-! ### Mixed-characteristic perfectoid pair `(A, A⁺)` along `ξ = p - [ϖ]` -/

-- The untilt along `ξ = p - [ϖ]` is a mixed-characteristic perfectoid Huber pair: `p` is a unit
-- (hence `p ≠ 0`), unlike the characteristic-`p` untilt along `(p)`.
example :
    letI := untilt.t2Space (isPrimitive_xi p)
    letI := untilt.completeSpace (isPrimitive_xi p)
    IsPerfectoidTateRing p (untilt p (pair p) (span {xi p})) ∧
      IsRingOfIntegralElements (untiltPlus p (pair p) (span {xi p})) ∧
      (untilt.pair (isPrimitive_xi p)).plus = untiltPlus p (pair p) (span {xi p}) ∧
      (p : untilt p (pair p) (span {xi p})) ≠ 0 := by
  have : Nontrivial (untilt p (pair p) (span {xi p})) := nontrivial_untilt_xi p
  have hsp : untilt.sharp p (pair p) (span {xi p}) (varpi p : uniformTilt p ℂ_[p]) = p := by
    rw [untilt.sharp_apply]
    have hmk : Ideal.Quotient.mk (span {xi p}) (teichmuller p (varpi p)) =
        Ideal.Quotient.mk (span {xi p}) (p : WittVector p (pair p).plus) := by
      rw [Ideal.Quotient.eq]
      have hneg : teichmuller p (varpi p) - (p : WittVector p (pair p).plus) = -(xi p) := by
        simp [xi]
      rw [hneg]
      exact Submodule.neg_mem _ (mem_span_singleton_self _)
    rw [hmk, map_natCast, map_natCast]
  have hp_ne : (p : untilt p (pair p) (span {xi p})) ≠ 0 := by
    rw [← hsp]
    exact (untilt.isPseudoUniformizer_sharp (isPseudoUniformizer_varpi p)).isUnit.ne_zero
  exact ⟨untilt.isPerfectoidTateRing (isPrimitive_xi p),
    untilt.isRingOfIntegralElements_untiltPlus (isPrimitive_xi p),
    untilt.pair_plus (isPrimitive_xi p), hp_ne⟩

/-! ### Discriminating evaluation of `tiltEquiv` on compatible roots -/

-- For compatible roots `ϖ_n = (φ^n)⁻¹ ϖ` in `ℂ_p♭`, the two tilt elements with coordinates
-- `sharp (ϖ_n)` and `sharp (ϖ_{n+1})` have sum sent by `tiltEquiv` to `ϖ_0 + ϖ_1`, while the
-- first element is NOT sent to `ϖ_0 ^ p`.
example :
    letI := untilt.t2Space (isPrimitive_xi p)
    letI := untilt.completeSpace (isPrimitive_xi p)
    letI := untilt.isUniform (isPrimitive_xi p)
    letI : Fact (IsTopologicallyNilpotent (p : untilt p (pair p) (span {xi p}))) :=
      ⟨untilt.isTopologicallyNilpotent_natCast (isPrimitive_xi p)⟩
    letI := untilt.isTateRing_uniformTilt (isPrimitive_xi p)
    let w : ℕ → uniformTilt p ℂ_[p] :=
      fun n ↦ (iterateFrobeniusEquiv (uniformTilt p ℂ_[p]) p n).symm
        (varpi p : uniformTilt p ℂ_[p])
    let x₀ : uniformTilt p (untilt p (pair p) (span {xi p})) :=
      (untilt.tiltEquiv (isPrimitive_xi p)).symm (w 0)
    let x₁ : uniformTilt p (untilt p (pair p) (span {xi p})) :=
      (untilt.tiltEquiv (isPrimitive_xi p)).symm (w 1)
    (∀ n, uniformTilt.coeff p _ n x₀ = untilt.sharp p (pair p) (span {xi p}) (w n)) ∧
      (∀ n, uniformTilt.coeff p _ n x₁ = untilt.sharp p (pair p) (span {xi p}) (w (n + 1))) ∧
      untilt.tiltEquiv (isPrimitive_xi p) (x₀ + x₁) = w 0 + w 1 ∧
      untilt.tiltEquiv (isPrimitive_xi p) x₀ ≠ (w 0) ^ p ∧
      IsHomeomorph (untilt.tiltEquiv (isPrimitive_xi p)) := by
  have := untilt.t2Space (isPrimitive_xi p)
  have := untilt.completeSpace (isPrimitive_xi p)
  have := untilt.isUniform (isPrimitive_xi p)
  have : Fact (IsTopologicallyNilpotent (p : untilt p (pair p) (span {xi p}))) :=
    ⟨untilt.isTopologicallyNilpotent_natCast (isPrimitive_xi p)⟩
  have := untilt.isTateRing_uniformTilt (isPrimitive_xi p)
  intro w x₀ x₁
  have hw0 : w 0 = (varpi p : uniformTilt p ℂ_[p]) := by
    apply (iterateFrobeniusEquiv (uniformTilt p ℂ_[p]) p 0).injective
    rw [RingEquiv.apply_symm_apply]
    simp
  have hx₀ : ∀ n, uniformTilt.coeff p _ n x₀ = untilt.sharp p (pair p) (span {xi p}) (w n) := by
    intro n
    rw [untilt.coeff_tiltEquiv_symm, hw0]
  have hx₁ : ∀ n, uniformTilt.coeff p _ n x₁ =
      untilt.sharp p (pair p) (span {xi p}) (w (n + 1)) := by
    intro n
    rw [untilt.coeff_tiltEquiv_symm]
    congr 1
    apply (iterateFrobeniusEquiv (uniformTilt p ℂ_[p]) p (n + 1)).injective
    rw [RingEquiv.apply_symm_apply]
    change (iterateFrobeniusEquiv (uniformTilt p ℂ_[p]) p n).symm (w 1) ^ p ^ (n + 1) =
      (varpi p : uniformTilt p ℂ_[p])
    rw [pow_succ, pow_mul]
    have hpow : (iterateFrobeniusEquiv (uniformTilt p ℂ_[p]) p n).symm (w 1) ^ p ^ n = w 1 :=
      (iterateFrobeniusEquiv (uniformTilt p ℂ_[p]) p n).apply_symm_apply (w 1)
    rw [hpow]
    have hpow1 : w 1 ^ p ^ 1 = (varpi p : uniformTilt p ℂ_[p]) :=
      (iterateFrobeniusEquiv (uniformTilt p ℂ_[p]) p 1).apply_symm_apply
        (varpi p : uniformTilt p ℂ_[p])
    rwa [pow_one] at hpow1
  have hsum : untilt.tiltEquiv (isPrimitive_xi p) (x₀ + x₁) = w 0 + w 1 := by
    rw [map_add, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hne : untilt.tiltEquiv (isPrimitive_xi p) x₀ ≠ (w 0) ^ p := by
    rw [RingEquiv.apply_symm_apply]
    intro heq
    have hc := congrArg (uniformTilt.coeff p ℂ_[p] 0) heq
    have hnorm : ‖uniformTilt.coeff p ℂ_[p] 0 (w 0)‖ =
        ‖uniformTilt.coeff p ℂ_[p] 0 (w 0)‖ ^ p := by
      rw [← norm_pow, ← map_pow, ← hc]
    have hpu : IsPseudoUniformizer (uniformTilt.coeff p ℂ_[p] 0 (w 0)) := by
      rw [hw0]
      simpa [varpi] using (parameter p).isPseudoUniformizer_root_zero
    obtain ⟨h0, hlt⟩ := isPseudoUniformizer_iff_norm_lt_one.mp hpu
    have hpos : 0 < ‖uniformTilt.coeff p ℂ_[p] 0 (w 0)‖ := norm_pos_iff.mpr h0
    have hpow_lt : ‖uniformTilt.coeff p ℂ_[p] 0 (w 0)‖ ^ p <
        ‖uniformTilt.coeff p ℂ_[p] 0 (w 0)‖ ^ 1 :=
      pow_lt_pow_right_of_lt_one₀ hpos hlt hp.out.one_lt
    rw [pow_one] at hpow_lt
    exact ne_of_gt hpow_lt hnorm
  exact ⟨hx₀, hx₁, hsum, hne, untilt.isHomeomorph_tiltEquiv (isPrimitive_xi p)⟩

/-! ### Fontaine's `θ` (`ker θ = (ξ)`) and almost vanishing of `A° ⧸ A⁺` -/

-- Both `ker_theta_eq` and `ker_fontaineTheta_eq` recover `Ideal.span {ξ}`.
example :
    letI := untilt.t2Space (isPrimitive_xi p)
    letI := untilt.completeSpace (isPrimitive_xi p)
    letI := untilt.isUniform (isPrimitive_xi p)
    letI : Fact (IsTopologicallyNilpotent (p : untilt p (pair p) (span {xi p}))) :=
      ⟨untilt.isTopologicallyNilpotent_natCast (isPrimitive_xi p)⟩
    letI := untilt.isTateRing_uniformTilt (isPrimitive_xi p)
    letI : Nontrivial (untilt p (pair p) (span {xi p})) := nontrivial_untilt_xi p
    letI : Fact ¬IsUnit (p : untiltPlus p (pair p) (span {xi p})) :=
      ⟨(untilt.isRingOfIntegralElements_untiltPlus
        (isPrimitive_xi p)).not_isUnit_natCast_of_isTopologicallyNilpotent p
          (untilt.isTopologicallyNilpotent_natCast (isPrimitive_xi p))⟩
    letI : IsAdicComplete (span {(p : untiltPlus p (pair p) (span {xi p}))})
        (untiltPlus p (pair p) (span {xi p})) :=
      (untilt.isRingOfIntegralElements_untiltPlus (isPrimitive_xi p)).isAdicComplete_span_natCast p
        (untilt.isTopologicallyNilpotent_natCast (isPrimitive_xi p))
    (RingHom.ker (uniformTilt.theta p
        (untilt.isRingOfIntegralElements_untiltPlus (isPrimitive_xi p)))).map
        (WittVector.map (untilt.tiltPlusEquiv (isPrimitive_xi p)).toRingHom) = span {xi p} ∧
      (RingHom.ker (WittVector.fontaineTheta (untiltPlus p (pair p) (span {xi p})) p)).map
        (WittVector.map (untilt.preTiltEquiv (isPrimitive_xi p)).toRingHom) = span {xi p} := by
  have := untilt.t2Space (isPrimitive_xi p)
  have := untilt.completeSpace (isPrimitive_xi p)
  have := untilt.isUniform (isPrimitive_xi p)
  have : Fact (IsTopologicallyNilpotent (p : untilt p (pair p) (span {xi p}))) :=
    ⟨untilt.isTopologicallyNilpotent_natCast (isPrimitive_xi p)⟩
  have := untilt.isTateRing_uniformTilt (isPrimitive_xi p)
  have : Nontrivial (untilt p (pair p) (span {xi p})) := nontrivial_untilt_xi p
  have : Fact ¬IsUnit (p : untiltPlus p (pair p) (span {xi p})) :=
    ⟨(untilt.isRingOfIntegralElements_untiltPlus
      (isPrimitive_xi p)).not_isUnit_natCast_of_isTopologicallyNilpotent p
        (untilt.isTopologicallyNilpotent_natCast (isPrimitive_xi p))⟩
  have : IsAdicComplete (span {(p : untiltPlus p (pair p) (span {xi p}))})
      (untiltPlus p (pair p) (span {xi p})) :=
    (untilt.isRingOfIntegralElements_untiltPlus (isPrimitive_xi p)).isAdicComplete_span_natCast p
      (untilt.isTopologicallyNilpotent_natCast (isPrimitive_xi p))
  exact ⟨untilt.ker_theta_eq (isPrimitive_xi p), untilt.ker_fontaineTheta_eq (isPrimitive_xi p)⟩

-- `A° ⧸ A⁺` is almost zero for the almost setup `(A⁺, A°°)`.
example :
    letI : Fact (1 < p) := ⟨hp.out.one_lt⟩
    letI := untilt.t2Space (isPrimitive_xi p)
    letI := untilt.completeSpace (isPrimitive_xi p)
    letI := untilt.isPerfectoidTateRing (isPrimitive_xi p)
    letI : Nonempty (PseudoUniformizerRoots p (untilt p (pair p) (span {xi p}))) :=
      PseudoUniformizerRoots.nonempty
    letI : Algebra (untiltPlus p (pair p) (span {xi p}))
        (powerBoundedSubring (untilt p (pair p) (span {xi p}))) :=
      (Subring.inclusion (untilt.isRingOfIntegralElements_untiltPlus
        (isPrimitive_xi p)).le_powerBoundedSubring).toAlgebra
    letI : IsScalarTower (untiltPlus p (pair p) (span {xi p}))
        (powerBoundedSubring (untilt p (pair p) (span {xi p})))
        (untilt p (pair p) (span {xi p})) :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    (almostSetupPlus p (untilt p (pair p) (span {xi p}))
        (untilt.isRingOfIntegralElements_untiltPlus (isPrimitive_xi p))).IsAlmostZero
      (powerBoundedSubring (untilt p (pair p) (span {xi p})) ⧸
        LinearMap.range (Algebra.linearMap (untiltPlus p (pair p) (span {xi p}))
          (powerBoundedSubring (untilt p (pair p) (span {xi p}))))) := by
  let : Algebra (untiltPlus p (pair p) (span {xi p}))
      (powerBoundedSubring (untilt p (pair p) (span {xi p}))) :=
    (Subring.inclusion (untilt.isRingOfIntegralElements_untiltPlus
      (isPrimitive_xi p)).le_powerBoundedSubring).toAlgebra
  have : IsScalarTower (untiltPlus p (pair p) (span {xi p}))
      (powerBoundedSubring (untilt p (pair p) (span {xi p})))
      (untilt p (pair p) (span {xi p})) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact untilt.isAlmostZero_powerBounded_quotient (isPrimitive_xi p)

end TauCeti.Examples.PrimitiveUntiltPerfectoid
