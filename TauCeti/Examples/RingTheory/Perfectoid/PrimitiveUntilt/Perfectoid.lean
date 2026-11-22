/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RingTheory.Perfectoid.PrimitiveUntilt.Basic
public import TauCeti.RingTheory.Perfectoid.AlmostSetup
public import TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Pair
public import TauCeti.RingTheory.Perfectoid.PseudoUniformizerRoots.Existence

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
  - `almostSetupPlus_isAlmostZero_powerBounded_quotient` verifies that `A° ⧸ A⁺` is almost zero for
    `(A⁺, A°°)`.
-/

public section

open Filter Ideal Topology TauCeti.Examples.PrimitiveUntilt TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples.PrimitiveUntiltPerfectoid

variable (p : ℕ) [hp : Fact p.Prime]

local instance : Fact (xi p).IsPrimitive := ⟨isPrimitive_xi p⟩

/-! ### Zero characteristic-`p` base -/

-- Over a zero characteristic-`p` base, the tilt of any primitive untilt is zero and `tiltEquiv`
-- sends every element to `0`.
example {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
    [IsTateRing R] [CompleteSpace R] [T2Space R] [CharP R p] [PerfectRing R p] [Subsingleton R]
    (P : Pair R) {ξ : WittVector p P.plus} [Fact ξ.IsPrimitive] :
    ∀ x, untilt.tiltEquiv (p := p) (P := P) (ξ := ξ) x = 0 := fun _ ↦ Subsingleton.elim _ _

/-! ### Mixed-characteristic perfectoid pair `(A, A⁺)` along `ξ = p - [ϖ]` -/

-- The untilt along `ξ = p - [ϖ]` is a mixed-characteristic perfectoid Huber pair: `p` is a unit
-- (hence `p ≠ 0`), unlike the characteristic-`p` untilt along `(p)`.
example :
    IsPerfectoidTateRing p (untilt p (pair p) (span {xi p})) ∧
      IsRingOfIntegralElements (untiltPlus p (pair p) (span {xi p})) ∧
      (untilt.pair (isPrimitive_xi p)).plus = untiltPlus p (pair p) (span {xi p}) ∧
      (p : untilt p (pair p) (span {xi p})) ≠ 0 := by
  have : Nontrivial (untilt p (pair p) (span {xi p})) := nontrivial_untilt_xi p
  have hp_ne : (p : untilt p (pair p) (span {xi p})) ≠ 0 := by
    rw [← sharp_varpi p]
    exact (untilt.isPseudoUniformizer_sharp (isPseudoUniformizer_varpi p)).isUnit.ne_zero
  exact ⟨untilt.isPerfectoidTateRing,
    untilt.isRingOfIntegralElements_untiltPlus (isPrimitive_xi p),
    untilt.pair_plus (isPrimitive_xi p), hp_ne⟩

/-! ### Discriminating evaluation of `tiltEquiv` on compatible roots -/

-- For compatible roots `ϖ_n = (φ^n)⁻¹ ϖ` in `ℂ_p♭`, the two tilt elements with coordinates
-- `sharp (ϖ_n)` and `sharp (ϖ_{n+1})` have sum sent by `tiltEquiv` to `ϖ_0 + ϖ_1`, while the
-- first element is NOT sent to `ϖ_0 ^ p`.
example :
    let w : ℕ → uniformTilt p ℂ_[p] :=
      fun n ↦ (iterateFrobeniusEquiv (uniformTilt p ℂ_[p]) p n).symm
        (varpi p : uniformTilt p ℂ_[p])
    let x₀ : uniformTilt p (untilt p (pair p) (span {xi p})) :=
      (untilt.tiltEquiv (p := p) (P := pair p) (ξ := xi p)).symm (w 0)
    let x₁ : uniformTilt p (untilt p (pair p) (span {xi p})) :=
      (untilt.tiltEquiv (p := p) (P := pair p) (ξ := xi p)).symm (w 1)
    (∀ n, uniformTilt.coeff p _ n x₀ = untilt.sharp p (pair p) (span {xi p}) (w n)) ∧
      (∀ n, uniformTilt.coeff p _ n x₁ = untilt.sharp p (pair p) (span {xi p}) (w (n + 1))) ∧
      untilt.tiltEquiv (p := p) (P := pair p) (ξ := xi p) (x₀ + x₁) = w 0 + w 1 ∧
      untilt.tiltEquiv (p := p) (P := pair p) (ξ := xi p) x₀ ≠ (w 0) ^ p ∧
      IsHomeomorph (untilt.tiltEquiv (p := p) (P := pair p) (ξ := xi p)) := by
  intro w x₀ x₁
  have hw0 : w 0 = (varpi p : uniformTilt p ℂ_[p]) := by simp [w]
  have hx₀ : ∀ n, uniformTilt.coeff p _ n x₀ = untilt.sharp p (pair p) (span {xi p}) (w n) := by
    intro n
    rw [untilt.coeff_tiltEquiv_symm, hw0]
  have hx₁ : ∀ n, uniformTilt.coeff p _ n x₁ =
      untilt.sharp p (pair p) (span {xi p}) (w (n + 1)) := by
    intro n
    rw [untilt.coeff_tiltEquiv_symm]
    congr 1
    apply (iterateFrobeniusEquiv (uniformTilt p ℂ_[p]) p (n + 1)).injective
    rw [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_def, pow_succ, pow_mul,
      iterateFrobeniusEquiv_symm_pow]
    simp [w]
  have hsum : untilt.tiltEquiv (p := p) (P := pair p) (ξ := xi p) (x₀ + x₁) = w 0 + w 1 := by
    rw [map_add, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hne : untilt.tiltEquiv (p := p) (P := pair p) (ξ := xi p) x₀ ≠ (w 0) ^ p := by
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
  exact ⟨hx₀, hx₁, hsum, hne, untilt.isHomeomorph_tiltEquiv⟩

/-! ### Fontaine's `θ` (`ker θ = (ξ)`) and almost vanishing of `A° ⧸ A⁺` -/

section

local instance : Nontrivial (untilt p (pair p) (span {xi p})) := nontrivial_untilt_xi p

local instance : Fact ¬IsUnit (p : untiltPlus p (pair p) (span {xi p})) :=
  ⟨(untilt.isRingOfIntegralElements_untiltPlus
    (isPrimitive_xi p)).not_isUnit_natCast_of_isTopologicallyNilpotent p
      (untilt.isTopologicallyNilpotent_natCast (isPrimitive_xi p))⟩

local instance : IsAdicComplete (span {(p : untiltPlus p (pair p) (span {xi p}))})
    (untiltPlus p (pair p) (span {xi p})) :=
  (untilt.isRingOfIntegralElements_untiltPlus (isPrimitive_xi p)).isAdicComplete_span_natCast p
    (untilt.isTopologicallyNilpotent_natCast (isPrimitive_xi p))

local instance : Fact (1 < p) := ⟨hp.out.one_lt⟩

local instance : IsPerfectoidTateRing p (untilt p (pair p) (span {xi p})) :=
  untilt.isPerfectoidTateRing

local instance : Nonempty (PseudoUniformizerRoots p (untilt p (pair p) (span {xi p}))) :=
  PseudoUniformizerRoots.nonempty

/-- Local `A⁺`-algebra structure on `A°` for the `almostSetupPlus` example. -/
noncomputable local instance : Algebra (untiltPlus p (pair p) (span {xi p}))
    (powerBoundedSubring (untilt p (pair p) (span {xi p}))) :=
  (Subring.inclusion (untilt.isRingOfIntegralElements_untiltPlus
    (isPrimitive_xi p)).le_powerBoundedSubring).toAlgebra

local instance : IsScalarTower (untiltPlus p (pair p) (span {xi p}))
    (powerBoundedSubring (untilt p (pair p) (span {xi p})))
    (untilt p (pair p) (span {xi p})) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

-- Both `ker_theta_eq` and `ker_fontaineTheta_eq` recover `Ideal.span {ξ}`.
example :
    (RingHom.ker (uniformTilt.theta p
        (untilt.isRingOfIntegralElements_untiltPlus (isPrimitive_xi p)))).map
        (WittVector.map (untilt.tiltPlusEquiv (p := p) (P := pair p) (ξ := xi p)).toRingHom) =
        span {xi p} ∧
      (RingHom.ker (WittVector.fontaineTheta (untiltPlus p (pair p) (span {xi p})) p)).map
        (WittVector.map (untilt.preTiltEquiv (p := p) (P := pair p) (ξ := xi p)).toRingHom) =
        span {xi p} :=
  ⟨untilt.ker_theta_eq, untilt.ker_fontaineTheta_eq⟩

-- `A° ⧸ A⁺` is almost zero for the almost setup `(A⁺, A°°)`.
example :
    (almostSetupPlus p (untilt p (pair p) (span {xi p}))
        (untilt.isRingOfIntegralElements_untiltPlus (isPrimitive_xi p))).IsAlmostZero
      (powerBoundedSubring (untilt p (pair p) (span {xi p})) ⧸
        LinearMap.range (Algebra.linearMap (untiltPlus p (pair p) (span {xi p}))
          (powerBoundedSubring (untilt p (pair p) (span {xi p}))))) :=
  almostSetupPlus_isAlmostZero_powerBounded_quotient
    (untilt.isRingOfIntegralElements_untiltPlus (isPrimitive_xi p))

end

end TauCeti.Examples.PrimitiveUntiltPerfectoid
