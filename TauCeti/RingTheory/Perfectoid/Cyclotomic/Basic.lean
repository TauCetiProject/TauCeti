/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.RingTheory.Perfectoid.Pair
public import TauCeti.RingTheory.Perfectoid.ShiftedFontaineTheta
public import TauCeti.RingTheory.WittVector.Cyclotomic.Level

import TauCeti.RingTheory.Perfection

/-!
# The cyclotomic generator of the kernel of Fontaine's map

Let `A` be a `p`-adically complete ring with tilt `A♭ = PreTilt A p`, let `ε ∈ A♭`, and let
`ζ = (ε ^ (1 / p))♯ ∈ A` be the untilt of its `p`-th root. Suppose that
`1 + ζ + ⋯ + ζ ^ (p - 1) = 0`; this holds whenever `ζ` is a primitive `p`-th root of unity
(`IsPrimitiveRoot.geom_sum_eq_zero`). In the main example `A = O_C` is the ring of
integers of a complete algebraically closed extension `C` of `ℚ_p` and
`ε = (1, ζ_p, ζ_{p²}, …)`.

Then `ε♯ = ζ ^ p = 1`, so Fontaine's map `θ : W(A♭) → A` sends the cyclotomic period elements
`μ = [ε] - 1`, `ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j` and `ξ' = φ(ξ)` (`TauCeti.WittVector.cyclotomicMu`,
`TauCeti.WittVector.cyclotomicXi`, `TauCeti.WittVector.cyclotomicXiTilde`) to `0`, `0` and `p`.
Moreover `ε - 1` lies in the Jacobson radical of `A♭`, because its zeroth coordinate in `A ⧸ p`
vanishes, so `ξ` is distinguished. When `A` is integral perfectoid, for instance in the regular
`π`-adic sense of `TauCeti.Perfectoid.IsIntegralPerfectoid.of_bijective_frobeniusModPow` or when `A`
is a ring of integral elements of a perfectoid Tate ring, a distinguished element of `ker θ`
generates it (by
`TauCeti.Perfectoid.IsIntegralPerfectoid.ker_fontaineTheta_eq_span_iff_isDistinguished`), so

* `ker θ = (ξ)`, and
* `ker θ' = (ξ')`, where `θ' = θ ∘ φ⁻¹` is the Frobenius-shifted Fontaine map
  (`TauCeti.WittVector.fontaineThetaTilde`).

The shifted map sends `μ` to `ζ - 1` rather than to `0`, and `ξ'` to `0` rather than to `p`.

## Main results

* `PreTilt.untilt_eq_one_of_isPrimitiveRoot`, `PreTilt.ne_one_of_isPrimitiveRoot`: if `ζ` is a
  primitive `p`-th root of unity, then `ε♯ = 1` and `ε ≠ 1`.
* `TauCeti.WittVector.fontaineTheta_cyclotomicMu_eq_zero`,
  `TauCeti.WittVector.fontaineTheta_cyclotomicXi_eq_zero`,
  `TauCeti.WittVector.fontaineTheta_cyclotomicXiTilde_eq_natCast`,
  `TauCeti.WittVector.fontaineTheta_frobeniusEquiv_symm_cyclotomicMu_ne_zero`,
  `TauCeti.WittVector.fontaineTheta_iterate_frobeniusEquiv_cyclotomicMu_eq_zero`,
  `TauCeti.WittVector.fontaineTheta_iterate_frobeniusEquiv_succ_cyclotomicXi`,
  `TauCeti.WittVector.fontaineTheta_iterate_frobeniusEquiv_cyclotomicXiLevel_eq_zero`: values of
  `θ` and `θ ∘ φʲ` on the cyclotomic period elements.
* `TauCeti.WittVector.fontaineThetaTilde_cyclotomicMu`,
  `TauCeti.WittVector.fontaineThetaTilde_cyclotomicXiTilde`,
  `TauCeti.WittVector.fontaineThetaTilde_cyclotomicXiTilde_eq_zero`: values of `θ'` on `μ` and
  `ξ'`.
* `TauCeti.WittVector.isDistinguished_cyclotomicXi_of_untilt_eq_one`: `ξ` is distinguished.
* `TauCeti.WittVector.ker_fontaineTheta_eq_span_cyclotomicXi`,
  `TauCeti.WittVector.ker_fontaineThetaTilde_eq_span_cyclotomicXiTilde`:
  `ker θ = (ξ)` and `ker θ' = (ξ')` in the regular `π`-adic setting.
* `TauCeti.Huber.IsRingOfIntegralElements.ker_fontaineTheta_eq_span_cyclotomicXi`,
  `TauCeti.Huber.IsRingOfIntegralElements.ker_fontaineTheta_eq_span_iff_associated_cyclotomicXi`,
  and `TauCeti.Huber.IsRingOfIntegralElements.ker_fontaineThetaTilde_eq_span_cyclotomicXiTilde`:
  the same for a ring of integral elements of a perfectoid Tate ring, such as `O_C`.

## Provenance

`TauCeti.WittVector.fontaineTheta_frobeniusEquiv_symm_cyclotomicMu_ne_zero` is adapted from
`New.Period.theta_tau_ne_zero` in `src/Lib/PadicHodge/PeriodRings/Ainf.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Example 3.16 and
  Proposition 3.17.
-/

public section

open Ideal _root_.WittVector
open scoped nonZeroDivisors

namespace PreTilt

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [CommRing A] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (span {(p : A)}) A]

/-- If the sharp of `ε ^ (1 / p)` is a primitive `p`-th root of unity, then `ε♯ = 1`. -/
theorem untilt_eq_one_of_isPrimitiveRoot (ε : PreTilt A p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    ε.untilt = 1 := by
  rw [← untilt_iterate_frobeniusEquiv_symm_pow ε 1, pow_one, Function.iterate_one,
    hε.pow_eq_one]

/-- If the sharp of `ε ^ (1 / p)` is a primitive `p`-th root of unity, then `ε ≠ 1`. -/
theorem ne_one_of_isPrimitiveRoot (ε : PreTilt A p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    ε ≠ 1 := by
  rintro rfl
  exact hε.ne_one hp.out.one_lt (by rw [map_one, map_one])

end PreTilt

namespace TauCeti.WittVector

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [CommRing A] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (span {(p : A)}) A]

local notation "A♭" => PreTilt A p

/-- Fontaine's map sends `μ = [ε] - 1` to `ε♯ - 1`. -/
@[simp]
theorem fontaineTheta_cyclotomicMu (ε : A♭) :
    fontaineTheta A p (cyclotomicMu p ε) = ε.untilt - 1 := by
  simp [cyclotomicMu_def, fontaineTheta_teichmuller]

/-- Fontaine's map sends `ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j` to `∑_{j < p} ζ ^ j`, where
`ζ = (ε ^ (1 / p))♯`. -/
@[simp]
theorem fontaineTheta_cyclotomicXi (ε : A♭) :
    fontaineTheta A p (cyclotomicXi p ε) =
      ∑ j ∈ Finset.range p, ((_root_.frobeniusEquiv A♭ p).symm ε).untilt ^ j := by
  simp [cyclotomicXi_def, fontaineTheta_teichmuller]

/-- Fontaine's map sends `ξ' = ∑_{j < p} [ε] ^ j` to `∑_{j < p} (ε♯) ^ j`. -/
@[simp]
theorem fontaineTheta_cyclotomicXiTilde (ε : A♭) :
    fontaineTheta A p (cyclotomicXiTilde p ε) = ∑ j ∈ Finset.range p, ε.untilt ^ j := by
  simp [cyclotomicXiTilde_eq_sum, fontaineTheta_teichmuller]

/-- The Frobenius-shifted Fontaine map sends `μ = [ε] - 1` to `ζ - 1`, where
`ζ = (ε ^ (1 / p))♯`. -/
@[simp]
theorem fontaineThetaTilde_cyclotomicMu (ε : A♭) :
    fontaineThetaTilde A p (cyclotomicMu p ε) =
      ((_root_.frobeniusEquiv A♭ p).symm ε).untilt - 1 := by
  simp [cyclotomicMu_def]

/-- The Frobenius-shifted Fontaine map sends `ξ' = φ(ξ)` to `∑_{j < p} ζ ^ j`, where
`ζ = (ε ^ (1 / p))♯`. -/
@[simp]
theorem fontaineThetaTilde_cyclotomicXiTilde (ε : A♭) :
    fontaineThetaTilde A p (cyclotomicXiTilde p ε) =
      ∑ j ∈ Finset.range p, ((_root_.frobeniusEquiv A♭ p).symm ε).untilt ^ j := by
  rw [← frobenius_cyclotomicXi, fontaineThetaTilde_frobenius, fontaineTheta_cyclotomicXi]

/-- If `ε♯ = 1`, then Fontaine's map kills `μ = [ε] - 1`. -/
@[simp high]
theorem fontaineTheta_cyclotomicMu_eq_zero {ε : A♭} (hε : ε.untilt = 1) :
    fontaineTheta A p (cyclotomicMu p ε) = 0 := by
  rw [fontaineTheta_cyclotomicMu, hε, sub_self]

/-- Over a domain, if `(ε ^ (1 / p))♯` is a primitive `p`-th root of unity, then Fontaine's map
kills `ξ`. -/
@[simp high]
theorem fontaineTheta_cyclotomicXi_eq_zero [IsDomain A] {ε : A♭}
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv A♭ p).symm ε)) p) :
    fontaineTheta A p (cyclotomicXi p ε) = 0 := by
  rw [fontaineTheta_cyclotomicXi]
  exact hε.geom_sum_eq_zero hp.out.one_lt

/-- If `ε♯ = 1`, then Fontaine's map sends `ξ' = φ(ξ)` to `p`. -/
theorem fontaineTheta_cyclotomicXiTilde_eq_natCast {ε : A♭} (hε : ε.untilt = 1) :
    fontaineTheta A p (cyclotomicXiTilde p ε) = p := by
  simp [hε]

/-- Over a domain, if `(ε ^ (1 / p))♯` is a primitive `p`-th root of unity, then the
Frobenius-shifted Fontaine map kills `ξ'`. -/
@[simp high]
theorem fontaineThetaTilde_cyclotomicXiTilde_eq_zero [IsDomain A] {ε : A♭}
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv A♭ p).symm ε)) p) :
    fontaineThetaTilde A p (cyclotomicXiTilde p ε) = 0 := by
  rw [← frobenius_cyclotomicXi, fontaineThetaTilde_frobenius, fontaineTheta_cyclotomicXi_eq_zero hε]

/-- If the sharp `ζ` of `ε ^ (1 / p)` is not `1`, then Fontaine's map does not kill
`φ⁻¹(μ) = [ε ^ (1 / p)] - 1`. -/
theorem fontaineTheta_frobeniusEquiv_symm_cyclotomicMu_ne_zero {ε : A♭}
    (hε : ((_root_.frobeniusEquiv A♭ p).symm ε).untilt ≠ 1) :
    fontaineTheta A p ((frobeniusEquiv p A♭).symm (cyclotomicMu p ε)) ≠ 0 := by
  rw [← fontaineThetaTilde_apply, fontaineThetaTilde_cyclotomicMu, sub_ne_zero]
  exact hε

/-- If `ε♯ = 1`, then Fontaine's map kills every Frobenius iterate `φʲ(μ)`. -/
theorem fontaineTheta_iterate_frobeniusEquiv_cyclotomicMu_eq_zero {ε : A♭} (hε : ε.untilt = 1)
    (j : ℕ) : fontaineTheta A p (((frobeniusEquiv p A♭)^[j]) (cyclotomicMu p ε)) = 0 := by
  rw [iterate_frobeniusEquiv_cyclotomicMu]
  exact fontaineTheta_cyclotomicMu_eq_zero (by rw [map_pow, hε, one_pow])

/-- If `ε♯ = 1`, then Fontaine's map sends `φʲ⁺¹(ξ)` to `p`. -/
theorem fontaineTheta_iterate_frobeniusEquiv_succ_cyclotomicXi {ε : A♭} (hε : ε.untilt = 1)
    (j : ℕ) : fontaineTheta A p (((frobeniusEquiv p A♭)^[j + 1]) (cyclotomicXi p ε)) = p := by
  rw [← frobeniusEquiv_symm_cyclotomicXiTilde, Function.iterate_succ_apply,
    RingEquiv.apply_symm_apply, iterate_frobeniusEquiv_cyclotomicXiTilde]
  exact fontaineTheta_cyclotomicXiTilde_eq_natCast (by rw [map_pow, hε, one_pow])

/-- If Fontaine's map kills `ξ`, then it kills `φʲ(ξ_r)` for every `j < r`. -/
theorem fontaineTheta_iterate_frobeniusEquiv_cyclotomicXiLevel_eq_zero {ε : A♭}
    (hξ : fontaineTheta A p (cyclotomicXi p ε) = 0) {j r : ℕ} (hj : j < r) :
    fontaineTheta A p (((frobeniusEquiv p A♭)^[j]) (cyclotomicXiLevel p ε r)) = 0 := by
  obtain ⟨c, hc⟩ := cyclotomicXi_dvd_iterate_frobeniusEquiv_cyclotomicXiLevel p ε hj
  rw [hc, map_mul, hξ, zero_mul]

/-- **`ξ` is distinguished** (Bhatt–Morrow–Scholze, Example 3.16). If `ε♯ = 1`, then the zeroth
coordinate of `ε - 1` in `A ⧸ p` vanishes; hence `ε - 1` lies in the Jacobson radical of `A♭` and
`ξ` is distinguished. -/
theorem isDistinguished_cyclotomicXi_of_untilt_eq_one {ε : A♭} (hε : ε.untilt = 1) :
    (cyclotomicXi p ε).IsDistinguished :=
  isDistinguished_cyclotomicXi p (PreTilt.sub_one_mem_jacobson_of_untilt_eq_one hε)

/-- If `ζ = (ε ^ (1 / p))♯` satisfies `∑_{j < p} ζ ^ j = 0`, then `ξ` lies in the kernel of
Fontaine's map. -/
theorem cyclotomicXi_mem_ker_fontaineTheta {ε : A♭}
    (hε : ∑ j ∈ Finset.range p, ((_root_.frobeniusEquiv A♭ p).symm ε).untilt ^ j = 0) :
    cyclotomicXi p ε ∈ RingHom.ker (fontaineTheta A p) := by
  rw [RingHom.mem_ker, fontaineTheta_cyclotomicXi, hε]

/-- **The cyclotomic generator of `ker θ`** (Bhatt–Morrow–Scholze, Example 3.16 and
Proposition 3.17). Let `A` be `π`-adically complete for a nonzerodivisor `π` with `π ^ p ∣ p` and
bijective relative Frobenius `A ⧸ (π) → A ⧸ (π ^ p)`, and let `ε ∈ A♭` be such that
`ζ = (ε ^ (1 / p))♯` satisfies `∑_{j < p} ζ ^ j = 0` (for instance, `ζ` is a primitive `p`-th root
of unity). Then the kernel of Fontaine's map `θ : W(A♭) → A` is generated by
`ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j`. -/
theorem ker_fontaineTheta_eq_span_cyclotomicXi {π : A} {hdvd : π ^ p ∣ (p : A)}
    [IsAdicComplete (span {π}) A] (hreg : π ∈ A⁰)
    (hbij : Function.Bijective (TauCeti.frobeniusModPow p hdvd)) {ε : A♭}
    (hε : ∑ j ∈ Finset.range p, ((_root_.frobeniusEquiv A♭ p).symm ε).untilt ^ j = 0) :
    RingHom.ker (fontaineTheta A p) = span {cyclotomicXi p ε} := by
  have := Perfectoid.IsIntegralPerfectoid.of_bijective_frobeniusModPow hreg hbij
  exact (Perfectoid.IsIntegralPerfectoid.ker_fontaineTheta_eq_span_iff_isDistinguished
    (cyclotomicXi_mem_ker_fontaineTheta hε)).mpr
    (isDistinguished_cyclotomicXi_of_untilt_eq_one (PreTilt.untilt_eq_one_of_geom_sum_eq_zero hε))

/-- **The cyclotomic generator of the kernel of `θ'`.** Under the hypotheses of
`ker_fontaineTheta_eq_span_cyclotomicXi`, the kernel of the Frobenius-shifted Fontaine map
`θ' = θ ∘ φ⁻¹ : W(A♭) → A` is generated by `ξ' = φ(ξ) = ∑_{j < p} [ε] ^ j`. -/
theorem ker_fontaineThetaTilde_eq_span_cyclotomicXiTilde {π : A}
    {hdvd : π ^ p ∣ (p : A)} [IsAdicComplete (span {π}) A] (hreg : π ∈ A⁰)
    (hbij : Function.Bijective (TauCeti.frobeniusModPow p hdvd)) {ε : A♭}
    (hε : ∑ j ∈ Finset.range p, ((_root_.frobeniusEquiv A♭ p).symm ε).untilt ^ j = 0) :
    RingHom.ker (fontaineThetaTilde A p) = span {cyclotomicXiTilde p ε} := by
  rw [← frobenius_cyclotomicXi]
  exact ker_fontaineThetaTilde_eq_span_frobenius
    (ker_fontaineTheta_eq_span_cyclotomicXi hreg hbij hε)

end TauCeti.WittVector

namespace TauCeti.Huber.IsRingOfIntegralElements

open TauCeti.Perfectoid TauCeti.WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R]
  [IsPerfectoidTateRing p R] {Rplus : Subring R} [Fact ¬IsUnit (p : Rplus)]
  [IsAdicComplete (span {(p : Rplus)}) Rplus]

/-- **The cyclotomic generator of `ker θ` for a perfectoid Tate ring** (Bhatt–Morrow–Scholze,
Example 3.16 and Proposition 3.17). Let `R⁺` be a ring of integral elements of a perfectoid Tate
ring, for instance `O_C` for a complete algebraically closed extension `C` of `ℚ_p`, and let
`ε ∈ R⁺♭` be such that `ζ = (ε ^ (1 / p))♯` satisfies `∑_{j < p} ζ ^ j = 0`. Then the kernel of
Fontaine's map `θ : W(R⁺♭) → R⁺` is generated by `ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j`. -/
theorem ker_fontaineTheta_eq_span_cyclotomicXi (hplus : IsRingOfIntegralElements Rplus)
    {ε : PreTilt Rplus p}
    (hε : ∑ j ∈ Finset.range p,
      ((_root_.frobeniusEquiv (PreTilt Rplus p) p).symm ε).untilt ^ j = 0) :
    RingHom.ker (fontaineTheta Rplus p) = span {cyclotomicXi p ε} :=
  (hplus.ker_fontaineTheta_eq_span_iff_isDistinguished (cyclotomicXi_mem_ker_fontaineTheta hε)).mpr
    (isDistinguished_cyclotomicXi_of_untilt_eq_one (PreTilt.untilt_eq_one_of_geom_sum_eq_zero hε))

/-- An element of `W(R⁺♭)` generates `ker θ` if and only if it is associated to `ξ`. -/
theorem ker_fontaineTheta_eq_span_iff_associated_cyclotomicXi [IsDomain Rplus]
    (hplus : IsRingOfIntegralElements Rplus) {ε : PreTilt Rplus p}
    (hε : ∑ j ∈ Finset.range p,
      ((_root_.frobeniusEquiv (PreTilt Rplus p) p).symm ε).untilt ^ j = 0)
    {y : _root_.WittVector p (PreTilt Rplus p)} :
    RingHom.ker (fontaineTheta Rplus p) = span {y} ↔ Associated y (cyclotomicXi p ε) := by
  rw [hplus.ker_fontaineTheta_eq_span_cyclotomicXi hε, eq_comm,
    Ideal.span_singleton_eq_span_singleton]

/-- **The cyclotomic generator of the kernel of `θ'` for a perfectoid Tate ring.** Under the
hypotheses of `ker_fontaineTheta_eq_span_cyclotomicXi`, the kernel of the Frobenius-shifted
Fontaine map `θ' = θ ∘ φ⁻¹ : W(R⁺♭) → R⁺` is generated by `ξ' = φ(ξ) = ∑_{j < p} [ε] ^ j`. -/
theorem ker_fontaineThetaTilde_eq_span_cyclotomicXiTilde
    (hplus : IsRingOfIntegralElements Rplus) {ε : PreTilt Rplus p}
    (hε : ∑ j ∈ Finset.range p,
      ((_root_.frobeniusEquiv (PreTilt Rplus p) p).symm ε).untilt ^ j = 0) :
    RingHom.ker (fontaineThetaTilde Rplus p) = span {cyclotomicXiTilde p ε} := by
  rw [← frobenius_cyclotomicXi]
  exact ker_fontaineThetaTilde_eq_span_frobenius (hplus.ker_fontaineTheta_eq_span_cyclotomicXi hε)

end TauCeti.Huber.IsRingOfIntegralElements
