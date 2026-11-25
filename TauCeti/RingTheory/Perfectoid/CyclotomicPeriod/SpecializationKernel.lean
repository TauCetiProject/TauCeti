/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.CyclotomicPeriod.Level
public import TauCeti.RingTheory.Perfectoid.PreTilt.ValuationRing

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import TauCeti.RingTheory.WittVector.Complete

/-!
# The infinite Witt specialization kernel

Let `C` be a complete algebraically closed nonarchimedean field of residue characteristic `p`,
with valuation ring `O_C`, tilt `O_C♭` and `A_inf = W(O_C♭)`. Fix `ε ∈ O_C♭` such that the sharp
of `ε ^ (1 / p)` is a primitive `p`-th root of unity, and let `μ = [ε] - 1` and
`ξ_r = ∏_{j < r} φ^(-j)(ξ)` be the cyclotomic periods. We prove that the ideals `(ξ_r)`,
`r ≥ 1`, intersect in `(μ)`:

`⋂_{r ≥ 1} (ξ_r) = (μ)`.

This is the kernel computation in Lemma 3.23 of Bhatt–Morrow–Scholze. Since `ξ_r` generates the
kernel of `θ_r`, the intersection is the kernel of `θ_∞ : A_inf → W(O_C)`.

Instead of the limit argument of the reference, we characterize `(μ)` directly: `a ∈ (μ)` if and
only if `θ(φ^j(a)) = 0` for every `j ≥ 0`. The ideal `I` of such `a` contains `μ` and is
saturated for `p`. Its zeroth Witt coordinates are all divisible by that of `μ`: otherwise
`μ₀ = a₀ * c` for some `a ∈ I` and a nonunit `c ∈ O_C♭`, and writing `a = ξ * b` (Fontaine's
kernel is `(ξ)`) shows that `φ(b) ∈ I` with `μ₀ = φ(b)₀ * c ^ p`. Iterating, every power of `c`
divides `μ₀ ≠ 0`, which is impossible in the rank-one valuation ring `O_C♭`. Then
`WittVector.eq_span_singleton_of_coeff_zero_dvd` gives `I = (μ)`. Finally, `a ∈ (ξ_(j+1))`
forces `θ(φ^j(a)) = 0`, because `ξ` divides `φ^j(ξ_(j+1))`.

As a consequence the ideal `(μ)` does not depend on the choice of `ε`.

## Main results

* `PreTilt.fontaineTheta_iterate_frobeniusEquiv_xiLevel`: `θ(φ^j(ξ_r)) = 0` for `j < r`.
* `PreTilt.mu_dvd_of_forall_fontaineTheta_iterate_eq_zero`: if `θ(φ^j(a)) = 0` for all `j`,
  then `μ ∣ a`.
* `PreTilt.mem_span_mu_iff`: `a ∈ (μ)` if and only if `θ(φ^j(a)) = 0` for all `j`.
* `PreTilt.span_mu_eq_span_mu`: the ideal `(μ)` is independent of `ε`.
* `PreTilt.iInf_span_xiLevel_eq_span_mu`: `⋂_{r ≥ 1} (ξ_r) = (μ)`.

## Provenance

The divisibility criterion `PreTilt.mu_dvd_of_forall_fontaineTheta_iterate_eq_zero` and the
coordinate argument behind it are adapted from `New.Period.mu_dvd_of_theta_frobEnd`,
`New.Period.Witt.dvd_of_mem_of_constantCoeff_dvd` and the auxiliary
`pow_pow_dvd_constantCoeff_mu_of_eq_mul` in `src/Lib/PadicHodge/PeriodRings/Ainf.lean` of
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), where
they are proved for `C = ℂ_p` with a fixed compatible system of roots of unity.

## References

* Bhatt, Morrow and Scholze, *Integral p-adic Hodge theory*, arXiv:1602.03148v3, Lemma 3.23.
-/

public section

namespace PreTilt

open TauCeti.Perfectoid _root_.WittVector

section FontaineValues

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [Fact ¬IsUnit (p : A)]
  [IsAdicComplete (Ideal.span {(p : A)}) A]

/-- If the sharp of `ε ^ (1 / p)` is a primitive `p`-th root of unity, then `ε♯ = 1`. -/
theorem untilt_eq_one_of_isPrimitiveRoot {ε : PreTilt A p}
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    ε.untilt = 1 := by
  rw [← untilt_iterate_frobeniusEquiv_symm_pow ε 1, pow_one, Function.iterate_one,
    hε.pow_eq_one]

/-- A primitive root makes the zeroth Witt coordinate `ε - 1` of `μ` nonzero. -/
theorem coeff_zero_mu_ne_zero {ε : PreTilt A p}
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p) :
    (mu p ε).coeff 0 ≠ 0 := by
  rw [mu_eq, ← constantCoeff_apply, map_sub, map_one, constantCoeff_apply,
    teichmuller_coeff_zero, sub_ne_zero]
  rintro rfl
  exact hε.ne_one (Fact.out : p.Prime).one_lt (by rw [map_one, map_one])

/-- If `ε♯ = 1`, then Fontaine's map kills every Frobenius iterate of `μ`. -/
theorem fontaineTheta_iterate_frobeniusEquiv_mu {ε : PreTilt A p} (hε : ε.untilt = 1)
    (j : ℕ) : fontaineTheta A p (((frobeniusEquiv p (PreTilt A p))^[j]) (mu p ε)) = 0 := by
  rw [iterate_frobeniusEquiv_mu]
  exact fontaineTheta_mu_eq_zero _ (by rw [map_pow, hε, one_pow])

/-- If `ε♯ = 1`, then Fontaine's map sends `φ^(j + 1)(ξ)` to `p`. -/
theorem fontaineTheta_iterate_frobeniusEquiv_succ_xi {ε : PreTilt A p} (hε : ε.untilt = 1)
    (j : ℕ) :
    fontaineTheta A p (((frobeniusEquiv p (PreTilt A p))^[j + 1]) (xi p ε)) = p := by
  rw [Function.iterate_succ_apply, ← xiTilde_eq, iterate_frobeniusEquiv_xiTilde]
  exact fontaineTheta_xiTilde _ (by rw [map_pow, hε, one_pow])

/-- A primitive root makes Fontaine's map kill `φ^j(ξ_r)` for every `j < r`. -/
theorem fontaineTheta_iterate_frobeniusEquiv_xiLevel [IsDomain A] (ε : PreTilt A p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt A p) p).symm ε)) p)
    {j r : ℕ} (hj : j < r) :
    fontaineTheta A p (((frobeniusEquiv p (PreTilt A p))^[j]) (xiLevel p ε r)) = 0 := by
  obtain ⟨c, hc⟩ := xi_dvd_iterate_frobeniusEquiv_xiLevel p ε hj
  rw [hc, map_mul, fontaineTheta_xi_eq_zero ε hε, zero_mul]

end FontaineValues

section RankOne

open scoped NormedField Valued

variable {p : ℕ} [Fact p.Prime] {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  [Fact ¬IsUnit (p : 𝒪[C])] [IsAdicComplete (Ideal.span {(p : 𝒪[C])}) (𝒪[C])]

/-- The tilt of `O_C` is separated for every nonunit: if every power of a nonunit `c` divides `a`,
then `a = 0`. The sharp map turns this into the inequality `‖a♯‖ ≤ ‖c♯‖ ^ n` with `‖c♯‖ < 1`. -/
theorem eq_zero_of_forall_pow_dvd {c a : PreTilt (𝒪[C]) p} (hc : ¬IsUnit c)
    (h : ∀ n, c ^ n ∣ a) : a = 0 := by
  by_contra ha
  have hc' : ‖(c.untilt : C)‖ < 1 := by
    refine lt_of_le_of_ne (Valued.integer.mem_iff.mp c.untilt.property) fun h1 ↦ hc ?_
    have hu : IsUnit c.untilt := Valued.integer.isUnit_iff_norm_eq_one.mpr h1
    rw [isUnit_iff_dvd_one, ← untilt_dvd_untilt_iff, map_one]
    exact hu.dvd
  have ha' : 0 < ‖(a.untilt : C)‖ := by
    rw [norm_pos_iff, ne_eq, ZeroMemClass.coe_eq_zero]
    exact untilt_ne_zero_iff.mpr ha
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ha' hc'
  obtain ⟨t, ht⟩ := map_dvd untilt (h n)
  have hle : ‖(a.untilt : C)‖ ≤ ‖(c.untilt : C)‖ ^ n := by
    rw [ht, map_pow, MulMemClass.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (Valued.integer.mem_iff.mp t.property)
  exact absurd hn hle.not_gt

end RankOne

section AlgebraicallyClosed

open scoped NormedField Valued

variable {p : ℕ} [Fact p.Prime] {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  [CompleteSpace C] [IsAlgClosed C]
  [Fact ¬IsUnit (p : 𝒪[C])] [IsAdicComplete (Ideal.span {(p : 𝒪[C])}) (𝒪[C])]

/-- The induction behind `mu_dvd_of_forall_fontaineTheta_iterate_eq_zero`: if `a` is killed by
every `θ ∘ φ^j` and `μ₀ = a₀ * c`, then `c ^ p ^ n` divides `μ₀` for every `n`. Writing `a = ξ * b`
gives `φ^(-1)(μ)₀ = b₀ * c`, hence `μ₀ = φ(b)₀ * c ^ p` with `φ(b)` again killed by every
`θ ∘ φ^j`. -/
private theorem pow_pow_dvd_coeff_zero_mu (ε : PreTilt (𝒪[C]) p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε)) p) (n : ℕ) :
    ∀ (a : WittVector p (PreTilt (𝒪[C]) p)) (c : PreTilt (𝒪[C]) p),
      (∀ j, fontaineTheta (𝒪[C]) p (((frobeniusEquiv p (PreTilt (𝒪[C]) p))^[j]) a) = 0) →
      (mu p ε).coeff 0 = a.coeff 0 * c → c ^ p ^ n ∣ (mu p ε).coeff 0 := by
  have hp0 : (p : 𝒪[C]) ≠ 0 := hε.neZero'.out
  induction n with
  | zero =>
    intro a c _ h
    rw [pow_zero, pow_one, h]
    exact dvd_mul_left _ _
  | succ n ih =>
    intro a c ha h
    obtain ⟨b, rfl⟩ : xi p ε ∣ a := by
      rw [← Ideal.mem_span_singleton, ← ker_fontaineTheta_eq_span_xi ε hε]
      exact ha 0
    -- `θ(φ^(j+1)(ξ)) = p ≠ 0`, so `φ(b)` is again killed by every `θ ∘ φ^j`
    have hb (j : ℕ) : fontaineTheta (𝒪[C]) p
        (((frobeniusEquiv p (PreTilt (𝒪[C]) p))^[j]) (frobeniusEquiv p _ b)) = 0 := by
      have := ha (j + 1)
      rw [iterate_map_mul, map_mul, fontaineTheta_iterate_frobeniusEquiv_succ_xi
        (untilt_eq_one_of_isPrimitiveRoot hε)] at this
      rw [← Function.iterate_succ_apply]
      exact (mul_eq_zero.mp this).resolve_left hp0
    have hμ := mu_eq_xi_mul_frobeniusEquiv_symm p ε
    have hξ0 : (xi p ε).coeff 0 ≠ 0 := fun h0 ↦ coeff_zero_mu_ne_zero hε (by
      rw [hμ, mul_coeff_zero, h0, zero_mul])
    -- cancelling `ξ₀` from `μ₀ = ξ₀ * b₀ * c` gives `φ^(-1)(μ)₀ = b₀ * c`
    have h1 : ((frobeniusEquiv p _).symm (mu p ε)).coeff 0 = b.coeff 0 * c := by
      refine mul_left_cancel₀ hξ0 ?_
      rw [← mul_coeff_zero, ← hμ, h, mul_coeff_zero, mul_assoc]
    have h2 : (mu p ε).coeff 0 = (frobeniusEquiv p _ b).coeff 0 * c ^ p := by
      conv_lhs => rw [← (frobeniusEquiv p _).apply_symm_apply (mu p ε)]
      rw [WittVector.frobeniusEquiv_apply, coeff_frobenius_charP, h1, coeff_frobenius_charP,
        mul_pow]
    simpa only [← pow_mul, ← pow_succ'] using ih _ (c ^ p) hb h2

/-- **Divisibility by `μ`.** If `θ(φ^j(a)) = 0` for every `j ≥ 0`, then `μ` divides `a`. The ideal
of such `a` contains `μ` and is saturated for `p`, and the zeroth Witt coordinate of `μ` divides
that of each of its elements, so it is `(μ)` by
`WittVector.eq_span_singleton_of_coeff_zero_dvd`. -/
theorem mu_dvd_of_forall_fontaineTheta_iterate_eq_zero (ε : PreTilt (𝒪[C]) p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε)) p)
    {a : WittVector p (PreTilt (𝒪[C]) p)}
    (ha : ∀ j, fontaineTheta (𝒪[C]) p (((frobeniusEquiv p (PreTilt (𝒪[C]) p))^[j]) a) = 0) :
    mu p ε ∣ a := by
  set φ := frobeniusEquiv p (PreTilt (𝒪[C]) p)
  let I : Ideal (WittVector p (PreTilt (𝒪[C]) p)) :=
    ⨅ j : ℕ, RingHom.ker ((fontaineTheta (𝒪[C]) p).comp ((φ : _ →+* _) ^ j))
  have hmem (x) : x ∈ I ↔ ∀ j, fontaineTheta (𝒪[C]) p ((φ^[j]) x) = 0 := by
    simp [I, RingHom.coe_pow]
  have hp0 : (p : 𝒪[C]) ≠ 0 := hε.neZero'.out
  have hI : I = Ideal.span {mu p ε} := by
    refine eq_span_singleton_of_coeff_zero_dvd
      ((hmem _).mpr (fontaineTheta_iterate_frobeniusEquiv_mu
        (untilt_eq_one_of_isPrimitiveRoot hε))) (fun x hx ↦ (hmem x).mpr fun j ↦ ?_)
      (fun x hx ↦ ?_)
    · have := (hmem _).mp hx j
      rw [iterate_map_mul, Function.iterate_fixed (map_natCast φ p), map_mul,
        map_natCast] at this
      exact (mul_eq_zero.mp this).resolve_left hp0
    · by_contra hndvd
      obtain ⟨c, hc⟩ := (ValuationRing.dvd_total _ _).resolve_left hndvd
      have hcu : ¬IsUnit c := fun hu ↦ hndvd (by rw [hc, hu.mul_right_dvd])
      exact coeff_zero_mu_ne_zero hε (eq_zero_of_forall_pow_dvd hcu fun n ↦
        (pow_dvd_pow c (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le).trans
          (pow_pow_dvd_coeff_zero_mu ε hε n x c ((hmem x).mp hx) hc))
  exact Ideal.mem_span_singleton.mp (hI ▸ (hmem a).mpr ha)


/-- An element of `A_inf` lies in `(μ)` exactly when it is killed by `θ ∘ φ^j` for every `j ≥ 0`.
-/
theorem mem_span_mu_iff (ε : PreTilt (𝒪[C]) p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε)) p)
    {a : WittVector p (PreTilt (𝒪[C]) p)} :
    a ∈ Ideal.span {mu p ε} ↔
      ∀ j, fontaineTheta (𝒪[C]) p (((frobeniusEquiv p (PreTilt (𝒪[C]) p))^[j]) a) = 0 := by
  refine ⟨fun h j ↦ ?_, fun h ↦
    Ideal.mem_span_singleton.mpr (mu_dvd_of_forall_fontaineTheta_iterate_eq_zero ε hε h)⟩
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp h
  rw [iterate_map_mul, map_mul,
    fontaineTheta_iterate_frobeniusEquiv_mu (untilt_eq_one_of_isPrimitiveRoot hε), zero_mul]

/-- The ideal `(μ)` does not depend on the choice of `ε`: any two admissible compatible systems
of roots of unity give the same ideal. -/
theorem span_mu_eq_span_mu {ε ε' : PreTilt (𝒪[C]) p}
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε)) p)
    (hε' : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε')) p) :
    Ideal.span {mu p ε} = Ideal.span {mu p ε'} := by
  ext a
  rw [mem_span_mu_iff ε hε, mem_span_mu_iff ε' hε']

/-- Any two admissible choices of `ε` give associated elements `μ`. -/
theorem associated_mu {ε ε' : PreTilt (𝒪[C]) p}
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε)) p)
    (hε' : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε')) p) :
    Associated (mu p ε) (mu p ε') :=
  Ideal.span_singleton_eq_span_singleton.mp (span_mu_eq_span_mu hε hε')

/-- **The infinite Witt specialization kernel** (Bhatt–Morrow–Scholze, Lemma 3.23). The finite
Fontaine kernels `(ξ_r)`, `r ≥ 1`, intersect in `(μ)`. -/
theorem iInf_span_xiLevel_eq_span_mu (ε : PreTilt (𝒪[C]) p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε)) p) :
    (⨅ (r : ℕ) (_ : 1 ≤ r), Ideal.span {xiLevel p ε r}) = Ideal.span {mu p ε} := by
  refine le_antisymm (fun a ha ↦ (mem_span_mu_iff ε hε).mpr fun j ↦ ?_)
    (le_iInf₂ fun r _ ↦ span_mu_le_span_xiLevel p ε r)
  simp only [Submodule.mem_iInf] at ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp (ha (j + 1) (Nat.le_add_left 1 j))
  rw [iterate_map_mul, map_mul,
    fontaineTheta_iterate_frobeniusEquiv_xiLevel ε hε (Nat.lt_succ_self j), zero_mul]

end AlgebraicallyClosed

end PreTilt
