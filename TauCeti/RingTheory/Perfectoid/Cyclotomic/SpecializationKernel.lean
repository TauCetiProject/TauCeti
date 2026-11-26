/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Cyclotomic.Level
public import TauCeti.RingTheory.Perfectoid.PreTilt.ValuationRing

import TauCeti.RingTheory.WittVector.Complete

/-!
# The infinite Witt specialization kernel

Let `C` be a complete perfectoid nonarchimedean field of residue characteristic `p`, with
valuation ring `O_C`, tilt `O_C♭` and `A_inf = W(O_C♭)`. Fix `ε ∈ O_C♭` such that the sharp of
`ε ^ (1 / p)` is a primitive `p`-th root of unity, and let `μ = [ε] - 1` and
`ξ_r = ∏_{j < r} φ^(-j)(ξ)` be the cyclotomic periods. We prove that the ideals `(ξ_r)`,
`r ≥ 1`, intersect in `(μ)`:

`⋂_{r ≥ 1} (ξ_r) = (μ)`.

In Lemma 3.23 of Bhatt–Morrow–Scholze, `ξ_r` generates the kernel of the specialization map
`θ_r`, and this intersection is read as the kernel of `θ_∞ : A_inf → W(O_C)`; the formal result
here is the ideal identity.

Instead of the limit argument of the reference, we characterize `(μ)` directly: `a ∈ (μ)` if and
only if `θ(φ^j(a)) = 0` for every `j ≥ 0`. The ideal `I` of such `a` contains `μ` and is
saturated for `p`. Its zeroth Witt coordinates are all divisible by that of `μ`: otherwise
`μ₀ = a₀ * c` for some `a ∈ I` and a nonunit `c ∈ O_C♭`, and writing `a = ξ * b` (Fontaine's
kernel is `(ξ)`) shows that `φ(b) ∈ I` with `μ₀ = φ(b)₀ * c ^ p`. Iterating, every power of `c`
divides `μ₀ ≠ 0`, which is impossible by `PreTilt.eq_zero_of_forall_pow_dvd`. Then
`WittVector.eq_span_singleton_of_coeff_zero_dvd` gives `I = (μ)`. Finally, `a ∈ (ξ_(j+1))`
forces `θ(φ^j(a)) = 0`, because `ξ` divides `φ^j(ξ_(j+1))`.

As a consequence the ideal `(μ)` does not depend on the choice of `ε`.

## Main results

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

section PerfectoidField

open scoped NormedField Valued

variable {p : ℕ} [Fact p.Prime] {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  [CompleteSpace C] [IsPerfectoidTateRing p C]
  [Fact ¬IsUnit (p : 𝒪[C])] [IsAdicComplete (Ideal.span {(p : 𝒪[C])}) (𝒪[C])]

/-- The induction behind `mu_dvd_of_forall_fontaineTheta_iterate_eq_zero`: if `a` is killed by
every `θ ∘ φ^j` and `μ₀ = a₀ * c`, then `c ^ p ^ n` divides `μ₀` for every `n`. -/
private theorem pow_pow_dvd_coeff_zero_mu (ε : PreTilt (𝒪[C]) p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε)) p) (n : ℕ) :
    ∀ (a : WittVector p (PreTilt (𝒪[C]) p)) (c : PreTilt (𝒪[C]) p),
      (∀ j, fontaineTheta (𝒪[C]) p (((frobeniusEquiv p (PreTilt (𝒪[C]) p))^[j]) a) = 0) →
      (mu p ε).coeff 0 = a.coeff 0 * c → c ^ p ^ n ∣ (mu p ε).coeff 0 := by
  -- Writing `a = ξ * b` gives `φ^(-1)(μ)₀ = b₀ * c`, hence `μ₀ = φ(b)₀ * c ^ p` with `φ(b)` again
  -- killed by every `θ ∘ φ^j`.
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
      simpa only [RingHom.mem_ker, Function.iterate_zero_apply] using ha 0
    -- `θ(φ^(j+1)(ξ)) = p ≠ 0`, so `φ(b)` is again killed by every `θ ∘ φ^j`
    have hb (j : ℕ) : fontaineTheta (𝒪[C]) p
        (((frobeniusEquiv p (PreTilt (𝒪[C]) p))^[j]) (frobeniusEquiv p _ b)) = 0 := by
      have := ha (j + 1)
      rw [iterate_map_mul, map_mul, fontaineTheta_iterate_frobeniusEquiv_succ_xi ε
        (ε.untilt_eq_one_of_isPrimitiveRoot hε)] at this
      rw [← Function.iterate_succ_apply]
      exact (mul_eq_zero.mp this).resolve_left hp0
    have hμ := mu_eq_xi_mul_frobeniusEquiv_symm p ε
    -- cancelling `ξ₀` from `μ₀ = ξ₀ * b₀ * c` gives `φ^(-1)(μ)₀ = b₀ * c`
    have h1 : ((frobeniusEquiv p _).symm (mu p ε)).coeff 0 = b.coeff 0 * c := by
      refine mul_left_cancel₀ (coeff_zero_xi_ne_zero p (ε.ne_one_of_isPrimitiveRoot hε)) ?_
      rw [← mul_coeff_zero, ← hμ, h, mul_coeff_zero, mul_assoc]
    have h2 : (mu p ε).coeff 0 = (frobeniusEquiv p _ b).coeff 0 * c ^ p := by
      conv_lhs => rw [← (frobeniusEquiv p _).apply_symm_apply (mu p ε)]
      rw [WittVector.frobeniusEquiv_apply, coeff_frobenius_charP, h1, coeff_frobenius_charP,
        mul_pow]
    simpa only [← pow_mul, ← pow_succ'] using ih _ (c ^ p) hb h2

/-- **Divisibility by `μ`.** If the sharp of `ε ^ (1 / p)` is a primitive `p`-th root of unity and
`θ(φ^j(a)) = 0` for every `j ≥ 0`, then `μ` divides `a`. -/
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
    -- `I` contains `μ`, is saturated for `p`, and `μ₀` divides the zeroth coordinates of `I`
    refine eq_span_singleton_of_coeff_zero_dvd (mu p ε)
      ((hmem _).mpr (fontaineTheta_iterate_frobeniusEquiv_mu_eq_zero ε
        (ε.untilt_eq_one_of_isPrimitiveRoot hε))) (fun x hx ↦ (hmem x).mpr fun j ↦ ?_)
      (fun x hx ↦ ?_)
    · have := (hmem _).mp hx j
      rw [iterate_map_mul, Function.iterate_fixed (map_natCast φ p), map_mul,
        map_natCast] at this
      exact (mul_eq_zero.mp this).resolve_left hp0
    · by_contra hndvd
      obtain ⟨c, hc⟩ := (ValuationRing.dvd_total _ _).resolve_left hndvd
      have hcu : ¬IsUnit c := fun hu ↦ hndvd (by rw [hc, hu.mul_right_dvd])
      exact coeff_zero_mu_ne_zero p (ε.ne_one_of_isPrimitiveRoot hε)
        (eq_zero_of_forall_pow_dvd c hcu fun n ↦
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
    fontaineTheta_iterate_frobeniusEquiv_mu_eq_zero ε (ε.untilt_eq_one_of_isPrimitiveRoot hε),
    zero_mul]

/-- The ideal `(μ)` does not depend on the choice of `ε`: any two admissible compatible systems
of roots of unity give the same ideal. -/
theorem span_mu_eq_span_mu (ε ε' : PreTilt (𝒪[C]) p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε)) p)
    (hε' : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε')) p) :
    Ideal.span {mu p ε} = Ideal.span {mu p ε'} := by
  ext a
  rw [mem_span_mu_iff ε hε, mem_span_mu_iff ε' hε']

/-- Any two admissible choices of `ε` give associated elements `μ`. -/
theorem associated_mu (ε ε' : PreTilt (𝒪[C]) p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε)) p)
    (hε' : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε')) p) :
    Associated (mu p ε) (mu p ε') :=
  Ideal.span_singleton_eq_span_singleton.mp (span_mu_eq_span_mu ε ε' hε hε')

/-- **The infinite Witt specialization kernel.** The ideals `(ξ_r)`, `r ≥ 1`, intersect in `(μ)`.
In Bhatt–Morrow–Scholze, Lemma 3.23, this is the kernel of `θ_∞ : A_inf → W(O_C)`. -/
theorem iInf_span_xiLevel_eq_span_mu (ε : PreTilt (𝒪[C]) p)
    (hε : IsPrimitiveRoot
      (PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (𝒪[C]) p) p).symm ε)) p) :
    (⨅ (r : ℕ) (_ : 1 ≤ r), Ideal.span {xiLevel p ε r}) = Ideal.span {mu p ε} := by
  refine le_antisymm (fun a ha ↦ (mem_span_mu_iff ε hε).mpr fun j ↦ ?_)
    (le_iInf₂ fun r _ ↦ span_mu_le_span_xiLevel p ε r)
  simp only [Submodule.mem_iInf] at ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp (ha (j + 1) (Nat.le_add_left 1 j))
  rw [iterate_map_mul, map_mul,
    fontaineTheta_iterate_frobeniusEquiv_xiLevel_eq_zero ε (fontaineTheta_xi_eq_zero ε hε)
      (Nat.lt_succ_self j), zero_mul]

end PerfectoidField

end PreTilt
