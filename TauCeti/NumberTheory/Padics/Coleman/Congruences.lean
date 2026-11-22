/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Coleman.Norm
public import TauCeti.RingTheory.AdicCompletion.Principal

import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Basic
import TauCeti.RingTheory.PowerSeries.Expand
import TauCeti.RingTheory.PowerSeries.Ideal

/-!
# Algebraic congruences for Coleman's norm

For a prime `p` and `(p)`-adically complete commutative ring `O`, this file establishes the
algebraic congruences satisfied by Coleman's norm `N = TauCeti.Coleman.norm p O`:
1. Congruence preservation `f ≡ g (mod p ^ k) → N(f) ≡ N(g) (mod p ^ k)`.
2. Mod-`p ^ k` contraction (`k ≥ 1`) near `1` (`N(1 + p ^ k * h) ≡ 1 (mod p ^ (k + 1))`) and at
   units (`IsUnit g`, `f ≡ g (mod p ^ k) → N(f) ≡ N(g) (mod p ^ (k + 1))`), uniformly for all primes
   including `p = 2`.
3. Characteristic-`p` identification `N(f) = PowerSeries.map (frobenius R p) f`, yielding
   `N(f) ≡ σ(f) (mod p)` for any Frobenius lift `σ : O →+* O`.

## Main results

* `TauCeti.Coleman.norm_eq_map_frobenius`: over any char-`p` commutative ring, `N` is
  coefficientwise Frobenius.
* `TauCeti.Coleman.norm_sub_norm_mem_span_pow`: `N` preserves congruences modulo `(p) ^ k`.
* `TauCeti.Coleman.norm_one_add_sub_one_mem_span_pow_succ`: `N(1 + p ^ k * h) ≡ 1 (mod p ^ (k + 1))`
  for `k ≥ 1`.
* `TauCeti.Coleman.norm_sub_norm_mem_span_pow_succ`:
  `f ≡ g (mod p ^ k) → N(f) ≡ N(g) (mod p ^ (k + 1))` at units for `k ≥ 1`.
* `TauCeti.Coleman.norm_sub_map_mem_span_p`: `N(f) ≡ σ(f) (mod p)` for any Frobenius lift `σ`.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §IV (Lemma 13,
  eq. (2)).
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §2.3.
* R. Sharifi, *Iwasawa Theory*, §5.4 (Prop. 5.4.6, Cor. 5.4.7).
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), Ch. 10
  (Prop. 10.10, Lemma 10.11).
* C. Birkbeck et al., `CBirkbeck/padic-L-functions` (`Coleman/NormOperator.lean`, commit
  `45307015169791f1316f23a459c8e92ed5961c54`).
-/

public noncomputable section

open PowerSeries

namespace TauCeti.Coleman

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O]

private theorem norm_eq_map_frobenius_of_isReduced {R : Type*} [CommRing R] [IsReduced R]
    [CharP R p] (f : R⟦X⟧) : norm p R f = PowerSeries.map (frobenius R p) f := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpow : (norm p R f) ^ p = (PowerSeries.map (frobenius R p) f) ^ p := by
    rw [← map_pow (norm p R), ← PowerSeries.map_frobenius_expand p hp, PowerSeries.map_expand,
      ← frobeniusHom_eq_expand (CharP.cast_eq_zero R p), norm_frobeniusHom]
  rw [← PowerSeries.map_frobenius_expand p hp, ← PowerSeries.map_frobenius_expand p hp] at hpow
  exact PowerSeries.expand_injective p hp (PowerSeries.map_injective _ (frobenius_inj R p) hpow)

/-- Over any commutative ring of characteristic `p`, `norm` is coefficientwise Frobenius. -/
theorem norm_eq_map_frobenius {R : Type*} [CommRing R] [CharP R p] (f : R⟦X⟧) :
    norm p R f = PowerSeries.map (frobenius R p) f := by
  let F : (MvPolynomial ℕ (ZMod p))⟦X⟧ := PowerSeries.mk MvPolynomial.X
  let φ : MvPolynomial ℕ (ZMod p) →+* R :=
    MvPolynomial.eval₂Hom (ZMod.castHom dvd_rfl R) (fun n ↦ coeff n f)
  have hF : PowerSeries.map φ F = f := ext fun n ↦ by
    rw [coeff_map, coeff_mk, MvPolynomial.eval₂Hom_X']
  have hc : φ.comp (frobenius _ p) = (frobenius R p).comp φ :=
    RingHom.ext fun x ↦ by simp only [RingHom.comp_apply, frobenius_def, map_pow]
  have h := congrArg (PowerSeries.map φ) (norm_eq_map_frobenius_of_isReduced (p := p) F)
  rwa [map_norm φ F, hF, ← RingHom.comp_apply, ← PowerSeries.map_comp, hc,
    PowerSeries.map_comp, RingHom.comp_apply, hF] at h

variable [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- Coleman's norm preserves congruences modulo `(p) ^ k`. -/
theorem norm_sub_norm_mem_span_pow {k : ℕ} {f g : O⟦X⟧}
    (hfg : f - g ∈ Ideal.span {(p : O⟦X⟧)} ^ k) :
    norm p O f - norm p O g ∈ Ideal.span {(p : O⟦X⟧)} ^ k := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  set q : O⟦X⟧ →+* O⟦X⟧ ⧸ Ideal.span {(p : O⟦X⟧)} ^ k := Ideal.Quotient.mk _
  rw [map_sub, sub_eq_zero, norm_eq_det_leftMulMatrix, norm_eq_det_leftMulMatrix,
    RingHom.map_det, RingHom.map_det]
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton.mp (by rwa [Ideal.span_singleton_pow] at hfg)
  have hpk : q (C ((p : O) ^ k)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr <| by
    rw [map_pow, map_natCast]; exact Ideal.pow_mem_pow (Ideal.subset_span rfl) k
  have hf : f = g + C ((p : O) ^ k) * h := by rw [map_pow, map_natCast, ← hh]; ring
  have hcoord (r : Fin p) : q (coord p O r f) = q (coord p O r g) := by
    rw [hf, map_add, coord_C_mul, map_add, map_mul, hpk, zero_mul, add_zero]
  congr 1; refine Matrix.ext fun i j ↦ ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, leftMulMatrix_apply]
  split_ifs <;> simp [hcoord]

/-- **Contraction near `1`.** For `k ≥ 1` and `h ∈ O⟦X⟧`, `N(1 + p ^ k * h) ≡ 1 (mod p ^ (k + 1))`
for all primes `p` including `p = 2` (Coleman Lemma 13; Sharifi Prop. 5.4.6; RJW Lemma 10.11). -/
theorem norm_one_add_sub_one_mem_span_pow_succ {k : ℕ} (hk : 1 ≤ k) (h : O⟦X⟧) :
    norm p O (1 + (p : O⟦X⟧) ^ k * h) - 1 ∈ Ideal.span {(p : O⟦X⟧)} ^ (k + 1) := by
  obtain ⟨r, hr⟩ := norm_one_add_frobeniusHom_mul (p := p) ((p : O⟦X⟧) ^ k) h
  rw [map_pow, map_natCast] at hr
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨coord p O ⟨0, (Fact.out : p.Prime).pos⟩ h + r * (p : O⟦X⟧) ^ (k - 1), ?_⟩
  rw [hr, trace_eq_p_mul_coord_zero]
  have hk' : (p : O⟦X⟧) ^ (k + 1) * (p : O⟦X⟧) ^ (k - 1) = ((p : O⟦X⟧) ^ k) ^ 2 := by
    rw [← pow_add, ← pow_mul]; congr 1; omega
  rw [mul_add, mul_left_comm _ r, hk', pow_succ']; ring

/-- **Contraction at units.** For `k ≥ 1` and `IsUnit g`, if `f ≡ g (mod p ^ k)` then
`N(f) ≡ N(g) (mod p ^ (k + 1))` (Coleman Lemma 13; Sharifi Cor. 5.4.7; RJW Lemma 10.11). -/
theorem norm_sub_norm_mem_span_pow_succ {k : ℕ} (hk : 1 ≤ k) {f g : O⟦X⟧} (hg : IsUnit g)
    (hfg : f - g ∈ Ideal.span {(p : O⟦X⟧)} ^ k) :
    norm p O f - norm p O g ∈ Ideal.span {(p : O⟦X⟧)} ^ (k + 1) := by
  obtain ⟨u, rfl⟩ := hg
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (by rwa [Ideal.span_singleton_pow] at hfg)
  have hf_eq : f = (u : O⟦X⟧) * (1 + (p : O⟦X⟧) ^ k * ((u⁻¹ : O⟦X⟧ˣ) * d)) := by
    rw [mul_add, mul_one, mul_left_comm, ← mul_assoc (u : O⟦X⟧), Units.mul_inv, one_mul, ← hd]
    ring
  have hnorm_eq : norm p O f - norm p O (u : O⟦X⟧) =
      norm p O (u : O⟦X⟧) * (norm p O (1 + (p : O⟦X⟧) ^ k * ((u⁻¹ : O⟦X⟧ˣ) * d)) - 1) := by
    rw [hf_eq, map_mul]; ring
  rw [hnorm_eq]
  exact Ideal.mul_mem_left _ _ (norm_one_add_sub_one_mem_span_pow_succ hk _)

/-- **Mod-`p` Frobenius congruence.** If `σ : O →+* O` lifts Frobenius modulo `(p)`, then
`N(f) ≡ σ(f) (mod p)` (Coleman §IV eq. (2); Sharifi Prop. 5.4.6; RJW Prop. 10.10). -/
theorem norm_sub_map_mem_span_p (σ : O →+* O)
    (hσ : ∀ c : O, σ c - c ^ p ∈ Ideal.span {(p : O)}) (f : O⟦X⟧) :
    norm p O f - PowerSeries.map σ f ∈ Ideal.span {(p : O⟦X⟧)} := by
  set q : O →+* O ⧸ Ideal.span {(p : O)} := Ideal.Quotient.mk _
  rw [← pow_one (Ideal.span {(p : O⟦X⟧)}), ← map_natCast (C : O →+* O⟦X⟧),
    PowerSeries.mem_span_C_pow_iff]
  intro n; rw [pow_one, ← Ideal.Quotient.eq_zero_iff_mem]
  nontriviality O ⧸ Ideal.span {(p : O)}
  have : CharP (O ⧸ Ideal.span {(p : O)}) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr <| by
      rw [← map_natCast q, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
  have hq : (frobenius (O ⧸ Ideal.span {(p : O)}) p).comp q = q.comp σ :=
    RingHom.ext fun c ↦ by
      simp only [RingHom.comp_apply, frobenius_def, ← map_pow]
      exact (Ideal.Quotient.eq.mpr (hσ c)).symm
  have hmap : PowerSeries.map q (norm p O f) = PowerSeries.map q (PowerSeries.map σ f) := by
    rw [map_norm q f, norm_eq_map_frobenius, ← RingHom.comp_apply, ← PowerSeries.map_comp,
      ← RingHom.comp_apply, ← PowerSeries.map_comp, hq]
  rw [map_sub, map_sub, ← coeff_map, hmap, coeff_map, sub_self]

end TauCeti.Coleman
