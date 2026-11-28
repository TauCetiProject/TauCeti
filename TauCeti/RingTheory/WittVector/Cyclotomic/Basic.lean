/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Frobenius.Basic
public import TauCeti.RingTheory.WittVector.Primitive.Basic
-- Proof-only: `ε ^ (1 / p) - 1` is a `p`-th root of `ε - 1`.
import TauCeti.RingTheory.Perfect.Basic

/-!
# Cyclotomic period elements of Witt vectors

Let `S` be a perfect ring of characteristic `p`, so that the Witt vector Frobenius `φ` of `W(S)`
is an automorphism, and let `ε ∈ S`. Write `[-]` for Teichmüller representatives. This file
defines the cyclotomic period elements

* `μ = [ε] - 1` (`TauCeti.WittVector.cyclotomicMu`),
* `ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j` (`TauCeti.WittVector.cyclotomicXi`), and
* `ξ' = φ(ξ) = ∑_{j < p} [ε] ^ j` (`TauCeti.WittVector.cyclotomicXiTilde`; usually written `ξ`
  with a tilde).

The elements are natural in `S`: a ring homomorphism `f : S →+* T` sends them, under
`WittVector.map f`, to the elements formed from `f ε` (for `ξ` and `ξ'` when `T` is perfect too).
At `ε = 1` they are `0`, `p`, and `p`. Hence if `f ε = 1`, then `W(f)` kills `μ` and sends `ξ'`
to `p`, and also `ξ` when `T` is reduced.

The geometric sum identity gives the factorisations `μ = ξ · φ⁻¹(μ)` and `φ(μ) = ξ' · μ` in
`W(S)`, with zeroth Witt coordinate relations `ξ.coeff 0 · (ε ^ (1 / p) - 1) = ε - 1` and
`ξ'.coeff 0 · (ε - 1) = ε ^ p - 1`. For `ε ≠ 1`, `μ`, `ξ`, and `ξ'` are nonzero and `p` divides
neither `μ` nor `φ⁻¹(μ)`. If `ε - 1` lies in the Jacobson radical of `S`, then modulo the Jacobson
radical `ξ` becomes `p`, so `ξ` and `ξ'` are distinguished.

## Main definitions

* `TauCeti.WittVector.cyclotomicMu`, `TauCeti.WittVector.cyclotomicXi`,
  `TauCeti.WittVector.cyclotomicXiTilde`: the elements `μ`, `ξ` and `ξ'` of `W(S)`.

## Main results

* `TauCeti.WittVector.map_cyclotomicMu`, `TauCeti.WittVector.map_cyclotomicXi`,
  `TauCeti.WittVector.map_cyclotomicXiTilde`: naturality of `μ`, `ξ` and `ξ'`.
* `TauCeti.WittVector.map_cyclotomicXi_eq_natCast`,
  `TauCeti.WittVector.map_cyclotomicXiTilde_eq_natCast`: if `f ε = 1`, then `W(f)` sends `ξ` (for
  reduced `T`) and `ξ'` to `p`.
* `TauCeti.WittVector.cyclotomicMu_eq_cyclotomicXi_mul`: `μ = ξ · φ⁻¹(μ)`.
* `TauCeti.WittVector.frobenius_cyclotomicMu_eq_cyclotomicXiTilde_mul`: `φ(μ) = ξ' · μ`.
* `TauCeti.WittVector.cyclotomicXi_coeff_zero_mul`,
  `TauCeti.WittVector.cyclotomicXiTilde_coeff_zero_mul`: zeroth Witt coordinate relations.
* `TauCeti.WittVector.cyclotomicXiTilde_eq_sum`: `ξ' = ∑_{j < p} [ε] ^ j`.
* `TauCeti.WittVector.frobeniusEquiv_symm_cyclotomicXi`,
  `TauCeti.WittVector.frobenius_cyclotomicXi`,
  `TauCeti.WittVector.cyclotomicXiTilde_eq_cyclotomicXi_pow`,
  `TauCeti.WittVector.iterate_frobeniusEquiv_cyclotomicMu`,
  `TauCeti.WittVector.iterate_frobeniusEquiv_symm_cyclotomicMu`,
  `TauCeti.WittVector.iterate_frobeniusEquiv_cyclotomicXiTilde`: Frobenius actions on `μ`, `ξ`,
  and `ξ'`.
* `TauCeti.WittVector.coeff_zero_cyclotomicMu_ne_zero`, `TauCeti.WittVector.cyclotomicMu_ne_zero`,
  `TauCeti.WittVector.not_natCast_dvd_cyclotomicMu`,
  `TauCeti.WittVector.not_natCast_dvd_frobeniusEquiv_symm_cyclotomicMu`,
  `TauCeti.WittVector.coeff_zero_cyclotomicXi_ne_zero`, `TauCeti.WittVector.cyclotomicXi_ne_zero`,
  `TauCeti.WittVector.cyclotomicXiTilde_ne_zero`: nonvanishing and non-divisibility by `p` when
  `ε ≠ 1`.
* `TauCeti.WittVector.map_mk_jacobson_cyclotomicXi_eq_natCast`,
  `TauCeti.WittVector.isDistinguished_cyclotomicXi`,
  `TauCeti.WittVector.isDistinguished_cyclotomicXiTilde`: if `ε - 1` lies in the Jacobson radical
  of `S`, then `ξ` reduces to `p` modulo the Jacobson radical, so `ξ` and `ξ'` are distinguished.

## Provenance

`TauCeti.WittVector.not_natCast_dvd_frobeniusEquiv_symm_cyclotomicMu` is adapted from
`New.Period.not_p_dvd_tau` in `src/Lib/PadicHodge/PeriodRings/Ainf.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, Example 3.16 and
  Proposition 3.17.
-/

public section

open _root_.WittVector

namespace TauCeti.WittVector

variable (p : ℕ) [hp : Fact p.Prime] {S T : Type*} [CommRing S] [CommRing T]

local notation "𝕎" => _root_.WittVector p

/-- The cyclotomic period element `μ = [ε] - 1` of `W(S)`. -/
noncomputable def cyclotomicMu (ε : S) : 𝕎 S :=
  teichmuller p ε - 1

/-- Unfolding lemma for `cyclotomicMu`. -/
theorem cyclotomicMu_def (ε : S) : cyclotomicMu p ε = teichmuller p ε - 1 := (rfl)

/-- For `ε = 1`, the period element `μ = [ε] - 1` vanishes. -/
@[simp]
theorem cyclotomicMu_one : cyclotomicMu p (1 : S) = 0 := by
  simp [cyclotomicMu_def]

/-- The period element `μ` is natural: `W(f)` sends `μ(ε) = [ε] - 1` to `μ(f ε) = [f ε] - 1`. -/
@[simp]
theorem map_cyclotomicMu (f : S →+* T) (ε : S) :
    map f (cyclotomicMu p ε) = cyclotomicMu p (f ε) := by
  simp [cyclotomicMu_def, map_teichmuller]

/-- In characteristic `p`, the Frobenius of `μ(ε) = [ε] - 1` is `μ(ε ^ p) = [ε ^ p] - 1`. -/
@[simp]
theorem frobenius_cyclotomicMu [CharP S p] (ε : S) :
    frobenius (cyclotomicMu p ε) = cyclotomicMu p (ε ^ p) := by
  simp [cyclotomicMu_def]

/-- The zeroth Witt coordinate of `μ = [ε] - 1` is `ε - 1`. -/
@[simp]
theorem cyclotomicMu_coeff_zero (ε : S) : (cyclotomicMu p ε).coeff 0 = ε - 1 := by
  rw [cyclotomicMu_def, ← constantCoeff_apply, map_sub, map_one, constantCoeff_apply,
    teichmuller_coeff_zero]

/-- For `ε ≠ 1`, the zeroth Witt coordinate of `μ` is nonzero. -/
theorem coeff_zero_cyclotomicMu_ne_zero {ε : S} (hε : ε ≠ 1) : (cyclotomicMu p ε).coeff 0 ≠ 0 := by
  rwa [cyclotomicMu_coeff_zero, sub_ne_zero]

/-- For `ε ≠ 1`, `μ` is nonzero. -/
theorem cyclotomicMu_ne_zero {ε : S} (hε : ε ≠ 1) : cyclotomicMu p ε ≠ 0 :=
  fun h ↦ coeff_zero_cyclotomicMu_ne_zero p hε (by rw [h, zero_coeff])

/-- For `ε ≠ 1`, `p` does not divide `μ`: its zeroth Witt coordinate `ε - 1` is nonzero, while
every multiple of `p` has zeroth coordinate `0` in characteristic `p`. -/
theorem not_natCast_dvd_cyclotomicMu [CharP S p] {ε : S} (hε : ε ≠ 1) :
    ¬ (p : 𝕎 S) ∣ cyclotomicMu p ε := by
  rintro ⟨b, hb⟩
  apply coeff_zero_cyclotomicMu_ne_zero p hε
  rw [hb, mul_comm, mul_charP_coeff_zero]

section Perfect

variable [CharP S p] [PerfectRing S p]

/-- The cyclotomic period element `ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j` of `W(S)`, for a perfect ring
`S` of characteristic `p`. It is defined without division, and `μ = ξ · φ⁻¹(μ)`
(`cyclotomicMu_eq_cyclotomicXi_mul`). -/
noncomputable def cyclotomicXi (ε : S) : 𝕎 S :=
  ∑ j ∈ Finset.range p, teichmuller p ((_root_.frobeniusEquiv S p).symm ε) ^ j

/-- Unfolding lemma for `cyclotomicXi`. -/
theorem cyclotomicXi_def (ε : S) :
    cyclotomicXi p ε =
      ∑ j ∈ Finset.range p, teichmuller p ((_root_.frobeniusEquiv S p).symm ε) ^ j :=
  (rfl)

/-- The cyclotomic period element `ξ' = φ(ξ)` of `W(S)`, the Frobenius twist of `cyclotomicXi`;
it equals `∑_{j < p} [ε] ^ j` (`cyclotomicXiTilde_eq_sum`). -/
noncomputable def cyclotomicXiTilde (ε : S) : 𝕎 S :=
  frobenius (cyclotomicXi p ε)

/-- Unfolding lemma for `cyclotomicXiTilde`. -/
theorem cyclotomicXiTilde_def (ε : S) : cyclotomicXiTilde p ε = frobenius (cyclotomicXi p ε) :=
  (rfl)

/-- The Frobenius of `ξ` is `ξ'`. -/
@[simp]
theorem frobenius_cyclotomicXi (ε : S) : frobenius (cyclotomicXi p ε) = cyclotomicXiTilde p ε :=
  (rfl)

/-- `ξ' = ∑_{j < p} [ε] ^ j`. -/
theorem cyclotomicXiTilde_eq_sum (ε : S) :
    cyclotomicXiTilde p ε = ∑ j ∈ Finset.range p, teichmuller p ε ^ j := by
  rw [cyclotomicXiTilde_def, cyclotomicXi_def, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_pow, frobenius_teichmuller, ← map_pow, frobeniusEquiv_symm_pow_p]

/-- `ξ'(ε) = ξ(ε ^ p)`. -/
theorem cyclotomicXiTilde_eq_cyclotomicXi_pow (ε : S) :
    cyclotomicXiTilde p ε = cyclotomicXi p (ε ^ p) := by
  rw [cyclotomicXiTilde_eq_sum, cyclotomicXi_def, frobeniusEquiv_symm_pow]

/-- For `ε = 1`, the period element `ξ = ∑_{j < p} [1] ^ j` is `p`. -/
@[simp]
theorem cyclotomicXi_one : cyclotomicXi p (1 : S) = p := by
  simp [cyclotomicXi_def]

/-- For `ε = 1`, the period element `ξ' = ∑_{j < p} [1] ^ j` is `p`. -/
@[simp]
theorem cyclotomicXiTilde_one : cyclotomicXiTilde p (1 : S) = p := by
  simp [cyclotomicXiTilde_eq_sum]

/-- If a ring homomorphism `f` sends `ε` to `1`, then `W(f)` sends `ξ' = ∑_{j < p} [ε] ^ j` to
`p`. -/
theorem map_cyclotomicXiTilde_eq_natCast {f : S →+* T} {ε : S} (hε : f ε = 1) :
    map f (cyclotomicXiTilde p ε) = p := by
  simp [cyclotomicXiTilde_eq_sum, map_sum, map_teichmuller, hε]

/-- If a ring homomorphism `f` to a reduced ring sends `ε` to `1`, then `W(f)` sends
`ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j` to `p`: `f (ε ^ (1 / p))` is then `1` too. Reducedness is needed:
otherwise `f (ε ^ (1 / p)) - 1` may be a nonzero element with vanishing `p`-th power. -/
theorem map_cyclotomicXi_eq_natCast [IsReduced T] {f : S →+* T} {ε : S} (hε : f ε = 1) :
    map f (cyclotomicXi p ε) = p := by
  -- `f (ε ^ (1 / p)) - 1` is a `p`-th root of `f (ε - 1) = 0`, so it vanishes
  have h : f ((_root_.frobeniusEquiv S p).symm ε) = 1 := by
    rw [← sub_eq_zero]
    refine IsReduced.eq_zero _ ⟨p, ?_⟩
    rw [← map_one f, ← map_sub, ← map_pow, frobeniusEquiv_symm_sub_one_pow]
    simp [hε]
  simp [cyclotomicXi_def, map_sum, map_teichmuller, h]

section Natural

variable [CharP T p] [PerfectRing T p]

/-- The period element `ξ` is natural for ring homomorphisms between perfect rings of
characteristic `p`: `W(f)` sends `ξ(ε)` to `ξ(f ε)`. -/
@[simp]
theorem map_cyclotomicXi (f : S →+* T) (ε : S) :
    map f (cyclotomicXi p ε) = cyclotomicXi p (f ε) := by
  simp [cyclotomicXi_def, map_sum, map_teichmuller, RingHom.map_frobeniusEquiv_symm]

/-- The period element `ξ'` is natural for ring homomorphisms between perfect rings of
characteristic `p`: `W(f)` sends `ξ'(ε)` to `ξ'(f ε)`. -/
@[simp]
theorem map_cyclotomicXiTilde (f : S →+* T) (ε : S) :
    map f (cyclotomicXiTilde p ε) = cyclotomicXiTilde p (f ε) := by
  simp [cyclotomicXiTilde_eq_sum, map_sum, map_teichmuller]

end Natural

/-- The inverse Frobenius of `μ(ε) = [ε] - 1` is `μ(ε ^ (1 / p)) = [ε ^ (1 / p)] - 1`. -/
@[simp]
theorem frobeniusEquiv_symm_cyclotomicMu (ε : S) :
    (frobeniusEquiv p S).symm (cyclotomicMu p ε) =
      cyclotomicMu p ((_root_.frobeniusEquiv S p).symm ε) := by
  simp [cyclotomicMu_def]

/-- Iterated Frobenius on `μ` replaces `ε` by `ε ^ p ^ j`. -/
theorem iterate_frobeniusEquiv_cyclotomicMu (ε : S) (j : ℕ) :
    ((frobeniusEquiv p S)^[j]) (cyclotomicMu p ε) = cyclotomicMu p (ε ^ p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, _root_.WittVector.frobeniusEquiv_apply,
      frobenius_cyclotomicMu, ← pow_mul, ← pow_succ]

/-- Iterated inverse Frobenius on `μ` replaces `ε` by `((_root_.frobeniusEquiv S p).symm^[j]) ε`.
-/
theorem iterate_frobeniusEquiv_symm_cyclotomicMu (ε : S) (j : ℕ) :
    ((frobeniusEquiv p S).symm^[j]) (cyclotomicMu p ε) =
      cyclotomicMu p (((_root_.frobeniusEquiv S p).symm^[j]) ε) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      frobeniusEquiv_symm_cyclotomicMu]

/-- For `ε ≠ 1`, `p` does not divide `φ⁻¹(μ)`. -/
theorem not_natCast_dvd_frobeniusEquiv_symm_cyclotomicMu {ε : S} (hε : ε ≠ 1) :
    ¬ (p : 𝕎 S) ∣ (frobeniusEquiv p S).symm (cyclotomicMu p ε) := by
  rw [← map_dvd_iff (frobeniusEquiv p S), map_natCast, RingEquiv.apply_symm_apply]
  exact not_natCast_dvd_cyclotomicMu p hε

/-- The inverse Frobenius of `ξ(ε) = ∑_{j < p} [ε ^ (1 / p)] ^ j` is `ξ(ε ^ (1 / p))`. -/
@[simp]
theorem frobeniusEquiv_symm_cyclotomicXi (ε : S) :
    (frobeniusEquiv p S).symm (cyclotomicXi p ε) =
      cyclotomicXi p ((_root_.frobeniusEquiv S p).symm ε) := by
  simp [cyclotomicXi_def, map_sum]

/-- Iterated inverse Frobenius on `ξ` replaces `ε` by `((_root_.frobeniusEquiv S p).symm^[j]) ε`.
-/
theorem iterate_frobeniusEquiv_symm_cyclotomicXi (ε : S) (j : ℕ) :
    ((frobeniusEquiv p S).symm^[j]) (cyclotomicXi p ε) =
      cyclotomicXi p (((_root_.frobeniusEquiv S p).symm^[j]) ε) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      frobeniusEquiv_symm_cyclotomicXi]

/-- The inverse Frobenius of `ξ'` is `ξ`. -/
@[simp]
theorem frobeniusEquiv_symm_cyclotomicXiTilde (ε : S) :
    (frobeniusEquiv p S).symm (cyclotomicXiTilde p ε) = cyclotomicXi p ε :=
  (frobeniusEquiv p S).symm_apply_apply (cyclotomicXi p ε)

/-- Iterated Frobenius on `ξ'` replaces `ε` by `ε ^ p ^ j`. -/
theorem iterate_frobeniusEquiv_cyclotomicXiTilde (ε : S) (j : ℕ) :
    ((frobeniusEquiv p S)^[j]) (cyclotomicXiTilde p ε) = cyclotomicXiTilde p (ε ^ p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, _root_.WittVector.frobeniusEquiv_apply,
      cyclotomicXiTilde_eq_sum, cyclotomicXiTilde_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_pow, frobenius_teichmuller, ← map_pow, ← pow_mul, pow_succ', mul_comm]

/-- **`μ = ξ · φ⁻¹(μ)`**: with `x = ε ^ (1 / p)`, this is the geometric sum identity
`[x] ^ p - 1 = (∑_{j < p} [x] ^ j) ([x] - 1)`. -/
theorem cyclotomicMu_eq_cyclotomicXi_mul (ε : S) :
    cyclotomicMu p ε = cyclotomicXi p ε * (frobeniusEquiv p S).symm (cyclotomicMu p ε) := by
  rw [frobeniusEquiv_symm_cyclotomicMu, cyclotomicXi_def, cyclotomicMu_def, cyclotomicMu_def,
    geom_sum_mul, ← map_pow, frobeniusEquiv_symm_pow_p]

/-- **`φ(μ) = ξ' · μ`**, the Frobenius twist of `cyclotomicMu_eq_cyclotomicXi_mul`. -/
theorem frobenius_cyclotomicMu_eq_cyclotomicXiTilde_mul (ε : S) :
    frobenius (cyclotomicMu p ε) = cyclotomicXiTilde p ε * cyclotomicMu p ε := by
  conv_lhs => rw [cyclotomicMu_eq_cyclotomicXi_mul]
  rw [map_mul, cyclotomicXiTilde_def, ← _root_.WittVector.frobeniusEquiv_apply,
    RingEquiv.apply_symm_apply]

/-- Zeroth Witt coordinate relation for `μ = ξ · φ⁻¹(μ)`: `ξ.coeff 0 · (ε ^ (1 / p) - 1) = ε - 1`.
-/
theorem cyclotomicXi_coeff_zero_mul (ε : S) :
    (cyclotomicXi p ε).coeff 0 * ((_root_.frobeniusEquiv S p).symm ε - 1) = ε - 1 := by
  simpa [mul_coeff_zero] using congrArg (·.coeff 0) (cyclotomicMu_eq_cyclotomicXi_mul p ε).symm

/-- Zeroth Witt coordinate relation for `φ(μ) = ξ' · μ`: `ξ'.coeff 0 · (ε - 1) = ε ^ p - 1`. -/
theorem cyclotomicXiTilde_coeff_zero_mul (ε : S) :
    (cyclotomicXiTilde p ε).coeff 0 * (ε - 1) = ε ^ p - 1 := by
  have h := congrArg (·.coeff 0) (frobenius_cyclotomicMu_eq_cyclotomicXiTilde_mul p ε).symm
  simpa [mul_coeff_zero, frobenius_cyclotomicMu] using h

/-- For `ε ≠ 1`, the zeroth Witt coordinate of `ξ` is nonzero: it divides `ε - 1 ≠ 0`. -/
theorem coeff_zero_cyclotomicXi_ne_zero {ε : S} (hε : ε ≠ 1) : (cyclotomicXi p ε).coeff 0 ≠ 0 :=
  fun h ↦ coeff_zero_cyclotomicMu_ne_zero p hε <| by
    rw [cyclotomicMu_coeff_zero, ← cyclotomicXi_coeff_zero_mul p ε, h, zero_mul]

/-- For `ε ≠ 1`, `ξ` is nonzero. -/
theorem cyclotomicXi_ne_zero {ε : S} (hε : ε ≠ 1) : cyclotomicXi p ε ≠ 0 :=
  fun h ↦ coeff_zero_cyclotomicXi_ne_zero p hε (by rw [h, zero_coeff])

/-- For `ε ≠ 1`, `ξ' = φ(ξ)` is nonzero. -/
theorem cyclotomicXiTilde_ne_zero {ε : S} (hε : ε ≠ 1) : cyclotomicXiTilde p ε ≠ 0 := by
  intro h
  rw [cyclotomicXiTilde_def, ← map_zero (frobenius : 𝕎 S →+* 𝕎 S)] at h
  exact cyclotomicXi_ne_zero p hε ((frobenius_bijective p S).1 h)

/-- Modulo the Jacobson radical of `S`, `W(q)` sends `ξ` to `p` whenever `ε - 1` lies in the
Jacobson radical of `S`. -/
theorem map_mk_jacobson_cyclotomicXi_eq_natCast {ε : S} (hε : ε - 1 ∈ Ring.jacobson S) :
    map (Ideal.Quotient.mk (Ring.jacobson S)) (cyclotomicXi p ε) = p := by
  have : IsReduced (S ⧸ Ring.jacobson S) :=
    (Ideal.isRadical_iff_quotient_reduced (Ring.jacobson S)).mp
      (Ideal.jacobson_bot (R := S) ▸ Ideal.isRadical_jacobson ⊥)
  refine map_cyclotomicXi_eq_natCast p ?_
  rw [← map_one (Ideal.Quotient.mk (Ring.jacobson S)), Ideal.Quotient.eq]
  exact hε

/-- **`ξ` is distinguished** (Bhatt–Morrow–Scholze, Example 3.16). If `ε - 1` lies in the
Jacobson radical of `S`, then the first Witt coordinate of `ξ = ∑_{j < p} [ε ^ (1 / p)] ^ j` is a
unit: modulo the Jacobson radical, `ε ^ (1 / p)` becomes `1` and `ξ` becomes `p`. -/
theorem isDistinguished_cyclotomicXi {ε : S} (hε : ε - 1 ∈ Ring.jacobson S) :
    (cyclotomicXi p ε).IsDistinguished := by
  let q := Ideal.Quotient.mk (Ring.jacobson S)
  have : IsLocalHom q := isLocalHom_of_le_jacobson le_rfl
  rw [isDistinguished_iff, ← isUnit_map_iff q, ← map_coeff,
    map_mk_jacobson_cyclotomicXi_eq_natCast p hε]
  rcases subsingleton_or_nontrivial (S ⧸ Ring.jacobson S) with _ | _
  · exact isUnit_of_subsingleton _
  · have : CharP (S ⧸ Ring.jacobson S) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr <| by
      rw [← map_natCast q, CharP.cast_eq_zero, map_zero]
    rw [coeff_p_one]
    exact isUnit_one

/-- **`ξ'` is distinguished.** If `ε - 1` lies in the Jacobson radical of `S`, then the first Witt
coordinate of `ξ' = φ(ξ)` is a unit: it is the `p`-th power of that of `ξ`. -/
theorem isDistinguished_cyclotomicXiTilde {ε : S} (hε : ε - 1 ∈ Ring.jacobson S) :
    (cyclotomicXiTilde p ε).IsDistinguished := by
  rw [cyclotomicXiTilde_def, isDistinguished_frobenius_iff]
  exact isDistinguished_cyclotomicXi p hε

end Perfect

end TauCeti.WittVector
