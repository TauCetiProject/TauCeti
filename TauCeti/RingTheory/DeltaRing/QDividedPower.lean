/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import TauCeti.Algebra.Ring.QInteger
public import TauCeti.RingTheory.DeltaRing.Basic

import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The q-divided power operation on δ-rings

Fix a prime `p`, a `δ`-ring `D` and an element `q : D`, and write
`[p]_q = TauCeti.QCrys.qInteger q p = ∑ i ∈ range p, q ^ i` for the `q`-analogue of `p` (so that
`[p]_q * (q - 1) = q ^ p - 1` and `[p]_1 = p`). This file develops the
operation `γ` underlying `q`-divided powers and `q`-crystalline cohomology:

* the ideal `N(D) = φ⁻¹([p]_q D)` of elements whose Frobenius is divisible by `[p]_q`
  (`TauCeti.QCrys.frobeniusPreimageIdeal`);
* for `x ∈ N(D)`, the element `γ x = φ x / [p]_q - δ x` (`TauCeti.QCrys.gamma`), characterised by
  `[p]_q * (γ x + δ x) = φ x` (`TauCeti.QCrys.pAnalog_mul_gamma`), and unique when `[p]_q` is a
  nonzerodivisor (`TauCeti.QCrys.gamma_eq_of_mul_eq`);
* the additivity and multiplicativity rules
  `γ (x + y) = γ x + γ y + ((x + y) ^ p - x ^ p - y ^ p) / p` and
  `γ (f * x) = φ f * γ x - x ^ p * δ f` (`TauCeti.QCrys.gamma_add`, `TauCeti.QCrys.gamma_mul`);
* for an ideal `I`, the ideal `TauCeti.QCrys.gammaIdeal` of the `x ∈ I ∩ N(D)` with `γ x ∈ I`. In
  particular the conditions `φ (I) ⊆ [p]_q D` and `γ (I) ⊆ I` defining a `q`-PD pair may be
  checked on generators of `I` (`TauCeti.QCrys.span_le_gammaIdeal_iff`);
* when `δ q = 0`: `q - 1 ∈ N(D)` with `γ (q - 1) = (q - 1) - δ (q - 1)`
  (`TauCeti.QCrys.sub_one_mem_frobeniusPreimageIdeal`, `TauCeti.QCrys.gamma_sub_one`), and the
  congruence `δ [p]_q ≡ 1` modulo `[p]_q` (`TauCeti.QCrys.delta_pAnalog_sub_one_mem`);
* at `q = 1`, where `[p]_q = p`, the operation is `x ↦ x ^ p / p`:
  `p * γ x = x ^ p` (`TauCeti.QCrys.natCast_mul_gamma_of_eq_one`).

The congruence `δ [p]_q ≡ 1` is proved universally: `δ [p]_q` is the image under `X ↦ q` of an
integral polynomial `G` with `p * G = [p]_{X ^ p} - [p]_X ^ p`, and since `[p]_X` is monic,
`[p]_X ∣ p * (G - 1)` forces `[p]_X ∣ G - 1` in `ℤ[X]`. No hypothesis on `p`-torsion in `D`
is needed.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  §16, Notation 16.1, Definition 16.2 and Remark 16.6.
-/

public section

open Finset Polynomial

namespace TauCeti

namespace QCrys

open DeltaRing

variable (p : ℕ) [Fact p.Prime] {D : Type*} [CommRing D] [DeltaRing p D] (q : D)

/-- The ideal `N(D) = φ⁻¹([p]_q D)` of a `δ`-ring `D` with an element `q`: the elements whose
Frobenius is divisible by `[p]_q = qInteger q p` (Bhatt and Scholze, *Prisms and prismatic
cohomology*, Notation 16.1). -/
def frobeniusPreimageIdeal : Ideal D :=
  (Ideal.span {qInteger q p}).comap (frobenius p D)

variable {p q}

theorem mem_frobeniusPreimageIdeal {x : D} :
    x ∈ frobeniusPreimageIdeal p q ↔ qInteger q p ∣ frobenius p D x := by
  rw [frobeniusPreimageIdeal, Ideal.mem_comap, Ideal.mem_span_singleton]

open scoped Classical in
variable (p q) in
/-- The `q`-divided power operation `γ x = φ x / [p]_q - δ x` on `N(D) = φ⁻¹([p]_q D)`, where
`[p]_q = qInteger q p` (Bhatt and Scholze, *Prisms and prismatic cohomology*,
Notation 16.1). For `x ∈ N(D)` it is characterised by `[p]_q * (γ x + δ x) = φ x`
(`pAnalog_mul_gamma`), uniquely when `[p]_q` is a nonzerodivisor (`gamma_eq_of_mul_eq`). Outside
`N(D)` it is `0` (`gamma_of_notMem`). -/
noncomputable def gamma (x : D) : D :=
  if h : qInteger q p ∣ frobenius p D x then h.choose - delta p x else 0

/-- The defining identity `[p]_q * (γ x + δ x) = φ x` of the `q`-divided power operation on
`N(D)`. -/
theorem pAnalog_mul_gamma {x : D} (hx : x ∈ frobeniusPreimageIdeal p q) :
    qInteger q p * (gamma p q x + delta p x) = frobenius p D x := by
  have h := mem_frobeniusPreimageIdeal.mp hx
  simp only [gamma, h, ↓reduceDIte, sub_add_cancel]
  exact h.choose_spec.symm

/-- Outside `N(D)` the operation `γ` takes the junk value `0`. -/
theorem gamma_of_notMem {x : D} (hx : x ∉ frobeniusPreimageIdeal p q) : gamma p q x = 0 := by
  simp [gamma, mem_frobeniusPreimageIdeal.not.mp hx]

/-- When `[p]_q` is a nonzerodivisor, `γ x` is the unique `y` with `[p]_q * (y + δ x) = φ x`. -/
theorem gamma_eq_of_mul_eq (hq : IsRegular (qInteger q p)) {x y : D}
    (h : qInteger q p * (y + delta p x) = frobenius p D x) : gamma p q x = y := by
  have hx : x ∈ frobeniusPreimageIdeal p q := mem_frobeniusPreimageIdeal.mpr ⟨_, h.symm⟩
  exact add_right_cancel (hq.left ((pAnalog_mul_gamma hx).trans h.symm))

/-- When `[p]_q` is a nonzerodivisor, `γ x = y` if and only if `[p]_q * (y + δ x) = φ x`, for
`x ∈ N(D)`. -/
theorem gamma_eq_iff (hq : IsRegular (qInteger q p)) {x y : D}
    (hx : x ∈ frobeniusPreimageIdeal p q) :
    gamma p q x = y ↔ qInteger q p * (y + delta p x) = frobenius p D x :=
  ⟨fun h => h ▸ pAnalog_mul_gamma hx, gamma_eq_of_mul_eq hq⟩

@[simp]
theorem gamma_zero (hq : IsRegular (qInteger q p)) : gamma p q (0 : D) = 0 :=
  gamma_eq_of_mul_eq hq (by simp)

/-- The sum rule `γ (x + y) = γ x + γ y + ((x + y) ^ p - x ^ p - y ^ p) / p`, where the last
quotient is the integral polynomial `-addCorrection p x y`. -/
theorem gamma_add (hq : IsRegular (qInteger q p)) {x y : D}
    (hx : x ∈ frobeniusPreimageIdeal p q) (hy : y ∈ frobeniusPreimageIdeal p q) :
    gamma p q (x + y) = gamma p q x + gamma p q y - addCorrection p x y := by
  refine gamma_eq_of_mul_eq hq ?_
  rw [map_add, ← pAnalog_mul_gamma hx, ← pAnalog_mul_gamma hy, delta_add]
  ring

/-- The product rule `γ (f * x) = φ f * γ x - x ^ p * δ f` for `x ∈ N(D)` and any `f`. -/
theorem gamma_mul (hq : IsRegular (qInteger q p)) (f : D) {x : D}
    (hx : x ∈ frobeniusPreimageIdeal p q) :
    gamma p q (f * x) = frobenius p D f * gamma p q x - x ^ p * delta p f := by
  refine gamma_eq_of_mul_eq hq ?_
  rw [map_mul, ← pAnalog_mul_gamma hx, delta_mul, frobenius_apply]
  ring

/-- At `q = 1`, where `[p]_q = p`, the operation `γ` is `x ↦ x ^ p / p`: `p * γ x = x ^ p` for
every `x ∈ N(D)`. No condition on `p`-torsion in `D` is needed. -/
theorem natCast_mul_gamma_of_eq_one (hq : q = 1) {x : D} (hx : x ∈ frobeniusPreimageIdeal p q) :
    (p : D) * gamma p q x = x ^ p := by
  subst hq
  have h := pAnalog_mul_gamma hx
  rw [qInteger_one_left, frobenius_apply] at h
  linear_combination h

section DeltaZero

variable (hq : delta p q = 0)
include hq

/-- If `δ q = 0`, then `φ (q - 1) = [p]_q * (q - 1)`. -/
theorem frobenius_sub_one_of_delta_eq_zero :
    frobenius p D (q - 1) = qInteger q p * (q - 1) := by
  rw [map_sub, map_one, frobenius_apply_of_delta_eq_zero hq, qInteger_mul_sub_one]

/-- If `δ q = 0`, then `q - 1 ∈ N(D)`. -/
theorem sub_one_mem_frobeniusPreimageIdeal : q - 1 ∈ frobeniusPreimageIdeal p q :=
  mem_frobeniusPreimageIdeal.mpr ⟨_, frobenius_sub_one_of_delta_eq_zero hq⟩

/-- If `δ q = 0` and `[p]_q` is a nonzerodivisor, then `γ (q - 1) = (q - 1) - δ (q - 1)`. -/
theorem gamma_sub_one (hreg : IsRegular (qInteger q p)) :
    gamma p q (q - 1) = q - 1 - delta p (q - 1) :=
  gamma_eq_of_mul_eq hreg (by rw [sub_add_cancel, frobenius_sub_one_of_delta_eq_zero hq])

omit [Fact p.Prime] in
/-- If `δ q = 0`, then `δ [n]_q = ∑ k < n, addCorrection p [k]_q (q ^ k)`. -/
theorem delta_qInteger_of_delta_eq_zero (n : ℕ) :
    delta p (qInteger q n) = ∑ k ∈ range n, addCorrection p (qInteger q k) (q ^ k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qInteger_succ, delta_add, ih, delta_pow_eq_zero hq, sum_range_succ, add_zero]

end DeltaZero

/-- The universal polynomial identity behind `delta_pAnalog_sub_one_mem`: in `ℤ[X]`, the
polynomial `G = ∑ k < p, addCorrection p [k]_X (X ^ k)` satisfies `G ≡ 1` modulo
`[p]_X`. -/
private theorem qInteger_X_dvd_addCorrection_sum_sub_one :
    qInteger (X : ℤ[X]) p ∣ ∑ k ∈ range p, addCorrection p (qInteger X k) (X ^ k) - 1 := by
  simp only [qInteger_eq_sum]
  set Φ : ℤ[X] := ∑ i ∈ range p, X ^ i
  set G : ℤ[X] := ∑ k ∈ range p, addCorrection p (∑ i ∈ range k, (X : ℤ[X]) ^ i) (X ^ k)
  have hp : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  -- `p * G = ∑ k < p, X ^ (p * k) - Φ ^ p` by telescoping.
  have hG : (p : ℤ[X]) * G = ∑ k ∈ range p, ((X : ℤ[X]) ^ p) ^ k - Φ ^ p := by
    simp only [G, mul_sum, natCast_mul_addCorrection]
    have := sum_range_sub (fun k => (∑ i ∈ range k, (X : ℤ[X]) ^ i) ^ p) p
    simp only [sum_range_succ, sum_range_zero, zero_pow (Fact.out : p.Prime).ne_zero,
      sub_zero] at this
    rw [← this, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    ring
  -- Each `X ^ (p * k) - 1` is divisible by `X ^ p - 1 = Φ * (X - 1)`, so `Φ ∣ p * (G - 1)`.
  have hdvd : Φ ∣ (p : ℤ) • (G - 1) := by
    have h1 : Φ ∣ ∑ k ∈ range p, (((X : ℤ[X]) ^ p) ^ k - 1) := by
      refine dvd_sum fun k _ => ?_
      have := sub_dvd_pow_sub_pow ((X : ℤ[X]) ^ p) 1 k
      rw [one_pow, ← geom_sum_mul] at this
      exact (dvd_mul_right _ _).trans this
    rw [sum_sub_distrib, sum_const, card_range, nsmul_one] at h1
    rw [zsmul_eq_mul, Int.cast_natCast, mul_sub, hG, mul_one]
    convert h1.sub (dvd_pow_self Φ (Fact.out : p.Prime).ne_zero) using 1
    ring
  -- Since `Φ` is monic, the factor `p` cancels.
  have hΦ : Φ.Monic := monic_geom_sum_X (Fact.out : p.Prime).ne_zero
  rw [← modByMonic_eq_zero_iff_dvd hΦ] at hdvd ⊢
  rw [smul_modByMonic] at hdvd
  exact (smul_eq_zero.mp hdvd).resolve_left hp

/-- If `δ q = 0`, then `δ [p]_q ≡ 1` modulo `[p]_q`, where `[p]_q = qInteger q p`
(Bhatt and Scholze, *Prisms and prismatic cohomology*, Remark 16.6). This holds in every
`δ`-ring, with no condition on `p`-torsion. -/
theorem delta_pAnalog_sub_one_mem (hq : delta p q = 0) :
    delta p (qInteger q p) - 1 ∈ Ideal.span {qInteger q p} := by
  rw [Ideal.mem_span_singleton, delta_qInteger_of_delta_eq_zero hq]
  have := map_dvd (aeval q) (qInteger_X_dvd_addCorrection_sum_sub_one (p := p))
  simpa [map_addCorrection] using this

/-- For an ideal `I` of `D`, the ideal of `x ∈ I` with `φ x ∈ [p]_q D` and `γ x ∈ I`, where `[p]_q`
is assumed to be a nonzerodivisor. The conditions `φ (I) ⊆ [p]_q D` and `γ (I) ⊆ I` say that
`I ≤ gammaIdeal hq I`, and can be checked on generators (`span_le_gammaIdeal_iff`). -/
def gammaIdeal (hq : IsRegular (qInteger q p)) (I : Ideal D) : Ideal D where
  carrier := {x | x ∈ I ∧ x ∈ frobeniusPreimageIdeal p q ∧ gamma p q x ∈ I}
  zero_mem' := ⟨I.zero_mem, Ideal.zero_mem _, by rw [gamma_zero hq]; exact I.zero_mem⟩
  add_mem' := by
    rintro x y ⟨hxI, hxN, hxγ⟩ ⟨hyI, hyN, hyγ⟩
    refine ⟨I.add_mem hxI hyI, Ideal.add_mem _ hxN hyN, ?_⟩
    rw [gamma_add hq hxN hyN]
    exact I.sub_mem (I.add_mem hxγ hyγ) (addCorrection_mem_of_mem_left y hxI)
  smul_mem' := by
    rintro f x ⟨hxI, hxN, hxγ⟩
    refine ⟨I.mul_mem_left f hxI, Ideal.mul_mem_left _ f hxN, ?_⟩
    rw [smul_eq_mul, gamma_mul hq f hxN]
    exact I.sub_mem (I.mul_mem_left _ hxγ)
      (I.mul_mem_right _ (I.pow_mem_of_mem hxI p (Fact.out : p.Prime).pos))

@[simp]
theorem mem_gammaIdeal (hq : IsRegular (qInteger q p)) {I : Ideal D} {x : D} :
    x ∈ gammaIdeal hq I ↔ x ∈ I ∧ x ∈ frobeniusPreimageIdeal p q ∧ gamma p q x ∈ I :=
  Iff.rfl

theorem gammaIdeal_le (hq : IsRegular (qInteger q p)) (I : Ideal D) :
    gammaIdeal hq I ≤ I :=
  fun _ hx => hx.1

theorem gammaIdeal_le_frobeniusPreimageIdeal (hq : IsRegular (qInteger q p))
    (I : Ideal D) : gammaIdeal hq I ≤ frobeniusPreimageIdeal p q :=
  fun _ hx => hx.2.1

/-- The conditions defining `gammaIdeal hq I` hold on the ideal generated by `S` as soon as they
hold on `S`. In particular `φ (span S) ⊆ [p]_q D` and `γ (span S) ⊆ span S` if and only if every
`s ∈ S` has `φ s ∈ [p]_q D` and `γ s ∈ span S`. -/
theorem span_le_gammaIdeal_iff (hq : IsRegular (qInteger q p)) {I : Ideal D}
    {S : Set D} :
    Ideal.span S ≤ gammaIdeal hq I ↔
      ∀ s ∈ S, s ∈ I ∧ s ∈ frobeniusPreimageIdeal p q ∧ gamma p q s ∈ I := by
  simp only [Ideal.span_le, Set.subset_def, SetLike.mem_coe, mem_gammaIdeal]

end QCrys

end TauCeti
