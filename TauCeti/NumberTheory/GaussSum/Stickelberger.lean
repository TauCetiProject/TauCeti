/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.Data.List.Prime
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.NumberTheory.JacobiSum.Basic
import TauCeti.NumberTheory.GaussSum.Basic
import TauCeti.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# Stickelberger's congruence for Gauss sums

Let `F` be a finite field with `q = p ^ f` elements, `R` a domain and `P` a maximal ideal of `R`
whose residue ring receives `F` through `f : F →+* R ⧸ P`. Let `ω : F → R` be a Teichmüller
character, a multiplicative character lifting `f` (`ω x ≡ f x (mod P)`), and let
`ψ(x) = ζ ^ Tr(x)` for an element `ζ` of `R`, `Tr` being the trace from `F` to `𝔽_p`; necessarily
`ζ ^ p = 1`. For `0 ≤ a < q - 1` with base-`p` digits `aᵢ`, put `s = ∑ aᵢ` and `h = ∏ aᵢ!`.
**Stickelberger's congruence** states that

  `h · (-g(ω⁻ᵃ, ψ)) ≡ (ζ - 1) ^ s (mod P ^ (s + 1))`.

Since `h` is prime to `p`, the Gauss sum `g(ω⁻ᵃ, ψ)` lies in `P ^ s`, and when `ζ - 1` has
valuation exactly `1` at `P` the Gauss sum has valuation exactly `s`. For `ζ` a primitive `p`-th
root of unity `p` then has valuation `p - 1`, so the valuation normalised by `v(p) = 1` gives the
Gauss sum the value `s / (p - 1)`. The standard instance is the ring of integers of
`ℚ(ζ_p, ζ_(q-1))`, a prime `P` above `p` and the Teichmüller character of its residue field; the
statements here only use the congruence data above.

The congruence determines the prime factorisation of Gauss sums, which is the input to
Stickelberger's theorem on the annihilation of class groups and to the Gross–Koblitz formula.

## Main results

* `TauCeti.stickelberger_congruence`: `h · (-g(ω⁻ᵃ, ψ)) ≡ (ζ - 1) ^ s (mod P ^ (s + 1))`.
* `TauCeti.gaussSum_inv_pow_mem_pow`: `g(ω⁻ᵃ, ψ) ∈ P ^ s`.
* `TauCeti.intValuation_gaussSum_inv_pow`: in a Dedekind domain, if `v(ζ - 1) = 1` then
  `v(g(ω⁻ᵃ, ψ)) = s`.
* `TauCeti.intValuation_gaussSum_inv_pow_pow_sub_one`: if moreover `ζ` is a primitive `p`-th root
  of unity, then `(p - 1) v(g(ω⁻ᵃ, ψ)) = s v(p)`.

## Implementation notes

Write `T(a) = -g(ω⁻ᵃ, ψ)` and `π = ζ - 1`. The case `a = 0` is `T(0) = 1 - ∑ ψ ≡ 1`. For `a = 1`,
expand `ψ(x) = (1 + π) ^ Tr(x) ≡ 1 + Tr(x) π (mod P ^ 2)`; since `ω⁻¹(x) ≡ x⁻¹ (mod P)` and
`∑ x⁻¹ Tr(x) = ∑ᵢ ∑ x ^ (pⁱ - 1) = -1` in `F`, this gives `T(1) ≡ π (mod P ^ 2)`. The relation
`g(ω⁻¹) g(ω⁻ˣ) = J(ω⁻¹, ω⁻ˣ) g(ω⁻⁽ˣ⁺¹⁾)` together with `J(ω⁻¹, ω⁻ˣ) ≡ -(x + 1) (mod P)`, a power
sum computation in `F`, raises the last digit by one; the invariance `g(χ ^ p, ψ) = g(χ, ψ)` under
the Frobenius shifts the digits, giving `T(p y) = T(y)`. Induction on `a = a₀ + p y` assembles the
digits. Only the leading term is tracked, so no multinomial congruence is needed.

## References

* K. Conrad, *Jacobi sums and Stickelberger's congruence*, Theorem 1.
* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §6.2.
-/

public section

open Finset

namespace TauCeti

/-- A power of a maximal ideal is primary: if `x ∉ P` and `x * y ∈ P ^ n`, then `y ∈ P ^ n`. -/
private theorem mem_pow_of_mul_mem {R : Type*} [CommRing R] {P : Ideal R} [P.IsMaximal] {n : ℕ}
    {x y : R} (hx : x ∉ P) (hxy : x * y ∈ P ^ n) : y ∈ P ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hrad : (P ^ n).radical = P := by
    rw [Ideal.radical_pow P hn.ne', Ideal.IsPrime.radical inferInstance]
  have hmax : (P ^ n).radical.IsMaximal := by rw [hrad]; infer_instance
  have hprim := Ideal.isPrimary_iff.1 (Ideal.isPrimary_of_isMaximal_radical hmax)
  rw [mul_comm] at hxy
  exact (hprim.2 hxy).resolve_right (by rwa [hrad])

/-- `(1 + π) ^ t ≡ 1 + t π` modulo `P ^ 2` when `π ∈ P`. -/
private theorem one_add_pow_sub_mem {R : Type*} [CommRing R] {P : Ideal R} {π : R} (hπ : π ∈ P)
    (t : ℕ) :
    (1 + π) ^ t - (1 + t * π) ∈ P ^ 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h : (1 + π) ^ (t + 1) - (1 + (t + 1 : ℕ) * π) =
        (1 + π) * ((1 + π) ^ t - (1 + t * π)) + t * (π * π) := by push_cast; ring
    rw [h]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih)
      (Ideal.mul_mem_left _ _ (by rw [pow_two]; exact Ideal.mul_mem_mul hπ hπ))

section

variable {p : ℕ} [hp : Fact p.Prime] {F : Type*} [Field F] [Fintype F] [Algebra (ZMod p) F]
  {R : Type*} [CommRing R] {P : Ideal R} {f : F →+* R ⧸ P} {ω : MulChar F R}

/-- Modulo `P`, the character `ω⁻ᵃ` is `x ↦ x ^ (q - 1 - a)` for `a < q - 1`. -/
private theorem mk_inv_pow_apply (hω : ∀ x, Ideal.Quotient.mk P (ω x) = f x) {a : ℕ}
    (ha : a < Fintype.card F - 1) (x : F) :
    Ideal.Quotient.mk P ((ω⁻¹ ^ a) x) = f (x ^ (Fintype.card F - 1 - a)) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [MulChar.map_zero, zero_pow (by omega), map_zero, map_zero]
  rw [← Units.val_mk0 hx, MulChar.pow_apply_coe, MulChar.inv_apply', map_pow, hω, ← map_pow,
    Units.val_mk0, inv_pow]
  congr 1
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← pow_add, Nat.sub_add_cancel ha.le, FiniteField.pow_card_sub_one_eq_one x hx]

/-- The power sums `∑ x, x ^ m` of a finite field of cardinality `q`, for `0 < m < 2 (q - 1)`. -/
private theorem sum_pow_of_pos_of_lt {m : ℕ} (hm : 0 < m)
    (hm' : m < 2 * (Fintype.card F - 1)) :
    ∑ x : F, x ^ m = if m = Fintype.card F - 1 then -1 else 0 := by
  classical
  have hsum : ∑ x : F, x ^ m = ∑ x : Fˣ, (x : F) ^ m := by
    let ι : Fˣ ↪ F := ⟨(↑), Units.val_injective⟩
    refine Eq.trans ?_ (Finset.sum_map univ ι (· ^ m))
    refine (Finset.sum_subset (subset_univ _) fun x _ hx ↦ ?_).symm
    have : x = 0 := by
      by_contra h
      exact hx (mem_map.2 ⟨Units.mk0 x h, mem_univ _, rfl⟩)
    simp [this, hm.ne']
  rw [hsum, FiniteField.sum_pow_units]
  congr 1
  refine propext ⟨fun ⟨k, hk⟩ ↦ ?_, fun h ↦ h ▸ dvd_rfl⟩
  have hk1 : k = 1 := by
    rcases k with _ | _ | k
    · omega
    · rfl
    · nlinarith
  rw [hk, hk1, mul_one]

omit [Algebra (ZMod p) F] in
/-- The finite-field sum `∑ y, y ^ (q - 2) (1 - y) ^ n` equals `n` for `n ≤ q - 1`. -/
private theorem sum_pow_mul_one_sub_pow (hq : 2 < Fintype.card F) {n : ℕ}
    (hn : n ≤ Fintype.card F - 1) :
    ∑ y : F, y ^ (Fintype.card F - 2) * (1 - y) ^ n = n := by
  have h : ∀ y : F, y ^ (Fintype.card F - 2) * (1 - y) ^ n =
      ∑ m ∈ range (n + 1), (-1) ^ m * (n.choose m : F) * y ^ (Fintype.card F - 2 + m) := by
    intro y
    rw [sub_eq_neg_add, add_pow, mul_sum]
    refine sum_congr rfl fun m _ ↦ ?_
    rw [neg_pow, one_pow, pow_add]
    ring
  simp_rw [h]
  rw [sum_comm]
  simp_rw [← mul_sum]
  rw [sum_eq_single 1]
  · rw [sum_pow_of_pos_of_lt (by omega) (by omega), ite_eq_left (by omega)]
    simp
  · intro m hm hm1
    rw [mem_range] at hm
    rw [sum_pow_of_pos_of_lt (by omega) (by omega), ite_eq_right (by omega), mul_zero]
  · intro h1
    rw [mem_range, not_lt] at h1
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- `∑ x, x⁻¹ Tr(x) = -1`, with `x⁻¹` written `x ^ (q - 2)`. -/
private theorem sum_pow_mul_trace (hq : 2 < Fintype.card F) :
    ∑ x : F, x ^ (Fintype.card F - 2) * algebraMap (ZMod p) F (Algebra.trace (ZMod p) F x) =
      -1 := by
  have hcard : Fintype.card F = p ^ Module.finrank (ZMod p) F := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hn : 0 < Module.finrank (ZMod p) F := by
    rcases Nat.eq_zero_or_pos (Module.finrank (ZMod p) F) with h | h
    · rw [h, pow_zero] at hcard; omega
    · exact h
  simp_rw [FiniteField.algebraMap_trace_eq_sum_pow, Nat.card_zmod, mul_sum, ← pow_add]
  rw [sum_comm, sum_eq_single_of_mem 0 (mem_range.2 hn)]
  · rw [pow_zero, sum_pow_of_pos_of_lt (by omega) (by omega), ite_eq_left (by omega)]
  · intro i hi hi0
    have hlt : p ^ i < Fintype.card F := hcard ▸ Nat.pow_lt_pow_right hp.out.one_lt (mem_range.1 hi)
    have hge : 2 ≤ p ^ i := le_trans hp.out.two_le (Nat.le_self_pow hi0 p)
    rw [sum_pow_of_pos_of_lt (by omega) (by omega), ite_eq_right (by omega)]

variable [P.IsMaximal]

omit [Fintype F] in
include f in
/-- The residue ring `R ⧸ P` has characteristic `p`. -/
private theorem charP_quotient : CharP (R ⧸ P) p :=
  have : CharP F p := charP_of_injective_algebraMap' (ZMod p) p
  charP_of_injective_ringHom f.injective p

omit [Fintype F] in
include f in
/-- A natural number lies in `P` exactly when `p` divides it. -/
private theorem natCast_mem_iff (n : ℕ) : (n : R) ∈ P ↔ p ∣ n := by
  have := charP_quotient (p := p) (f := f)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff (R ⧸ P) p]

omit [Fintype F] [P.IsMaximal] in
/-- The reduction of the natural-number lift of `z : ZMod p` is the image of `z` in `F`. -/
private theorem mk_natCast_val (z : ZMod p) :
    Ideal.Quotient.mk P (z.val : R) = f (algebraMap (ZMod p) F z) := by
  rw [map_natCast, ← map_natCast f, ← map_natCast (algebraMap (ZMod p) F), ZMod.natCast_zmod_val]

omit [P.IsMaximal] in
include f in
/-- The cardinality of `F` vanishes in `R ⧸ P`. -/
private theorem mk_natCast_card : (Fintype.card F : R ⧸ P) = 0 := by
  rw [← map_natCast f, FiniteField.cast_card_eq_zero, map_zero]

variable {ζ : R} {ψ : AddChar F R}

omit [Fintype F] [P.IsMaximal] in
/-- `ζ` is a `p`-th root of unity, since `ψ` takes the value `ζ` where the trace is `1`. -/
private theorem zeta_pow_eq_one [Finite F]
    (hψ : ∀ x, ψ x = ζ ^ (Algebra.trace (ZMod p) F x).val) : ζ ^ p = 1 := by
  have : CharP F p := charP_of_injective_algebraMap' (ZMod p) p
  obtain ⟨x, hx⟩ := Algebra.trace_surjective (ZMod p) F 1
  have h := hψ x
  rw [hx, ZMod.val_one, pow_one] at h
  rw [← h, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, CharP.cast_eq_zero F p, zero_mul,
    AddChar.map_zero_eq_one]

omit [Fintype F] in
include f in
/-- `ζ - 1 ∈ P`, since `ζ ^ p = 1` and `R ⧸ P` has characteristic `p`. -/
private theorem sub_one_mem [Finite F]
    (hψ : ∀ x, ψ x = ζ ^ (Algebra.trace (ZMod p) F x).val) : ζ - 1 ∈ P := by
  have := charP_quotient (p := p) (f := f)
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← pow_eq_zero_iff hp.out.ne_zero, map_sub, sub_pow_char,
    ← map_pow, zeta_pow_eq_one hψ, map_one, one_pow, sub_self]

omit [Fintype F] in
include f in
/-- The values of `ψ` are congruent to `1` modulo `P`. -/
private theorem mk_apply [Finite F]
    (hψ : ∀ x, ψ x = ζ ^ (Algebra.trace (ZMod p) F x).val) (x : F) :
    Ideal.Quotient.mk P (ψ x) = 1 := by
  have h := Ideal.Quotient.eq_zero_iff_mem.2 (sub_one_mem (f := f) hψ)
  rw [map_sub, map_one, sub_eq_zero] at h
  rw [hψ, map_pow, h, one_pow]

omit [Fintype F] [P.IsMaximal] in
/-- The character `x ↦ ζ ^ Tr(x)` is invariant under the Frobenius. -/
private theorem apply_pow_char [Finite F]
    (hψ : ∀ x, ψ x = ζ ^ (Algebra.trace (ZMod p) F x).val) (x : F) :
    ψ (x ^ p) = ψ x := by
  have h : x ^ p = FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F x := by
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card]
  rw [hψ, hψ, h, Algebra.trace_eq_of_algEquiv]

/-- The characters `ω⁻ᵃ` are nontrivial for `0 < a < q - 1`. -/
private theorem inv_pow_ne_one (hω : ∀ x, Ideal.Quotient.mk P (ω x) = f x) {a : ℕ} (ha0 : 0 < a)
    (ha : a < Fintype.card F - 1) : ω⁻¹ ^ a ≠ 1 := by
  classical
  intro h
  have h1 := congrArg (fun χ : MulChar F R ↦ Ideal.Quotient.mk P (∑ x, χ x)) h
  simp only [map_sum, mk_inv_pow_apply hω ha] at h1
  rw [← map_sum, FiniteField.sum_pow_lt_card_sub_one _ _ (by omega), map_zero, ← map_sum,
    MulChar.sum_one_eq_card_units, Fintype.card_units, map_natCast,
    Nat.cast_sub Fintype.card_pos, mk_natCast_card (f := f), Nat.cast_one, zero_sub] at h1
  exact one_ne_zero (neg_eq_zero.1 h1.symm)

omit [P.IsMaximal] in
/-- `J(ω⁻¹, ω⁻ˣ) ≡ -(x + 1)` modulo `P` for `x < q - 1`. -/
private theorem mk_jacobiSum (hω : ∀ x, Ideal.Quotient.mk P (ω x) = f x) (hq : 2 < Fintype.card F)
    {x : ℕ} (hx : x < Fintype.card F - 1) :
    Ideal.Quotient.mk P (jacobiSum ω⁻¹ (ω⁻¹ ^ x)) = -((x : R ⧸ P) + 1) := by
  have h1 : ∀ y, Ideal.Quotient.mk P (ω⁻¹ y) = f (y ^ (Fintype.card F - 2)) := fun y ↦ by
    rw [← pow_one ω⁻¹, mk_inv_pow_apply hω (by omega), Nat.sub_sub]
  simp only [jacobiSum, map_sum, map_mul, h1, mk_inv_pow_apply hω hx]
  simp only [← map_mul]
  rw [← map_sum, sum_pow_mul_one_sub_pow hq (by omega), map_natCast,
    Nat.cast_sub (by omega), Nat.cast_sub Fintype.card_pos, mk_natCast_card (f := f)]
  ring

/-- The case `a = 0`: `-g(1, ψ) ≡ 1` modulo `P`. -/
private theorem neg_gaussSum_one_sub_mem (hω : ∀ x, Ideal.Quotient.mk P (ω x) = f x)
    (hψ : ∀ x, ψ x = ζ ^ (Algebra.trace (ZMod p) F x).val) :
    -gaussSum 1 ψ - 1 ∈ P := by
  have h0 : ∀ y, Ideal.Quotient.mk P ((1 : MulChar F R) y) = f (y ^ (Fintype.card F - 1)) :=
    fun y ↦ by
      rw [← pow_zero ω⁻¹, mk_inv_pow_apply hω (by have := Fintype.one_lt_card (α := F); omega),
        Nat.sub_zero]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_neg, gaussSum, map_sum]
  simp only [map_mul, h0, mk_apply (f := f) hψ, mul_one]
  have := Fintype.one_lt_card (α := F)
  rw [← map_sum, sum_pow_of_pos_of_lt (by omega) (by omega), ite_eq_left rfl, map_neg, map_one,
    map_one, neg_neg, sub_self]

/-- The case `a = 1`: `-g(ω⁻¹, ψ) ≡ ζ - 1` modulo `P ^ 2`. -/
private theorem neg_gaussSum_inv_sub_mem [IsDomain R] (hω : ∀ x, Ideal.Quotient.mk P (ω x) = f x)
    (hψ : ∀ x, ψ x = ζ ^ (Algebra.trace (ZMod p) F x).val) (hq : 2 < Fintype.card F) :
    -gaussSum ω⁻¹ ψ - (ζ - 1) ∈ P ^ 2 := by
  set π := ζ - 1 with hπ_def
  have hπ : π ∈ P := sub_one_mem (f := f) hψ
  set t : F → R := fun x ↦ ((Algebra.trace (ZMod p) F x).val : R) with ht
  have he : ∀ x, ψ x - (1 + t x * π) ∈ P ^ 2 := fun x ↦ by
    rw [hψ, show ζ = 1 + π by rw [hπ_def]; ring]
    exact one_add_pow_sub_mem hπ _
  have hsum : ∑ x, ω⁻¹ x = 0 :=
    MulChar.sum_eq_zero_of_ne_one (by simpa using inv_pow_ne_one hω one_pos (by omega) (a := 1))
  have hmk : ∑ x, ω⁻¹ x * t x + 1 ∈ P := by
    have h1 : ∀ y, Ideal.Quotient.mk P (ω⁻¹ y) = f (y ^ (Fintype.card F - 2)) := fun y ↦ by
      rw [← pow_one ω⁻¹, mk_inv_pow_apply hω (by omega), Nat.sub_sub]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_sum]
    simp only [map_mul, h1, ht, mk_natCast_val (f := f)]
    simp only [← map_mul]
    rw [← map_sum, sum_pow_mul_trace hq, map_neg, map_one, map_one, neg_add_cancel]
  have hg : gaussSum ω⁻¹ ψ = ∑ x, ω⁻¹ x +
      (π * ∑ x, ω⁻¹ x * t x + ∑ x, ω⁻¹ x * (ψ x - (1 + t x * π))) := by
    rw [gaussSum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun x _ ↦ by ring
  rw [hsum, zero_add] at hg
  rw [hg, show ∀ a b : R, -(π * a + b) - π = -(π * (a + 1)) - b from fun a b ↦ by ring]
  refine Ideal.sub_mem _ ((Ideal.neg_mem_iff _).2 ?_) (Ideal.sum_mem _ fun x _ ↦
    Ideal.mul_mem_left _ _ (he x))
  rw [pow_two]
  exact Ideal.mul_mem_mul hπ hmk

omit [P.IsMaximal] in
/-- `P ^ m * P ^ n ⊆ P ^ (m + n)`, elementwise. -/
private theorem mem_pow_add_mul {m n : ℕ} {x y : R} (hx : x ∈ P ^ m) (hy : y ∈ P ^ n) :
    x * y ∈ P ^ (m + n) := by
  rw [pow_add]; exact Ideal.mul_mem_mul hx hy

/-- One step of the induction: from `h G ≡ π ^ s (mod P ^ (s + 1))`, `G₁ ≡ π (mod P ^ 2)` and
`G₁ G = u G'` with `u ≡ c (mod P)`, deduce `h' G' ≡ π ^ (s + 1) (mod P ^ (s + 2))` for any
`h' ≡ h c (mod P)` outside `P`. -/
private theorem step_mem {G₁ G G' u π c h h' : R} {s : ℕ} (hπ : π ∈ P) (hG₁ : G₁ - π ∈ P ^ 2)
    (hG : h * G - π ^ s ∈ P ^ (s + 1)) (hrel : G₁ * G = u * G') (hu : u - c ∈ P)
    (hh' : h' - h * c ∈ P) (hh'P : h' ∉ P) :
    h' * G' - π ^ (s + 1) ∈ P ^ (s + 1 + 1) := by
  have hcP : h * c ∉ P := fun hc ↦ hh'P (by simpa using Ideal.add_mem _ hh' hc)
  have hhP : h ∉ P := fun hh ↦ hcP (Ideal.mul_mem_right _ _ hh)
  have huP : u ∉ P := fun hu' ↦ hcP (Ideal.mul_mem_left _ _ (by simpa using Ideal.sub_mem _ hu' hu))
  have hπs : π ^ s ∈ P ^ s := Ideal.pow_mem_pow hπ s
  have hG₁P : G₁ ∈ P := by
    simpa using Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero hG₁) hπ
  have hGs : G ∈ P ^ s := mem_pow_of_mul_mem hhP (by
    simpa using Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ s) hG) hπs)
  have hG' : G' ∈ P ^ (s + 1) := mem_pow_of_mul_mem huP (by
    rw [← hrel, add_comm]; exact mem_pow_add_mul (by rwa [pow_one]) hGs)
  have key : h' * G' - π ^ (s + 1) =
      (h' - h * u) * G' + ((h * G - π ^ s) * G₁ + π ^ s * (G₁ - π)) := by
    linear_combination (-h) * hrel
  rw [key]
  refine Ideal.add_mem _ ?_ (Ideal.add_mem _ ?_ ?_)
  · have : h' - h * u ∈ P := by
      simpa [mul_sub] using Ideal.sub_mem _ hh' (Ideal.mul_mem_left _ h hu)
    rw [add_comm]
    exact mem_pow_add_mul (m := 1) (by rwa [pow_one]) hG'
  · exact mem_pow_add_mul (n := 1) hG (by rwa [pow_one])
  · rw [show s + 1 + 1 = s + 2 by ring]; exact mem_pow_add_mul hπs hG₁

omit [Fintype F] [Algebra (ZMod p) F] [P.IsMaximal] in
include hp in
/-- Digit sum and digit factorial product of `j + p y` for a digit `j < p`. -/
private theorem digits_add_mul {j : ℕ} (hj : j < p) (y : ℕ) :
    (Nat.digits p (j + p * y)).sum = j + (Nat.digits p y).sum ∧
      ((Nat.digits p (j + p * y)).map Nat.factorial).prod =
        j.factorial * ((Nat.digits p y).map Nat.factorial).prod := by
  rcases eq_or_ne j 0 with rfl | hj0
  · rcases eq_or_ne y 0 with rfl | hy0
    · simp
    rw [Nat.digits_add p hp.out.one_lt 0 y hj (Or.inr hy0)]
    simp
  rw [Nat.digits_add p hp.out.one_lt j y hj (Or.inl hj0)]
  simp

omit [Fintype F] [Algebra (ZMod p) F] [P.IsMaximal] in
include hp in
/-- `p` does not divide the product of the factorials of the base-`p` digits of `n`. -/
private theorem not_dvd_prod_factorial_digits (n : ℕ) :
    ¬p ∣ ((Nat.digits p n).map Nat.factorial).prod := by
  rw [hp.out.prime.dvd_prod_iff]
  rintro ⟨_, hm, hdvd⟩
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hm
  exact absurd ((Nat.Prime.dvd_factorial hp.out).1 hdvd)
    (not_le.2 (Nat.digits_lt_base hp.out.one_lt hd))

/-- The inductive core of Stickelberger's congruence. -/
private theorem stickelberger_aux [IsDomain R] (hω : ∀ x, Ideal.Quotient.mk P (ω x) = f x)
    (hψ : ∀ x, ψ x = ζ ^ (Algebra.trace (ZMod p) F x).val) (a : ℕ)
    (ha : a < Fintype.card F - 1) :
    (((Nat.digits p a).map Nat.factorial).prod : R) * -gaussSum (ω⁻¹ ^ a) ψ -
      (ζ - 1) ^ (Nat.digits p a).sum ∈ P ^ ((Nat.digits p a).sum + 1) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  rcases eq_or_ne a 0 with rfl | ha0
  · simpa using neg_gaussSum_one_sub_mem hω hψ
  set y := a / p
  have hdiv : a % p + p * y = a := Nat.mod_add_div a p
  have hy := ih y (Nat.div_lt_self (Nat.pos_of_ne_zero ha0) hp.out.one_lt)
    (lt_of_le_of_lt (Nat.div_le_self a p) ha)
  -- Frobenius invariance: `T (p * y) = T y`.
  have : CharP F p := charP_of_injective_algebraMap' (ZMod p) p
  rw [← gaussSum_pow_char _ (apply_pow_char hψ), ← pow_mul] at hy
  -- Climb from `p * y` to `a = a % p + p * y` one unit at a time.
  have hclimb : ∀ j ≤ a % p, ((j.factorial * ((Nat.digits p y).map Nat.factorial).prod : ℕ) : R) *
      -gaussSum (ω⁻¹ ^ (j + p * y)) ψ - (ζ - 1) ^ (j + (Nat.digits p y).sum) ∈
        P ^ (j + (Nat.digits p y).sum + 1) := by
    intro j hj
    induction j with
    | zero => simpa [mul_comm p] using hy
    | succ j ihj =>
      have hjp : j + 1 < p := lt_of_le_of_lt hj (Nat.mod_lt _ hp.out.pos)
      have hxa : j + 1 + p * y ≤ a := by omega
      have hq : 2 < Fintype.card F := by omega
      have hrel := jacobiSum_mul_nontrivial (χ := ω⁻¹) (φ := ω⁻¹ ^ (j + p * y))
        (by rw [← pow_succ']; exact inv_pow_ne_one hω (by omega) (by omega)) ψ
      rw [← pow_succ'] at hrel
      have hstep := step_mem (sub_one_mem (f := f) hψ) (neg_gaussSum_inv_sub_mem hω hψ hq)
        (ihj (by omega)) (u := -jacobiSum ω⁻¹ (ω⁻¹ ^ (j + p * y)))
        (G' := -gaussSum (ω⁻¹ ^ (j + p * y + 1)) ψ) (c := ((j + 1 : ℕ) : R))
        (h' := (((j + 1).factorial * ((Nat.digits p y).map Nat.factorial).prod : ℕ) : R))
        (by rw [neg_mul_neg, neg_mul_neg, ← hrel, mul_comm])
        (by
          have := charP_quotient (p := p) (f := f)
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_neg, mk_jacobiSum hω hq (by omega),
            neg_neg, map_natCast]
          push_cast
          rw [CharP.cast_eq_zero (R ⧸ P) p]
          ring)
        (by rw [Nat.factorial_succ]; push_cast; ring_nf; exact Ideal.zero_mem _)
        (by
          rw [natCast_mem_iff (p := p) (f := f)]
          exact hp.out.prime.not_dvd_mul
            (fun h ↦ absurd ((Nat.Prime.dvd_factorial hp.out).1 h) (by omega))
            (not_dvd_prod_factorial_digits y))
      simpa [add_assoc, add_comm 1, add_left_comm 1] using hstep
  obtain ⟨hs, hh⟩ := digits_add_mul (Nat.mod_lt a hp.out.pos) y
  simpa only [← hs, ← hh, hdiv] using hclimb (a % p) le_rfl

/-- **Stickelberger's congruence.** Let `ω` be a multiplicative character of the finite field `F`
lifting `f : F →+* R ⧸ P` for a maximal ideal `P` of the domain `R`, and let `ψ(x) = ζ ^ Tr(x)`.
If `0 ≤ a < q - 1` has base-`p` digits `aᵢ`, then with `s = ∑ aᵢ` and `h = ∏ aᵢ!`,
`h · (-g(ω⁻ᵃ, ψ)) ≡ (ζ - 1) ^ s` modulo `P ^ (s + 1)`. -/
theorem stickelberger_congruence [IsDomain R] (hω : ∀ x, Ideal.Quotient.mk P (ω x) = f x)
    (hψ : ∀ x, ψ x = ζ ^ (Algebra.trace (ZMod p) F x).val) {a : ℕ}
    (ha : a < Fintype.card F - 1) :
    (((Nat.digits p a).map Nat.factorial).prod : R) * -gaussSum (ω⁻¹ ^ a) ψ ≡
      (ζ - 1) ^ (Nat.digits p a).sum [SMOD P ^ ((Nat.digits p a).sum + 1)] :=
  SModEq.sub_mem.2 (stickelberger_aux hω hψ a ha)

/-- The Gauss sum `g(ω⁻ᵃ, ψ)` lies in `P ^ s`, where `s` is the base-`p` digit sum of
`0 ≤ a < q - 1`. -/
theorem gaussSum_inv_pow_mem_pow [IsDomain R] (hω : ∀ x, Ideal.Quotient.mk P (ω x) = f x)
    (hψ : ∀ x, ψ x = ζ ^ (Algebra.trace (ZMod p) F x).val) {a : ℕ}
    (ha : a < Fintype.card F - 1) :
    gaussSum (ω⁻¹ ^ a) ψ ∈ P ^ (Nat.digits p a).sum := by
  have h := Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ _) (stickelberger_aux hω hψ a ha))
    (Ideal.pow_mem_pow (sub_one_mem (f := f) hψ) (Nat.digits p a).sum)
  rw [sub_add_cancel] at h
  have hh : (((Nat.digits p a).map Nat.factorial).prod : R) ∉ P := by
    rw [natCast_mem_iff (p := p) (f := f)]
    exact not_dvd_prod_factorial_digits a
  rw [← Ideal.neg_mem_iff]
  exact mem_pow_of_mul_mem hh h

end

open IsDedekindDomain in
/-- **The valuation of a Gauss sum.** In a Dedekind domain `R`, at a height-one prime `v` with
`v(ζ - 1) = exp(-1)`, the Gauss sum `g(ω⁻ᵃ, ψ)` has valuation `exp(-s)`, where `s` is the base-`p`
digit sum of `0 ≤ a < q - 1`. -/
theorem intValuation_gaussSum_inv_pow {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Fintype F]
    [Algebra (ZMod p) F] {R : Type*} [CommRing R] [IsDedekindDomain R]
    {v : HeightOneSpectrum R} {f : F →+* R ⧸ v.asIdeal} {ω : MulChar F R} {ζ : R}
    {ψ : AddChar F R} (hω : ∀ x, Ideal.Quotient.mk v.asIdeal (ω x) = f x)
    (hψ : ∀ x, ψ x = ζ ^ (Algebra.trace (ZMod p) F x).val)
    (hζ : v.intValuation (ζ - 1) = WithZero.exp (-1)) {a : ℕ} (ha : a < Fintype.card F - 1) :
    v.intValuation (gaussSum (ω⁻¹ ^ a) ψ) = WithZero.exp (-((Nat.digits p a).sum : ℤ)) := by
  have := v.isMaximal
  set s := (Nat.digits p a).sum
  set h : R := ((((Nat.digits p a).map Nat.factorial).prod : ℕ) : R)
  have hh : v.intValuation h = 1 := by
    rw [HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl, Ideal.mem_primeCompl_iff,
      natCast_mem_iff (p := p) (f := f)]
    exact not_dvd_prod_factorial_digits a
  have hπs : v.intValuation ((ζ - 1) ^ s) = WithZero.exp (-(s : ℤ)) := by
    rw [map_pow, hζ, ← WithZero.exp_nsmul, smul_neg, nsmul_one]
  have hlt : v.intValuation (h * -gaussSum (ω⁻¹ ^ a) ψ - (ζ - 1) ^ s) <
      v.intValuation ((ζ - 1) ^ s) := by
    refine lt_of_le_of_lt ((v.intValuation_le_pow_iff_mem _ (s + 1)).2
      (stickelberger_aux hω hψ a ha)) ?_
    rw [hπs, WithZero.exp_lt_exp]
    push_cast
    omega
  have := Valuation.map_add_eq_of_lt_left (v := v.intValuation) hlt
  rwa [add_sub_cancel, map_mul, hh, one_mul, Valuation.map_neg, hπs] at this

open IsDedekindDomain in
/-- **The Gauss sum valuation normalised at `p`.** If moreover `ζ` is a primitive `p`-th root of
unity, then `v(g(ω⁻ᵃ, ψ)) ^ (p - 1) = v(p) ^ s`: for the valuation normalised by `v(p) = 1`, the
Gauss sum has valuation `s / (p - 1)`. -/
theorem intValuation_gaussSum_inv_pow_pow_sub_one {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Fintype F] [Algebra (ZMod p) F] {R : Type*} [CommRing R] [IsDedekindDomain R]
    {v : HeightOneSpectrum R} {f : F →+* R ⧸ v.asIdeal} {ω : MulChar F R} {ζ : R}
    {ψ : AddChar F R} (hω : ∀ x, Ideal.Quotient.mk v.asIdeal (ω x) = f x)
    (hψ : ∀ x, ψ x = ζ ^ (Algebra.trace (ZMod p) F x).val) (hζp : IsPrimitiveRoot ζ p)
    (hζ : v.intValuation (ζ - 1) = WithZero.exp (-1)) {a : ℕ} (ha : a < Fintype.card F - 1) :
    v.intValuation (gaussSum (ω⁻¹ ^ a) ψ) ^ (p - 1) =
      v.intValuation (p : R) ^ (Nat.digits p a).sum := by
  obtain ⟨u, hu⟩ := hζp.associated_sub_one_pow_prime
  have hu1 : v.intValuation (u : R) = 1 := by
    rw [HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl, Ideal.mem_primeCompl_iff]
    exact fun h ↦ v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)
  rw [← hu, map_mul, hu1, mul_one, map_pow, hζ, intValuation_gaussSum_inv_pow hω hψ hζ ha,
    ← pow_mul, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul]
  congr 1
  simp only [smul_neg, nsmul_eq_mul, mul_one]
  push_cast
  ring

end TauCeti
