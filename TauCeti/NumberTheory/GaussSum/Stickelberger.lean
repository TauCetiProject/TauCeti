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
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.Data.Nat.Digits
import TauCeti.FieldTheory.Finite.PowerSums
import TauCeti.NumberTheory.GaussSum.Basic
import TauCeti.RingTheory.Ideal.IsPrimary
import TauCeti.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# Stickelberger's congruence for Gauss sums

Let `F` be a finite field with `q = p ^ n` elements, `R` a domain and `P` a maximal ideal of `R`
whose residue ring receives `F` through `f : F →+* R ⧸ P`. Let `ω : F → R` be a Teichmüller
character, a multiplicative character lifting `f` (`ω x ≡ f x (mod P)`), and let
`ψ(x) = ζ ^ Tr(x)` for an element `ζ` of `R`, `Tr` being the trace from `F` to `𝔽_p`; necessarily
`ζ ^ p = 1`. For `0 ≤ a < q - 1` with base-`p` digits `aᵢ`, put `s = ∑ aᵢ` and `h = ∏ aᵢ!`.
**Stickelberger's congruence** states that

  `h · (-g(ω⁻ᵃ, ψ)) ≡ (ζ - 1) ^ s (mod P ^ (s + 1))`.

Since `h` is prime to `p`, the Gauss sum `g(ω⁻ᵃ, ψ)` lies in `P ^ s`, and when `ζ - 1` has
valuation exactly `1` at `P` the Gauss sum has valuation exactly `s`. Then `ζ ≠ 1`, so `ζ` is a
primitive `p`-th root of unity and `p` has valuation `p - 1`, so the valuation normalised by
`v(p) = 1` gives the Gauss sum the value `s / (p - 1)`. The standard instance is the ring of
integers of `ℚ(ζ_p, ζ_(q-1))`, a prime `P` above `p` and the Teichmüller character of its residue
field; the statements here only use the congruence data above.

The congruence determines the prime factorisation of Gauss sums, which is the input to
Stickelberger's theorem on the annihilation of class groups and to the Gross–Koblitz formula.

## Main results

* `TauCeti.stickelberger_congruence`: `h · (-g(ω⁻ᵃ, ψ)) ≡ (ζ - 1) ^ s (mod P ^ (s + 1))`.
* `TauCeti.gaussSum_inv_pow_mem_pow`: `g(ω⁻ᵃ, ψ) ∈ P ^ s`.
* `TauCeti.intValuation_gaussSum_inv_pow`: in a Dedekind domain, if `v(ζ - 1) = 1` then
  `v(g(ω⁻ᵃ, ψ)) = s`.
* `TauCeti.intValuation_gaussSum_inv_pow_pow_sub_one`: under the same hypotheses,
  `(p - 1) v(g(ω⁻ᵃ, ψ)) = s v(p)`.

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

/-- Modulo `P`, the character `ω⁻¹` is `x ↦ x ^ (q - 2)` when `2 < q`. -/
private theorem mk_inv_apply (hω : ∀ x, Ideal.Quotient.mk P (ω x) = f x)
    (hq : 2 < Fintype.card F) (x : F) :
    Ideal.Quotient.mk P (ω⁻¹ x) = f (x ^ (Fintype.card F - 2)) := by
  rw [← pow_one ω⁻¹, mk_inv_pow_apply hω (by omega), Nat.sub_sub]

/-- Modulo `P`, the trivial character is `x ↦ x ^ (q - 1)`. -/
private theorem mk_one_apply (hω : ∀ x, Ideal.Quotient.mk P (ω x) = f x) (x : F) :
    Ideal.Quotient.mk P ((1 : MulChar F R) x) = f (x ^ (Fintype.card F - 1)) := by
  rw [← pow_zero ω⁻¹, mk_inv_pow_apply hω (by have := Fintype.one_lt_card (α := F); omega),
    Nat.sub_zero]

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
  simp only [jacobiSum, map_sum, map_mul, mk_inv_apply hω hq, mk_inv_pow_apply hω hx]
  simp only [← map_mul]
  rw [← map_sum, FiniteField.sum_pow_mul_one_sub_pow hq (by omega), map_natCast,
    Nat.cast_sub (by omega), Nat.cast_sub Fintype.card_pos, mk_natCast_card (f := f)]
  ring

/-- The case `a = 0`: `-g(1, ψ) ≡ 1` modulo `P`. -/
private theorem neg_gaussSum_one_sub_mem (hω : ∀ x, Ideal.Quotient.mk P (ω x) = f x)
    (hψ : ∀ x, ψ x = ζ ^ (Algebra.trace (ZMod p) F x).val) :
    -gaussSum 1 ψ - 1 ∈ P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_neg, gaussSum, map_sum]
  simp only [map_mul, mk_one_apply hω, mk_apply (f := f) hψ, mul_one]
  have := Fintype.one_lt_card (α := F)
  rw [← map_sum, FiniteField.sum_pow_of_pos_of_lt (by omega) (by omega), ite_eq_left rfl, map_neg,
    map_one, map_one, neg_neg, sub_self]

/-- The case `a = 1`: `-g(ω⁻¹, ψ) ≡ ζ - 1` modulo `P ^ 2`. -/
private theorem neg_gaussSum_inv_sub_mem [IsDomain R] (hω : ∀ x, Ideal.Quotient.mk P (ω x) = f x)
    (hψ : ∀ x, ψ x = ζ ^ (Algebra.trace (ZMod p) F x).val) (hq : 2 < Fintype.card F) :
    -gaussSum ω⁻¹ ψ - (ζ - 1) ∈ P ^ 2 := by
  set π := ζ - 1 with hπ_def
  have hπ : π ∈ P := sub_one_mem (f := f) hψ
  set t : F → R := fun x ↦ ((Algebra.trace (ZMod p) F x).val : R) with ht
  have he : ∀ x, ψ x - (1 + t x * π) ∈ P ^ 2 := fun x ↦ by
    obtain ⟨c, hc⟩ := sq_dvd_add_pow_sub_sub π 1 (Algebra.trace (ZMod p) F x).val
    rw [hψ, show ζ = 1 + π by rw [hπ_def]; ring,
      show (1 + π) ^ _ - (1 + t x * π) = π ^ 2 * c by rw [← hc, ht]; ring]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπ 2)
  have hsum : ∑ x, ω⁻¹ x = 0 :=
    MulChar.sum_eq_zero_of_ne_one (by simpa using inv_pow_ne_one hω one_pos (by omega) (a := 1))
  have hmk : ∑ x, ω⁻¹ x * t x + 1 ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_sum]
    simp only [map_mul, mk_inv_apply hω hq, ht, mk_natCast_val (f := f)]
    simp only [← map_mul]
    rw [← map_sum, FiniteField.sum_pow_mul_trace hq, map_neg, map_one, map_one, neg_add_cancel]
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
  have hGs : G ∈ P ^ s := Ideal.mem_pow_of_mul_mem hhP (by
    simpa using Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ s) hG) hπs)
  have hG' : G' ∈ P ^ (s + 1) := Ideal.mem_pow_of_mul_mem huP (by
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
  rw [← gaussSum_pow_char_left _ (apply_pow_char_of_trace (g := fun t ↦ ζ ^ t.val) hψ),
    ← pow_mul] at hy
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
        (by
          rw [show (((j + 1).factorial * ((Nat.digits p y).map Nat.factorial).prod : ℕ) : R) -
              ((j.factorial * ((Nat.digits p y).map Nat.factorial).prod : ℕ) : R) *
                ((j + 1 : ℕ) : R) = 0 by push_cast [Nat.factorial_succ]; ring]
          exact Ideal.zero_mem _)
        (by
          rw [natCast_mem_iff (p := p) (f := f)]
          exact hp.out.prime.not_dvd_mul
            (fun h ↦ absurd ((Nat.Prime.dvd_factorial hp.out).1 h) (by omega))
            (hp.out.not_dvd_prod_factorial_digits y))
      rwa [show j + p * y + 1 = j + 1 + p * y by omega,
        show j + (Nat.digits p y).sum + 1 = j + 1 + (Nat.digits p y).sum by omega] at hstep
  have hs := Nat.sum_digits_add_mul (Nat.mod_lt a hp.out.pos) y
  have hh := Nat.prod_map_digits_add_mul Nat.factorial_zero (Nat.mod_lt a hp.out.pos) y
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
    exact hp.out.not_dvd_prod_factorial_digits a
  rw [← Ideal.neg_mem_iff]
  exact Ideal.mem_pow_of_mul_mem hh h

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
    exact (Fact.out : p.Prime).not_dvd_prod_factorial_digits a
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
/-- **The Gauss sum valuation normalised at `p`.** Under the hypotheses of
`intValuation_gaussSum_inv_pow`, `ζ` is a primitive `p`-th root of unity, and
`v(g(ω⁻ᵃ, ψ)) ^ (p - 1) = v(p) ^ s`: for the valuation normalised by `v(p) = 1`, the Gauss sum
has valuation `s / (p - 1)`. -/
theorem intValuation_gaussSum_inv_pow_pow_sub_one {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Fintype F] [Algebra (ZMod p) F] {R : Type*} [CommRing R] [IsDedekindDomain R]
    {v : HeightOneSpectrum R} {f : F →+* R ⧸ v.asIdeal} {ω : MulChar F R} {ζ : R}
    {ψ : AddChar F R} (hω : ∀ x, Ideal.Quotient.mk v.asIdeal (ω x) = f x)
    (hψ : ∀ x, ψ x = ζ ^ (Algebra.trace (ZMod p) F x).val)
    (hζ : v.intValuation (ζ - 1) = WithZero.exp (-1)) {a : ℕ} (ha : a < Fintype.card F - 1) :
    v.intValuation (gaussSum (ω⁻¹ ^ a) ψ) ^ (p - 1) =
      v.intValuation (p : R) ^ (Nat.digits p a).sum := by
  have hζ1 : ζ ≠ 1 := fun h ↦ by
    rw [h, sub_self, map_zero] at hζ
    exact WithZero.exp_ne_zero hζ.symm
  have hζp : IsPrimitiveRoot ζ p :=
    IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime (zeta_pow_eq_one hψ) hζ1)
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
