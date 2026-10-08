/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Basic
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import TauCeti.Data.ZMod.Torsion
import TauCeti.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import TauCeti.NumberTheory.ModularForms.JacobiTheta.GaussSum

/-!
# Gauss sums of the odd cyclic generators

For an odd prime `p`, `k ≥ 0` and `θ` prime to `p`, this file computes the Gauss-sum invariant
of Nikulin's cyclic generator `q_θ^{(p)}(p^k)`, the odd-prime values of Nikulin's
Proposition 1.11.2:

```text
sign q_θ^{(p)}(p^k) ≡ k²(1 - p) + 4kη (mod 8),   where (θ/p) = (-1)^η.
```

The invariant is first shown to be periodic with period two in the exponent, for every odd `p`:
the `p`-torsion in `ℤ/p^{k+2}` consists of the multiples of `p^{k+1}` and is
quadratic-isotropic, and multiplication by `p`, followed by reduction modulo `p^k`, identifies
the remaining quadratic form with `q_θ^{(p)}(p^k)`. Isotropic reduction therefore preserves the
Gauss-sum invariant, and the formula reduces to the exponents `0` and `1`. The exponent `0` is
the trivial module. At exponent `1` the form is `x ↦ θx²/(2p)`, with division by `2` modulo
`p`, so its Gauss sum is `(θ/p)(2/p)` times the classical quadratic Gauss sum
`∑_{r < p} e^{2πi r²/p}` (`TauCeti.sum_addChar_mul_sq`). Gauss's evaluation of that sum
(`TauCeti.sum_range_cexp_two_pi_I_sq_div`) and the second supplementary law
`(2/p) = χ₈(p)` give the value `(1 - p) + 4η`.

## Main declarations

* `TauCeti.FiniteQuadraticModule.gaussSign_oddCyclic_pow_add_two`: increasing the exponent
  of an odd-base cyclic form by two does not change its Gauss-sum invariant.
* `TauCeti.FiniteQuadraticModule.gaussSign_oddCyclic`:
  `sign q_θ^{(p)}(p^k) = k²(1 - p) + 2k(1 - (θ/p))`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.11.2.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti.FiniteQuadraticModule

/-- **The Gauss-sum invariant of an odd-base cyclic form is periodic with period two in the
exponent.** The `p`-torsion in `ℤ/p^{k+2}` is quadratic-isotropic, and multiplication by `p`
followed by reduction modulo `p^k` carries its quadratic form to that of `ℤ/p^k`. In particular,
this applies to Nikulin's odd-prime cyclic generators. -/
@[simp]
theorem gaussSign_oddCyclic_pow_add_two {p : ℕ} (hp : Odd p) (k : ℕ) {θ : ℤ}
    (hθ : IsCoprime (p : ℤ) θ) :
    (oddCyclic (p ^ (k + 2)) hp.pow θ).gaussSign =
      (oddCyclic (p ^ k) hp.pow θ).gaussSign := by
  have hp0 : p ≠ 0 := hp.pos.ne'
  let _ : NeZero p := ⟨hp0⟩
  have hoddA : Odd (p ^ (k + 2)) := hp.pow
  have hoddB : Odd (p ^ k) := hp.pow
  have hdvd : p ^ k ∣ p ^ (k + 2) := pow_dvd_pow p (by omega)
  let r := (ZMod.castHom hdvd (ZMod (p ^ k))).toAddMonoidHom
  have hnondegA : (oddCyclic (p ^ (k + 2)) hoddA θ).IsNondegenerate := by
    rw [isNondegenerate_oddCyclic_iff]
    simpa only [Nat.cast_pow] using hθ.pow_left
  have hnondegB : (oddCyclic (p ^ k) hoddB θ).IsNondegenerate := by
    rw [isNondegenerate_oddCyclic_iff]
    simpa only [Nat.cast_pow] using hθ.pow_left
  have hiso (x : ZMod (p ^ (k + 2))) (hx : (p : ℤ) • x = 0) :
      (oddCyclic (p ^ (k + 2)) hoddA θ).quadratic x = 0 := by
    obtain ⟨t, rfl⟩ :=
      ZMod.exists_eq_pow_mul_of_zsmul_eq_zero (p := p) (n := k + 1) (by simpa using hx)
    rw [oddCyclic_quadratic_intCast]
    obtain ⟨s, hs⟩ := hoddA
    rw [hs]
    exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).2
      ⟨θ * (s + 1) * p ^ k * t ^ 2, by
        have hs' : p ^ k * (p * p) = 2 * s + 1 := by
          simpa only [pow_add, pow_two] using hs
        have hs'Q : (p : ℚ) ^ k * ((p : ℚ) * p) = 2 * s + 1 := by
          exact_mod_cast hs'
        have hsHalf : (s : ℚ) + 1 = ((p : ℚ) ^ k * (p * p) + 1) / 2 := by
          rw [hs'Q]
          ring
        rw [zsmul_eq_mul]
        push_cast
        rw [hsHalf, ← hs'Q]
        field_simp
        rw [pow_add (p : ℚ) k 1, pow_one]
        ring⟩
  have hq (y : ZMod (p ^ (k + 2))) :
      (oddCyclic (p ^ (k + 2)) hoddA θ).quadratic ((p : ℤ) • y) =
        (oddCyclic (p ^ k) hoddB θ).quadratic (r y) := by
    obtain ⟨s, hs⟩ := hp
    obtain ⟨j, rfl⟩ := ZMod.intCast_surjective y
    simp only [r, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, map_intCast,
      zsmul_eq_mul, ← Int.cast_mul, oddCyclic_quadratic_intCast]
    push_cast
    rw [← AddCircle.coe_add_intCast
      (θ * (p ^ k + 1) * j ^ 2 / (2 * p ^ k) : ℚ) (2 * θ * (s + 1) * s * j ^ 2)]
    congr 1
    rw [hs]
    push_cast
    field_simp
    ring
  exact gaussSign_eq_of_quadratic_zsmul_eq hnondegA hnondegB p
    ((isIsotropic_def _).2 fun x hx ↦ hiso x ((zsmulAddGroupHom_apply p x).symm.trans hx)) r
    (ZMod.castHom_surjective hdvd) hq

/-! ## The values on the generators -/

open Complex
open scoped Real

/-- `e^{2πi · 2j/8} = i^j`. -/
private theorem expCircle_toRatAddCircle_eight_two_mul (j : ℕ) :
    expCircle (ZMod.toRatAddCircle 8 ((2 * j : ℕ) : ZMod 8)) = I ^ j := by
  rw [Nat.cast_mul, mul_comm, ← nsmul_eq_mul, map_nsmul, AddChar.map_nsmul_eq_pow,
    ZMod.toRatAddCircle_natCast, show ((2 : ℕ) : ℚ) / (8 : ℕ) = 1 / 4 by norm_num,
    expCircle_one_div_four]

/-- The Gauss sum of `q_θ^{(p)}(p)` is `(θ/p)(2/p) G_p`, where
`G_p = ∑_{r < p} e^{2πi r²/p}` is the classical quadratic Gauss sum: the form is
`x ↦ θ x² / (2p)` with division by `2` modulo `p`, and the factor `(θ · 2⁻¹ / p) = (θ/p)(2/p)`
comes from `TauCeti.sum_addChar_mul_sq`. -/
private theorem gaussSum_oddCyclic_prime {p : ℕ} [Fact p.Prime] (hp : Odd p) {θ : ℤ}
    (hθ : IsCoprime (p : ℤ) θ) :
    (oddCyclic p hp θ).gaussSum = legendreSym p θ * ZMod.χ₈ p *
      ∑ r ∈ Finset.range p, cexp (2 * π * I * r ^ 2 / p) := by
  let _ : Fintype (oddCyclic p hp θ) := inferInstanceAs (Fintype (ZMod p))
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.2 hp even_two
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  let ψ : AddChar (ZMod p) ℂ := expCircle.compAddMonoidHom (ZMod.toRatAddCircle p)
  have hψ : ψ.IsPrimitive := by
    refine AddChar.IsPrimitive.of_ne_one fun h ↦ one_ne_zero (α := ZMod p) ?_
    have h1 := DFunLike.congr_fun h 1
    rwa [AddChar.one_apply, AddChar.compAddMonoidHom_apply, expCircle_eq_one_iff,
      ZMod.toRatAddCircle_eq_zero] at h1
  set h : ZMod p := (((p + 1) / 2 : ℕ) : ZMod p) with hh
  have h2 : (2 : ZMod p) * h = 1 := by
    rw [hh, ← Nat.cast_ofNat, ← Nat.cast_mul, Nat.mul_div_cancel' (hp.add_one).two_dvd,
      Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  have hθ0 : (θ : ZMod p) ≠ 0 :=
    (isCoprime_zero_left.1 (by simpa using hθ.intCast (R := ZMod p))).ne_zero
  have hc : (θ : ZMod p) * h ≠ 0 := mul_ne_zero hθ0 (left_ne_zero_of_mul_eq_one (b := 2)
    (by rw [mul_comm, h2]))
  -- `χ(2⁻¹) = χ(2) = χ₈(p)` because `χ(2)² = 1`.
  have hχh : (quadraticChar (ZMod p) h : ℂ) = ZMod.χ₈ p := by
    have h2' := legendreSym.at_two hp2
    rw [legendreSym, Int.cast_ofNat] at h2'
    have hsq := quadraticChar_sq_one (F := ZMod p) (a := 2) (by
      intro h0; simp [h0] at h2)
    rw [← h2', ← one_mul (quadraticChar (ZMod p) h), ← hsq, sq, mul_assoc, ← map_mul, h2,
      map_one, mul_one]
  have hsum : ∑ x : ZMod p, ψ (x ^ 2) = ∑ r ∈ Finset.range p, cexp (2 * π * I * r ^ 2 / p) := by
    refine (Finset.sum_nbij' (fun r : ℕ ↦ (r : ZMod p)) (fun x ↦ x.val) (by simp)
      (fun x _ ↦ Finset.mem_range.2 (ZMod.val_lt x)) (fun r hr ↦ ?_) (fun x _ ↦ by simp)
      fun r _ ↦ ?_).symm
    · exact ZMod.val_cast_of_lt (Finset.mem_range.1 hr)
    · simp only [ψ, AddChar.compAddMonoidHom_apply, ← Nat.cast_pow, ZMod.toRatAddCircle_natCast,
        expCircle_coe]
      push_cast
      ring_nf
  rw [gaussSum_eq_sum]
  calc ∑ x : ZMod p, expCircle ((oddCyclic p hp θ).quadratic x)
      = ∑ x : ZMod p, ψ ((θ * h) * x ^ 2) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [oddCyclic_quadratic, ← hh, AddChar.compAddMonoidHom_apply]
    _ = _ := by
        rw [sum_addChar_mul_sq hF hψ hc, hsum, map_mul, Int.cast_mul, hχh, legendreSym]

/-- For odd `p`, `χ₈(p) G_p / √p = e^{2πi(1 - p)/8}`, checked on the residues of `p` modulo `8`
with Gauss's evaluation `G_p = (1 + i)/2 · (1 + (-i)^p) · √p`. -/
private theorem chi_eight_mul_gaussFactor {p : ℕ} (hp : Odd p) :
    (ZMod.χ₈ p : ℂ) * ((1 + I) / 2 * (1 + (-I) ^ p)) =
      expCircle (ZMod.toRatAddCircle 8 ((1 - p : ℤ) : ZMod 8)) := by
  have hmod := Nat.mod_add_div p 8
  have hI8 : (-I) ^ 8 = 1 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, neg_sq, I_sq, show (-1 : ℂ) ^ 4 = 1 by norm_num]
  have hpow : (-I) ^ p = (-I) ^ (p % 8) := by
    conv_lhs => rw [← hmod]
    rw [pow_add, pow_mul, hI8, one_pow, mul_one]
  have hcast : ((1 - p : ℤ) : ZMod 8) = ((1 - (p % 8 : ℕ) : ℤ) : ZMod 8) := by
    rw [Int.cast_sub, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_mod]
  rw [hpow, hcast, ZMod.χ₈_nat_mod_eight]
  have hodd : p % 8 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 8)]
    exact Nat.odd_iff.1 hp
  have hlt : p % 8 < 8 := Nat.mod_lt p (by norm_num)
  generalize p % 8 = b at hodd hlt
  -- In each case `1 - b ≡ 2j (mod 8)` and both sides are `i^j`.
  interval_cases b <;> try omega
  · rw [show ((1 - (1 : ℕ) : ℤ) : ZMod 8) = ((2 * 0 : ℕ) : ZMod 8) by decide,
      expCircle_toRatAddCircle_eight_two_mul]
    simp only [show ZMod.χ₈ ((1 : ℕ) : ZMod 8) = 1 by decide]
    apply Complex.ext <;> norm_num [pow_succ]
  · rw [show ((1 - (3 : ℕ) : ℤ) : ZMod 8) = ((2 * 3 : ℕ) : ZMod 8) by decide,
      expCircle_toRatAddCircle_eight_two_mul]
    simp only [show ZMod.χ₈ ((3 : ℕ) : ZMod 8) = -1 by decide]
    apply Complex.ext <;> norm_num [pow_succ]
  · rw [show ((1 - (5 : ℕ) : ℤ) : ZMod 8) = ((2 * 2 : ℕ) : ZMod 8) by decide,
      expCircle_toRatAddCircle_eight_two_mul]
    simp only [show ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 by decide]
    apply Complex.ext <;> norm_num [pow_succ]
  · rw [show ((1 - (7 : ℕ) : ℤ) : ZMod 8) = ((2 * 1 : ℕ) : ZMod 8) by decide,
      expCircle_toRatAddCircle_eight_two_mul]
    simp only [show ZMod.χ₈ ((7 : ℕ) : ZMod 8) = 1 by decide]
    apply Complex.ext <;> norm_num [pow_succ]

/-- A Legendre symbol `(θ/p) = ±1` is `e^{2πi · 2(1 - (θ/p))/8}`. -/
private theorem legendreSym_eq_expCircle {p : ℕ} [Fact p.Prime] {θ : ℤ} (hθ : (θ : ZMod p) ≠ 0) :
    (legendreSym p θ : ℂ) =
      expCircle (ZMod.toRatAddCircle 8 ((2 * (1 - legendreSym p θ) : ℤ) : ZMod 8)) := by
  rcases legendreSym.eq_one_or_neg_one p hθ with h | h <;> rw [h]
  · simp
  · rw [show ((2 * (1 - -1) : ℤ) : ZMod 8) = ((2 * 2 : ℕ) : ZMod 8) by decide,
      expCircle_toRatAddCircle_eight_two_mul, I_sq, Int.cast_neg, Int.cast_one]

/-- **The Gauss-sum invariant of `q_θ^{(p)}(p)`** is `(1 - p) + 4η`, where `(θ/p) = (-1)^η`. -/
private theorem gaussSign_oddCyclic_prime {p : ℕ} [Fact p.Prime] (hp : Odd p) {θ : ℤ}
    (hθ : IsCoprime (p : ℤ) θ) :
    (oddCyclic p hp θ).gaussSign = ((1 - p + 2 * (1 - legendreSym p θ) : ℤ) : ZMod 8) := by
  have hθ0 : (θ : ZMod p) ≠ 0 :=
    (isCoprime_zero_left.1 (by simpa using hθ.intCast (R := ZMod p))).ne_zero
  -- The carrier of `oddCyclic p hp θ` is `ℤ/p` by definition.
  have hcard : Nat.card (oddCyclic p hp θ) = p := Nat.card_zmod p
  refine gaussSign_eq_of_gaussSum_eq _ ?_
  rw [gaussSum_oddCyclic_prime hp hθ, sum_range_cexp_two_pi_I_sq_div, hcard, Int.cast_add,
    map_add, AddChar.map_add_eq_mul, ← chi_eight_mul_gaussFactor hp, ← legendreSym_eq_expCircle hθ0]
  ring

/-- The Gauss-sum invariant of the trivial module `oddCyclic 1` is `0`. -/
private theorem gaussSign_oddCyclic_one (h1 : Odd 1) (θ : ℤ) :
    (oddCyclic 1 h1 θ).gaussSign = 0 := by
  -- The carrier of `oddCyclic 1 h1 θ` is `ℤ/1` by definition.
  have hcard : Nat.card (oddCyclic 1 h1 θ) = 1 := Nat.card_zmod 1
  have := (Nat.card_eq_one_iff_unique.1 hcard).1
  let _ : Fintype (oddCyclic 1 h1 θ) := Fintype.ofFinite _
  refine gaussSign_eq_of_gaussSum_eq _ ?_
  rw [gaussSum_eq_sum, Fintype.sum_subsingleton _ 0, QuadraticMap.map_zero, hcard]
  simp

/-- **Nikulin's Gauss-sum invariant of the odd cyclic generator** `q_θ^{(p)}(p^k)`: for an odd
prime `p` and `θ` prime to `p`, `sign q_θ^{(p)}(p^k) ≡ k²(1 - p) + 4kη (mod 8)`, where
`(θ/p) = (-1)^η`. Since `4η = 2(1 - (θ/p))`, the invariant is stated with the Legendre symbol. -/
theorem gaussSign_oddCyclic {p : ℕ} [Fact p.Prime] (hp : Odd p) (k : ℕ) {θ : ℤ}
    (hθ : IsCoprime (p : ℤ) θ) :
    (oddCyclic (p ^ k) hp.pow θ).gaussSign =
      ((k ^ 2 * (1 - p) + 2 * k * (1 - legendreSym p θ) : ℤ) : ZMod 8) := by
  induction k using Nat.twoStepInduction with
  | zero => simpa using gaussSign_oddCyclic_one _ θ
  | one => simpa using gaussSign_oddCyclic_prime hp hθ
  | more k ih _ =>
    rw [gaussSign_oddCyclic_pow_add_two hp k hθ, ih]
    -- The difference `4(k + 1)(1 - p) + 4(1 - (θ/p))` is divisible by `8`.
    obtain ⟨t, ht⟩ := hp
    have h8 : (8 : ZMod 8) = 0 := by decide
    have hθ0 : (θ : ZMod p) ≠ 0 :=
      (isCoprime_zero_left.1 (by simpa using hθ.intCast (R := ZMod p))).ne_zero
    rcases legendreSym.eq_one_or_neg_one p hθ0 with h | h <;>
      rw [h, ht] <;> push_cast
    · linear_combination (t * (k + 1) : ZMod 8) * h8
    · linear_combination (t * (k + 1) - 1 : ZMod 8) * h8

end TauCeti.FiniteQuadraticModule
