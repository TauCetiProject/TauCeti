/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

/-!
# Square roots of prime discriminants in a field of roots of unity

This file extracts the square roots of the prime discriminants from roots of unity. Let `L` be a
field of characteristic zero and let `F` be an intermediate field of `L / ℚ`.

* if `F` contains a primitive `p`-th root of unity for an odd prime `p`, it contains a square root
  of the odd prime discriminant `p* = (-1)^((p-1)/2) p`;
* if `F` contains a primitive fourth root of unity, it contains a square root of `-1`;
* if `F` contains a primitive eighth root of unity, it contains a square root of `2`.

Up to rational squares these are all the prime discriminants, since `-4 = -1 · 2²` and
`±8 = ±2 · 2²`, and they are the arithmetic input to the containment of a multiquadratic field in a
cyclotomic field.

The odd case is the classical quadratic Gauss sum `g = ∑_{a} (a/p) ζ^a`, whose square is `p*`.
Mathlib's `gaussSum_sq` already computes `g²` as `χ(-1)` times the cardinality of the source, for
any nontrivial quadratic character `χ` and primitive additive character `ψ` valued in a domain;
specialising `χ` to the quadratic
character of `ZMod p` pushed into `L` and `ψ` to the additive character attached to `ζ`
(`AddChar.zmodChar`) turns that computation into the statement above, since
`(-1/p) = (-1)^((p-1)/2)`. Mathlib uses this only in positive characteristic, where the Gauss sum
produces the quadratic reciprocity law; here the target is characteristic zero, where it produces
a square root.

The two even cases are direct computations: a primitive fourth root of unity squares to `-1`
(its square is a primitive square root of unity), and for a primitive eighth root of unity `ζ`
the element `ζ + ζ⁷` squares to `2`, because `ζ⁴ = -1`.

For the classical account of the quadratic Gauss sum see K. Ireland and M. Rosen, *A Classical
Introduction to Modern Number Theory*, Chapter 6.

## Main results

* `TauCeti.Multiquadratic.exists_mem_sq_eq_oddPrimeDiscriminant`: a primitive `p`-th root of unity
  carries a square root of `p*`.
* `TauCeti.Multiquadratic.exists_mem_sq_eq_neg_one`: a primitive fourth root of unity is a square
  root of `-1`.
* `TauCeti.Multiquadratic.exists_mem_sq_eq_two`: a primitive eighth root of unity carries a square
  root of `2`.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

variable {L : Type*} [Field L] [CharZero L] {F : IntermediateField ℚ L} {ζ : L}

/-- **The quadratic Gauss sum is a square root of the prime discriminant.** If an intermediate
field `F` of `L / ℚ` contains a primitive `p`-th root of unity for an odd prime `p`, then it
contains a square root of the odd prime discriminant `p*`.

The witness is the Gauss sum `∑_{a : ZMod p} (a/p) ζ^a`, a `ℤ`-linear combination of powers of
`ζ`; `gaussSum_sq` evaluates its square as `(-1/p) · p`, which is `p*`. -/
theorem exists_mem_sq_eq_oddPrimeDiscriminant {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : IsPrimitiveRoot ζ p) (hmem : ζ ∈ F) :
    ∃ x ∈ F, x ^ 2 = ((oddPrimeDiscriminant p : ℤ) : L) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  set χ : MulChar (ZMod p) L := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom L) with hχ
  set ψ : AddChar (ZMod p) L := AddChar.zmodChar p ((IsPrimitiveRoot.iff_def ζ p).mp hζ).left
    with hψdef
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hζ
  have hχ₂ : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
  have hrc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hχ₁ : χ ≠ 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hrc
    refine MulChar.ne_one_iff.mpr ⟨a, ?_⟩
    simp only [hχ, MulChar.ringHomComp_apply, ha, eq_intCast, Int.cast_neg, Int.cast_one]
    exact Ring.neg_one_ne_one_of_char_ne_two (by simp [ringChar.eq_zero])
  refine ⟨gaussSum χ ψ, sum_mem fun a _ => mul_mem ?_ ?_, ?_⟩
  · have hval : χ a = ((quadraticChar (ZMod p) a : ℤ) : L) := by
      simp [hχ, MulChar.ringHomComp_apply]
    rw [hval]
    exact intCast_mem F _
  · have hval : ψ a = ζ ^ a.val := rfl
    rw [hval]
    exact pow_mem hmem _
  · rw [gaussSum_sq hχ₁ hχ₂ hψ]
    have hval : χ (-1) = ((quadraticChar (ZMod p) (-1) : ℤ) : L) := by
      simp [hχ, MulChar.ringHomComp_apply]
    rw [hval, quadraticChar_neg_one hrc, ZMod.card p,
      ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp (hp.odd_of_ne_two hp2)),
      oddPrimeDiscriminant_eq_neg_one_pow_div_two_mul (hp.odd_of_ne_two hp2)]
    push_cast
    ring

/-- **A primitive fourth root of unity is a square root of `-1`.** -/
theorem exists_mem_sq_eq_neg_one (hζ : IsPrimitiveRoot ζ 4) (hmem : ζ ∈ F) :
    ∃ x ∈ F, x ^ 2 = (-1 : L) :=
  ⟨ζ, hmem, (hζ.pow (by norm_num) (by norm_num : 4 = 2 * 2)).eq_neg_one_of_two_right⟩

/-- **A primitive eighth root of unity carries a square root of `2`.** The witness is
`ζ + ζ⁷ = ζ + ζ⁻¹`, whose square is `ζ² + 2 + ζ⁻²`, and `ζ⁻² = -ζ²` because `ζ⁴ = -1`. -/
theorem exists_mem_sq_eq_two (hζ : IsPrimitiveRoot ζ 8) (hmem : ζ ∈ F) :
    ∃ x ∈ F, x ^ 2 = (2 : L) := by
  have h4 : ζ ^ 4 = -1 := (hζ.pow (by norm_num) (by norm_num : 8 = 4 * 2)).eq_neg_one_of_two_right
  have h8 : ζ ^ 8 = 1 := hζ.pow_eq_one
  refine ⟨ζ + ζ ^ 7, add_mem hmem (pow_mem hmem 7), ?_⟩
  have expand : (ζ + ζ ^ 7) ^ 2 = ζ ^ 2 + 2 * ζ ^ 8 + ζ ^ 8 * (ζ ^ 4 * ζ ^ 2) := by ring
  rw [expand, h8, h4]
  ring

end TauCeti.Multiquadratic
