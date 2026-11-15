/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Ideal
import Mathlib.RingTheory.Coprime.Lemmas
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# Cubic residue symbols of rational integers

In the third cyclotomic field, the cubic residue symbol `(n / m)₃` is `1` for coprime
rational integers `n` and `m`, where the denominator means the ideal `m 𝓞 K`.
In particular this handles two distinct inert rational primes in cubic reciprocity.
No primality or sign condition is needed: conjugation fixes both rational integers
and their principal ideals, but squares every cube root of unity.

The proof uses `Ideal.map_powerResidueSymbolIdeal` and Mathlib's cyclotomic Galois
coordinate `IsCyclotomicExtension.Rat.galEquivZMod`. It applies also at denominators
divisible by `3`, with the convention that prime factors above `3` contribute the
trivial character to the power residue symbol.

## References

* N. Xu, *Reciprocity Laws*, §4, proof of Theorem 4.6, Case 1.
* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §3,
  proof of Theorem 3.1, first case.
-/

public section

open NumberField IsCyclotomicExtension.Rat

namespace Ideal

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
  [HasEnoughRootsOfUnity (𝓞 K) 3]

/-- The cubic residue symbol of coprime rational integers is trivial in the third
cyclotomic field. In particular, `(n / q)₃ = 1` for a rational prime `q ≡ 2 (mod 3)`
and an integer `n` prime to `q`. The denominator is the principal ideal `m 𝓞 K`. -/
@[simp]
theorem powerResidueSymbolIdeal_intCast_three {m n : ℤ} (h : IsCoprime n m) :
    powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 3 n = 1 := by
  let σ := (galEquivZMod 3 K).symm (-1)
  let τ := MulSemiringAction.toRingEquiv Gal(K/ℚ) (𝓞 K) σ
  let x := powerResidueSymbolIdeal (span {(m : 𝓞 K)}) 3 (Quotient.mk _ (n : 𝓞 K))
  have hu : IsUnit (Quotient.mk (span {(m : 𝓞 K)}) (n : 𝓞 K)) := by
    apply Quotient.isUnit_mk_iff.mpr
    apply isCoprime_iff_sup_eq.mp
    exact (isCoprime_span_singleton_iff _ _).mpr (h.map (Int.castRingHom (𝓞 K)))
  have hx : x ^ 3 = 1 := powerResidueSymbolIdeal_pow_eq_one hu
  have hmap : (span {(m : 𝓞 K)}).map τ = span {(m : 𝓞 K)} := by
    rw [map_span, Set.image_singleton, map_intCast]
  have hfixed : τ x = x := by
    have hf := map_powerResidueSymbolIdeal (n := 3) (span {(m : 𝓞 K)}) τ (n : 𝓞 K)
    rw [hmap, map_intCast τ] at hf
    exact hf
  have hsq : τ x = x ^ 2 := by
    have he := (galEquivZMod 3 K).apply_symm_apply (-1)
    have hs := galEquivZMod_smul_of_pow_eq 3 K σ hx
    rw [he] at hs
    exact hs
  have hx0 : x ≠ 0 := by
    intro hz
    simp [hz] at hx
  have hresult : x = 1 :=
    mul_left_cancel₀ hx0 (by simpa only [sq, mul_one] using hsq.symm.trans hfixed)
  simpa only [x, map_intCast] using hresult

/- The inert rational primes `5` and `2`, including a numerator even or larger than
the denominator. -/
example : powerResidueSymbolIdeal (span {((5 : ℤ) : 𝓞 K)}) 3
    (Quotient.mk _ ((2 : ℤ) : 𝓞 K)) = 1 := by
  simpa only [map_intCast] using
    powerResidueSymbolIdeal_intCast_three (K := K) (by decide : IsCoprime (2 : ℤ) 5)

example : powerResidueSymbolIdeal (span {((2 : ℤ) : 𝓞 K)}) 3
    (Quotient.mk _ ((7 : ℤ) : 𝓞 K)) = 1 := by
  simpa only [map_intCast] using
    powerResidueSymbolIdeal_intCast_three (K := K) (by decide : IsCoprime (7 : ℤ) 2)

/- The theorem also includes split primes and composite negative denominators. -/
example : powerResidueSymbolIdeal (span {((7 : ℤ) : 𝓞 K)}) 3
    (Quotient.mk _ ((3 : ℤ) : 𝓞 K)) = 1 := by
  simpa only [map_intCast] using
    powerResidueSymbolIdeal_intCast_three (K := K) (by decide : IsCoprime (3 : ℤ) 7)

example : powerResidueSymbolIdeal (span {((-10 : ℤ) : 𝓞 K)}) 3
    (Quotient.mk _ ((3 : ℤ) : 𝓞 K)) = 1 := by
  simpa only [map_intCast] using
    powerResidueSymbolIdeal_intCast_three (K := K) (by decide : IsCoprime (3 : ℤ) (-10))

end Ideal
