/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import TauCeti.NumberTheory.JacobiSum.Cubic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Three.Primary
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Basic
public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Basic

/-!
# The Jacobi sum of a cubic character is primary

Let `χ` be a multiplicative character of order `3` on a finite field `F`, with values in the ring
of integers `𝓞 K` of a field `K` of characteristic zero, for instance a number field. Then the
Jacobi sum `J(χ, χ)` is *primary*: `J(χ, χ) ≡ 2 (mod 3)` in `𝓞 K`. For the cubic residue symbol
`χ = (· / π)_3` of a prime `π` of `ℤ[ω]` this is the first step in the identification
`J(χ, χ) = π` of the Jacobi sum with the primary generator of `π`, on which the proof of cubic
reciprocity rests.

## Main results

* `TauCeti.isPrimaryEisenstein_jacobiSum`: `J(χ, χ)` is primary for every character `χ` of
  order `3` with values in `𝓞 K`.
* `Ideal.isPrimaryEisenstein_jacobiSum_powerResidueSymbol`: the case of the cubic residue symbol
  `(· / P)_3` at a prime `P` of the ring of integers of a number field, whose norm is prime
  to `3`.

The congruence `J(χ, χ) ≡ -1 (mod 3)` is `TauCeti.three_dvd_jacobiSum_add_one` in a domain that
carries a primitive additive character of `F`. Here that domain is the ring of integers of the
cyclotomic extension `K(ζ_p)`, where `p` is the characteristic of `F`, and the congruence descends
to `𝓞 K` by `NumberField.RingOfIntegers.algebraMap_dvd_algebraMap_iff`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 8, §3,
  Proposition 8.3.4.
* N. Xu, *Reciprocity Laws*, Proposition 4.8.
* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §3, Lemma 3.2.
-/

public section

open NumberField

namespace TauCeti

variable {K F : Type*} [Field K] [Field F] [Fintype F]

/-- **The Jacobi sum of a cubic character is primary.** If `χ` is a multiplicative character of
order `3` on a finite field, with values in the ring of integers `𝓞 K` of a field of
characteristic zero, then `J(χ, χ) ≡ 2 (mod 3)` in `𝓞 K`. -/
theorem isPrimaryEisenstein_jacobiSum [CharZero K] {χ : MulChar F (𝓞 K)} (hχ : orderOf χ = 3) :
    IsPrimaryEisenstein (jacobiSum χ χ) := by
  -- Form the Gauss sums in the ring of integers of the cyclotomic extension `L = K(ζ_p)`.
  have hchar : ringChar K ≠ ringChar F := by
    rw [ringChar.eq_zero]
    exact (CharP.char_ne_zero_of_finite F _).symm
  let ψ₀ := AddChar.FiniteField.primitiveChar F K hchar
  let L := CyclotomicField ψ₀.n K
  obtain ⟨ψ, hψ, -⟩ := ψ₀.prim.exists_ringOfIntegers
  let f := algebraMap (𝓞 K) (𝓞 L)
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)
  have hχ' : orderOf (χ.ringHomComp f) = 3 := by
    rw [← hχ]
    exact orderOf_injective (MulChar.ringHomCompHom f) (MulChar.injective_ringHomComp hf) χ
  have h := three_dvd_jacobiSum_add_one hχ' hψ
  rw [jacobiSum_ringHomComp] at h
  -- The congruence `J(χ, χ) ≡ -1 (mod 3)` descends from `𝓞 L` to `𝓞 K`.
  rw [isPrimaryEisenstein_iff, ← RingOfIntegers.algebraMap_dvd_algebraMap_iff (L := L), map_sub,
    map_ofNat, map_ofNat]
  rw [show f (jacobiSum χ χ) - 2 = f (jacobiSum χ χ) + 1 - 3 by ring]
  exact dvd_sub h dvd_rfl

end TauCeti

namespace Ideal

variable {K : Type*} [Field K] [NumberField K] [HasEnoughRootsOfUnity (𝓞 K) 3]
  {P : Ideal (𝓞 K)} [P.IsMaximal] [Fintype (𝓞 K ⧸ P)]

/-- **The Jacobi sum of the cubic residue symbol is primary.** If `P` is a prime of `𝓞 K` whose
norm is prime to `3`, and `χ = (· / P)_3` is the cubic residue symbol at `P`, then
`J(χ, χ) ≡ 2 (mod 3)` in `𝓞 K`. -/
theorem isPrimaryEisenstein_jacobiSum_powerResidueSymbol (hP : (absNorm P).Coprime 3) :
    TauCeti.IsPrimaryEisenstein
      (jacobiSum (powerResidueSymbol P 3) (powerResidueSymbol P 3)) := by
  let _ := Ideal.Quotient.field P
  exact TauCeti.isPrimaryEisenstein_jacobiSum (orderOf_powerResidueSymbol hP)

end Ideal
