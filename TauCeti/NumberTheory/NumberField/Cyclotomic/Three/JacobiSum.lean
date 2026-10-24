/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.JacobiSum.Cubic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Three.Primary
public import TauCeti.NumberTheory.NumberField.PowerResidueSymbol.Basic

/-!
# The Jacobi sum of a cubic character is primary

Let `χ` be a multiplicative character of order `3` on a finite field `F`, with values in an
integral domain `R`. Then the Jacobi sum `J(χ, χ)` is *primary*: `J(χ, χ) ≡ 2 (mod 3)` in `R`.
For the cubic residue symbol `χ = (· / π)_3` of a prime `π` of `ℤ[ω]` this is the first step in
the identification `J(χ, χ) = π` of the Jacobi sum with the primary generator of `π`, on which the
proof of cubic reciprocity rests.

## Main results

* `TauCeti.isPrimaryEisenstein_jacobiSum`: `J(χ, χ)` is primary for every character `χ` of
  order `3` with values in an integral domain.
* `Ideal.isPrimaryEisenstein_jacobiSum_powerResidueSymbol`: the case of the cubic residue symbol
  `(· / P)_3` at a prime `P` of the ring of integers of a number field, whose norm is prime
  to `3`.

The proof rewrites `J(χ, χ) - 2` as `(J(χ, χ) + 1) - 3` and uses the congruence
`TauCeti.three_dvd_jacobiSum_add_one`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 8, §3,
  Proposition 8.3.4.
* N. Xu, *Reciprocity Laws*, Proposition 4.8.
* S. D. Adhikari, *The early reciprocity laws: from Gauss to Eisenstein*, §3, Lemma 3.2.
-/

public section

open NumberField

namespace TauCeti

variable {F R : Type*} [Field F] [Fintype F] [CommRing R] [IsDomain R]

/-- **The Jacobi sum of a cubic character is primary.** If `χ` is a multiplicative character of
order `3` on a finite field, with values in an integral domain `R`, then `J(χ, χ) ≡ 2 (mod 3)`
in `R`. -/
theorem isPrimaryEisenstein_jacobiSum {χ : MulChar F R} (hχ : orderOf χ = 3) :
    IsPrimaryEisenstein (jacobiSum χ χ) := by
  rw [isPrimaryEisenstein_iff, show jacobiSum χ χ - 2 = jacobiSum χ χ + 1 - 3 by ring]
  exact dvd_sub (three_dvd_jacobiSum_add_one hχ) dvd_rfl

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
