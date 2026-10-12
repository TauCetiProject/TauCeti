/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.GaloisDual.Basic
public import TauCeti.FieldTheory.Finite.Frobenius

/-!
# Hermitian duals for the Frobenius automorphism

The Galois dual of a code for a semiring automorphism `σ` uses the form
`h(x, y) = ∑ i, x i * σ (y i)`. This file specializes `σ` to the Frobenius automorphism
`frobeniusEquiv K p`, sending `x` to `x ^ p`, of a finite field `K` of order `p ^ 2`. There the
Frobenius is an involution (`TauCeti.FiniteField.frobeniusEquiv_involutive`), so its Galois dual
is a Hermitian dual: the dual of a row space is the kernel of the entrywise `p`-th power of the
generator. The remaining consequences of involutivity, such as `RingEquiv.galoisDual_galoisDual`,
apply verbatim to `frobeniusEquiv K p` with that involutivity proof, and membership in the dual
is `RingEquiv.mem_galoisDual` with `σ (y i) = y i ^ p`. For `p = 2` this is Hermitian duality
over the field of four elements, the setting of the Hermitian self-dual hexacode. Omitting the
entrywise `p`-th power computes the Euclidean dual instead.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*, §1.3.
-/

public section

namespace RingEquiv

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
  [CharP K p]

/-- Over a field of order `p ^ 2`, the Frobenius Galois dual of a row space is the kernel of the
entrywise `p`-th power of the generator. -/
theorem galoisDual_range_vecMulLinear_frobeniusEquiv (hK : Nat.card K = p ^ 2)
    {ρ : Type*} [Fintype ρ] (G : Matrix ρ ι K) :
    galoisDual (frobeniusEquiv K p) (LinearMap.range G.vecMulLinear) =
      LinearMap.ker (G.map (frobenius K p)).mulVecLin := by
  simpa only [coe_frobeniusEquiv] using
    galoisDual_range_vecMulLinear_of_involutive _
      (TauCeti.FiniteField.frobeniusEquiv_involutive hK) G

end RingEquiv
