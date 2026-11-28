/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.FrobeniusCycle.Forms
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Edge pairings for Frobenius cycles

For a Frobenius cycle `T` over a local ring `W` and commutative ring `R` with `N` letters and
Frobenius power `P = p ^ e`, put `c₀ = k ^ 2 * (e * N)`
(`TauCeti.FrobeniusCycle.multinomialExponent`).
An *edge pairing* `(b, b')` on forms of degree `n` in each letter is a pair of weight vectors
`Exponent N k n → R` such that `b β * ρ_n(gᵀ) β α = b α * ρ_n(g) α β` and
`b β * b' β = p ^ (N * c₀)`.

## Main definitions and results

* `TauCeti.FrobeniusCycle.multinomialExponent`: the exponent `c₀ = k ^ 2 * (T.e * N)`.
* `TauCeti.FrobeniusCycle.IsEdgePairing`: the structure packaging adjointness of `T.letterRep n g`
  and `T.letterRep n gᵀ` under the `b`-weighted pairing, together with `b β * b' β = p ^ (N * c₀)`.
* `TauCeti.FrobeniusCycle.IsEdgePairing.dotProduct_letterRep_mulVec`: adjointness
  `h' ⬝ᵥ (b * T.letterRep n g *ᵥ h) = (T.letterRep n gᵀ *ᵥ h') ⬝ᵥ (b * h)`.
* `TauCeti.FrobeniusCycle.IsEdgePairing.pairing_mul_eq_pow_mul_dotProduct`: near-duality
  `h' ⬝ᵥ (b * (b' * η)) = p ^ (N * c₀) * (h' ⬝ᵥ η)`.
* `TauCeti.FrobeniusCycle.IsEdgePairing.dvd_pairing_letterRep_single`: pairing with a translate of
  a basis vector extracts the corresponding entry of the transpose translate weighted by `b`.

## References

* Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`),
  `src/New/UpperBound/ElementaryDivisors/Edges.lean`
  (`New.FrobeniusCycle.multinomialExponent`, `New.FrobeniusCycle.IsEdgePairing`,
  `New.FrobeniusCycle.IsEdgePairing.dotProduct_letterRep_mulVec`,
  `New.FrobeniusCycle.IsEdgePairing.pairing_mul_eq_pow_mul_dotProduct`).
-/

public section

namespace TauCeti.FrobeniusCycle

open Matrix

/-- The multinomial exponent `c₀ = k ^ 2 * (T.e * N)` for a Frobenius cycle `T` with `N` letters
and Frobenius power `P = T.p ^ T.e`. -/
def multinomialExponent {W R : Type*} [CommRing W] [IsLocalRing W] [CommRing R] {N : ℕ}
    (T : FrobeniusCycle W R N) (k : ℕ) : ℕ :=
  k ^ 2 * (T.e * N)

/-- A pair of weight vectors `b, b' : Exponent N k n → R` is an edge pairing for `T` if
`diag(b) * ρ_n(gᵀ) = ρ_n(g)ᵀ * diag(b)` for all `g : GL (Fin k) W` and
`b β * b' β = (T.p : R) ^ (N * T.multinomialExponent k)` for all `β`. -/
structure IsEdgePairing {W R : Type*} [CommRing W] [IsLocalRing W] [CommRing R] {N k n : ℕ}
    (T : FrobeniusCycle W R N) (b b' : Exponent N k n → R) : Prop where
  /-- Adjointness of `T.letterRep n g` and `T.letterRep n gᵀ` for the `b`-weighted pairing. -/
  adjoint : ∀ (g : GL (Fin k) W) (α β : Exponent N k n),
    b β * T.letterRep n (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin k) g).unop β α =
      b α * T.letterRep n g α β
  /-- The weights `b` and `b'` multiply pointwise to `p ^ (N * c₀)`. -/
  mul_eq_pow : ∀ β : Exponent N k n, b β * b' β = (T.p : R) ^ (N * T.multinomialExponent k)

/-- For an edge pairing `(b, b')`, translation by `g` is adjoint to translation by `gᵀ` under the
`b`-weighted pairing `⟨h, h'⟩ = h' ⬝ᵥ (b * h)`. -/
theorem IsEdgePairing.dotProduct_letterRep_mulVec {W R : Type*} [CommRing W] [IsLocalRing W]
    [CommRing R] {N k n : ℕ} {T : FrobeniusCycle W R N} {b b' : Exponent N k n → R}
    (hb : T.IsEdgePairing b b') (g : GL (Fin k) W) (h h' : Exponent N k n → R) :
    h' ⬝ᵥ (b * (T.letterRep n g *ᵥ h)) =
      (T.letterRep n (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin k) g).unop *ᵥ h') ⬝ᵥ
        (b * h) := by
  classical
  have h_diag (v : Exponent N k n → R) : b * v = diagonal b *ᵥ v :=
    funext fun β ↦ (mulVec_diagonal b v β).symm
  have h_adj : diagonal b * T.letterRep n g =
      (T.letterRep n (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin k) g).unop)ᵀ *
        diagonal b :=
    Matrix.ext fun α β ↦ by
      rw [diagonal_mul, mul_diagonal, transpose_apply, ← hb.adjoint, mul_comm]
  rw [h_diag, h_diag, mulVec_mulVec, h_adj, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- Every linear form `h' ↦ h' ⬝ᵥ η`, scaled by `p ^ (N * c₀)`, is realized by the edge pairing
with `b' * η`. -/
theorem IsEdgePairing.pairing_mul_eq_pow_mul_dotProduct {W R : Type*} [CommRing W]
    [IsLocalRing W] [CommRing R] {N k n : ℕ} {T : FrobeniusCycle W R N}
    {b b' : Exponent N k n → R} (hb : T.IsEdgePairing b b') (η h' : Exponent N k n → R) :
    h' ⬝ᵥ (b * (b' * η)) = (T.p : R) ^ (N * T.multinomialExponent k) * (h' ⬝ᵥ η) := by
  have h_mul : b * (b' * η) = (T.p : R) ^ (N * T.multinomialExponent k) • η :=
    funext fun β ↦ by simp [← mul_assoc, hb.mul_eq_pow]
  simp [h_mul]

/-- If `d` divides `(T.letterRep n gᵀ *ᵥ h') β`, then `d` divides the edge pairing of `h'` with
the `g`-translate of the basis vector `Pi.single β 1`. -/
theorem IsEdgePairing.dvd_pairing_letterRep_single {W R : Type*} [CommRing W] [IsLocalRing W]
    [CommRing R] {N k n : ℕ} {T : FrobeniusCycle W R N} {b b' : Exponent N k n → R}
    (hb : T.IsEdgePairing b b') (g : GL (Fin k) W) (h' : Exponent N k n → R)
    (β : Exponent N k n) {d : R}
    (hd : d ∣ (T.letterRep n
      (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin k) g).unop *ᵥ h') β) :
    d ∣ h' ⬝ᵥ (b * (T.letterRep n g *ᵥ Pi.single β 1)) := by
  classical
  rw [hb.dotProduct_letterRep_mulVec]
  let gT : GL (Fin k) W := (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin k) g).unop
  have h_single : (T.letterRep n gT *ᵥ h') ⬝ᵥ (b * Pi.single β 1) =
      (T.letterRep n gT *ᵥ h') β * b β := by
    simp [dotProduct, Pi.single_apply]
  rw [h_single]
  exact dvd_mul_of_dvd_left hd (b β)

end TauCeti.FrobeniusCycle
