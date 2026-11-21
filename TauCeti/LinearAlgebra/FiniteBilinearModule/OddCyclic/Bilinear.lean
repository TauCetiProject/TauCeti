/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.Decomposition
public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.PiClassification
import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic.Refinement

/-!
# Symmetric pairings on finite abelian `p`-groups at odd `p`

On a finite abelian group of odd order, a symmetric pairing has a unique quadratic refinement
(`TauCeti.FiniteBilinearModule.quadraticRefinement`), and finite quadratic modules of odd order are
classified by their bilinear modules alone
(`TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd`).

Through this refinement, Nikulin's decomposition and the classification of orthogonal sums of odd
cyclic generators pass from quadratic modules to symmetric pairings. For an odd prime `p`, every
nondegenerate symmetric pairing on a finite abelian `p`-group is an orthogonal sum of the pairings
`b_θ^{(p)}(p^k)` of the generators `q_θ^{(p)}(p^k)`, on `ℤ/p^k` with `b(x, y) = θxy / p^k`, for
`k ≥ 1` and `θ` prime to `p`. Two such orthogonal sums are isometric exactly when, for every
`m ≥ 1`, they have the same number of summands of order `p^m`, and the Legendre symbols of the
coefficients of these summands have the same product; that product is the Legendre symbol of the
determinant `∏ θᵢ` of the homogeneous summand of order `p^m`.

## Main declarations

* `TauCeti.FiniteBilinearModule.exists_isometry_pi_oddCyclic_of_natCard_eq_pow`: at an odd prime
  `p`, a nondegenerate finite bilinear module of order `p^N` is an orthogonal sum of the pairings
  `b_θ^{(p)}(p^k)`, `k ≥ 1`, with `θ` prime to `p`.
* `TauCeti.FiniteBilinearModule.nonempty_isometry_pi_oddCyclic_iff`: the classification of
  orthogonal sums of the pairings `b_θ^{(p)}(p^k)` by the numbers of summands of each order and
  the products of the Legendre symbols of their coefficients.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.8.
* C. T. C. Wall, *Quadratic forms on finite groups, and related topics*, Topology 2 (1963),
  281–298.
-/

public section

namespace TauCeti

universe u

namespace FiniteBilinearModule

open Finset
open FiniteQuadraticModule (oddCyclic pi)

variable {p : ℕ} [Fact p.Prime]

/-- **Decomposition of symmetric pairings on `p`-groups at an odd prime.** A nondegenerate finite
bilinear module of order `p^N`, for an odd prime `p`, is isometric to an orthogonal sum of the
pairings `b_θ^{(p)}(p^k)` of the odd cyclic generators, with `k ≥ 1` and `θ` prime to `p`. -/
theorem exists_isometry_pi_oddCyclic_of_natCard_eq_pow (hp : Odd p) (A : FiniteBilinearModule.{u})
    (hA : A.IsNondegenerate) {N : ℕ} (hN : Nat.card A = p ^ N) :
    ∃ (n : ℕ) (k : Fin n → ℕ) (θ : Fin n → ℤ), (∀ i, 0 < k i ∧ IsCoprime (p : ℤ) (θ i)) ∧
      Nonempty (Isometry
        (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i)).toFiniteBilinearModule A) := by
  -- The bilinear module of the refinement is `A` by definition
  -- (`quadraticRefinement_toFiniteBilinearModule`), so `hA` and `f.toFiniteBilinearModule` apply.
  obtain ⟨n, k, θ, hkθ, ⟨f⟩⟩ :=
    (A.quadraticRefinement (hN ▸ hp.pow)).exists_isometry_pi_oddCyclic_of_natCard_eq_pow hp hA hN
  exact ⟨n, k, θ, hkθ, ⟨f.toFiniteBilinearModule⟩⟩

/-- **Classification of symmetric pairings on `p`-groups at an odd prime.** For an odd prime `p`,
exponents `k_i`, `l_j` and coefficients `θ_i`, `η_j` prime to `p`, the orthogonal sums of the
pairings `b_{θ_i}^{(p)}(p^{k_i})` and `b_{η_j}^{(p)}(p^{l_j})` are isometric exactly when, for
every `m ≥ 1`, they have the same number of summands of order `p^m`, and the Legendre symbols of
the coefficients of these summands have the same product. -/
theorem nonempty_isometry_pi_oddCyclic_iff (hp : Odd p) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ι → ℕ) (l : κ → ℕ) {θ : ι → ℤ} {η : κ → ℤ} (hθ : ∀ i, IsCoprime (p : ℤ) (θ i))
    (hη : ∀ j, IsCoprime (p : ℤ) (η j)) :
    Nonempty (Isometry (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i)).toFiniteBilinearModule
      (pi fun j ↦ oddCyclic (p ^ l j) hp.pow (η j)).toFiniteBilinearModule) ↔
      ∀ m, 0 < m → #{i | k i = m} = #{j | l j = m} ∧
        ∏ i with k i = m, legendreSym p (θ i) = ∏ j with l j = m, legendreSym p (η j) := by
  have hodd : Odd (Nat.card (pi fun i ↦ oddCyclic (p ^ k i) hp.pow (θ i))) := by
    rw [Nat.card_pi]
    simpa [Finset.prod_pow_eq_pow_sum] using hp.pow
  rw [← FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd hodd]
  exact FiniteQuadraticModule.nonempty_isometry_pi_oddCyclic_iff hp k l hθ hη

end FiniteBilinearModule

end TauCeti
