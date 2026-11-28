/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.PrincipalMinorProd

/-!
# K-dominant weights for indefinite unitary groups

For a labelling `ε` of the indices (for `U(p, q)`, the signs of `diag ε`) and an injective ranking
`o`, the weight `w` is `K`-dominant for `o` (`TauCeti.IsKDominant ε o w`) if `w b ≤ w a` whenever
`ε a = ε b` and `o a < o b`. Then a matrix `b` that is block diagonal for `ε` and triangular for
`o` satisfies `m_w(x b) = m_w(x) · ∏_a b_aa ^ w_a`
(`TauCeti.IsKDominant.principalMinorProd_mul_right`), and one that is block diagonal for `ε` and
triangular for the reversed ranking satisfies `m_w(b x) = (∏_a b_aa ^ w_a) · m_w(x)`
(`TauCeti.IsKDominant.principalMinorProd_mul_left`).

These equivariance identities are used in the holomorphic extension of coefficients of highest
vectors for `U(p, q)` and in Flensted-Jensen's integral formula for discrete series coefficients.

## Main definitions

* `TauCeti.IsKDominant ε o w`: `w` is antitone along `o` on each fibre of `ε`.

## Main results

* `TauCeti.IsKDominant.blockTriangular_toDual`, `TauCeti.IsKDominant.blockTriangular`: a block
  diagonal triangular matrix is block triangular for the order given by `w`.
* `TauCeti.IsKDominant.principalMinorProd_mul_right`,
  `TauCeti.IsKDominant.principalMinorProd_mul_left`: equivariance under block diagonal triangular
  matrices.

## References

* M. Flensted-Jensen, *Discrete series for semisimple symmetric spaces*, Ann. of Math. 111 (1980),
  253–311.
* The shorter formal proof of the Riemann hypothesis for Dirichlet `L`-functions,
  <https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh>
  (Apache 2.0): the definition here follows `New.IsKDominant` in
  `src/Lib/DiscreteSeries/FlenstedJensen/Defs.lean`, and the equivariance statements follow
  `New.IsKDominant.weightMinors_mul_borel` and `New.IsKDominant.weightMinors_oppBorel_mul` in
  `src/Lib/DiscreteSeries/Holomorphic/MaximalCompactMinors.lean`.
-/

public section

open Finset

namespace TauCeti

variable {ι α β : Type*} [LinearOrder α]

/-- A weight `w` is **`K`-dominant** for a labelling `ε` and a ranking `o` of the indices if it is
antitone along `o` on each fibre of `ε`: `w b ≤ w a` whenever `ε a = ε b` and `o a < o b`. For the
unitary group of `diag ε`, whose maximal compact subgroup consists of the matrices that are block
diagonal for `ε`, these are the weights dominant for the Borel subgroup of that compact subgroup
determined by `o`. -/
def IsKDominant (ε : ι → β) (o : ι → α) (w : ι → ℤ) : Prop :=
  ∀ a b, ε a = ε b → o a < o b → w b ≤ w a

theorem isKDominant_iff {ε : ι → β} {o : ι → α} {w : ι → ℤ} :
    IsKDominant ε o w ↔ ∀ a b, ε a = ε b → o a < o b → w b ≤ w a :=
  Iff.rfl

namespace IsKDominant

variable {R : Type*} [Zero R] {ε : ι → β} {o : ι → α} {w : ι → ℤ} {b : Matrix ι ι R}

/-- For a `K`-dominant weight `w`, a matrix that is block diagonal for `ε` and triangular for an
injective ranking `o` is block upper triangular for the decreasing values of `w`. -/
theorem blockTriangular_toDual (hw : IsKDominant ε o w) (ho : Function.Injective o)
    (hbε : ∀ a c, ε a ≠ ε c → b a c = 0) (hbo : b.BlockTriangular o) :
    b.BlockTriangular (OrderDual.toDual ∘ w) := by
  intro i j hij
  simp only [Function.comp_apply, OrderDual.toDual_lt_toDual] at hij
  by_cases hε : ε i = ε j
  · rcases lt_trichotomy (o i) (o j) with h | h | h
    · exact absurd (hw i j hε h) (not_le.mpr hij)
    · exact absurd (ho h ▸ hij) (lt_irrefl _)
    · exact hbo h
  · exact hbε i j hε

/-- For a `K`-dominant weight `w`, a matrix that is block diagonal for `ε` and triangular for the
reverse of an injective ranking `o` is block upper triangular for the increasing values of `w`. -/
theorem blockTriangular (hw : IsKDominant ε o w) (ho : Function.Injective o)
    (hbε : ∀ a c, ε a ≠ ε c → b a c = 0) (hbo : b.BlockTriangular (OrderDual.toDual ∘ o)) :
    b.BlockTriangular w := by
  intro i j hij
  by_cases hε : ε i = ε j
  · rcases lt_trichotomy (o i) (o j) with h | h | h
    · exact hbo (OrderDual.toDual_lt_toDual.mpr h)
    · exact absurd (ho h ▸ hij) (lt_irrefl _)
    · exact absurd (hw j i hε.symm h) (not_le.mpr hij)
  · exact hbε i j hε

variable {K : Type*} [Fintype ι] [DecidableEq ι] [Field K] {b : Matrix ι ι K}

/-- **Equivariance on the right.** For a `K`-dominant weight `w` and a matrix `b` that is block
diagonal for `ε` and triangular for an injective ranking `o`, with nonzero diagonal entries,
`m_w(x * b) = m_w(x) * ∏_a b_aa ^ w_a`. -/
theorem principalMinorProd_mul_right (hw : IsKDominant ε o w) (ho : Function.Injective o)
    (hbε : ∀ a c, ε a ≠ ε c → b a c = 0) (hbo : b.BlockTriangular o) (hd : ∀ a, b a a ≠ 0)
    (x : Matrix ι ι K) :
    (x * b).principalMinorProd w = x.principalMinorProd w * ∏ a, b a a ^ w a := by
  rw [(hw.blockTriangular_toDual ho hbε hbo).principalMinorProd_mul_right,
    hbo.principalMinorProd_eq_prod_zpow ho hd]

/-- **Equivariance on the left.** For a `K`-dominant weight `w` and a matrix `b` that is block
diagonal for `ε` and triangular for the reverse of an injective ranking `o`, with nonzero
diagonal entries, `m_w(b * x) = (∏_a b_aa ^ w_a) * m_w(x)`. -/
theorem principalMinorProd_mul_left (hw : IsKDominant ε o w) (ho : Function.Injective o)
    (hbε : ∀ a c, ε a ≠ ε c → b a c = 0) (hbo : b.BlockTriangular (OrderDual.toDual ∘ o))
    (hd : ∀ a, b a a ≠ 0) (x : Matrix ι ι K) :
    (b * x).principalMinorProd w = (∏ a, b a a ^ w a) * x.principalMinorProd w := by
  rw [(hw.blockTriangular ho hbε hbo).principalMinorProd_mul_left,
    hbo.principalMinorProd_eq_prod_zpow (OrderDual.toDual.injective.comp ho) hd]

end IsKDominant

end TauCeti
