/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.RankOne

/-!
# The power basis of the coordinate ring of `αₚ`

Over a base ring `R` of prime characteristic `p`, the coordinate ring of `αₚ` is
`R[x] / (xᵖ)` (`TauCeti.AlphaP.CoordinateRing`). Through the identification of `R[x]` with the
polynomial ring (`SymmetricAlgebra.equivPolynomial`), it is `AdjoinRoot (Xᵖ)`
(`TauCeti.AlphaP.coordinateRingEquivAdjoinRoot`). Write `[x]` for the class of `x`. Transporting
Mathlib's `AdjoinRoot.powerBasis'`, the coordinate ring is free over `R` with basis
`1, [x], …, [x]ᵖ⁻¹` (`TauCeti.AlphaP.powerBasis`).

## Main definitions

* `TauCeti.AlphaP.coordinateRingEquivAdjoinRoot`: the algebra isomorphism
  `R[x] / (xᵖ) ≃ AdjoinRoot (Xᵖ)`.
* `TauCeti.AlphaP.powerBasis`: the power basis `1, [x], …, [x]ᵖ⁻¹` of `R[x] / (xᵖ)`.

## Main results

* `TauCeti.AlphaP.powerBasis_gen`: the generator of the power basis is `[x]`.
* `TauCeti.AlphaP.powerBasis_dim`: the power basis has `p` elements.
* `TauCeti.AlphaP.powerBasis_basis_apply`: its `i`-th vector is `[x]ⁱ`.
-/

public section

open Polynomial SymmetricAlgebra

namespace TauCeti

namespace AlphaP

universe u

variable {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- The coordinate ring of `αₚ` is `AdjoinRoot (Xᵖ)`, through the identification of the
coordinate ring of `𝔾ₐ` with the polynomial ring. -/
noncomputable def coordinateRingEquivAdjoinRoot :
    CoordinateRing (R := R) p ≃ₐ[R] AdjoinRoot (X ^ p : R[X]) :=
  Ideal.quotientEquivAlg _ _ SymmetricAlgebra.equivPolynomial <| by
    rw [hopfIdeal_toIdeal, Ideal.map_span, Set.image_singleton, map_pow, RingHom.coe_coe,
      equivPolynomial_ι_one]

/-- The isomorphism `R[x] / (xᵖ) ≃ AdjoinRoot (Xᵖ)` sends the class of `f` to the class of the
polynomial corresponding to `f`. -/
@[simp]
theorem coordinateRingEquivAdjoinRoot_mk (f : SymmetricAlgebra R R) :
    coordinateRingEquivAdjoinRoot p
        (Ideal.Quotient.mk (Ideal.span {(ι R R 1 : SymmetricAlgebra R R) ^ p}) f) =
      AdjoinRoot.mk (X ^ p) (equivPolynomial f) := by
  exact Ideal.quotientEquivAlg_mk ..

/-- **The power basis `1, [x], …, [x]ᵖ⁻¹` of the coordinate ring of `αₚ`.** -/
noncomputable def powerBasis : PowerBasis R (CoordinateRing (R := R) p) :=
  (AdjoinRoot.powerBasis' (monic_X_pow p)).map (coordinateRingEquivAdjoinRoot p).symm

/-- The generator of `TauCeti.AlphaP.powerBasis` is the class of `x`. -/
theorem powerBasis_gen :
    (powerBasis (R := R) p).gen =
      Ideal.Quotient.mk (hopfIdeal (R := R) p).toIdeal (ι R R 1 : SymmetricAlgebra R R) := by
  rw [powerBasis, PowerBasis.map_gen, AdjoinRoot.powerBasis'_gen, AlgEquiv.symm_apply_eq]
  -- `coordinateRingEquivAdjoinRoot_mk` is stated over `Ideal.span {x ^ p}`, which is the ideal
  -- `(hopfIdeal p).toIdeal` of the goal by `hopfIdeal_toIdeal` (`rfl`). Neither `rw` nor `simp`
  -- can rewrite that ideal, because the quotient type depends on it, so `Eq.trans` uses the
  -- definitional equality directly.
  refine Eq.trans ?_ (coordinateRingEquivAdjoinRoot_mk p _).symm
  rw [equivPolynomial_ι_one, AdjoinRoot.mk_X]

/-- The power basis of the coordinate ring of `αₚ` has `p` elements. -/
@[simp]
theorem powerBasis_dim : (powerBasis (R := R) p).dim = p := by
  have := CharP.nontrivial_of_char_ne_one (R := R) (Fact.out (p := p.Prime)).ne_one
  rw [powerBasis, PowerBasis.map_dim, AdjoinRoot.powerBasis'_dim, natDegree_X_pow]

/-- The `i`-th vector of the power basis of the coordinate ring of `αₚ` is the class of `xⁱ`. -/
theorem powerBasis_basis_apply (i : Fin (powerBasis (R := R) p).dim) :
    (powerBasis (R := R) p).basis i =
      Ideal.Quotient.mk (hopfIdeal (R := R) p).toIdeal
        ((ι R R 1 : SymmetricAlgebra R R) ^ (i : ℕ)) := by
  rw [PowerBasis.coe_basis, map_pow, powerBasis_gen]

end AlphaP

end TauCeti
