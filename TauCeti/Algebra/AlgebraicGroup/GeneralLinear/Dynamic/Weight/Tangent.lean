/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.ClosedImmersion.Ideals
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Parabolic.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Unipotent.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Tangent
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Unipotent.Tangent

/-!
# Dynamic tangent spaces in a faithful matrix representation

Let a closed subgroup `G` of `GL_N` carry a cocharacter that acts diagonally with integer
weights `w i` on the ambient representation. Its dynamic parabolic tangent space consists
exactly of the tangent vectors whose matrix entries have nonnegative weight difference
`w i - w j`; its dynamic unipotent tangent space consists exactly of those with strictly
positive weight difference. These are equations on the differential of the given closed
immersion, with no smoothness, field, or finite-type assumptions.

These criteria also apply to nonreduced subgroups and coefficient algebras.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), §§10 and 13.
-/

public section

open TauCeti.Cocharacter

namespace TauCeti.GeneralLinear.Dynamic

universe u v w

variable {R : Type u} [CommRing R] {N : ℕ}
variable {H : Type v} [CommRing H] [HopfAlgebra R H]
variable {B : Type w} [CommRing B] [Algebra R B]

/-- In a faithful representation with diagonal cocharacter, the dynamic parabolic Lie
algebra is cut out by the negative-weight matrix entries of the differential. -/
theorem mem_lieSubalgebra_parabolicDefiningHopfIdeal_iff_of_weightCocharacter
    (w : Fin N → ℤ) (φ : coordinateHopfAlgebra R N →ₐc[R] H)
    (hφ : Function.Surjective φ) (l : H →ₐc[R] LaurentPolynomial R)
    (hl : l.comp φ = weightCocharacter (R := R) w)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    d ∈ (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B) ↔
      (tangentMatrix N (derivationCompLieHom (B := B) φ d)).BlockTriangular
        (OrderDual.toDual ∘ w) := by
  -- Combine the closed-immersion identities from Dynamic.ClosedImmersion.Ideals
  -- with the matrix criterion in GeneralLinear.Weight.Parabolic.Tangent.
  rw [φ.parabolicDefiningHopfIdeal_eq_map_of_surjective hφ l, hl,
    parabolicDefiningHopfIdeal_weightCocharacter]
  exact mem_lieSubalgebra_map_weightParabolicDefiningHopfIdeal_iff w φ d

/-- In a faithful representation with diagonal cocharacter, the dynamic unipotent Lie
algebra is cut out by the nonpositive-weight matrix entries of the differential. -/
theorem mem_lieSubalgebra_unipotentDefiningHopfIdeal_iff_of_weightCocharacter
    (w : Fin N → ℤ) (φ : coordinateHopfAlgebra R N →ₐc[R] H)
    (hφ : Function.Surjective φ) (l : H →ₐc[R] LaurentPolynomial R)
    (hl : l.comp φ = weightCocharacter (R := R) w)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    d ∈ l.unipotentDefiningHopfIdeal.lieSubalgebra (B := B) ↔
      ∀ i j, w i ≤ w j → tangentMatrix N (derivationCompLieHom (B := B) φ d) i j = 0 := by
  -- Combine the closed-immersion identities from Dynamic.ClosedImmersion.Ideals
  -- with the matrix criterion in GeneralLinear.Weight.Unipotent.Tangent.
  rw [φ.unipotentDefiningHopfIdeal_eq_map_of_surjective hφ l, hl,
    unipotentDefiningHopfIdeal_weightCocharacter]
  exact mem_lieSubalgebra_map_weightUnipotentDefiningHopfIdeal_iff w φ d

end TauCeti.GeneralLinear.Dynamic
