/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Unipotent.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent

/-!
# Tangent equations of weight-unipotent subgroups

The Lie algebra of the weight-unipotent subgroup of `GL_N` consists of matrices whose
`(i,j)` entry vanishes whenever `w i ≤ w j`. Thus only strictly positive weight differences
occur. The inverse-image criterion applies the same equations to the differential of any
homomorphism into `GL_N`, over arbitrary commutative base and coefficient rings.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10 and 13.
-/

public section

namespace TauCeti.GeneralLinear

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {N : ℕ}

/-- A tangent vector belongs to the weight-unipotent subgroup exactly when every entry
of nonpositive weight difference vanishes. -/
theorem mem_lieSubalgebra_weightUnipotentDefiningHopfIdeal_iff (w : Fin N → ℤ)
    (d : Derivation R (coordinateHopfAlgebra R N)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R N) B)) :
    d ∈ HopfIdeal.lieSubalgebra (B := B) (weightUnipotentDefiningHopfIdeal R w) ↔
      ∀ i j, w i ≤ w j → tangentMatrix N d i j = 0 := by
  -- Use HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span and the tangent-matrix map
  -- of GeneralLinear.Tangent, as in the weight-parabolic calculation.
  rw [HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _
    (weightUnipotentDefiningHopfIdeal_toIdeal R w)]
  have hentry (i j : Fin N) :
      d ((genericMatrix R N) i j -
        (1 : Matrix (Fin N) (Fin N) (coordinateHopfAlgebra R N)) i j) =
      d ((genericMatrix R N) i j) := by
    classical
    simp only [map_sub, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · intro hd i j hij
    have hz := hd _ (sub_one_apply_mem_weightUnipotentRelationSet R w hij)
    rw [hentry] at hz
    rw [tangentMatrix_apply, ← genericMatrix_apply, hz, map_zero]
  · intro hd x hx
    obtain ⟨i, j, hij, rfl⟩ := (mem_weightUnipotentRelationSet_iff R w x).mp hx
    rw [hentry]
    apply (Bialgebra.CounitAlgebra.algEquivSelf R (coordinateHopfAlgebra R N) B).injective
    rw [map_zero, genericMatrix_apply, ← tangentMatrix_apply]
    exact hd i j hij

/-- The tangent space of the inverse image of a weight-unipotent subgroup is cut out by
the nonpositive-weight entries of the differential. -/
theorem mem_lieSubalgebra_map_weightUnipotentDefiningHopfIdeal_iff
    {H : Type*} [CommRing H] [HopfAlgebra R H]
    (w : Fin N → ℤ) (f : coordinateHopfAlgebra R N →ₐc[R] H)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    d ∈ HopfIdeal.lieSubalgebra (B := B) ((weightUnipotentDefiningHopfIdeal R w).map f) ↔
      ∀ i j, w i ≤ w j → tangentMatrix N (derivationCompLieHom (B := B) f d) i j = 0 := by
  rw [HopfIdeal.lieSubalgebra_map, LieSubalgebra.mem_comap]
  exact mem_lieSubalgebra_weightUnipotentDefiningHopfIdeal_iff w _

end TauCeti.GeneralLinear
