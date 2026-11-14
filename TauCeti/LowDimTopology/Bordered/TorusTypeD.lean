/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.PointedMatchedCircle
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Occupancy
public import TauCeti.LowDimTopology.Bordered.TypeD

/-!
# An unbounded type `D` structure over the torus algebra

The box tensor product `M ⊠ N` of a type `A` module with a type `D` structure has the differential
`∂ (m ⊗ x) = ∑_k (m_{k+1} ⊗ 1) (m ⊗ δ^k x)`, a finite sum only under a boundedness hypothesis
(`TauCeti.TypeDStructure.IsBounded`). This file shows that a finite set of generators is not such a
hypothesis, with the one-generator example of Lipshitz, Ozsváth and Thurston over the torus
algebra.

The torus algebra is the summand `A(Z, 0)` with one strand of the algebra of the genus-one pointed
matched circle `Z`, whose points `0, 1, 2, 3` are matched as `{0, 2}` and `{1, 3}`
(`TauCeti.PointedMatchedCircle.genusOne`); it is `matchedSummand R genusOne.pair 1`, a differential
algebra with the restricted differential `matchedSummandDifferential R genusOne.pair 1`. Its
idempotents are the `I({p})` of the matched pairs `p`
(`TauCeti.StrandsAlgebra.oneStrandIdem R genusOne.pair p`), and the chord `ρ₁₂` from `0` to `2`
(`TauCeti.StrandsAlgebra.oneStrandChord R genusOne.pair`) runs between the two matched points `0`
and `2`, so it starts and ends at the idempotent `ι₀ = I({0}) + I({2})` of the pair
`genusOne.pair 0 = {0, 2}`.

The type `D` structure `TauCeti.StrandsAlgebra.torusRho₁₂TypeD` has one generator `x` at `ι₀` and
structure map `δ¹ x = ρ₁₂ ⊗ x`. Its structure equation `d ρ₁₂ + ρ₁₂ ρ₁₂ = 0` holds since a single
strand has no crossing and `ρ₁₂` ends at `2`, where it does not start. Its iterates are
`δᵏ x = ρ₁₂ ⊗ ⋯ ⊗ ρ₁₂ ⊗ x` (`TauCeti.StrandsAlgebra.iteratedCoeff_torusRho₁₂TypeD`), which are
nonzero over every nontrivial ring although `ρ₁₂ ρ₁₂ = 0`: the iterates are tensor powers, not
products, and the coordinate of the strand `ρ₁₂` takes the value `1` on each factor. So the
structure is not bounded (`TauCeti.StrandsAlgebra.not_isBounded_torusRho₁₂TypeD`), and paired with
a type `A` module whose operations `m_{k+1}(y, ρ₁₂, …, ρ₁₂)` are nonzero for every `k` its box
tensor differential would be an infinite sum.

## Main definitions

* `TauCeti.StrandsAlgebra.torusRho₁₂TypeD`: the type `D` structure `δ¹ x = ρ₁₂ ⊗ x`.

## Main results

* `TauCeti.StrandsAlgebra.iteratedCoeff_torusRho₁₂TypeD`: `δᵏ x = ρ₁₂^{⊗ k} ⊗ x`.
* `TauCeti.StrandsAlgebra.not_isBounded_torusRho₁₂TypeD`: over a nontrivial ring the structure
  is not bounded.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  §2.2 (boundedness of type `D` structures and the box tensor product) and §3.2 (the torus
  algebra).
-/

public section

noncomputable section

namespace TauCeti

namespace StrandsAlgebra

open PointedMatchedCircle StrandDiagram

variable (R : Type*) [CommRing R]

/-- **The type `D` structure `δ¹ x = ρ₁₂ ⊗ x`** over the torus algebra: one generator `x` at the
idempotent `ι₀ = I({0}) + I({2})` of the pair `genusOne.pair 0 = {0, 2}`, whose only coefficient is
the chord `ρ₁₂` from `0` to `2`. -/
def torusRho₁₂TypeD :
    TypeDStructure (matchedSummandDifferential R genusOne.pair 1) (oneStrandIdem R genusOne.pair)
      Unit where
  idem _ := Set.rangeFactorization genusOne.pair 0
  coeff := Matrix.of fun _ _ ↦ oneStrandChord R genusOne.pair (by decide : (0 : Fin 4) < 2)
  idem_mul_coeff _ _ := by simp
  coeff_mul_idem _ _ := by simp
  map_coeff_add_coeff_mul_coeff := Matrix.ext fun _ _ ↦ by
    simp [Matrix.mul_apply,
      oneStrandChord_mul_oneStrandChord_of_ne _ _ _ (by decide : (2 : Fin 4) ≠ 0)]

@[simp]
theorem torusRho₁₂TypeD_idem (x : Unit) :
    (torusRho₁₂TypeD R).idem x = Set.rangeFactorization genusOne.pair 0 :=
  (rfl)

@[simp]
theorem torusRho₁₂TypeD_coeff (x y : Unit) :
    (torusRho₁₂TypeD R).coeff x y = oneStrandChord R genusOne.pair (by decide : (0 : Fin 4) < 2) :=
  (rfl)

/-- **The iterates of `δ¹ x = ρ₁₂ ⊗ x`** are `δᵏ x = ρ₁₂ ⊗ ⋯ ⊗ ρ₁₂ ⊗ x`, with `k` factors `ρ₁₂`. -/
@[simp]
theorem iteratedCoeff_torusRho₁₂TypeD (k : ℕ) (x z : Unit) :
    (torusRho₁₂TypeD R).iteratedCoeff k x z = PiTensorProduct.tprod R fun _ ↦
      oneStrandChord R genusOne.pair (by decide : (0 : Fin 4) < 2) :=
  (torusRho₁₂TypeD R).iteratedCoeff_self_of_coeff_eq_zero
    (fun y hy ↦ absurd (Subsingleton.elim y x) hy) k

/-- **The type `D` structure `δ¹ x = ρ₁₂ ⊗ x` is not bounded.** Over a nontrivial ring its iterates
`δᵏ x = ρ₁₂^{⊗ k} ⊗ x` never vanish, although `ρ₁₂ ρ₁₂ = 0` and there is a single generator. -/
theorem not_isBounded_torusRho₁₂TypeD [Nontrivial R] : ¬(torusRho₁₂TypeD R).IsBounded := by
  refine (torusRho₁₂TypeD R).not_isBounded_of_coeff_eq_zero_of_tprod_ne_zero (x := ())
    (fun y hy ↦ absurd (Subsingleton.elim y ()) hy) fun k h ↦ ?_
  -- The coordinate of the strand `ρ₁₂` takes the value `1` on each factor of `ρ₁₂^{⊗ k}`.
  have := congrArg (PiTensorProduct.dualDistrib (PiTensorProduct.tprod R fun _ : Fin k ↦
    ((basis R (Fin 4)).coord (single 0 2 (by decide))).comp
      (matchedSummand R genusOne.pair 1).toSubmodule.subtype)) h
  simp [PiTensorProduct.dualDistrib_apply] at this

end StrandsAlgebra

end TauCeti
