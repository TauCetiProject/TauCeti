/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.Torus.TypeA
public import TauCeti.LowDimTopology.Bordered.Torus.TypeD
import TauCeti.Algebra.BigOperators.Fin

/-!
# Pairing the solid-torus modules over the torus algebra

By the pairing theorem of bordered Floer homology, gluing two solid tori along their boundary
tori gives a closed three-manifold `Y` with `HF̂(Y)` the homology of the box tensor product
`M ⊠ N` of the type `A` module `M` of one solid torus with the type `D` structure `N` of the other.
Varying the parametrization of the boundary of the second solid torus gives the genus-one
Heegaard splittings of `S³`, `S¹ × S²` and the lens spaces `L(p, 1)`, whose `HF̂` have ranks `1`,
`2` and `p`. This file computes these ranks algebraically, over any ring `R` of characteristic
two, from the solid-torus modules of `TauCeti.LowDimTopology.Bordered.Torus.TypeA` and the type `D`
structures of `TauCeti.LowDimTopology.Bordered.Torus.TypeD`. The box tensor product is
`TauCeti.TypeDStructure.typeABoxTensor`, with the differential
`TauCeti.TypeDStructure.typeABoxTensorDifferential`, and its homology is
`LinearMap.homology`.

The type `A` modules are the one-generator modules of three points `k < i < j` of
`TauCeti.StrandsAlgebra.threePointTypeA`, whose operations read the coordinates of their inputs.
By `TauCeti.LowDimTopology.Bordered.TypeA.OneStrand`, if the coefficients of a type `D` structure
`N` have no component along the idempotent `I(i)`, and none along the chord `ρ_ij` read by the
first input of the higher operations
(`TauCeti.StrandsAlgebra.typeABoxDifferential_threePointTypeA_eq_zero_of_coord_eq_zero_left`) or
along the chord `ρ_ki` read by the last
(`TauCeti.StrandsAlgebra.typeABoxDifferential_threePointTypeA_eq_zero_of_coord_eq_zero_right`),
then the box tensor differential vanishes, and the homology is free on the generators of `N` at
`I(i)` (`TauCeti.StrandsAlgebra.finrank_homology_threePointTypeA_of_typeABoxDifferential_eq_zero`).

Over the torus algebra, write `M₀` for `TauCeti.StrandsAlgebra.torusRho₂Rho₁TypeA`, with
`m_{n+3}(x, ρ₂, ρ₁₂, …, ρ₁₂, ρ₁) = x` and its generator at `ι₁`, and `M_∞` for
`TauCeti.StrandsAlgebra.torusRho₃Rho₂TypeA`, with `m_{n+3}(x, ρ₃, ρ₂₃, …, ρ₂₃, ρ₂) = x` and its
generator at `ι₀`. The chord `ρ₂` is read by both, by the first input of `M₀` and by the last of
`M_∞`, and no coefficient of the chains `TauCeti.StrandsAlgebra.torusChainTypeD n` lies along it.
So both pairings with the chains have vanishing differential:

* `M₀ ⊠ torusChainTypeD n` has homology of rank `n + 1`, the generators `γ₀, …, γₙ`
  (`TauCeti.StrandsAlgebra.finrank_homology_torusRho₂Rho₁TypeA_torusChainTypeD`): this is the rank
  of `HF̂(L(n + 1, 1))`, and of `HF̂(S³)` for `n = 0`;
* `M_∞ ⊠ torusChainTypeD n` has homology of rank `1`, the generator `x`
  (`TauCeti.StrandsAlgebra.finrank_homology_torusRho₃Rho₂TypeA_torusChainTypeD`), the rank of
  `HF̂(S³)`.

The framing `0`, which gives `S¹ × S²`, needs the bounded model
`TauCeti.StrandsAlgebra.torusBoundedRho₁₂TypeD` of `δ¹ x = ρ₁₂ ⊗ x`. The naive pairing of `M₀`
with `δ¹ x = ρ₁₂ ⊗ x` is zero, since the generator `x` sits at `ι₀` and the generator of `M₀` at
`ι₁`; as neither side is bounded, the box tensor product need not be invariant under homotopy
equivalence, and the bounded model, homotopy equivalent to `δ¹ x = ρ₁₂ ⊗ x`, gives the correct
rank. In `M₀ ⊠ torusBoundedRho₁₂TypeD` the two paths from `y₁` to `y₂` contribute `m₂(y₁, ι₁)` and
`m₃(y₁, ρ₂, ρ₁)`, both `y₁`, which cancel in characteristic two:

* `M₀ ⊠ torusBoundedRho₁₂TypeD` has homology of rank `2`, the generators `y₁` and `y₂`
  (`TauCeti.StrandsAlgebra.finrank_homology_torusRho₂Rho₁TypeA_torusBoundedRho₁₂TypeD`), the rank
  of `HF̂(S¹ × S²)`;
* `M_∞ ⊠ torusBoundedRho₁₂TypeD` has homology of rank `1`, the generator `x`
  (`TauCeti.StrandsAlgebra.finrank_homology_torusRho₃Rho₂TypeA_torusBoundedRho₁₂TypeD`).

So the same type `A` module `M₀`, paired with the structures of framings `-1`, `0` and `-p`, gives
the ranks `1`, `2` and `p`, while `M_∞` gives `1` in every framing. These are computations with the
algebraic modules and structures: identifying them with the invariants defined by holomorphic
curves, and the pairing theorem itself, are not part of this file.

## Main results

* `TauCeti.StrandsAlgebra.finrank_homology_torusRho₂Rho₁TypeA_torusChainTypeD`,
  `TauCeti.StrandsAlgebra.finrank_homology_torusRho₃Rho₂TypeA_torusChainTypeD`,
  `TauCeti.StrandsAlgebra.finrank_homology_torusRho₂Rho₁TypeA_torusBoundedRho₁₂TypeD`,
  `TauCeti.StrandsAlgebra.finrank_homology_torusRho₃Rho₂TypeA_torusBoundedRho₁₂TypeD`: the ranks of
  the pairings.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Theorem 1.3 (the pairing theorem), Chapter 2 (the box tensor product, equation (2.29)) and
  Chapter 11 (solid tori and knot complements).
-/

public section

noncomputable section

namespace TauCeti

namespace StrandsAlgebra

open PointedMatchedCircle

/-! ### The pairings over the torus algebra -/

section Torus

variable (R : Type*) [CommRing R]

/-- The coefficients of the chains have no component along an idempotent. -/
private theorem oneStrandIdemCoord_torusChainTypeD_coeff (n : ℕ) (p : Set.range genusOne.pair)
    (x y : Option (Fin (n + 1))) :
    oneStrandIdemCoord R genusOne.pair p ((torusChainTypeD R n).coeff x y) = 0 := by
  rcases x with _ | l <;> rcases y with _ | l' <;>
    simp [apply_ite (oneStrandIdemCoord _ _ _)]

/-- The coefficients of the chains have no component along `ρ₂`. -/
private theorem oneStrandChordCoord_one_two_torusChainTypeD_coeff (n : ℕ)
    (x y : Option (Fin (n + 1))) :
    oneStrandChordCoord R genusOne.pair (by decide : (1 : Fin 4) < 2)
      ((torusChainTypeD R n).coeff x y) = 0 := by
  rcases x with _ | l <;> rcases y with _ | l' <;>
    simp only [torusChainTypeD_coeff_none_some, torusChainTypeD_coeff_some_some,
      torusChainTypeD_coeff_none_right, map_add, map_zero, apply_ite (oneStrandChordCoord _ _ _),
      oneStrandChordCoord_oneStrandChord] <;> simp

/-- The box tensor differential with `torusBoundedRho₁₂TypeD` as a sum over the paths of length at
most two, the largest index of a generator. -/
private theorem typeABoxDifferential_torusBoundedRho₁₂TypeD_apply
    {Mm : UngradedAInfinityRightModule (matchedSummandDifferential R genusOne.pair 1) R}
    (φ : Fin 3 → R) (z : Fin 3) :
    (torusBoundedRho₁₂TypeD R).typeABoxDifferential Mm φ z = ∑ n ∈ Finset.range 3,
      ∑ x : Fin (n + 1) → Fin 3, if x (Fin.last n) = z then
        Mm.act n (fun l ↦ (torusBoundedRho₁₂TypeD R).coeff (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 := by
  rw [TypeDStructure.typeABoxDifferential_apply_eq_sum_of_lt _ _ (fun x : Fin 3 ↦ (x : ℕ))
    fun x y h ↦ by fin_cases x <;> fin_cases y <;> simp_all,
    (by decide : (Finset.univ.sup fun x : Fin 3 ↦ (x : ℕ)) = 2)]

/-- The coefficients of `torusBoundedRho₁₂TypeD` have no component along the idempotent `ι₀` of the
point `2`. -/
private theorem oneStrandIdemCoord_two_torusBoundedRho₁₂TypeD_coeff (x y : Fin 3) :
    oneStrandIdemCoord R genusOne.pair ⟨genusOne.pair 2, 2, rfl⟩
      ((torusBoundedRho₁₂TypeD R).coeff x y) = 0 := by
  fin_cases x <;> fin_cases y <;> simp [Subtype.ext_iff, genusOne_pair_one, genusOne_pair_two]

/-- The coefficients of `torusBoundedRho₁₂TypeD` have no component along `ρ₃`. -/
private theorem oneStrandChordCoord_two_three_torusBoundedRho₁₂TypeD_coeff (x y : Fin 3) :
    oneStrandChordCoord R genusOne.pair (by decide : (2 : Fin 4) < 3)
      ((torusBoundedRho₁₂TypeD R).coeff x y) = 0 := by
  fin_cases x <;> fin_cases y <;> simp

variable [CharP R 2]

/-- The box tensor differential of `torusRho₂Rho₁TypeA` with the chain `torusChainTypeD n`
vanishes: no coefficient of the chain lies along `ρ₂`, which the first input of every higher
operation of the module reads. -/
theorem typeABoxDifferential_torusRho₂Rho₁TypeA_torusChainTypeD (n : ℕ) :
    (torusChainTypeD R n).typeABoxDifferential (torusRho₂Rho₁TypeA R) = 0 := by
  rw [torusRho₂Rho₁TypeA_eq_threePointTypeA]
  exact typeABoxDifferential_threePointTypeA_eq_zero_of_coord_eq_zero_left
    (oneStrandIdemCoord_torusChainTypeD_coeff R n _)
    (oneStrandChordCoord_one_two_torusChainTypeD_coeff R n)

/-- The box tensor differential of `torusRho₃Rho₂TypeA` with the chain `torusChainTypeD n`
vanishes: no coefficient of the chain lies along `ρ₂`, which the last input of every higher
operation of the module reads. -/
theorem typeABoxDifferential_torusRho₃Rho₂TypeA_torusChainTypeD (n : ℕ) :
    (torusChainTypeD R n).typeABoxDifferential (torusRho₃Rho₂TypeA R) = 0 := by
  rw [torusRho₃Rho₂TypeA_eq_threePointTypeA]
  exact typeABoxDifferential_threePointTypeA_eq_zero_of_coord_eq_zero_right
    (oneStrandIdemCoord_torusChainTypeD_coeff R n _)
    (oneStrandChordCoord_one_two_torusChainTypeD_coeff R n)

/-- The box tensor differential of `torusRho₂Rho₁TypeA` with `torusBoundedRho₁₂TypeD` vanishes:
the two paths `y₁ → y₂` and `y₁ → x → y₂` contribute `m₂(y₁, ι₁) = y₁` and `m₃(y₁, ρ₂, ρ₁) = y₁`,
which cancel in characteristic two, and every other path contributes zero. -/
theorem typeABoxDifferential_torusRho₂Rho₁TypeA_torusBoundedRho₁₂TypeD :
    (torusBoundedRho₁₂TypeD R).typeABoxDifferential (torusRho₂Rho₁TypeA R) = 0 := by
  refine LinearMap.ext fun φ ↦ funext fun z ↦ ?_
  rw [typeABoxDifferential_torusBoundedRho₁₂TypeD_apply, torusRho₂Rho₁TypeA_eq_threePointTypeA]
  fin_cases z <;>
    simp [Finset.sum_range_succ, Fintype.sum_finTwoArrow, Fintype.sum_finThreeArrow,
      Fin.sum_univ_three, threePointTypeA_act_one_apply, threePointTypeA_act_add_two_apply,
      Subtype.ext_iff, genusOne_pair_one, CharTwo.add_self_eq_zero]

/-- The box tensor differential of `torusRho₃Rho₂TypeA` with `torusBoundedRho₁₂TypeD` vanishes:
no coefficient of `torusBoundedRho₁₂TypeD` lies along the idempotent `ι₀` of the module, or along
`ρ₃`, which the first input of every higher operation of the module reads. -/
theorem typeABoxDifferential_torusRho₃Rho₂TypeA_torusBoundedRho₁₂TypeD :
    (torusBoundedRho₁₂TypeD R).typeABoxDifferential (torusRho₃Rho₂TypeA R) = 0 := by
  rw [torusRho₃Rho₂TypeA_eq_threePointTypeA]
  exact typeABoxDifferential_threePointTypeA_eq_zero_of_coord_eq_zero_left
    (oneStrandIdemCoord_two_torusBoundedRho₁₂TypeD_coeff R)
    (oneStrandChordCoord_two_three_torusBoundedRho₁₂TypeD_coeff R)

/-- **The pairing of `torusRho₂Rho₁TypeA` with the chain `torusChainTypeD n` has homology of rank
`n + 1`**, the rank of `HF̂` of the lens space `L(n + 1, 1)`. -/
theorem finrank_homology_torusRho₂Rho₁TypeA_torusChainTypeD (n : ℕ) :
    Module.finrank R (LinearMap.homology _
      (TypeDStructure.typeABoxTensorDifferential_comp_self_eq_zero_of_typeABoxDifferential_eq_zero
        (isStrictlyUnital_torusRho₂Rho₁TypeA R)
        (fun _ ↦ matchedSummandDifferential_apply_of_le_one le_rfl _)
        (typeABoxDifferential_torusRho₂Rho₁TypeA_torusChainTypeD R n))) = n + 1 := by
  rw [finrank_homology_threePointTypeA_of_typeABoxDifferential_eq_zero _ _
    (torusRho₂Rho₁TypeA_eq_threePointTypeA R)
    (typeABoxDifferential_torusRho₂Rho₁TypeA_torusChainTypeD R n)]
  -- The generators at `ι₁` are the `γₗ`.
  refine (Fintype.card_congr ((Equiv.subtypeEquivRight fun x ↦ ?_).trans
    (Equiv.optionIsSomeEquiv _))).trans (Fintype.card_fin _)
  rcases x with _ | l <;> simp [Subtype.ext_iff, genusOne_pair_zero, genusOne_pair_one]

/-- **The pairing of `torusRho₃Rho₂TypeA` with the chain `torusChainTypeD n` has homology of rank
`1`**, the rank of `HF̂(S³)`. -/
theorem finrank_homology_torusRho₃Rho₂TypeA_torusChainTypeD (n : ℕ) :
    Module.finrank R (LinearMap.homology _
      (TypeDStructure.typeABoxTensorDifferential_comp_self_eq_zero_of_typeABoxDifferential_eq_zero
        (isStrictlyUnital_torusRho₃Rho₂TypeA R)
        (fun _ ↦ matchedSummandDifferential_apply_of_le_one le_rfl _)
        (typeABoxDifferential_torusRho₃Rho₂TypeA_torusChainTypeD R n))) = 1 := by
  rw [finrank_homology_threePointTypeA_of_typeABoxDifferential_eq_zero _ _
    (torusRho₃Rho₂TypeA_eq_threePointTypeA R)
    (typeABoxDifferential_torusRho₃Rho₂TypeA_torusChainTypeD R n)]
  -- The only generator at `ι₀` is `x`.
  refine (Fintype.card_congr (Equiv.subtypeEquivRight fun x ↦ ?_)).trans
    (Fintype.card_subtype_eq none)
  rcases x with _ | l <;>
    simp [Subtype.ext_iff, genusOne_pair_zero, genusOne_pair_one, genusOne_pair_two]

/-- **The pairing of `torusRho₂Rho₁TypeA` with `torusBoundedRho₁₂TypeD` has homology of rank `2`**,
the rank of `HF̂(S¹ × S²)`. -/
theorem finrank_homology_torusRho₂Rho₁TypeA_torusBoundedRho₁₂TypeD :
    Module.finrank R (LinearMap.homology _
      (TypeDStructure.typeABoxTensorDifferential_comp_self_eq_zero_of_typeABoxDifferential_eq_zero
        (isStrictlyUnital_torusRho₂Rho₁TypeA R)
        (fun _ ↦ matchedSummandDifferential_apply_of_le_one le_rfl _)
        (typeABoxDifferential_torusRho₂Rho₁TypeA_torusBoundedRho₁₂TypeD R))) = 2 := by
  rw [finrank_homology_threePointTypeA_of_typeABoxDifferential_eq_zero _ _
    (torusRho₂Rho₁TypeA_eq_threePointTypeA R)
    (typeABoxDifferential_torusRho₂Rho₁TypeA_torusBoundedRho₁₂TypeD R)]
  -- The generators at `ι₁` are `y₁` and `y₂`.
  refine (Fintype.card_congr (Equiv.subtypeEquivRight fun x ↦ ?_)).trans
    (by decide : Fintype.card {x : Fin 3 // x ≠ 1} = 2)
  fin_cases x <;> simp [Subtype.ext_iff, genusOne_pair_zero, genusOne_pair_one]

/-- **The pairing of `torusRho₃Rho₂TypeA` with `torusBoundedRho₁₂TypeD` has homology of rank `1`**,
the rank of `HF̂(S³)`. -/
theorem finrank_homology_torusRho₃Rho₂TypeA_torusBoundedRho₁₂TypeD :
    Module.finrank R (LinearMap.homology _
      (TypeDStructure.typeABoxTensorDifferential_comp_self_eq_zero_of_typeABoxDifferential_eq_zero
        (isStrictlyUnital_torusRho₃Rho₂TypeA R)
        (fun _ ↦ matchedSummandDifferential_apply_of_le_one le_rfl _)
        (typeABoxDifferential_torusRho₃Rho₂TypeA_torusBoundedRho₁₂TypeD R))) = 1 := by
  rw [finrank_homology_threePointTypeA_of_typeABoxDifferential_eq_zero _ _
    (torusRho₃Rho₂TypeA_eq_threePointTypeA R)
    (typeABoxDifferential_torusRho₃Rho₂TypeA_torusBoundedRho₁₂TypeD R)]
  -- The only generator at `ι₀` is `x`.
  refine (Fintype.card_congr (Equiv.subtypeEquivRight fun x ↦ ?_)).trans
    (Fintype.card_subtype_eq (1 : Fin 3))
  fin_cases x <;> simp [Subtype.ext_iff, genusOne_pair_zero, genusOne_pair_one, genusOne_pair_two]

end Torus

end StrandsAlgebra

end TauCeti
