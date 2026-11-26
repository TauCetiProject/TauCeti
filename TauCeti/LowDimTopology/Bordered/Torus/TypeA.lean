/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.PointedMatchedCircle
public import TauCeti.LowDimTopology.Bordered.TypeA.OneStrand

/-!
# The solid-torus type `A` modules over the torus algebra

The torus algebra is the summand `matchedSummand R genusOne.pair 1` of the algebra of the genus-one
pointed matched circle, whose points `0, 1, 2, 3` are matched as `{0, 2}` and `{1, 3}`
(`TauCeti.PointedMatchedCircle.genusOne`). Its chords are `ρ₁ = (0 ↦ 1)`, `ρ₂ = (1 ↦ 2)`,
`ρ₃ = (2 ↦ 3)`, `ρ₁₂ = (0 ↦ 2)`, `ρ₂₃ = (1 ↦ 3)` and `ρ₁₂₃ = (0 ↦ 3)`, and its idempotents
are `ι₀ = I({0, 2})` and `ι₁ = I({1, 3})`.

The one-generator type `A` modules of bordered Floer homology for solid tori have a generator `x`
with `m₂(x, ι) = x` for one idempotent `ι` and a single family of higher operations of the shape
`m_{n+3}(x, σ, τ, …, τ, ρ) = x`, where `σ`, `τ` and `ρ` are three chords with `ρ σ = τ`. Over a
ring of characteristic two this file realizes the two such families given by three consecutive
points of the genus-one circle whose outer points are matched, as instances of the module of three
points `TauCeti.StrandsAlgebra.threePointTypeA`:

* `TauCeti.StrandsAlgebra.torusRho₃Rho₂TypeA`, for the points `1 < 2 < 3`, with
  `m₂(x, ι₀) = x` (`TauCeti.StrandsAlgebra.torusRho₃Rho₂TypeA_act_one_oneStrandIdem`) and
  `m_{n+3}(x, ρ₃, ρ₂₃, …, ρ₂₃, ρ₂) = x` (`TauCeti.StrandsAlgebra.torusRho₃Rho₂TypeA_act_cons_snoc`);
* `TauCeti.StrandsAlgebra.torusRho₂Rho₁TypeA`, for the points `0 < 1 < 2`, with
  `m₂(x, ι₁) = x` (`TauCeti.StrandsAlgebra.torusRho₂Rho₁TypeA_act_one_oneStrandIdem`) and
  `m_{n+3}(x, ρ₂, ρ₁₂, …, ρ₁₂, ρ₁) = x` (`TauCeti.StrandsAlgebra.torusRho₂Rho₁TypeA_act_cons_snoc`).

Both are strictly unital for the idempotents. Their remaining operations are those of
`TauCeti.StrandsAlgebra.threePointTypeA`, to which they unfold
(`TauCeti.StrandsAlgebra.torusRho₃Rho₂TypeA_eq_threePointTypeA`,
`TauCeti.StrandsAlgebra.torusRho₂Rho₁TypeA_eq_threePointTypeA`). Identifying them with the Floer
modules of particular framed solid tori, and pairing them with type `D` structures to recover the
genus-one splittings of `S³`, `S¹ × S²` and the lens spaces, are not part of this file.

## Main definitions

* `TauCeti.StrandsAlgebra.torusRho₃Rho₂TypeA`, `TauCeti.StrandsAlgebra.torusRho₂Rho₁TypeA`: the
  two solid-torus type `A` modules.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 11 (bordered manifolds with torus boundary, and the type `A` modules of solid tori).
-/

public section

noncomputable section

namespace TauCeti

namespace StrandsAlgebra

open PointedMatchedCircle

variable (R : Type*) [CommRing R] [CharP R 2]

/-- **The solid-torus type `A` module with `m_{n+3}(x, ρ₃, ρ₂₃, …, ρ₂₃, ρ₂) = x`** over the torus
algebra: the module of the three points `1 < 2 < 3`, of which `1` and `3` are matched. Its
operation `m₂` fixes the generator at the idempotent `ι₀ = I({0, 2})` of the point `2`. -/
def torusRho₃Rho₂TypeA :
    UngradedAInfinityRightModule (matchedSummandDifferential R genusOne.pair 1) R :=
  threePointTypeA R genusOne.pair (by decide : (1 : Fin 4) < 2) (by decide : (2 : Fin 4) < 3)
    (genusOne_pair_one.trans genusOne_pair_three.symm) (by decide)

/-- The module `torusRho₃Rho₂TypeA` is the module of the three points `1 < 2 < 3`. -/
theorem torusRho₃Rho₂TypeA_eq_threePointTypeA :
    torusRho₃Rho₂TypeA R =
      threePointTypeA R genusOne.pair (by decide : (1 : Fin 4) < 2) (by decide : (2 : Fin 4) < 3)
        (genusOne_pair_one.trans genusOne_pair_three.symm) (by decide) :=
  (rfl)

/-- `m₂(x, ι₀) = x`: the idempotent `ι₀ = I({0, 2})` of the point `2` fixes the generator. -/
theorem torusRho₃Rho₂TypeA_act_one_oneStrandIdem (x : R) :
    (torusRho₃Rho₂TypeA R).act 1
      (fun _ ↦ oneStrandIdem R genusOne.pair ⟨genusOne.pair 2, 2, rfl⟩) x = x := by
  rw [torusRho₃Rho₂TypeA_eq_threePointTypeA, threePointTypeA_act_one_oneStrandIdem, ite_eq_left rfl]

/-- `m_{n+3}(x, ρ₃, ρ₂₃, …, ρ₂₃, ρ₂) = x`, with `n` copies of `ρ₂₃`. -/
theorem torusRho₃Rho₂TypeA_act_cons_snoc (n : ℕ) (x : R) :
    (torusRho₃Rho₂TypeA R).act (n + 2)
        (Fin.cons (oneStrandChord R genusOne.pair (by decide : (2 : Fin 4) < 3))
          (Fin.snoc (fun _ : Fin n ↦ oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 3))
            (oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 2)))) x = x :=
  threePointTypeA_act_cons_snoc _ _ n x

/-- `torusRho₃Rho₂TypeA` is strictly unital: its operations `m_{n+1}`, `n ≥ 2`, vanish as soon as
one input is an idempotent `I({p})`. -/
theorem isStrictlyUnital_torusRho₃Rho₂TypeA :
    (torusRho₃Rho₂TypeA R).IsStrictlyUnital (oneStrandIdem R genusOne.pair) :=
  isStrictlyUnital_threePointTypeA _ _

/-- **The solid-torus type `A` module with `m_{n+3}(x, ρ₂, ρ₁₂, …, ρ₁₂, ρ₁) = x`** over the torus
algebra: the module of the three points `0 < 1 < 2`, of which `0` and `2` are matched. Its
operation `m₂` fixes the generator at the idempotent `ι₁ = I({1, 3})` of the point `1`. -/
def torusRho₂Rho₁TypeA :
    UngradedAInfinityRightModule (matchedSummandDifferential R genusOne.pair 1) R :=
  threePointTypeA R genusOne.pair (by decide : (0 : Fin 4) < 1) (by decide : (1 : Fin 4) < 2)
    (genusOne_pair_zero.trans genusOne_pair_two.symm) (by decide)

/-- The module `torusRho₂Rho₁TypeA` is the module of the three points `0 < 1 < 2`. -/
theorem torusRho₂Rho₁TypeA_eq_threePointTypeA :
    torusRho₂Rho₁TypeA R =
      threePointTypeA R genusOne.pair (by decide : (0 : Fin 4) < 1) (by decide : (1 : Fin 4) < 2)
        (genusOne_pair_zero.trans genusOne_pair_two.symm) (by decide) :=
  (rfl)

/-- `m₂(x, ι₁) = x`: the idempotent `ι₁ = I({1, 3})` of the point `1` fixes the generator. -/
theorem torusRho₂Rho₁TypeA_act_one_oneStrandIdem (x : R) :
    (torusRho₂Rho₁TypeA R).act 1
      (fun _ ↦ oneStrandIdem R genusOne.pair ⟨genusOne.pair 1, 1, rfl⟩) x = x := by
  rw [torusRho₂Rho₁TypeA_eq_threePointTypeA, threePointTypeA_act_one_oneStrandIdem, ite_eq_left rfl]

/-- `m_{n+3}(x, ρ₂, ρ₁₂, …, ρ₁₂, ρ₁) = x`, with `n` copies of `ρ₁₂`. -/
theorem torusRho₂Rho₁TypeA_act_cons_snoc (n : ℕ) (x : R) :
    (torusRho₂Rho₁TypeA R).act (n + 2)
        (Fin.cons (oneStrandChord R genusOne.pair (by decide : (1 : Fin 4) < 2))
          (Fin.snoc (fun _ : Fin n ↦ oneStrandChord R genusOne.pair (by decide : (0 : Fin 4) < 2))
            (oneStrandChord R genusOne.pair (by decide : (0 : Fin 4) < 1)))) x = x :=
  threePointTypeA_act_cons_snoc _ _ n x

/-- `torusRho₂Rho₁TypeA` is strictly unital: its operations `m_{n+1}`, `n ≥ 2`, vanish as soon as
one input is an idempotent `I({p})`. -/
theorem isStrictlyUnital_torusRho₂Rho₁TypeA :
    (torusRho₂Rho₁TypeA R).IsStrictlyUnital (oneStrandIdem R genusOne.pair) :=
  isStrictlyUnital_threePointTypeA _ _

end StrandsAlgebra

end TauCeti
