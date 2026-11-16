/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.PointedMatchedCircle
public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.StrandCount

/-!
# The torus algebra

The genus-one pointed matched circle `Z` has four points, written `0, 1, 2, 3` here and
`1, 2, 3, 4` by Lipshitz, Ozsváth and Thurston, matched as `{0, 2}` and `{1, 3}`
(`TauCeti.PointedMatchedCircle.genusOne`). Its algebra `A(Z)` is the matched subalgebra of the
strands algebra `A(4)` for the matching `Z.pair`, and the summand `A(Z, 0)` with one strand is the
**torus algebra**. By the basis of the one-strand part of a matched subalgebra
(`TauCeti.StrandsAlgebra.oneStrandBasis`), it has the basis consisting of the idempotents
`ι₀ = I({0}) + I({2})` and `ι₁ = I({1}) + I({3})` of the two pairs and the single strands of the
six chords, `ρ₁ = (0 ↦ 1)`, `ρ₂ = (1 ↦ 2)`, `ρ₃ = (2 ↦ 3)`, `ρ₁₂ = (0 ↦ 2)`, `ρ₂₃ = (1 ↦ 3)`
and `ρ₁₂₃ = (0 ↦ 3)`, so it is eight-dimensional (`TauCeti.StrandsAlgebra.finrank_genusOne`).

Two chords multiply to their concatenation when the first ends where the second starts, and to zero
otherwise: `ρ₁ ρ₂ = ρ₁₂` but `ρ₂ ρ₁ = 0`, since `ρ₂` ends at `2`, where `ρ₁` does not start. A
single strand has no crossing, so the differential vanishes on the torus algebra. These are
checked below.

As elements of the summand `matchedSummand R genusOne.pair 1`, the idempotents are
`TauCeti.StrandsAlgebra.oneStrandIdem R genusOne.pair p` and the chords are
`TauCeti.StrandsAlgebra.oneStrandChord R genusOne.pair h`.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.2 (the
  genus-one pointed matched circle and its algebra).
-/

public section

namespace TauCeti

namespace StrandsAlgebra

open StrandDiagram PointedMatchedCircle

/-- **The torus algebra is eight-dimensional**: the one-strand part of the algebra of the genus-one
pointed matched circle has a basis of two idempotents and six chords. -/
theorem finrank_genusOne (R : Type*) [CommSemiring R] [StrongRankCondition R] :
    Module.finrank R ((matchedSubalgebra R genusOne.pair).toSubmodule ⊓ strandCountPart R 1 :
      Submodule R (StrandsAlgebra R (Fin 4))) = 8 := by
  have hpair : genusOne.pair = ![s(0, 2), s(1, 3), s(0, 2), s(1, 3)] := by
    funext i
    fin_cases i <;> rw [pair_def, genusOne_matching] <;> decide
  have h₁ : Fintype.card (Set.range genusOne.pair) = 2 := by
    rw [← Set.toFinset_card, Set.toFinset_range, hpair]
    decide
  have h₂ : Fintype.card {p : Fin 4 × Fin 4 // p.1 < p.2} = 6 := by
    decide
  rw [finrank_oneStrand, h₁, h₂]

end StrandsAlgebra

end TauCeti

open TauCeti StrandsAlgebra StrandDiagram

/-! ### Products and the differential in the torus algebra -/

/-- `ρ₁ ρ₂ = ρ₁₂`. -/
example :
    (of (single 0 1 (by decide)) * of (single 1 2 (by decide)) :
      StrandsAlgebra (ZMod 2) (Fin 4)) = of (single 0 2 (by decide)) :=
  of_single_mul_of_single _ _

/-- `ρ₂ ρ₁ = 0`: `ρ₂` ends at `2`, where `ρ₁` does not start. -/
example :
    (of (single 1 2 (by decide)) * of (single 0 1 (by decide)) :
      StrandsAlgebra (ZMod 2) (Fin 4)) = 0 :=
  of_single_mul_of_single_of_ne _ _ (by decide)

/-- `ρ₁₂ ρ₃ = ρ₁ ρ₂₃ = ρ₁₂₃`. -/
example :
    (of (single 0 2 (by decide)) * of (single 2 3 (by decide)) :
      StrandsAlgebra (ZMod 2) (Fin 4)) = of (single 0 1 (by decide)) * of (single 1 3 (by decide)) ∧
    (of (single 0 1 (by decide)) * of (single 1 3 (by decide)) :
      StrandsAlgebra (ZMod 2) (Fin 4)) = of (single 0 3 (by decide)) := by
  simp

/-- The differential vanishes on the torus algebra. -/
example (x : StrandsAlgebra (ZMod 2) (Fin 4))
    (hx : x ∈ (matchedSubalgebra (ZMod 2) PointedMatchedCircle.genusOne.pair).toSubmodule ⊓
      strandCountPart (ZMod 2) 1) :
    differential (ZMod 2) (Fin 4) x = 0 :=
  differential_eq_zero_of_mem_strandCountPart le_rfl hx.2
