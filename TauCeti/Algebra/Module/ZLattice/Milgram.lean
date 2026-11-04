/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Level
public import TauCeti.LinearAlgebra.IntegralLattice.TwoElementary

/-!
# Even lattices of level dividing two

Let `L` be an even full lattice in a finite-dimensional real inner product space `E`, and suppose
that its level divides `2`, that is, `‖x‖²` is an integer for every `x` in the dual lattice `L^∨`.
Then the rank `n` of `L` is divisible by `4`. Equivalently, writing `n = 2k`, the weight `k` of
the theta series of `L` is even.

This is a consequence of Milgram's theorem. The half-norm discriminant form
`q_L(x + L) = ‖x‖² / 2 mod ℤ` takes values in `½ℤ/ℤ`, so every term `e(q_L(γ)) = ±1` of the Gauss
sum `∑_{γ ∈ A_L} e(q_L(γ)) = √|A_L| · e(n/8)` is real, and `e(n/8)` must be `±1`. The proof reads
the statement off the rational model `ZLattice.ratModel L`, where Milgram's theorem is
`TauCeti.IntegralLattice.gaussSign_discriminantQuadraticModule_eq_sigPos_sub_sigNeg`.

The parity of the weight is what matters for modular forms. The central element `-I` of
`SL(2, ℤ)` acts in weight `k` by `(-1)^k` (`ModularForm.slash_neg_one`), and it lies in the
principal congruence subgroup `Γ(N)` exactly when `N ∣ 2`. So `-I` fixes the theta series of the
cosets of `L` in `L^∨` when the level divides `2`. The examples are `D₄`, of level `2` and rank
`4`, and `√2 • E₈`, of level `2` and rank `8`. Neither hypothesis can be dropped: the lattice
`√2 • ℤ²` is even of level `4` and rank `2`, and the odd lattice `ℤ ⊆ ℝ` has level `2` and rank
`1`.

## Main statements

* `ZLattice.IsEven.four_dvd_finrank_of_level_dvd_two`: an even full lattice of level dividing `2`
  has rank divisible by `4`.
* `ZLattice.IsEven.even_of_level_dvd_two`: if moreover the rank is `2k`, then `k` is even.

## References

* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
* W. Ebeling, *Lattices and Codes*, 3rd ed., Chapter 3.
-/

public section

open Module

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- **An even lattice of level dividing `2` has rank divisible by `4`.** -/
theorem IsEven.four_dvd_finrank_of_level_dvd_two (hL : IsEven L) (h2 : level L ∣ 2) :
    4 ∣ finrank ℝ E := by
  have h := (ratModel hL.isIntegral).four_dvd_finrank_of_level_dvd_two
    ((isEven_ratModel_iff hL.isIntegral).mpr hL) (by rwa [level_ratModel])
    (isPosDef_ratModel hL.isIntegral)
  rwa [← (ratModel hL.isIntegral).finrank_carrier, finrank_ratModel] at h

/-- **The weight of an even lattice of level dividing `2` is even**: if the rank is `2k`, then
`k` is even. -/
theorem IsEven.even_of_level_dvd_two (hL : IsEven L) (h2 : level L ∣ 2) {k : ℕ}
    (hk : finrank ℝ E = 2 * k) : Even k := by
  obtain ⟨m, hm⟩ := hL.four_dvd_finrank_of_level_dvd_two h2
  exact ⟨m, by omega⟩

end ZLattice
