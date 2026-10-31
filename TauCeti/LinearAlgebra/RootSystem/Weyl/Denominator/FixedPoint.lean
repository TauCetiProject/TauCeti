/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Denominator.WeylGroup
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Numerator
public import Mathlib.Algebra.BigOperators.Field

/-!
# The fixed-point sum of a Weyl numerator

The Weyl character formula has two classical rational forms. The normalized one is
`N(λ) / Δ`, with `N(λ) = ∑_{w ∈ W} sgn(w) e^{w(λ + ρ) - ρ}` the Weyl numerator and
`Δ = ∏_{α > 0} (1 - e^{-α})` the Weyl denominator. The fixed-point one, the shape of the
Atiyah–Bott localization of the character to the fixed points of the torus on the flag variety,
is

`∑_{w ∈ W} e^{w λ} / ∏_{α > 0} (1 - e^{-w α})`.

This file proves that the two agree. Both sides are quotients, so the identity is stated after a
ring homomorphism `f : ℤ[M] →+* F` into a field under which `Δ` does not vanish. Taking for `f`
the inclusion of `ℤ[M]` into a fraction field gives the identity of rational functions; taking for
`f` the evaluation of the exponentials at a point of a torus gives the identity of values at every
regular point.

Each `w` contributes exactly one normalized term: the denominator `∏_{α > 0} (1 - e^{-w α})` is
the image `w Δ` of `Δ` under `w` (`RootPairing.mapDomain_smul_weylDenominator_eq_prod`), and
`e^{w λ} Δ = sgn(w) e^{w ⬝ λ} (w Δ)` (`TauCeti.single_smul_mul_weylDenominator`), so the sign and
the shift `ρ - w ρ` that every inverted factor `1 - e^{β} = -e^{β} (1 - e^{-β})` produces are
absorbed into the dot action. In particular `w Δ` does not vanish when `Δ` does not
(`RootPairing.map_mapDomain_smul_weylDenominator_ne_zero`): it is `Δ` times a signed exponential.

## Main results

* `RootPairing.map_single_div_map_mapDomain_smul_weylDenominator`: the fixed-point term of `w`
  is its normalized term, `f(e^{w λ}) / f(w Δ) = sgn(w) f(e^{w ⬝ λ}) / f(Δ)`.
* `RootPairing.sum_map_single_div_prod_eq_map_weylNumerator_div`: **the fixed-point sum is the
  normalized quotient**,
  `∑_{w ∈ W} f(e^{w λ}) / ∏_{α > 0} (1 - f(e^{-w α})) = f(N(λ)) / f(Δ)`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6, Ch. VI, §3.
* M. F. Atiyah, R. Bott, *A Lefschetz fixed point formula for elliptic complexes. II.
  Applications*, Ann. of Math. 88 (1968), 451–491, where the Weyl character formula is the
  holomorphic Lefschetz fixed-point formula on the flag variety.
-/

public section

namespace RootPairing

open TauCeti

universe u v w x y

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] (b : P.Base)

variable {F : Type y} [Field F] (f : AddMonoidAlgebra ℤ M →+* F)

variable [IsDomain R] [P.IsCrystallographic] [P.IsReduced] [Invertible (2 : R)]

/-- **The fixed-point term of `w` is its normalized term**:
`f(e^{w λ}) / f(w Δ) = sgn(w) f(e^{w ⬝ λ}) / f(Δ)` when `f Δ ≠ 0`. -/
theorem map_single_div_map_mapDomain_smul_weylDenominator (hf : f (weylDenominator P b) ≠ 0)
    (w : P.weylGroup) (lam : M) :
    f (AddMonoidAlgebra.single (w • lam) 1) /
        f (AddMonoidAlgebra.mapDomain (w • ·) (weylDenominator P b)) =
      f (AddMonoidAlgebra.single (dotAction P b w lam) (weylSign P b w : ℤ)) /
        f (weylDenominator P b) := by
  rw [div_eq_div_iff (map_mapDomain_smul_weylDenominator_ne_zero P b f hf w) hf, ← map_mul,
    ← map_mul, single_smul_mul_weylDenominator, ← smul_mul_assoc, AddMonoidAlgebra.smul_single',
    mul_one]

/-- **The fixed-point form of the Weyl numerator**: for a ring homomorphism `f : ℤ[M] →+* F` into a
field with `f Δ ≠ 0`,

`∑_{w ∈ W} f(e^{w λ}) / ∏_{α > 0} (1 - f(e^{-w α})) = f(N(λ)) / f(Δ)`.

Every denominator on the left is nonzero, and the `w`-th summand is `sgn(w) f(e^{w ⬝ λ}) / f(Δ)`,
the `w`-th term of the Weyl numerator over the Weyl denominator. -/
theorem sum_map_single_div_prod_eq_map_weylNumerator_div [Fintype P.weylGroup]
    (hf : f (weylDenominator P b) ≠ 0) (lam : M) :
    ∑ w : P.weylGroup, f (AddMonoidAlgebra.single (w • lam) 1) /
        ∏ i ∈ posRootsFinset P b, (1 - f (AddMonoidAlgebra.single (-(w • P.root i)) 1)) =
      f (weylNumerator P b lam) / f (weylDenominator P b) := by
  rw [weylNumerator_def, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hden : ∏ i ∈ posRootsFinset P b, (1 - f (AddMonoidAlgebra.single (-(w • P.root i)) 1)) =
      f (AddMonoidAlgebra.mapDomain (w • ·) (weylDenominator P b)) := by
    simp [mapDomain_smul_weylDenominator_eq_prod, map_prod]
  rw [hden, map_single_div_map_mapDomain_smul_weylDenominator P b f hf]

end RootPairing
