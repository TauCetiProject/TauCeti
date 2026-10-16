/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Curve

/-!
# Good and multiplicative outputs of Tate's algorithm

These simplification rules evaluate the canonical `WeierstrassCurve.reductionSymbol` directly:
good reduction gives `I₀`, and multiplicative reduction gives `Iₙ` with `n` the local
minimal-discriminant valuation. Positivity in the multiplicative case is recorded by
`WeierstrassCurve.localMinimalDiscriminantValuation_pos_of_hasMultiplicativeReduction`.

## References

* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*,
  LNM 476 (1975).
-/

public section

namespace WeierstrassCurve

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] [PerfectField (IsLocalRing.ResidueField R)]

/-- Tate's canonical output is `I₀` for an equation with good reduction. -/
@[simp]
theorem reductionSymbol_eq_I_zero_of_hasGoodReduction (W : WeierstrassCurve K) [W.IsElliptic]
    [W.HasGoodReduction R] : W.reductionSymbol R = TauCeti.ReductionSymbol.I 0 := by
  exact (reductionSymbol_eq_I_zero_iff W).2
    ((inferInstance : W.HasGoodReduction R).hasGoodReduction_minimal R)

/-- Tate's canonical output at multiplicative reduction has index equal to the
minimal-discriminant valuation. -/
@[simp]
theorem reductionSymbol_eq_I_of_hasMultiplicativeReduction (W : WeierstrassCurve K)
    [W.IsElliptic] [W.HasMultiplicativeReduction R] :
    W.reductionSymbol R = TauCeti.ReductionSymbol.I (W.localMinimalDiscriminantValuation R) := by
  refine (reductionSymbol_eq_I_iff W _).2 ⟨?_, rfl⟩
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal R
  rw [hasAdditiveReduction_iff_of_isMinimal_smul (R := R) C hC]
  exact (inferInstance : W.HasMultiplicativeReduction R).not_hasAdditiveReduction R

end WeierstrassCurve
