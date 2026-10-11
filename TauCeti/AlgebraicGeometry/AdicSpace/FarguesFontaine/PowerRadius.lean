/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.GaussPoint
public import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The reciprocal radius parameter of a Gauss point

Write the valuation of a pseudouniformiser as `p ^ (-α)` and the Gauss radius as `p ^ (-r)`,
where `r > 0`. The order-theoretic radius of the resulting Gauss point is `α / r`: its lower
and upper rational radius bounds are exactly the rational bounds on that real number. Thus a
window `a ≤ κ ≤ b` selects the interval `a ≤ α / r ≤ b` in the reciprocal radius parameter.

This is the change of variables used when identifying Frobenius windows with affinoid spectra
of the interval rings `B^I`; it does not assign a real radius to arbitrary higher-rank points.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, Arizona Winter School 2017 notes, §3.1.
* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, §4.
-/

public section

open scoped NNReal

namespace TauCeti.FarguesFontaine

open TauCeti.ValuationSpectrum _root_.WittVector

variable {p : ℕ} [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K]
  [CharP O p] [PerfectRing O p] {v : Valuation K ℝ≥0}

private theorem one_lt_prime_nnreal : (1 : ℝ≥0) < p := by
  exact_mod_cast (Fact.out : p.Prime).one_lt

/-- For `v(ϖ) = p ^ (-α)` and Gauss radius `ρ = p ^ (-r)`, `q` is a lower radius bound of
the Gauss point exactly when `q ≤ α / r`. -/
theorem isRadiusLowerBound_gaussPoint_pPower_iff (hv : v.Integers O) (ϖ : O)
    (r α : ℝ) (hr : 0 < r) (hϖ : v (algebraMap O K ϖ) = (p : ℝ≥0) ^ (-α))
    (q : ℚ≥0) :
    IsRadiusLowerBound p ϖ q
      (gaussPoint p hv ((p : ℝ≥0) ^ (-r))
        (NNReal.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (Fact.out : p.Prime).one_lt) (neg_neg_of_pos hr))) ↔
      (q : ℝ) ≤ α / r := by
  rw [isRadiusLowerBound_gaussPoint_iff, hϖ]
  exact NNReal.rpow_num_den_le_iff one_lt_prime_nnreal r hr α q

/-- For `v(ϖ) = p ^ (-α)` and Gauss radius `ρ = p ^ (-r)`, `q` is an upper radius bound of
the Gauss point exactly when `α / r ≤ q`. -/
theorem isRadiusUpperBound_gaussPoint_pPower_iff (hv : v.Integers O) (ϖ : O)
    (r α : ℝ) (hr : 0 < r) (hϖ : v (algebraMap O K ϖ) = (p : ℝ≥0) ^ (-α))
    (q : ℚ≥0) :
    IsRadiusUpperBound p ϖ q
      (gaussPoint p hv ((p : ℝ≥0) ^ (-r))
        (NNReal.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (Fact.out : p.Prime).one_lt) (neg_neg_of_pos hr))) ↔
      α / r ≤ (q : ℝ) := by
  rw [isRadiusUpperBound_gaussPoint_iff, hϖ]
  exact NNReal.rpow_den_num_le_iff one_lt_prime_nnreal r hr α q

end TauCeti.FarguesFontaine

end
