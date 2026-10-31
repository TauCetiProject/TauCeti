/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Uniform.Modulus
public import TauCeti.MeasureTheory.Function.Lp.UniformConvex

/-!
# A quantitative modulus of convexity for `Lᵖ`

For `2 ≤ p < ∞`, Clarkson's inequality gives the closed-unit-ball estimate

`δ(ε) ≥ 1 - (2 ^ p - ε ^ p) ^ (1 / p) / 2`, for `0 ≤ ε ≤ 2`.

This is the usual bound `1 - (1 - (ε / 2) ^ p) ^ (1 / p)`, expressed without
moving a scalar through the root. The underlying measure is arbitrary and the target
may be any normed group satisfying the parallelogram identity, including real and
complex Hilbert spaces. Neither completeness nor finiteness of the measure is needed.

## References

* J. A. Clarkson, *Uniformly convex spaces*, Trans. Amer. Math. Soc. 40 (1936), 396–414.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 4.10.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpaceable E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Clarkson's quantitative lower bound for the modulus of convexity of `Lᵖ`,
for `2 ≤ p < ∞` and separation between zero and two. -/
theorem le_modulusOfConvexity (hp : 2 ≤ p) (hp_top : p ≠ ∞) {ε : ℝ}
    (hε : 0 ≤ ε) (hε₂ : ε ≤ 2) :
    1 - (2 ^ p.toReal - ε ^ p.toReal) ^ p.toReal⁻¹ / 2 ≤
      TauCeti.modulusOfConvexity (Lp E p μ) ε := by
  have hq : 2 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
  have hq0 : 0 < p.toReal := by linarith
  have hepow : ε ^ p.toReal ≤ (2 : ℝ) ^ p.toReal :=
    Real.rpow_le_rpow hε hε₂ hq0.le
  apply (TauCeti.le_modulusOfConvexity_iff (Lp E p μ)).2
  refine ⟨sub_le_self _ (div_nonneg (Real.rpow_nonneg (sub_nonneg.2 hepow) _) zero_le_two),
    fun f g hf hg hfg ↦ ?_⟩
  have hclarkson := norm_add_rpow_add_norm_sub_rpow_le hp hp_top f g
  have hf' : ‖f‖ ^ p.toReal ≤ 1 := by
    simpa using Real.rpow_le_rpow (norm_nonneg f) hf hq0.le
  have hg' : ‖g‖ ^ p.toReal ≤ 1 := by
    simpa using Real.rpow_le_rpow (norm_nonneg g) hg hq0.le
  have hsum : 2 ^ (p.toReal - 1) * (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) ≤
      (2 : ℝ) ^ p.toReal := by
    calc
      _ ≤ (2 : ℝ) ^ (p.toReal - 1) * (1 + 1) := by gcongr
      _ = (2 : ℝ) ^ p.toReal := by rw [Real.rpow_sub_one two_ne_zero]; ring
  have hsub : ε ^ p.toReal ≤ ‖f - g‖ ^ p.toReal :=
    Real.rpow_le_rpow hε hfg hq0.le
  have hadd : ‖f + g‖ ^ p.toReal ≤ 2 ^ p.toReal - ε ^ p.toReal := by linarith
  have hroot : ‖f + g‖ ≤ (2 ^ p.toReal - ε ^ p.toReal) ^ p.toReal⁻¹ := by
    calc ‖f + g‖ = (‖f + g‖ ^ p.toReal) ^ p.toReal⁻¹ :=
          (Real.rpow_rpow_inv (norm_nonneg _) hq0.ne').symm
         _ ≤ _ := Real.rpow_le_rpow (by positivity) hadd (inv_nonneg.2 hq0.le)
  linarith

end MeasureTheory.Lp
