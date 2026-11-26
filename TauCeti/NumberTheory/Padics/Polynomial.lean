/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Monoid

/-!
# Integral polynomials are dense among polynomials over `ℤ_ℓ`

The natural numbers are dense in `ℤ_ℓ`, so a polynomial `G ∈ ℤ_ℓ[X]` is the coefficientwise
limit of integral polynomials `F_N ∈ ℤ[X]`. Consequently, at every point `r` of a normed
`ℚ_ℓ`-algebra, the values `F_N(r)` converge to `G(r)`. This lets an identity between continuous
functions of the values of test polynomials pass from integral test polynomials to `ℓ`-adic ones.

## Main results

* `Polynomial.exists_seq_int_tendsto_aeval_map_coe`: a polynomial over `ℤ_ℓ` is the pointwise
  limit, on every normed `ℚ_ℓ`-algebra, of a sequence of integral polynomials.
-/

public section

open Filter Topology

namespace Polynomial

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- A polynomial `G` with coefficients in `ℤ_ℓ` is the coefficientwise limit of integral
polynomials, so its values at every point of a normed `ℚ_ℓ`-algebra `L` are limits of values of
integral polynomials. -/
theorem exists_seq_int_tendsto_aeval_map_coe {L : Type*} [SeminormedRing L]
    [NormedAlgebra ℚ_[ℓ] L] (G : ℤ_[ℓ][X]) :
    ∃ F : ℕ → ℤ[X], ∀ r : L,
      Tendsto (fun N ↦ aeval r (F N)) atTop (𝓝 (aeval r (G.map PadicInt.Coe.ringHom))) := by
  -- Natural numbers approximate the coefficients of `G` to precision `1 / (N + 1)`.
  have happr (N i : ℕ) : ∃ n : ℕ, dist (G.coeff i) n < 1 / (N + 1) :=
    PadicInt.denseRange_natCast.exists_dist_lt (G.coeff i) Nat.one_div_pos_of_nat
  choose z hz using happr
  refine ⟨fun N ↦ ∑ i ∈ Finset.range (G.natDegree + 1), C (z N i : ℤ) * X ^ i, fun r ↦ ?_⟩
  rw [aeval_eq_sum_range' (natDegree_map_le.trans_lt G.natDegree.lt_succ_self)]
  simp only [map_sum]
  refine tendsto_finsetSum _ fun i _ ↦ ?_
  have hc : Tendsto (fun N ↦ (z N i : ℤ_[ℓ])) atTop (𝓝 (G.coeff i)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun N ↦ ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_comm]
    exact (hz N i).le
  have hcL : Tendsto (fun N ↦ algebraMap ℚ_[ℓ] L ((z N i : ℤ_[ℓ]) : ℚ_[ℓ])) atTop
      (𝓝 (algebraMap ℚ_[ℓ] L (G.coeff i))) :=
    ((continuous_algebraMap ℚ_[ℓ] L).tendsto _).comp ((continuous_subtypeVal.tendsto _).comp hc)
  simpa [Algebra.smul_def, coeff_map] using hcL.mul_const (r ^ i)

end Polynomial
