/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.DominantMinor
public import TauCeti.Analysis.Normed.Operator.RowCompact.Diagonal
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Diagonal
public import TauCeti.RingTheory.Valuation.NormNormalization
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Exact Fredholm slopes of diagonal operators

Let `K` be a complete ultrametric field whose norm is recovered from a real additive valuation
`v` by `‖x‖ = b ^ (-v x)` with `b > 1`. A diagonal operator `diag (d i)` on `C₀(ℕ, K)` whose
entries have strictly decreasing norms tending to zero satisfies the hypotheses of the exact
dominant-minor criterion: its normalised matrix `(d i)⁻¹ * diag (d i)` is the identity, so all
its principal minors equal one. Its Fredholm slopes are therefore the valuations `v (d i)`, each
of multiplicity one.

For a scalar `π` of valuation `s > 0` and a strictly increasing exponent sequence `e`, the
entries `d i = π ^ e i` give the slopes `s * e i`. This gives the following checks:

* with `v ϖ = 1`, the entries `ϖ ^ i` give each natural number `n` as a slope of multiplicity one;
* with `v ϖ = 1`, the entries `ϖ ^ (2 * i + 1)` give each odd natural number as a slope of
  multiplicity one;
* with `v π = 1 / 2`, for instance in a complete extension containing a square root of `ϖ`, the
  entries `π ^ (2 * i + 1)` give each `n + 1 / 2` as a slope of multiplicity one, while no
  natural number is a slope.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§5 and 7.
-/

public section

open Filter Topology ContinuousLinearMap ZeroAtInftyContinuousMap
open scoped ZeroAtInfty BoundedContinuousFunction

namespace TauCeti.DominantMinorExample

variable {K : Type*} [NontriviallyNormedField K]

/-- For a scalar `π` with `‖π‖ < 1` and exponents `e`, the bounded diagonal entries
`i ↦ π ^ e i` on `ℕ`. -/
noncomputable def powEntries (π : K) (hπ : ‖π‖ < 1) (e : ℕ → ℕ) : ℕ →ᵇ K :=
  .ofNormedAddCommGroupDiscrete (fun i ↦ π ^ e i) 1 fun i ↦ by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hπ.le

@[simp]
theorem powEntries_apply (π : K) (hπ : ‖π‖ < 1) (e : ℕ → ℕ) (i : ℕ) :
    powEntries π hπ e i = π ^ e i := (rfl)

variable [IsUltrametricDist K] [CompleteSpace K] (v : AddValuation K (WithTop ℝ)) {b : ℝ}
  (hb : 1 < b) (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- **Slopes of a diagonal operator.** If the entries of `d` have strictly decreasing norms tending
to zero, the multiplicity of a slope `σ` of the Fredholm series of `diag (d i)` on `C₀(ℕ, K)` is
the number of indices `i` with `v (d i) = σ`. -/
theorem newtonSlopeMultiplicity_diagonalCLM (d : ℕ →ᵇ K) (hdec : StrictAnti fun i ↦ ‖d i‖)
    (hd₀ : Tendsto d atTop (𝓝 0)) (σ : ℝ) :
    (diagonalCLM d).matrixCoeff.charPowerSeries.newtonSlopeMultiplicity v σ =
      {i | v (d i) = σ}.ncard := by
  refine IsRowCompact.newtonSlopeMultiplicity_charPowerSeries_matrixCoeff_eq_ncard v hb hv
    (isRowCompact_diagonalCLM (by rwa [Nat.cofinite_eq_atTop])) hdec (fun i j ↦ ?_)
      (fun n ↦ ?_) σ
  · by_cases hij : i = j
    · subst hij
      simp [matrixCoeff_diagonalCLM]
    · simp [matrixCoeff_diagonalCLM, hij]
  · -- The normalised matrix `(d i)⁻¹ * diag (d i)` has principal minors `∏ (d i)⁻¹ * d i = 1`.
    rw [matrixCoeff_diagonalCLM, Matrix.principalMinor_mul_column, Matrix.principalMinor_diagonal,
      ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun i _ ↦ inv_mul_cancel₀ (TauCeti.ne_zero_of_strictAnti_norm hdec i),
      norm_one]

/-- **Slopes of a diagonal of powers.** For a scalar `π` of valuation `s > 0` and strictly
increasing exponents `e`, the multiplicity of a slope `σ` of the Fredholm series of
`diag (π ^ e i)` is the number of indices `i` with `e i * s = σ`. -/
theorem newtonSlopeMultiplicity_diagonalCLM_powEntries {π : K} {s : ℝ} (hs : 0 < s)
    (hπ : v π = s) {e : ℕ → ℕ} (he : StrictMono e) (σ : ℝ) :
    (diagonalCLM (powEntries π ((v.norm_lt_one_iff hb hv).2 (hπ ▸ WithTop.coe_pos.2 hs)) e)
      ).matrixCoeff.charPowerSeries.newtonSlopeMultiplicity v σ =
      {i | (e i : ℝ) * s = σ}.ncard := by
  have hπ1 := (v.norm_lt_one_iff hb hv).2 (hπ ▸ WithTop.coe_pos.2 hs)
  have hπ0 : 0 < ‖π‖ := norm_pos_iff.2 fun h ↦ by simp [h] at hπ
  rw [newtonSlopeMultiplicity_diagonalCLM v hb hv]
  · congr 1
    ext i
    simp only [powEntries_apply, AddValuation.map_pow, hπ, Set.mem_ofPred_eq, ← WithTop.coe_nsmul,
      nsmul_eq_mul, WithTop.coe_eq_coe]
  · intro i j hij
    simpa only [powEntries_apply, norm_pow] using pow_lt_pow_right_of_lt_one₀ hπ0 hπ1 (he hij)
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [powEntries_apply, norm_pow, Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hπ0.le hπ1).comp he.tendsto_atTop

/-- **Integral slopes.** If `v ϖ = 1`, every natural number `n` is a slope of multiplicity one of
the Fredholm series of `diag (ϖ ^ i)`. -/
theorem newtonSlopeMultiplicity_diagonalCLM_pow_id {ϖ : K} (hϖ : v ϖ = (1 : ℝ)) (n : ℕ) :
    (diagonalCLM (powEntries ϖ ((v.norm_lt_one_iff hb hv).2 (hϖ ▸ WithTop.coe_pos.2 one_pos)) id)
      ).matrixCoeff.charPowerSeries.newtonSlopeMultiplicity v n = 1 := by
  rw [newtonSlopeMultiplicity_diagonalCLM_powEntries v hb hv one_pos hϖ strictMono_id,
    Set.ncard_eq_one]
  refine ⟨n, ?_⟩
  ext i
  simp

/-- **Odd slopes.** If `v ϖ = 1`, every odd natural number `2 * n + 1` is a slope of multiplicity
one of the Fredholm series of `diag (ϖ ^ (2 * i + 1))`. -/
theorem newtonSlopeMultiplicity_diagonalCLM_pow_two_mul_add_one {ϖ : K} (hϖ : v ϖ = (1 : ℝ))
    (n : ℕ) :
    (diagonalCLM (powEntries ϖ ((v.norm_lt_one_iff hb hv).2 (hϖ ▸ WithTop.coe_pos.2 one_pos))
      fun i ↦ 2 * i + 1)).matrixCoeff.charPowerSeries.newtonSlopeMultiplicity v
        (2 * n + 1 : ℕ) = 1 := by
  rw [newtonSlopeMultiplicity_diagonalCLM_powEntries v hb hv one_pos hϖ
    (fun i j hij ↦ by omega), Set.ncard_eq_one]
  refine ⟨n, ?_⟩
  ext i
  simp only [Set.mem_ofPred_eq, mul_one, Nat.cast_inj, Set.mem_singleton_iff]
  omega

/-- **Half-integral slopes.** If `v π = 1 / 2`, every `n + 1 / 2` with `n` a natural number is a
slope of multiplicity one of the Fredholm series of `diag (π ^ (2 * i + 1))`. -/
theorem newtonSlopeMultiplicity_diagonalCLM_pow_two_mul_add_one_add_half {π : K}
    (hπ : v π = (1 / 2 : ℝ)) (n : ℕ) :
    (diagonalCLM (powEntries π ((v.norm_lt_one_iff hb hv).2 (hπ ▸ WithTop.coe_pos.2 one_half_pos))
      fun i ↦ 2 * i + 1)).matrixCoeff.charPowerSeries.newtonSlopeMultiplicity v
        (n + 1 / 2) = 1 := by
  rw [newtonSlopeMultiplicity_diagonalCLM_powEntries v hb hv one_half_pos hπ
    (fun i j hij ↦ by omega), Set.ncard_eq_one]
  refine ⟨n, ?_⟩
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  push_cast
  constructor
  · intro h
    exact_mod_cast (by linarith : (i : ℝ) = n)
  · rintro rfl
    ring

/-- **No integral slopes.** If `v π = 1 / 2`, no natural number is a slope of the Fredholm series
of `diag (π ^ (2 * i + 1))`: its slopes `i + 1 / 2` are all nonintegral. -/
theorem newtonSlopeMultiplicity_diagonalCLM_pow_two_mul_add_one_natCast_eq_zero {π : K}
    (hπ : v π = (1 / 2 : ℝ)) (n : ℕ) :
    (diagonalCLM (powEntries π ((v.norm_lt_one_iff hb hv).2 (hπ ▸ WithTop.coe_pos.2 one_half_pos))
      fun i ↦ 2 * i + 1)).matrixCoeff.charPowerSeries.newtonSlopeMultiplicity v n = 0 := by
  rw [newtonSlopeMultiplicity_diagonalCLM_powEntries v hb hv one_half_pos hπ
    (fun i j hij ↦ by omega)]
  convert Set.ncard_empty ℕ using 2
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  push_cast
  intro h
  -- `2 * i + 1 = 2 * n` is impossible by parity.
  have h' : ((2 * i + 1 : ℕ) : ℝ) = ((2 * n : ℕ) : ℝ) := by
    push_cast
    linarith
  have := Nat.cast_injective h'
  omega

end TauCeti.DominantMinorExample
