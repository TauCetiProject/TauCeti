/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Lebesgue
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.PosDef
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Instances.Matrix

/-!
# Divergence of the Wishart cone integral off the positive-definite cone

For a positive-definite weight matrix `B` and `(p - 1) / 2 < a`, the integral of
`(det A) ^ (a - (p + 1) / 2) * exp (-trace (B * A))` over the cone of positive-definite symmetric
`p × p` matrices is finite; for `B = 1` its value is the multivariate Gamma function
(`TauCeti.integral_posDef_multivariateGamma`). This file proves the converse: when the symmetric
weight `B` is not positive definite, the integral is infinite, and the integrand is not
integrable on the cone.

Together the two statements give the exact domain on which a trace statistic of a Wishart density
has finite exponential moments: tilting the density `exp (-trace (S⁻¹ * A) / 2)` by
`exp (t * trace (Θ * A))` produces the weight `B = S⁻¹ / 2 - t • Θ`, and the moment is finite
exactly when that weight is positive definite.

The proof uses a direction `v` with `v ⬝ᵥ B *ᵥ v ≤ 0`, along which the weight does not decay.
Translating a small closed ball `K` inside the cone by the multiples `k • v vᵀ`, `k : ℕ`, gives
pairwise disjoint subsets of the cone, since adding a positive-semidefinite matrix preserves
positive definiteness. By translation invariance of `TauCeti.symmetricLebesgue`, the integral over
the `k`-th translate is the integral over `K` of the translated integrand. On `K` the exponential
factor stays bounded below, because
`trace (B * (A + k • v vᵀ)) = trace (B * A) + k * (v ⬝ᵥ B *ᵥ v)`, and the determinant
`det A * (1 + k * (v ⬝ᵥ A⁻¹ *ᵥ v))` grows at most linearly in `k`. Since the exponent
`a - (p + 1) / 2` is at least `-1`, the translates contribute a multiple of the harmonic series.

## Main results

* `TauCeti.lintegral_posDef_det_rpow_mul_exp_neg_trace_mul_eq_top_of_dotProduct_mulVec_nonpos` —
  the integral is infinite as soon as some nonzero `v` has `v ⬝ᵥ B *ᵥ v ≤ 0`;
* `TauCeti.lintegral_posDef_det_rpow_mul_exp_neg_trace_mul_eq_top` — the integral is infinite for
  every symmetric weight that is not positive definite;
* `TauCeti.not_integrableOn_posDef_det_rpow_mul_exp_neg_trace_mul` — the corresponding
  non-integrability statement.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, Section 2.1 and
  Theorem 3.2.3.
-/

public section

noncomputable section

open MeasureTheory Real

open scoped Matrix

namespace TauCeti

variable {p : ℕ} {a : ℝ} {B : Matrix (Fin p) (Fin p) ℝ}

/-- The disjoint-translates lower bound: if the closed ball `K` of radius `r` lies in the cone and
`E` is a positive-semidefinite symmetric matrix of norm at least `3 * r`, then the translates
`k • E + K` are pairwise disjoint subsets of the cone, and the integrals of `g` over them add up
to at most the integral of `g` over the cone. -/
private theorem tsum_setLIntegral_add_smul_le {g : selfAdjoint.submodule ℝ
      (Matrix (Fin p) (Fin p) ℝ) → ENNReal} (hg : Measurable g)
    {E A₀ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)}
    (hE : (E : Matrix (Fin p) (Fin p) ℝ).PosSemidef) {r : ℝ} (hrE : 3 * r ≤ ‖E‖)
    (hK : Metric.closedBall A₀ r ⊆ {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef}) (hE0 : E ≠ 0) :
    ∑' k : ℕ, ∫⁻ A in Metric.closedBall A₀ r, g ((k : ℝ) • E + A) ∂symmetricLebesgue p ≤
      ∫⁻ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef}, g A ∂symmetricLebesgue p := by
  set S : ℕ → Set (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
    fun k => (fun A => -((k : ℝ) • E) + A) ⁻¹' Metric.closedBall A₀ r with hS
  have hSm : ∀ k, MeasurableSet (S k) := fun k =>
    (Metric.isClosed_closedBall.preimage (continuous_const.add continuous_id)).measurableSet
  have hSdisj : Pairwise (Function.onFun Disjoint S) := by
    intro k l hkl
    refine Set.disjoint_left.2 fun A hk hl => ?_
    have hk' : dist (-((k : ℝ) • E) + A) A₀ ≤ r := hk
    have hl' : dist (-((l : ℝ) • E) + A) A₀ ≤ r := hl
    -- Two points of `K` differ by a nonzero integer multiple of `E`, which is too long.
    have hdist : dist (-((k : ℝ) • E) + A) (-((l : ℝ) • E) + A) = |(k : ℝ) - l| * ‖E‖ := by
      rw [dist_add_right, dist_eq_norm, neg_sub_neg, ← sub_smul, norm_smul, Real.norm_eq_abs,
        abs_sub_comm]
    have h1 : 1 ≤ |(k : ℝ) - l| := by
      have hklz : (k : ℤ) ≠ l := by exact_mod_cast hkl
      have h := Int.one_le_abs (sub_ne_zero.2 hklz)
      exact_mod_cast h
    have htri := dist_triangle_right (-((k : ℝ) • E) + A) (-((l : ℝ) • E) + A) A₀
    have hEpos : 0 < ‖E‖ := norm_pos_iff.2 hE0
    nlinarith
  have hSP : (⋃ k, S k) ⊆ {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
    refine Set.iUnion_subset fun k A hA => ?_
    have hA' : ((-((k : ℝ) • E) + A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ).PosDef := hK hA
    have hcoe : (A : Matrix (Fin p) (Fin p) ℝ) =
        ((-((k : ℝ) • E) + A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
          Matrix (Fin p) (Fin p) ℝ) + (k : ℝ) • (E : Matrix (Fin p) (Fin p) ℝ) := by
      simp
    rw [Set.mem_ofPred_eq, hcoe]
    exact hA'.add_posSemidef (hE.smul (Nat.cast_nonneg k))
  calc ∑' k : ℕ, ∫⁻ A in Metric.closedBall A₀ r, g ((k : ℝ) • E + A) ∂symmetricLebesgue p
      = ∑' k : ℕ, ∫⁻ A in S k, g A ∂symmetricLebesgue p := by
        refine tsum_congr fun k => ?_
        have hpre : (fun A => (k : ℝ) • E + A) ⁻¹' S k = Metric.closedBall A₀ r := by
          ext A
          simp [hS]
        rw [← (measurePreserving_add_left (symmetricLebesgue p)
          ((k : ℝ) • E)).setLIntegral_comp_preimage (hSm k) hg, hpre]
    _ = ∫⁻ A in ⋃ k, S k, g A ∂symmetricLebesgue p := (lintegral_iUnion hSm hSdisj g).symm
    _ ≤ _ := lintegral_mono_set hSP

/-- The scalar estimate behind the divergence: if `d₁ ≤ d ≤ D`, `0 ≤ w ≤ c` and `-1 ≤ e`, then
`(d * (1 + k * w)) ^ e` is at least a fixed positive multiple of `(k + 1)⁻¹`. -/
private theorem min_rpow_mul_inv_le_rpow {d₁ d D w c e : ℝ} (hd₁ : 0 < d₁) (hd₁d : d₁ ≤ d)
    (hdD : d ≤ D) (hw : 0 ≤ w) (hwc : w ≤ c) (he : -1 ≤ e) (k : ℕ) :
    min (d₁ ^ e) ((D * (1 + c)) ^ e) * ((k : ℝ) + 1)⁻¹ ≤ (d * (1 + k * w)) ^ e := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlo : d₁ ≤ d * (1 + k * w) :=
    hd₁d.trans (le_mul_of_one_le_right (hd₁.le.trans hd₁d) (by nlinarith))
  have hhi : d * (1 + k * w) ≤ D * (1 + c) * (k + 1) := by
    have h1 : 1 + k * w ≤ (1 + c) * (k + 1) := by nlinarith
    calc d * (1 + k * w) ≤ D * (1 + k * w) := mul_le_mul_of_nonneg_right hdD (by positivity)
      _ ≤ D * ((1 + c) * (k + 1)) := by gcongr; linarith
      _ = D * (1 + c) * (k + 1) := by ring
  rcases le_total 0 e with he0 | he0
  · calc min (d₁ ^ e) ((D * (1 + c)) ^ e) * ((k : ℝ) + 1)⁻¹ ≤ d₁ ^ e :=
          (mul_le_of_le_one_right (le_min (Real.rpow_nonneg hd₁.le _) (Real.rpow_nonneg
            (by nlinarith) _)) (inv_le_one_of_one_le₀ (by linarith))).trans (min_le_left _ _)
      _ ≤ (d * (1 + k * w)) ^ e := Real.rpow_le_rpow hd₁.le hlo he0
  · have hD1 : 0 ≤ D * (1 + c) := by nlinarith
    calc min (d₁ ^ e) ((D * (1 + c)) ^ e) * ((k : ℝ) + 1)⁻¹
        ≤ (D * (1 + c)) ^ e * ((k : ℝ) + 1) ^ e := by
          refine mul_le_mul (min_le_right _ _) ?_ (by positivity) (Real.rpow_nonneg hD1 _)
          rw [← Real.rpow_neg_one]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) he
      _ = (D * (1 + c) * (k + 1)) ^ e := (Real.mul_rpow hD1 (by linarith)).symm
      _ ≤ (d * (1 + k * w)) ^ e := Real.rpow_le_rpow_of_nonpos (hd₁.trans_le hlo) hhi he0

/-- The estimate on one translate: for a positive-definite `A` whose determinant, inverse
quadratic form `v ⬝ᵥ A⁻¹ *ᵥ v` and trace pairing with `B` obey the given bounds, the integrand at
`A + k • v vᵀ` is at least a fixed positive multiple of `(k + 1)⁻¹`, provided
`v ⬝ᵥ B *ᵥ v ≤ 0`. -/
private theorem mul_exp_neg_mul_inv_le_det_rpow_mul_exp_neg_trace
    {A : Matrix (Fin p) (Fin p) ℝ} (hA : A.PosDef) {v : Fin p → ℝ} (hvB : v ⬝ᵥ B *ᵥ v ≤ 0)
    {d₁ D c τ e : ℝ} (hd₁ : 0 < d₁) (hd₁A : d₁ ≤ A.det) (hAD : A.det ≤ D)
    (hwc : v ⬝ᵥ A⁻¹ *ᵥ v ≤ c) (hτ : (B * A).trace ≤ τ) (he : -1 ≤ e) (k : ℕ) :
    min (d₁ ^ e) ((D * (1 + c)) ^ e) * exp (-τ) * ((k : ℝ) + 1)⁻¹ ≤
      (A + (k : ℝ) • Matrix.vecMulVec v v).det ^ e *
        exp (-(B * (A + (k : ℝ) • Matrix.vecMulVec v v)).trace) := by
  have hw0 : 0 ≤ v ⬝ᵥ A⁻¹ *ᵥ v := by simpa using hA.inv.posSemidef.dotProduct_mulVec_nonneg v
  have hdet : (A + (k : ℝ) • Matrix.vecMulVec v v).det = A.det * (1 + k * (v ⬝ᵥ A⁻¹ *ᵥ v)) := by
    rw [← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq Unit,
      Matrix.det_add_replicateCol_mul_replicateRow hA.det_pos.ne'.isUnit, Matrix.mul_assoc,
      ← Matrix.replicateCol_mulVec, Matrix.det_unique (1 + _)]
    simp [Matrix.mulVec_smul, smul_eq_mul]
  have htr : (B * (A + (k : ℝ) • Matrix.vecMulVec v v)).trace =
      (B * A).trace + k * (v ⬝ᵥ B *ᵥ v) := by
    rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  rw [hdet, htr]
  have hexp : exp (-τ) ≤ exp (-((B * A).trace + k * (v ⬝ᵥ B *ᵥ v))) :=
    exp_le_exp.2 (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  calc min (d₁ ^ e) ((D * (1 + c)) ^ e) * exp (-τ) * ((k : ℝ) + 1)⁻¹
      = (min (d₁ ^ e) ((D * (1 + c)) ^ e) * ((k : ℝ) + 1)⁻¹) * exp (-τ) := by ring
    _ ≤ _ := mul_le_mul (min_rpow_mul_inv_le_rpow hd₁ hd₁A hAD hw0 hwc he k) hexp (exp_pos _).le
        (Real.rpow_nonneg (mul_nonneg hA.det_pos.le (by positivity)) _)

/-- A closed ball inside the positive-definite cone, of radius `r` with `3 * r ≤ δ`, on which the
determinant is pinched between two positive constants and the inverse quadratic form
`v ⬝ᵥ A⁻¹ *ᵥ v` and the trace pairing with `B` are bounded above. -/
private theorem exists_closedBall_subset_posDef_bounds (B : Matrix (Fin p) (Fin p) ℝ)
    (v : Fin p → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (A₀ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (r : ℝ), 0 < r ∧ 3 * r ≤ δ ∧
      Metric.closedBall A₀ r ⊆ {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef} ∧
      ∃ d₁ D c τ : ℝ, 0 < d₁ ∧ ∀ A ∈ Metric.closedBall A₀ r,
        d₁ ≤ (A : Matrix (Fin p) (Fin p) ℝ).det ∧ (A : Matrix (Fin p) (Fin p) ℝ).det ≤ D ∧
          v ⬝ᵥ (A : Matrix (Fin p) (Fin p) ℝ)⁻¹ *ᵥ v ≤ c ∧
            (B * (A : Matrix (Fin p) (Fin p) ℝ)).trace ≤ τ := by
  let A₀ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
    ⟨1, Matrix.isHermitian_iff_isSelfAdjoint.1 Matrix.isHermitian_one⟩
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.1 (isOpen_setOfPred_posDefMatrix p) A₀ Matrix.PosDef.one
  set r := min (ε / 2) (δ / 3)
  have hr0 : 0 < r := lt_min (half_pos hε) (by positivity)
  set K := Metric.closedBall A₀ r
  have hKP : K ⊆ {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef} :=
    (Metric.closedBall_subset_ball (by linarith [min_le_left (ε / 2) (δ / 3)])).trans hball
  have hKP' : ∀ A ∈ K, (A : Matrix (Fin p) (Fin p) ℝ).PosDef := fun A hA => hKP hA
  have hKc : IsCompact K := isCompact_closedBall A₀ r
  -- Each quantity is continuous on the compact set `K`, the inverse because `K` lies in the cone.
  have hdet : Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (A : Matrix (Fin p) (Fin p) ℝ).det := continuous_subtype_val.matrix_det
  obtain ⟨A₁, hA₁K, hA₁min⟩ :=
    hKc.exists_isMinOn (Metric.nonempty_closedBall.2 hr0.le) hdet.continuousOn
  obtain ⟨D, hD⟩ := hKc.exists_bound_of_continuousOn hdet.continuousOn
  have hw : ContinuousOn (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      v ⬝ᵥ (A : Matrix (Fin p) (Fin p) ℝ)⁻¹ *ᵥ v) K := by
    intro A hA
    have hu : IsUnit (A : Matrix (Fin p) (Fin p) ℝ).det := (hKP' A hA).det_pos.ne'.isUnit
    have hinv : ContinuousAt (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (A : Matrix (Fin p) (Fin p) ℝ)⁻¹) A :=
      (continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt hu.unit)).comp
        continuous_subtype_val.continuousAt
    exact ((continuous_const.dotProduct
      (continuous_id.matrix_mulVec continuous_const)).continuousAt.comp hinv).continuousWithinAt
  obtain ⟨c, hc⟩ := hKc.exists_bound_of_continuousOn hw
  obtain ⟨τ, hτ⟩ := hKc.exists_bound_of_continuousOn
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace.continuousOn :
      ContinuousOn (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (B * (A : Matrix (Fin p) (Fin p) ℝ)).trace) K)
  exact ⟨A₀, r, hr0, by linarith [min_le_right (ε / 2) (δ / 3)], hKP,
    (A₁ : Matrix (Fin p) (Fin p) ℝ).det, D, c, τ, (hKP' A₁ hA₁K).det_pos, fun A hA =>
      ⟨hA₁min hA, (le_abs_self _).trans (hD A hA), (le_abs_self _).trans (hc A hA),
        (le_abs_self _).trans (hτ A hA)⟩⟩

/-- **The Wishart cone integral diverges along a non-decaying direction.** If a nonzero vector `v`
satisfies `v ⬝ᵥ B *ᵥ v ≤ 0` and `(p - 1) / 2 ≤ a`, then the integral of
`(det A) ^ (a - (p + 1) / 2) * exp (-trace (B * A))` over the positive-definite cone against
`TauCeti.symmetricLebesgue p` is infinite. -/
theorem lintegral_posDef_det_rpow_mul_exp_neg_trace_mul_eq_top_of_dotProduct_mulVec_nonpos
    {v : Fin p → ℝ} (hv : v ≠ 0) (hvB : v ⬝ᵥ B *ᵥ v ≤ 0) (ha : ((p : ℝ) - 1) / 2 ≤ a) :
    ∫⁻ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
      ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
        exp (-(B * (A : Matrix (Fin p) (Fin p) ℝ)).trace)) ∂symmetricLebesgue p = ⊤ := by
  have he : -1 ≤ a - ((p : ℝ) + 1) / 2 := by linarith
  -- The step `E = v vᵀ` of the translates.
  have hvv : (Matrix.vecMulVec v v).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star v
  let E : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
    ⟨Matrix.vecMulVec v v, Matrix.isHermitian_iff_isSelfAdjoint.1 hvv.isHermitian⟩
  have hE0 : E ≠ 0 := fun h => by
    have hzero : Matrix.vecMulVec v v = 0 := congrArg Subtype.val h
    simp [hv] at hzero
  -- A closed ball `K` inside the cone, of radius at most a third of `‖E‖`, with uniform bounds.
  obtain ⟨A₀, r, hr0, hrE, hKP, d₁, D, c, τ, hd₁, hK⟩ :=
    exists_closedBall_subset_posDef_bounds B v (norm_pos_iff.2 hE0)
  set m := min (d₁ ^ (a - ((p : ℝ) + 1) / 2)) ((D * (1 + c)) ^ (a - ((p : ℝ) + 1) / 2))
  have hm0 : 0 < m := by
    obtain ⟨hdA, hAD, hwc, -⟩ := hK A₀ (Metric.mem_closedBall_self hr0.le)
    have hA₀ : (A₀ : Matrix (Fin p) (Fin p) ℝ).PosDef := hKP (Metric.mem_closedBall_self hr0.le)
    have hw0 : 0 ≤ v ⬝ᵥ (A₀ : Matrix (Fin p) (Fin p) ℝ)⁻¹ *ᵥ v := by
      simpa using hA₀.inv.posSemidef.dotProduct_mulVec_nonneg v
    exact lt_min (Real.rpow_pos_of_pos hd₁ _) (Real.rpow_pos_of_pos (by nlinarith) _)
  -- On the `k`-th translate the integrand is at least `m * exp (-τ) / (k + 1)`.
  have hbound : ∀ k : ℕ, ∀ A ∈ Metric.closedBall A₀ r,
      ENNReal.ofReal (m * exp (-τ) * ((k : ℝ) + 1)⁻¹) ≤
      ENNReal.ofReal ((((k : ℝ) • E + A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
          Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
        exp (-(B * (((k : ℝ) • E + A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
          Matrix (Fin p) (Fin p) ℝ)).trace)) := fun k A hA => by
    obtain ⟨hdA, hAD, hwc, hτA⟩ := hK A hA
    rw [Submodule.coe_add, Submodule.coe_smul, add_comm _ (A : Matrix (Fin p) (Fin p) ℝ)]
    exact ENNReal.ofReal_le_ofReal (mul_exp_neg_mul_inv_le_det_rpow_mul_exp_neg_trace (hKP hA)
      hvB hd₁ hdA hAD hwc hτA he k)
  -- These lower bounds form a divergent harmonic series.
  have hsum : ∑' k : ℕ, ENNReal.ofReal (m * exp (-τ) * ((k : ℝ) + 1)⁻¹) = ⊤ := by
    have hns : ¬ Summable fun k : ℕ => m * exp (-τ) * ((k : ℝ) + 1)⁻¹ := by
      rw [summable_mul_left_iff (mul_pos hm0 (exp_pos _)).ne']
      have h := Real.not_summable_natCast_inv
      rw [← summable_nat_add_iff 1] at h
      simpa using h
    by_contra h
    exact hns (ENNReal.summable_toReal h |>.congr fun k => ENNReal.toReal_ofReal (by positivity))
  refine eq_top_iff.2 ?_
  calc (⊤ : ENNReal)
      = ∑' k : ℕ, ENNReal.ofReal (m * exp (-τ) * ((k : ℝ) + 1)⁻¹) *
          symmetricLebesgue p (Metric.closedBall A₀ r) := by
        rw [ENNReal.tsum_mul_right, hsum,
          ENNReal.top_mul (Metric.measure_closedBall_pos _ _ hr0).ne']
    _ ≤ _ := by
        refine le_trans (ENNReal.tsum_le_tsum fun k => ?_)
          (tsum_setLIntegral_add_smul_le (by fun_prop) hvv hrE hKP hE0)
        rw [← setLIntegral_const]
        exact setLIntegral_mono' Metric.isClosed_closedBall.measurableSet (hbound k)

/-- **The Wishart cone integral diverges off the positive-definite cone.** For a symmetric weight
`B` that is not positive definite and `(p - 1) / 2 ≤ a`, the integral of
`(det A) ^ (a - (p + 1) / 2) * exp (-trace (B * A))` over the positive-definite cone against
`TauCeti.symmetricLebesgue p` is infinite. -/
theorem lintegral_posDef_det_rpow_mul_exp_neg_trace_mul_eq_top (hB : B.IsHermitian)
    (hBpd : ¬ B.PosDef) (ha : ((p : ℝ) - 1) / 2 ≤ a) :
    ∫⁻ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef},
      ENNReal.ofReal ((A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
        exp (-(B * (A : Matrix (Fin p) (Fin p) ℝ)).trace)) ∂symmetricLebesgue p = ⊤ := by
  simp only [Matrix.posDef_iff_dotProduct_mulVec, hB, true_and, not_forall, not_lt] at hBpd
  obtain ⟨v, hv, hvB⟩ := hBpd
  exact lintegral_posDef_det_rpow_mul_exp_neg_trace_mul_eq_top_of_dotProduct_mulVec_nonpos hv
    (by simpa using hvB) ha

/-- For a symmetric weight `B` that is not positive definite and `(p - 1) / 2 ≤ a`, the integrand
`(det A) ^ (a - (p + 1) / 2) * exp (-trace (B * A))` is not integrable over the positive-definite
cone against `TauCeti.symmetricLebesgue p`. -/
theorem not_integrableOn_posDef_det_rpow_mul_exp_neg_trace_mul (hB : B.IsHermitian)
    (hBpd : ¬ B.PosDef) (ha : ((p : ℝ) - 1) / 2 ≤ a) :
    ¬ IntegrableOn (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
        (A : Matrix (Fin p) (Fin p) ℝ).det ^ (a - ((p : ℝ) + 1) / 2) *
          exp (-(B * (A : Matrix (Fin p) (Fin p) ℝ)).trace))
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef} (symmetricLebesgue p) := by
  intro h
  have hfin := h.2
  rw [hasFiniteIntegral_iff_enorm] at hfin
  refine hfin.ne ?_
  rw [← lintegral_posDef_det_rpow_mul_exp_neg_trace_mul_eq_top hB hBpd ha]
  -- On the cone the determinant is positive, so the integrand is its own norm.
  refine setLIntegral_congr_fun (measurableSet_posDefMatrix p) fun A hA => ?_
  exact Real.enorm_eq_ofReal
    (mul_nonneg (Real.rpow_nonneg (Matrix.PosDef.det_pos hA).le _) (exp_nonneg _))

end TauCeti
