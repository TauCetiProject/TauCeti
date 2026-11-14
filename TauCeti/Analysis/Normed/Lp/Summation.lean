/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import TauCeti.Analysis.Normed.Operator.MetricSurjection
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Lp.MapCLM

/-!
# Summation operators out of scalar `ℓ¹` spaces

Every bounded linear operator `U : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F` from a scalar `ℓ¹` space into a
seminormed space expands along coordinate vectors (`ContinuousLinearMap.hasSum_lp_single_smul`) and
has operator norm equal to the supremum of the norms of its values at unit coordinate vectors
(`ContinuousLinearMap.opNorm_lpOne_eq_iSup`, `ContinuousLinearMap.opNNNorm_lpOne_eq_iSup`). When
`F` is Hausdorff, operators out of `lp (fun _ : ι ↦ 𝕜) q` for `q ≠ ∞` are determined by their
values on unit coordinate vectors (`ContinuousLinearMap.ext_lp_of_ne_top`).

Conversely, given a complete normed space `E` and any family `v : ι → E` whose norms are bounded
above, `TauCeti.lpOneSummation 𝕜 v hv : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] E` sums `α ↦ ∑' i, α i • v i`
by composing `lp.tsumCLM` with `lp.mapCLM` of `ContinuousLinearMap.toSpanSingleton 𝕜 (v i)`. It is
the unique bounded linear map sending each unit coordinate vector `lp.single 1 i 1` to `v i`
(`TauCeti.eq_lpOneSummation_iff`), and its operator norm is `⨆ i, ‖v i‖`
(`TauCeti.norm_lpOneSummation`).

Specializing `v` to the inclusion of the closed unit ball `Metric.closedBall (0 : E) 1` of a
complete normed space `E` produces the canonical summation surjection
`TauCeti.unitBallSummation 𝕜 E : lp (fun _ : Metric.closedBall (0 : E) 1 ↦ 𝕜) 1 →L[𝕜] E`. Over a
densely normed field `𝕜`, this map is a metric surjection
(`TauCeti.isMetricSurjection_unitBallSummation`).

## Main definitions and results

* `ContinuousLinearMap.opNorm_lpOne_le`, `opNorm_lpOne_eq_iSup`, `opNNNorm_lpOne_eq_iSup`:
  coordinate-supremum formula for the norm of an operator on scalar `ℓ¹`.
* `ContinuousLinearMap.ext_lp_of_ne_top`: coordinate extensionality on scalar `ℓ^q` for `q ≠ ∞`.
* `TauCeti.lpOneSummation`: bounded summation operator `α ↦ ∑' i, α i • v i` on `ℓ¹(ι, 𝕜)`.
* `TauCeti.eq_lpOneSummation_iff` and `TauCeti.norm_lpOneSummation`: universal property and exact
  operator norm of `TauCeti.lpOneSummation`.
* `TauCeti.unitBallSummation`: canonical summation map from `ℓ¹` on the closed unit ball of `E`.
* `TauCeti.isMetricSurjection_unitBallSummation`: `TauCeti.unitBallSummation 𝕜 E` is a metric
  surjection over any densely normed field `𝕜`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §4.
* A. Pietsch, *Operator Ideals*, North-Holland (1980), §C.3.2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §2.2 and §2.4.
-/

public section

open scoped ENNReal NNReal Topology lp
open Filter

namespace ContinuousLinearMap

section LpCoord

variable {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [DecidableEq ι]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The value of a bounded linear operator out of scalar `ℓ^q` at any unit coordinate vector has
norm at most the operator norm. -/
theorem norm_apply_lp_single_one_le (U : lp (fun _ : ι ↦ 𝕜) q →L[𝕜] F) (i : ι) :
    ‖U (lp.single q i 1)‖ ≤ ‖U‖ := by
  simpa [lp.norm_single (zero_lt_one.trans_le Fact.out)] using
    U.le_opNorm (lp.single q i (1 : 𝕜))

/-- A bounded linear operator out of scalar `ℓ^q` scales its value on a unit coordinate vector:
`U (lp.single q i c) = c • U (lp.single q i 1)`. -/
theorem apply_lp_single_eq_smul (U : lp (fun _ : ι ↦ 𝕜) q →L[𝕜] F) (i : ι) (c : 𝕜) :
    U (lp.single q i c) = c • U (lp.single q i 1) := by
  simpa [← lp.single_smul] using U.map_smul c (lp.single q i 1)

/-- The norms of the images of unit coordinate vectors under a bounded linear operator out of
scalar `ℓ^q` are bounded above by `‖U‖`. -/
theorem bddAbove_range_norm_apply_lp_single_one (U : lp (fun _ : ι ↦ 𝕜) q →L[𝕜] F) :
    BddAbove (Set.range fun i ↦ ‖U (lp.single q i 1)‖) :=
  ⟨‖U‖, Set.forall_mem_range.mpr U.norm_apply_lp_single_one_le⟩

/-- Every bounded linear operator out of scalar `ℓ^q` with `q ≠ ∞` expands each input `α` as the
unconditional sum `∑ i, α i • U (lp.single q i 1)`. -/
theorem hasSum_lp_single_smul (hq : q ≠ ∞) (U : lp (fun _ : ι ↦ 𝕜) q →L[𝕜] F)
    (α : lp (fun _ : ι ↦ 𝕜) q) :
    HasSum (fun i ↦ α i • U (lp.single q i 1)) (U α) := by
  convert (lp.hasSum_single hq α).map U U.continuous using 1
  ext i
  exact (U.apply_lp_single_eq_smul i (α i)).symm

end LpCoord

section LpExt

variable {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [DecidableEq ι]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Two bounded linear operators from scalar `ℓ^q` (`q ≠ ∞`) into a normed space are equal as soon
as they agree on every unit coordinate vector `lp.single q i 1`. -/
theorem ext_lp_of_ne_top (hq : q ≠ ∞) {U₁ U₂ : lp (fun _ : ι ↦ 𝕜) q →L[𝕜] F}
    (h : ∀ i : ι, U₁ (lp.single q i 1) = U₂ (lp.single q i 1)) : U₁ = U₂ := by
  ext α
  refine (U₁.hasSum_lp_single_smul hq α).unique ?_
  simpa only [h] using U₂.hasSum_lp_single_smul hq α

end LpExt

section LpOneNorm

variable {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [DecidableEq ι]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Bounding a bounded linear operator out of scalar `ℓ¹` on every unit coordinate vector by `C ≥ 0`
bounds its operator norm by `C`. -/
theorem opNorm_lpOne_le (U : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hU : ∀ i : ι, ‖U (lp.single 1 i 1)‖ ≤ C) : ‖U‖ ≤ C := by
  refine U.opNorm_le_bound hC fun α ↦ ?_
  have hlim₁ : Tendsto (fun s : Finset ι ↦ ‖∑ i ∈ s, α i • U (lp.single 1 i 1)‖) atTop (𝓝 ‖U α‖) :=
    (continuous_norm.tendsto (U α)).comp (U.hasSum_lp_single_smul ENNReal.one_ne_top α)
  have hlim₂ : Tendsto (fun s : Finset ι ↦ ∑ i ∈ s, C * ‖α i‖) atTop (𝓝 (C * ‖α‖)) :=
    (lp.hasSum_norm_one α).mul_left C
  refine le_of_tendsto_of_tendsto hlim₁ hlim₂ (Eventually.of_forall fun s ↦ ?_)
  calc ‖∑ i ∈ s, α i • U (lp.single 1 i 1)‖
      ≤ ∑ i ∈ s, ‖α i • U (lp.single 1 i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, C * ‖α i‖ := Finset.sum_le_sum fun i _ ↦ by
        rw [norm_smul, mul_comm C]
        exact mul_le_mul_of_nonneg_left (hU i) (norm_nonneg (α i))

/-- The operator norm of a bounded linear map out of scalar `ℓ¹` is the supremum of the norms of
its values at unit coordinate vectors (`0` when the index type is empty). -/
theorem opNorm_lpOne_eq_iSup (U : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F) :
    ‖U‖ = ⨆ i : ι, ‖U (lp.single 1 i 1)‖ :=
  le_antisymm
    (U.opNorm_lpOne_le (Real.iSup_nonneg fun _ ↦ norm_nonneg _)
      fun i ↦ le_ciSup U.bddAbove_range_norm_apply_lp_single_one i)
    (Real.iSup_le U.norm_apply_lp_single_one_le (norm_nonneg U))

/-- The nonnegative operator norm of a bounded linear map out of scalar `ℓ¹` is the supremum of the
nonnegative norms of its values at unit coordinate vectors. -/
theorem opNNNorm_lpOne_eq_iSup (U : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F) :
    ‖U‖₊ = ⨆ i : ι, ‖U (lp.single 1 i 1)‖₊ := by
  have hbdd : BddAbove (Set.range fun i ↦ ‖U (lp.single 1 i 1)‖₊) :=
    ⟨‖U‖₊, Set.forall_mem_range.mpr fun i ↦ by exact_mod_cast U.norm_apply_lp_single_one_le i⟩
  refine le_antisymm ?_ (ciSup_le' fun i ↦ by exact_mod_cast U.norm_apply_lp_single_one_le i)
  exact_mod_cast U.opNorm_lpOne_le (NNReal.coe_nonneg _)
    fun i ↦ NNReal.coe_le_coe.mpr (le_ciSup hbdd i)

end LpOneNorm

end ContinuousLinearMap

namespace TauCeti

section LpOneSummation

/-- **Bounded summation on scalar `ℓ¹`.** For any norm-bounded family `v : ι → E` in a complete
normed space, `lpOneSummation 𝕜 v hv : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] E` sends `α` to
`∑' i, α i • v i`. It depends on the bound only through the proposition `hv`. -/
noncomputable def lpOneSummation (𝕜 : Type*) {ι E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (v : ι → E) (hv : BddAbove (Set.range fun i ↦ ‖v i‖)) :
    lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] E :=
  lp.tsumCLM 𝕜 ι E ∘L
    lp.mapCLM 1 (fun i ↦ ContinuousLinearMap.toSpanSingleton 𝕜 (v i))
      (Real.iSup_nonneg fun _ ↦ norm_nonneg _)
      (fun i ↦ (ContinuousLinearMap.norm_toSpanSingleton (v i)).trans_le (le_ciSup hv i))

variable {𝕜 ι E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Evaluating `lpOneSummation 𝕜 v hv` at `α` computes the series `∑' i, α i • v i`. -/
@[simp]
theorem lpOneSummation_apply (v : ι → E) (hv : BddAbove (Set.range fun i ↦ ‖v i‖))
    (α : lp (fun _ : ι ↦ 𝕜) 1) :
    lpOneSummation 𝕜 v hv α = ∑' i : ι, α i • v i := by
  simp [lpOneSummation]

/-- On a coordinate vector `lp.single 1 i c`, `lpOneSummation 𝕜 v hv` evaluates to `c • v i`. -/
@[simp high] -- Apply before `lpOneSummation_apply` expands the evaluation into a `tsum`.
theorem lpOneSummation_single [DecidableEq ι] (v : ι → E)
    (hv : BddAbove (Set.range fun i ↦ ‖v i‖)) (i : ι) (c : 𝕜) :
    lpOneSummation 𝕜 v hv (lp.single 1 i c) = c • v i := by
  simp only [lpOneSummation, ContinuousLinearMap.comp_apply, lp.mapCLM_single,
    ContinuousLinearMap.toSpanSingleton_apply, lp.tsumCLM_apply]
  rw [tsum_eq_single i]
  · simp
  · intro j hj
    simp [hj]

/-- For every `α : lp (fun _ : ι ↦ 𝕜) 1`, the family `i ↦ α i • v i` is unconditionally summable to
`lpOneSummation 𝕜 v hv α`. -/
theorem hasSum_lpOneSummation (v : ι → E) (hv : BddAbove (Set.range fun i ↦ ‖v i‖))
    (α : lp (fun _ : ι ↦ 𝕜) 1) :
    HasSum (fun i ↦ α i • v i) (lpOneSummation 𝕜 v hv α) := by
  classical
  have h := (lpOneSummation 𝕜 v hv).hasSum_lp_single_smul ENNReal.one_ne_top α
  simpa only [lpOneSummation_single, one_smul] using h

/-- **Universal property of `lpOneSummation`.** A bounded linear map out of scalar `ℓ¹` equals
`lpOneSummation 𝕜 v hv` if and only if it maps each unit coordinate vector `lp.single 1 i 1` to
`v i`. -/
theorem eq_lpOneSummation_iff [DecidableEq ι] (U : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] E) (v : ι → E)
    (hv : BddAbove (Set.range fun i ↦ ‖v i‖)) :
    U = lpOneSummation 𝕜 v hv ↔ ∀ i : ι, U (lp.single 1 i 1) = v i := by
  refine ⟨fun h i ↦ by simp [h], fun h ↦ U.ext_lp_of_ne_top ENNReal.one_ne_top fun i ↦ ?_⟩
  simp [h i]

/-- Two summation operators on scalar `ℓ¹` agree if and only if their underlying families agree. -/
theorem lpOneSummation_inj {v w : ι → E} (hv : BddAbove (Set.range fun i ↦ ‖v i‖))
    (hw : BddAbove (Set.range fun i ↦ ‖w i‖)) :
    lpOneSummation 𝕜 v hv = lpOneSummation 𝕜 w hw ↔ v = w := by
  classical
  rw [eq_lpOneSummation_iff, funext_iff]
  simp

/-- Postcomposing `lpOneSummation 𝕜 v hv` with a bounded linear operator `T` into a complete normed
space gives `lpOneSummation 𝕜 (fun i ↦ T (v i)) _`. -/
theorem comp_lpOneSummation [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) (v : ι → E) (hv : BddAbove (Set.range fun i ↦ ‖v i‖))
    (hTv : BddAbove (Set.range fun i ↦ ‖T (v i)‖)) :
    T ∘L lpOneSummation 𝕜 v hv = lpOneSummation 𝕜 (fun i ↦ T (v i)) hTv := by
  classical
  rw [eq_lpOneSummation_iff]
  intro i
  simp

variable (𝕜) in
/-- The operator norm of `lpOneSummation 𝕜 v hv` is the supremum `⨆ i, ‖v i‖`. -/
theorem norm_lpOneSummation (v : ι → E) (hv : BddAbove (Set.range fun i ↦ ‖v i‖)) :
    ‖lpOneSummation 𝕜 v hv‖ = ⨆ i : ι, ‖v i‖ := by
  classical
  simpa using (lpOneSummation 𝕜 v hv).opNorm_lpOne_eq_iSup

variable (𝕜) in
/-- The nonnegative operator norm of `lpOneSummation 𝕜 v hv` is `⨆ i, ‖v i‖₊`. -/
theorem nnnorm_lpOneSummation (v : ι → E) (hv : BddAbove (Set.range fun i ↦ ‖v i‖)) :
    ‖lpOneSummation 𝕜 v hv‖₊ = ⨆ i : ι, ‖v i‖₊ := by
  classical
  simpa using (lpOneSummation 𝕜 v hv).opNNNorm_lpOne_eq_iSup

variable (𝕜) in
/-- A uniform bound `0 ≤ C` on `‖v i‖` bounds `‖lpOneSummation 𝕜 v hv‖` by `C`. -/
theorem norm_lpOneSummation_le (v : ι → E) (hv : BddAbove (Set.range fun i ↦ ‖v i‖)) {C : ℝ}
    (hC : 0 ≤ C) (hvC : ∀ i : ι, ‖v i‖ ≤ C) :
    ‖lpOneSummation 𝕜 v hv‖ ≤ C := by
  rw [norm_lpOneSummation]
  exact Real.iSup_le hvC hC

end LpOneSummation

section UnitBallSummation

/-- **Canonical unit-ball summation.** For a complete normed space `E` over `𝕜`,
`unitBallSummation 𝕜 E` sums `ℓ¹` families indexed by the closed unit ball `Metric.closedBall 0 1`
in `E` via `α ↦ ∑' x, α x • (x : E)`. -/
noncomputable def unitBallSummation (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
    lp (fun _ : Metric.closedBall (0 : E) 1 ↦ 𝕜) 1 →L[𝕜] E :=
  lpOneSummation 𝕜 (Subtype.val : Metric.closedBall (0 : E) 1 → E)
    ⟨1, mem_upperBounds.mpr (Set.forall_mem_range.mpr fun x ↦ mem_closedBall_zero_iff.mp x.2)⟩

section NontriviallyNormedField

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- `unitBallSummation 𝕜 E` is `lpOneSummation` specialized to `Subtype.val` on the closed unit
ball. -/
theorem unitBallSummation_eq_lpOneSummation :
    unitBallSummation 𝕜 E = lpOneSummation 𝕜 (Subtype.val : Metric.closedBall (0 : E) 1 → E)
      ⟨1, mem_upperBounds.mpr (Set.forall_mem_range.mpr fun x ↦ mem_closedBall_zero_iff.mp x.2)⟩ :=
  (rfl)

/-- Evaluating `unitBallSummation 𝕜 E` at `α` computes `∑' x, α x • (x : E)`. -/
@[simp]
theorem unitBallSummation_apply (α : lp (fun _ : Metric.closedBall (0 : E) 1 ↦ 𝕜) 1) :
    unitBallSummation 𝕜 E α = ∑' x : Metric.closedBall (0 : E) 1, α x • (x : E) :=
  lpOneSummation_apply _ _ α

/-- Evaluating `unitBallSummation 𝕜 E` on a coordinate vector `lp.single 1 x c` gives `c • x`. -/
@[simp high] -- Apply before `unitBallSummation_apply` expands the evaluation into a `tsum`.
theorem unitBallSummation_single [DecidableEq (Metric.closedBall (0 : E) 1)]
    (x : Metric.closedBall (0 : E) 1) (c : 𝕜) :
    unitBallSummation 𝕜 E (lp.single 1 x c) = c • (x : E) :=
  lpOneSummation_single _ _ x c

variable (𝕜 E) in
/-- `unitBallSummation 𝕜 E` has operator norm at most `1` over every nontrivially normed field. -/
theorem norm_unitBallSummation_le : ‖unitBallSummation 𝕜 E‖ ≤ 1 :=
  norm_lpOneSummation_le 𝕜 (Subtype.val : Metric.closedBall (0 : E) 1 → E) _ zero_le_one
    fun x ↦ mem_closedBall_zero_iff.mp x.2

variable (𝕜 E) in
/-- `unitBallSummation 𝕜 E` is surjective over every nontrivially normed field. -/
theorem surjective_unitBallSummation : Function.Surjective (unitBallSummation 𝕜 E) := fun y ↦ by
  classical
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 ‖y‖
  have hc0 : c ≠ 0 := norm_pos_iff.mp ((norm_nonneg y).trans_lt hc)
  have hz : c⁻¹ • y ∈ Metric.closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv]
    exact inv_mul_le_one_of_le₀ hc.le (norm_nonneg c)
  exact ⟨lp.single 1 ⟨c⁻¹ • y, hz⟩ c, by simp [smul_inv_smul₀ hc0]⟩

end NontriviallyNormedField

section DenselyNormedField

variable (𝕜 E : Type*) [DenselyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Over a densely normed field, `unitBallSummation 𝕜 E` is a metric surjection. -/
theorem isMetricSurjection_unitBallSummation :
    (unitBallSummation 𝕜 E).IsMetricSurjection where
  norm_le_one := norm_unitBallSummation_le 𝕜 E
  exists_apply_eq_norm_lt y {ε} hε := by
    classical
    obtain ⟨c, hcy, hclt⟩ := DenselyNormedField.lt_norm_lt (α := 𝕜) ‖y‖ (‖y‖ + ε)
      (norm_nonneg y) (lt_add_of_pos_right ‖y‖ hε)
    have hc0 : c ≠ 0 := norm_pos_iff.mp ((norm_nonneg y).trans_lt hcy)
    have hz : c⁻¹ • y ∈ Metric.closedBall (0 : E) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv]
      exact inv_mul_le_one_of_le₀ hcy.le (norm_nonneg c)
    refine ⟨lp.single 1 ⟨c⁻¹ • y, hz⟩ c, by simp [smul_inv_smul₀ hc0], ?_⟩
    simpa [lp.norm_single zero_lt_one] using hclt

/-- Over a densely normed field and on a nontrivial space, `unitBallSummation 𝕜 E` has norm `1`. -/
@[simp]
theorem norm_unitBallSummation [Nontrivial E] : ‖unitBallSummation 𝕜 E‖ = 1 :=
  (isMetricSurjection_unitBallSummation 𝕜 E).norm_eq_one

/-- Over a densely normed field and on a nontrivial space, `unitBallSummation 𝕜 E` has nonnegative
operator norm `1`. -/
@[simp]
theorem nnnorm_unitBallSummation [Nontrivial E] : ‖unitBallSummation 𝕜 E‖₊ = 1 :=
  (isMetricSurjection_unitBallSummation 𝕜 E).nnnorm_eq_one

end DenselyNormedField

end UnitBallSummation

end TauCeti

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [DenselyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Precomposing with `TauCeti.unitBallSummation 𝕜 E` preserves the operator norm. -/
@[simp]
theorem opNorm_comp_unitBallSummation (T : E →L[𝕜] F) :
    ‖T ∘L TauCeti.unitBallSummation 𝕜 E‖ = ‖T‖ :=
  (TauCeti.isMetricSurjection_unitBallSummation 𝕜 E).opNorm_comp T

/-- Precomposing with `TauCeti.unitBallSummation 𝕜 E` preserves the nonnegative operator norm. -/
@[simp]
theorem opNNNorm_comp_unitBallSummation (T : E →L[𝕜] F) :
    ‖T ∘L TauCeti.unitBallSummation 𝕜 E‖₊ = ‖T‖₊ :=
  (TauCeti.isMetricSurjection_unitBallSummation 𝕜 E).opNNNorm_comp T

end ContinuousLinearMap
