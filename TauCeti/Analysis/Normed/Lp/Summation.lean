/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import TauCeti.Analysis.Normed.Module.Quotient
import TauCeti.Analysis.Normed.Lp.MapCLM

/-!
# Summation operators out of scalar `ℓ¹` spaces

Given a complete normed space `E` and any family `v : ι → E` whose norms are bounded above,
`TauCeti.lpOneSummation 𝕜 v hv : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] E` sums `α ↦ ∑' i, α i • v i`
by composing `lp.tsumCLM` with `lp.mapCLM` of `ContinuousLinearMap.toSpanSingleton 𝕜 (v i)`. By
the coordinate extensionality and `ℓ¹` operator-norm formulas in `TauCeti.Analysis.Normed.Lp.Basic`,
it is the unique bounded linear map sending each unit coordinate vector `lp.single 1 i 1` to `v i`
(`ContinuousLinearMap.eq_lpOneSummation_iff`), and its operator norm is `⨆ i, ‖v i‖`
(`TauCeti.norm_lpOneSummation`).

Specializing `v` to the inclusion of the closed unit ball `Metric.closedBall (0 : E) 1` of a
complete normed space `E` produces the canonical summation surjection
`TauCeti.unitBallSummation 𝕜 E : lp (fun _ : Metric.closedBall (0 : E) 1 ↦ 𝕜) 1 →L[𝕜] E`,
characterized by its values on unit coordinate vectors
(`ContinuousLinearMap.eq_unitBallSummation_iff`). Over a densely normed field `𝕜`, its underlying
bounded additive homomorphism is a normed quotient map
(`TauCeti.isQuotient_toNormedAddGroupHom_unitBallSummation`).

## Main definitions and results

* `TauCeti.lpOneSummation`: bounded summation operator `α ↦ ∑' i, α i • v i` on `ℓ¹(ι, 𝕜)`.
* `ContinuousLinearMap.eq_lpOneSummation_iff` and `TauCeti.norm_lpOneSummation`: universal property
  and exact operator norm of `TauCeti.lpOneSummation`.
* `TauCeti.unitBallSummation` and `ContinuousLinearMap.eq_unitBallSummation_iff`: canonical
  summation map from `ℓ¹` on the closed unit ball of `E` and its universal property.
* `TauCeti.isQuotient_toNormedAddGroupHom_unitBallSummation`: `TauCeti.unitBallSummation 𝕜 E` is a
  normed quotient map (`NormedAddGroupHom.IsQuotient`) over any densely normed field `𝕜`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §4.
* A. Pietsch, *Operator Ideals*, North-Holland (1980), §C.3.2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §2.2 and §2.4.
-/

public section

open scoped ENNReal NNReal

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
  have h := (lpOneSummation 𝕜 v hv).hasSum_smul_lp_single ENNReal.one_ne_top α
  simpa only [lpOneSummation_single, one_smul] using h

/-- **Universal property of `TauCeti.lpOneSummation`.** A bounded linear map out of scalar `ℓ¹`
equals `TauCeti.lpOneSummation 𝕜 v hv` if and only if it maps each unit coordinate vector
`lp.single 1 i 1` to `v i`. -/
theorem _root_.ContinuousLinearMap.eq_lpOneSummation_iff [DecidableEq ι]
    (U : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] E) (v : ι → E)
    (hv : BddAbove (Set.range fun i ↦ ‖v i‖)) :
    U = lpOneSummation 𝕜 v hv ↔ ∀ i : ι, U (lp.single 1 i 1) = v i := by
  refine ⟨fun h i ↦ by simp [h], fun h ↦ U.ext_lp_of_ne_top ENNReal.one_ne_top fun i ↦ ?_⟩
  simp [h i]

/-- Two summation operators on scalar `ℓ¹` agree if and only if their underlying families agree. -/
theorem lpOneSummation_inj {v w : ι → E} (hv : BddAbove (Set.range fun i ↦ ‖v i‖))
    (hw : BddAbove (Set.range fun i ↦ ‖w i‖)) :
    lpOneSummation 𝕜 v hv = lpOneSummation 𝕜 w hw ↔ v = w := by
  classical
  rw [(lpOneSummation 𝕜 v hv).eq_lpOneSummation_iff, funext_iff]
  simp

/-- Postcomposing `TauCeti.lpOneSummation 𝕜 v hv` with a bounded linear operator `T` into a
complete normed space gives `TauCeti.lpOneSummation 𝕜 (fun i ↦ T (v i)) _`. -/
theorem _root_.ContinuousLinearMap.comp_lpOneSummation
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) (v : ι → E) (hv : BddAbove (Set.range fun i ↦ ‖v i‖))
    (hTv : BddAbove (Set.range fun i ↦ ‖T (v i)‖)) :
    T ∘L lpOneSummation 𝕜 v hv = lpOneSummation 𝕜 (fun i ↦ T (v i)) hTv := by
  classical
  rw [(T ∘L lpOneSummation 𝕜 v hv).eq_lpOneSummation_iff]
  intro i
  simp

variable (𝕜) in
/-- The operator norm of `lpOneSummation 𝕜 v hv` is the supremum `⨆ i, ‖v i‖`. -/
theorem norm_lpOneSummation (v : ι → E) (hv : BddAbove (Set.range fun i ↦ ‖v i‖)) :
    ‖lpOneSummation 𝕜 v hv‖ = ⨆ i : ι, ‖v i‖ := by
  classical
  simpa using (lpOneSummation 𝕜 v hv).norm_eq_ciSup_norm_lp_single

variable (𝕜) in
/-- The nonnegative operator norm of `lpOneSummation 𝕜 v hv` is `⨆ i, ‖v i‖₊`. -/
theorem nnnorm_lpOneSummation (v : ι → E) (hv : BddAbove (Set.range fun i ↦ ‖v i‖)) :
    ‖lpOneSummation 𝕜 v hv‖₊ = ⨆ i : ι, ‖v i‖₊ := by
  classical
  simpa using (lpOneSummation 𝕜 v hv).nnnorm_eq_ciSup_nnnorm_lp_single

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
    ⟨1, mem_upperBounds.mpr (Set.forall_mem_range.mpr fun x ↦ mem_closedBall_zero_iff.mp
        x.property)⟩

section NontriviallyNormedField

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

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

/-- **Universal property of `TauCeti.unitBallSummation`.** A bounded linear map from `ℓ¹` on the
closed unit ball of `E` into `E` equals `TauCeti.unitBallSummation 𝕜 E` if and only if it maps each
unit coordinate vector `lp.single 1 x 1` to `(x : E)`. -/
theorem _root_.ContinuousLinearMap.eq_unitBallSummation_iff
    [DecidableEq (Metric.closedBall (0 : E) 1)]
    (U : lp (fun _ : Metric.closedBall (0 : E) 1 ↦ 𝕜) 1 →L[𝕜] E) :
    U = unitBallSummation 𝕜 E ↔
      ∀ x : Metric.closedBall (0 : E) 1, U (lp.single 1 x 1) = (x : E) :=
  U.eq_lpOneSummation_iff _ _

variable (𝕜 E) in
/-- `unitBallSummation 𝕜 E` has operator norm at most `1` over every nontrivially normed field. -/
theorem norm_unitBallSummation_le : ‖unitBallSummation 𝕜 E‖ ≤ 1 :=
  norm_lpOneSummation_le 𝕜 (Subtype.val : Metric.closedBall (0 : E) 1 → E) _ zero_le_one
    fun x ↦ mem_closedBall_zero_iff.mp x.property

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

/-- Over a densely normed field, the bounded additive homomorphism underlying
`unitBallSummation 𝕜 E` is a normed quotient map. -/
theorem isQuotient_toNormedAddGroupHom_unitBallSummation :
    (unitBallSummation 𝕜 E).toNormedAddGroupHom.IsQuotient := by
  refine .of_norm_lift (by simpa using norm_unitBallSummation_le 𝕜 E) fun {ε} hε y ↦ ?_
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
theorem norm_unitBallSummation [Nontrivial E] : ‖unitBallSummation 𝕜 E‖ = 1 := by
  simpa using (isQuotient_toNormedAddGroupHom_unitBallSummation 𝕜 E).norm_eq_one

/-- Over a densely normed field and on a nontrivial space, `unitBallSummation 𝕜 E` has nonnegative
operator norm `1`. -/
@[simp]
theorem nnnorm_unitBallSummation [Nontrivial E] : ‖unitBallSummation 𝕜 E‖₊ = 1 := by
  simpa using (isQuotient_toNormedAddGroupHom_unitBallSummation 𝕜 E).nnnorm_eq_one

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
  T.opNorm_comp_of_isQuotient (TauCeti.isQuotient_toNormedAddGroupHom_unitBallSummation 𝕜 E)

/-- Precomposing with `TauCeti.unitBallSummation 𝕜 E` preserves the nonnegative operator norm. -/
@[simp]
theorem opNNNorm_comp_unitBallSummation (T : E →L[𝕜] F) :
    ‖T ∘L TauCeti.unitBallSummation 𝕜 E‖₊ = ‖T‖₊ :=
  T.opNNNorm_comp_of_isQuotient (TauCeti.isQuotient_toNormedAddGroupHom_unitBallSummation 𝕜 E)

end ContinuousLinearMap
