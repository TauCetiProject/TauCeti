/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Summation
public import TauCeti.Analysis.Normed.Operator.SNumbers.Kolmogorov
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
import Mathlib.Topology.Algebra.SeparationQuotient.FiniteDimensional
import Mathlib.Topology.Algebra.SeparationQuotient.Section

/-!
# Metric surjectivity of Kolmogorov numbers and Pietsch's lifting identity

Every operator satisfies `dₙ(T) ≤ aₙ(T)` (`ContinuousLinearMap.kolmogorovNumber_le_singularValue`),
and precomposing `T` with any metric surjection `Q` leaves all Kolmogorov numbers unchanged:
`dₙ(T ∘ Q) = dₙ(T)` (`ContinuousLinearMap.IsMetricSurjection.kolmogorovNumber_comp`). Both results
hold over every nontrivially normed field and between arbitrary seminormed spaces across
independent universes.

When the domain is a scalar `ℓ¹` space `lp (fun _ : ι ↦ 𝕜) 1` over a complete nontrivially normed
field `𝕜`, the inequality `dₙ ≤ aₙ` reverses: every bounded operator
`S : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F` into a seminormed space satisfies `aₙ(S) = dₙ(S)`
(`ContinuousLinearMap.singularValue_lpOne_eq_kolmogorovNumber`). Given a subspace `V ≤ F` of
dimension at most `n`, near-best approximants in `V` for the unit coordinate images of `S` project
into `SeparationQuotient V`, which is Hausdorff and finite-dimensional over `𝕜`, hence complete;
summing there with `TauCeti.lpOneSummation` and lifting back along `SeparationQuotient.outCLM 𝕜 V`
produces an approximant of rank at most `n` within `‖V.mkQL ∘L S‖ + ε` of `S`.

Combining `aₙ = dₙ` on scalar `ℓ¹` with metric-surjection invariance of `dₙ` yields **Pietsch's
lifting identity**:
* for any metric surjection `Q : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] E` over a complete field `𝕜`,
  `(T ∘L Q).singularValue n = T.kolmogorovNumber n`
  (`ContinuousLinearMap.IsMetricSurjection.singularValue_comp_lpOne`);
* in particular, over a complete densely normed field `𝕜` and for a complete normed domain `E`,
  `(T ∘L TauCeti.unitBallSummation 𝕜 E).singularValue n = T.kolmogorovNumber n`
  (`ContinuousLinearMap.singularValue_comp_unitBallSummation`).

## Main results

* `ContinuousLinearMap.kolmogorovNumber_le_singularValue`: `dₙ(T) ≤ aₙ(T)` in general.
* `ContinuousLinearMap.IsMetricSurjection.kolmogorovNumber_comp`: `dₙ(T ∘ Q) = dₙ(T)` for every
  metric surjection `Q`.
* `ContinuousLinearMap.singularValue_lpOne_eq_kolmogorovNumber`: `aₙ(S) = dₙ(S)` for operators
  out of `lp (fun _ : ι ↦ 𝕜) 1` over complete scalar fields.
* `ContinuousLinearMap.IsMetricSurjection.singularValue_comp_lpOne`: `aₙ(T ∘ Q) = dₙ(T)` for
  every metric surjection `Q` from scalar `ℓ¹`.
* `ContinuousLinearMap.singularValue_comp_unitBallSummation`: Pietsch's lifting identity.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §4, Theorem 4.3.
* A. Pietsch, *Operator Ideals*, North-Holland (1980), §11.5.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §2.4.
-/

public section

open scoped ENNReal NNReal

namespace ContinuousLinearMap

section General

variable {𝕜 D E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup D] [NormedSpace 𝕜 D]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Every Kolmogorov number is bounded above by the corresponding approximation number:
decomposing `T = R + (T - R)` for a rank-at-most-`n` approximant `R` bounds `dₙ(T)` by
`‖T - R‖₊`. -/
theorem kolmogorovNumber_le_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    T.kolmogorovNumber n ≤ T.singularValue n := by
  refine le_singularValue_iff.mpr fun R hR ↦ ?_
  simpa [R.kolmogorovNumber_eq_zero_of_rank_le hR] using R.kolmogorovNumber_add_le (T - R) n

/-- **Metric surjectivity of Kolmogorov numbers.** Precomposing with a metric surjection leaves
all Kolmogorov numbers unchanged, over every nontrivially normed field. -/
theorem IsMetricSurjection.kolmogorovNumber_comp {Q : D →L[𝕜] E} (hQ : Q.IsMetricSurjection)
    (T : E →L[𝕜] F) (n : ℕ) :
    (T ∘L Q).kolmogorovNumber n = T.kolmogorovNumber n := by
  simp only [kolmogorovNumber_def, ← comp_assoc, hQ.opNNNorm_comp]

end General

section LpOneLifting

variable {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Given a finite-dimensional subspace `V ≤ F` over a complete scalar field and coordinate-wise
approximants `v i ∈ V` within `C ≥ 0` of `S (lp.single 1 i 1)`, summing in `SeparationQuotient V`
and lifting along `SeparationQuotient.outCLM 𝕜 V` produces a bounded operator `L` with range in `V`
and `‖S - L‖ ≤ C`. -/
private theorem exists_range_le_norm_sub_le_of_lpOne [DecidableEq ι]
    (S : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F) (V : Submodule 𝕜 F) [FiniteDimensional 𝕜 V]
    {C : ℝ} (hC : 0 ≤ C) {v : ι → V} (hv : ∀ i : ι, ‖S (lp.single 1 i 1) - (v i : F)‖ ≤ C) :
    ∃ L : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F, L.range ≤ V ∧ ‖S - L‖ ≤ C := by
  have : CompleteSpace (SeparationQuotient V) :=
    FiniteDimensional.completeSpace 𝕜 (SeparationQuotient V)
  let u : ι → SeparationQuotient V := fun i ↦ SeparationQuotient.mk (v i)
  have hu : BddAbove (Set.range fun i ↦ ‖u i‖) := by
    refine ⟨‖S‖ + C, mem_upperBounds.mpr <| Set.forall_mem_range.mpr fun i ↦ ?_⟩
    rw [SeparationQuotient.norm_mk]
    calc ‖v i‖ = ‖(v i : F)‖ := rfl
      _ = ‖S (lp.single 1 i 1) - (S (lp.single 1 i 1) - (v i : F))‖ := by abel_nf
      _ ≤ ‖S (lp.single 1 i 1)‖ + ‖S (lp.single 1 i 1) - (v i : F)‖ := norm_sub_le _ _
      _ ≤ ‖S‖ + C := add_le_add (S.norm_apply_lp_single_one_le i) (hv i)
  set L : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F :=
    V.subtypeL ∘L SeparationQuotient.outCLM 𝕜 V ∘L TauCeti.lpOneSummation 𝕜 u hu with hL
  have hL_range : L.range ≤ V := by
    rintro _ ⟨α, rfl⟩
    rw [hL]
    exact Subtype.prop _
  have hL_single (i : ι) :
      L (lp.single 1 i 1) = (SeparationQuotient.outCLM 𝕜 V (u i) : F) := by
    rw [hL, comp_apply, comp_apply, TauCeti.lpOneSummation_single, one_smul]
    rfl
  refine ⟨L, hL_range, (S - L).opNorm_lpOne_le hC fun i ↦ ?_⟩
  have hout : ‖(v i : F) - L (lp.single 1 i 1)‖ = 0 := by
    rw [hL_single]
    change ‖v i - SeparationQuotient.outCLM 𝕜 V (u i)‖ = 0
    rw [← SeparationQuotient.norm_mk, SeparationQuotient.mk_sub, SeparationQuotient.mk_outCLM,
      sub_self, norm_zero]
  rw [sub_apply]
  calc ‖S (lp.single 1 i 1) - L (lp.single 1 i 1)‖
      ≤ ‖S (lp.single 1 i 1) - (v i : F)‖ + ‖(v i : F) - L (lp.single 1 i 1)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C + 0 := add_le_add (hv i) hout.le
    _ = C := add_zero C

/-- **Lifting property of scalar `ℓ¹`.** Over a complete nontrivially normed field, the
approximation numbers and Kolmogorov numbers coincide for every bounded operator out of
`lp (fun _ : ι ↦ 𝕜) 1` into a seminormed space. -/
theorem singularValue_lpOne_eq_kolmogorovNumber (S : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] F) (n : ℕ) :
    S.singularValue n = S.kolmogorovNumber n := by
  classical
  refine le_antisymm ?_ (S.kolmogorovNumber_le_singularValue n)
  refine le_kolmogorovNumber_iff.mpr fun V hV ↦
    NNReal.coe_le_coe.mp <| le_of_forall_pos_lt_add fun ε hε ↦ ?_
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
  have hex (i : ι) : ∃ v : V, ‖S (lp.single 1 i 1) - v.1‖ ≤ ‖V.mkQL ∘L S‖ + ε / 2 := by
    obtain ⟨m, hm, hmlt⟩ :=
      Submodule.Quotient.norm_mk_lt (V.mkQL (S (lp.single 1 i 1))) (half_pos hε)
    refine ⟨⟨S (lp.single 1 i 1) - m, (Submodule.Quotient.eq V).mp hm.symm⟩, ?_⟩
    rw [sub_sub_cancel]
    refine hmlt.le.trans (add_le_add_left ?_ _)
    simpa [lp.norm_single zero_lt_one] using (V.mkQL ∘L S).le_opNorm (lp.single 1 i (1 : 𝕜))
  choose v hv using hex
  obtain ⟨L, hLrange, hnorm⟩ :=
    exists_range_le_norm_sub_le_of_lpOne S V (by positivity) hv
  have hle : (S.singularValue n : ℝ) ≤ ‖S - L‖ := by
    exact_mod_cast S.singularValue_le_nnnorm_sub ((Submodule.rank_mono hLrange).trans hV)
  calc (S.singularValue n : ℝ) ≤ ‖V.mkQL ∘L S‖ + ε / 2 := hle.trans hnorm
    _ < (‖V.mkQL ∘L S‖₊ : ℝ) + ε := by
      rw [coe_nnNorm]
      linarith

/-- Precomposing `T : E →L[𝕜] F` with any metric surjection out of scalar `ℓ¹` turns the
Kolmogorov numbers of `T` into approximation numbers, over any complete nontrivially normed
field. -/
theorem IsMetricSurjection.singularValue_comp_lpOne {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Q : lp (fun _ : ι ↦ 𝕜) 1 →L[𝕜] E} (hQ : Q.IsMetricSurjection) (T : E →L[𝕜] F) (n : ℕ) :
    (T ∘L Q).singularValue n = T.kolmogorovNumber n :=
  ((T ∘L Q).singularValue_lpOne_eq_kolmogorovNumber n).trans (hQ.kolmogorovNumber_comp T n)

end LpOneLifting

section UnitBallLifting

variable {𝕜 E F : Type*} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Pietsch's lifting identity.** Over a complete densely normed field and for a complete normed
domain `E`, the approximation numbers of `T ∘L TauCeti.unitBallSummation 𝕜 E` equal the Kolmogorov
numbers of `T`. -/
@[simp]
theorem singularValue_comp_unitBallSummation (T : E →L[𝕜] F) (n : ℕ) :
    (T ∘L TauCeti.unitBallSummation 𝕜 E).singularValue n = T.kolmogorovNumber n :=
  (TauCeti.isMetricSurjection_unitBallSummation 𝕜 E).singularValue_comp_lpOne T n

end UnitBallLifting

end ContinuousLinearMap
