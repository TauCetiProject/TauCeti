/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Gelfand
public import TauCeti.Analysis.Normed.Operator.SNumbers.Kolmogorov

import TauCeti.Analysis.Normed.Module.KadecSnobar
import TauCeti.Analysis.Normed.Operator.SNumbers.Approximation
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Projection
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.SeparationQuotient

/-!
# Projection bounds between approximation, Gelfand, and Kolmogorov numbers

For every bounded linear operator `T : E →L[𝕜] F` over a nontrivially normed field, both the
Gelfand numbers `cₙ(T)` and the Kolmogorov numbers `dₙ(T)` are bounded above by the approximation
numbers `aₙ(T)` (`ContinuousLinearMap.gelfandNumber_le_singularValue`,
`ContinuousLinearMap.kolmogorovNumber_le_singularValue`), so `max (cₙ(T), dₙ(T)) ≤ aₙ(T)`.

Reversing these inequalities uses the finite-rank projection bounds from
`TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Projection` together with the Garling–Gordon
and Kadec–Snobar projection theorems (`TauCeti.Analysis.Normed.Module.KadecSnobar`). Over an
`IsRCLikeNormedField` (in particular `ℝ` or `ℂ`) and between arbitrary seminormed spaces, passing
to the normed separation quotients (`SeparationQuotient`) lets us apply those projection theorems:
in the normed separation quotients, closed subspaces of codimension at most `n` are, for each
`ε > 0`, kernels of bounded projections of norm at most `√n + ε`, while subspaces of dimension at
most `n` are ranges of bounded projections of norm at most `√n`. This yields the universal upper
bounds `aₙ(T) ≤ (1 + √n) cₙ(T)`, `aₙ(T) ≤ (1 + √n) dₙ(T)`, and
`aₙ(T) ≤ (1 + √n) min (cₙ(T), dₙ(T))`. Because the approximation numbers dominate every s-number
sequence, the same bounds hold with `aₙ(T)` replaced by an arbitrary s-number sequence `s T n`,
and in particular `cₙ(T)` and `dₙ(T)` lie within a factor of `1 + √n` of each other.

## Main results

* `ContinuousLinearMap.max_gelfandNumber_kolmogorovNumber_le_singularValue`:
  `max (cₙ(T), dₙ(T)) ≤ aₙ(T)` over any nontrivially normed field.
* `ContinuousLinearMap.singularValue_le_one_add_sqrt_mul_gelfandNumber`:
  `aₙ(T) ≤ (1 + √n) cₙ(T)` over an `IsRCLikeNormedField`.
* `ContinuousLinearMap.singularValue_le_one_add_sqrt_mul_kolmogorovNumber`:
  `aₙ(T) ≤ (1 + √n) dₙ(T)` over an `IsRCLikeNormedField`.
* `ContinuousLinearMap.singularValue_le_one_add_sqrt_mul_min_gelfandNumber_kolmogorovNumber`:
  `aₙ(T) ≤ (1 + √n) min (cₙ(T), dₙ(T))` over an `IsRCLikeNormedField`.
* `ContinuousLinearMap.gelfandNumber_le_one_add_sqrt_mul_kolmogorovNumber`,
  `ContinuousLinearMap.kolmogorovNumber_le_one_add_sqrt_mul_gelfandNumber`:
  mutual `(1 + √n)` comparison between Gelfand and Kolmogorov numbers.
* `TauCeti.SNumbers.IsSNumberSequence.le_one_add_sqrt_mul_gelfandNumber`,
  `TauCeti.SNumbers.IsSNumberSequence.le_one_add_sqrt_mul_kolmogorovNumber`,
  `TauCeti.SNumbers.IsSNumberSequence.le_one_add_sqrt_mul_min_gelfandNumber_kolmogorovNumber`:
  universal `(1 + √n)` upper bounds for an arbitrary s-number sequence.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), 1.5.5, 1.7.17, and
  2.10.2.
* D. J. H. Garling and Y. Gordon, *Relations between some constants associated with finite
  dimensional Banach spaces*, Israel J. Math. **9** (1971), 346–361.
* M. I. Kadec and M. G. Snobar, *Certain functionals on the Minkowski compactum*, Mat. Zametki
  **10** (1971), 453–457.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Inequalities.lean`: an earlier Lean formalization of projection inequalities between
  s-numbers.
-/

public section

open Module
open scoped NNReal

namespace ContinuousLinearMap

section NontriviallyNormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Both the `n`-th Gelfand number and the `n`-th Kolmogorov number are bounded above by the
`n`-th approximation number: `max (cₙ(T), dₙ(T)) ≤ aₙ(T)`. -/
theorem max_gelfandNumber_kolmogorovNumber_le_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    max (T.gelfandNumber n) (T.kolmogorovNumber n) ≤ T.singularValue n :=
  max_le (T.gelfandNumber_le_singularValue n) (T.kolmogorovNumber_le_singularValue n)

end NontriviallyNormedField

/-! ### `(1 + √n)` projection bounds over `ℝ` or `ℂ` -/

section NormedSteppingStones

private theorem singularValue_le_one_add_sqrt_mul_gelfandNumber_of_normed
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (n : ℕ) :
    (T.singularValue n : ℝ) ≤ (1 + √n) * T.gelfandNumber n := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  have hpos : (0 : ℝ≥0) < 1 + NNReal.sqrt n := by positivity
  suffices h : T.singularValue n / (1 + NNReal.sqrt n) ≤ T.gelfandNumber n by
    have hmul := (div_le_iff₀' hpos).mp h
    simpa [Real.coe_sqrt] using NNReal.coe_le_coe.mpr hmul
  refine le_gelfandNumber_iff.mpr fun M hM hrank ↦ (div_le_iff₀' hpos).mpr ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  have : FiniteDimensional 𝕜 (E ⧸ M) :=
    Module.rank_lt_aleph0_iff.mp (hrank.trans_lt Cardinal.natCast_lt_aleph0)
  have hfin : finrank 𝕜 (E ⧸ M) ≤ n :=
    Nat.cast_le.mp ((finrank_eq_rank 𝕜 (E ⧸ M)).trans_le hrank)
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  set c : ℝ := ‖T ∘L M.subtypeL‖
  set ε : ℝ := δ / (c + 1)
  have : 0 ≤ c := norm_nonneg _
  have hε : 0 < ε := div_pos hδ (by positivity)
  obtain ⟨P, hP, hker, hPnorm⟩ :=
    M.exists_isIdempotentElem_ker_eq_norm_le_sqrt_finrank_add hM hε
  have hle : (T.singularValue n : ℝ) ≤ (1 + ‖P‖) * c := by
    exact_mod_cast
      T.singularValue_le_one_add_nnnorm_mul_nnnorm_comp_subtypeL_of_isIdempotentElem hP hker hrank
  have hsqrt : √(finrank 𝕜 (E ⧸ M)) ≤ √n := Real.sqrt_le_sqrt (Nat.cast_le.mpr hfin)
  have hεc : ε * c ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  calc
    (T.singularValue n : ℝ) ≤ (1 + ‖P‖) * c := hle
    _ ≤ (1 + (√n + ε)) * c := by gcongr; linarith
    _ = (1 + √n) * c + ε * c := by ring
    _ ≤ (1 + √n) * c + δ := by linarith

private theorem singularValue_le_one_add_sqrt_mul_kolmogorovNumber_of_normed
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (n : ℕ) :
    (T.singularValue n : ℝ) ≤ (1 + √n) * T.kolmogorovNumber n := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  have hpos : (0 : ℝ≥0) < 1 + NNReal.sqrt n := by positivity
  suffices h : T.singularValue n / (1 + NNReal.sqrt n) ≤ T.kolmogorovNumber n by
    have hmul := (div_le_iff₀' hpos).mp h
    simpa [Real.coe_sqrt] using NNReal.coe_le_coe.mpr hmul
  refine le_kolmogorovNumber_iff.mpr fun V hV ↦ (div_le_iff₀' hpos).mpr ?_
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (hV.trans_lt Cardinal.natCast_lt_aleph0)
  have hfin : finrank 𝕜 V ≤ n :=
    Nat.cast_le.mp ((finrank_eq_rank 𝕜 V).trans_le hV)
  obtain ⟨P, hP, hPnorm⟩ := V.exists_projection_norm_le_sqrt_finrank
  have hPnn : ‖P‖₊ ≤ NNReal.sqrt n := by
    rw [← NNReal.coe_le_coe, coe_nnNorm, Real.coe_sqrt]
    exact hPnorm.trans (Real.sqrt_le_sqrt (Nat.cast_le.mpr hfin))
  refine (T.singularValue_le_one_add_nnnorm_mul_nnnorm_mkQL_comp_of_proj hV hP).trans ?_
  gcongr

end NormedSteppingStones

section IsRCLikeNormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Gelfand projection bound.** Over an `IsRCLikeNormedField` (in particular `ℝ` or `ℂ`), the
`n`-th approximation number of `T` is at most `(1 + √n)` times its `n`-th Gelfand number:
`aₙ(T) ≤ (1 + √n) cₙ(T)`. -/
theorem singularValue_le_one_add_sqrt_mul_gelfandNumber (T : E →L[𝕜] F) (n : ℕ) :
    (T.singularValue n : ℝ) ≤ (1 + √n) * T.gelfandNumber n := by
  let s := SeparationQuotient.outCLM 𝕜 E
  have hcs : (T ∘L s).gelfandNumber n ≤ T.gelfandNumber n * ‖s‖₊ := by
    simpa using T.gelfandNumber_comp_add_le_mul s n 0
  have hc : (T ∘L s).gelfandNumber n ≤ T.gelfandNumber n :=
    hcs.trans (mul_le_of_le_one_right' SeparationQuotient.nnNorm_outCLM_le)
  calc
    (T.singularValue n : ℝ) = ((T ∘L s).singularValue n : ℝ) := by
      rw [T.singularValue_comp_outCLM]
    _ ≤ (1 + √n) * (T ∘L s).gelfandNumber n :=
      singularValue_le_one_add_sqrt_mul_gelfandNumber_of_normed (T ∘L s) n
    _ ≤ (1 + √n) * T.gelfandNumber n := by gcongr

/-- Over an `IsRCLikeNormedField`, the `n`-th Kolmogorov number is at most `(1 + √n)` times the
`n`-th Gelfand number: `dₙ(T) ≤ (1 + √n) cₙ(T)`. -/
theorem kolmogorovNumber_le_one_add_sqrt_mul_gelfandNumber (T : E →L[𝕜] F) (n : ℕ) :
    (T.kolmogorovNumber n : ℝ) ≤ (1 + √n) * T.gelfandNumber n :=
  (NNReal.coe_le_coe.mpr (T.kolmogorovNumber_le_singularValue n)).trans
    (T.singularValue_le_one_add_sqrt_mul_gelfandNumber n)

/-- **Kolmogorov projection bound.** Over an `IsRCLikeNormedField` (in particular `ℝ` or `ℂ`), the
`n`-th approximation number of `T` is at most `(1 + √n)` times its `n`-th Kolmogorov number:
`aₙ(T) ≤ (1 + √n) dₙ(T)`. -/
theorem singularValue_le_one_add_sqrt_mul_kolmogorovNumber (T : E →L[𝕜] F) (n : ℕ) :
    (T.singularValue n : ℝ) ≤ (1 + √n) * T.kolmogorovNumber n := by
  let q := SeparationQuotient.mkCLM 𝕜 F
  have hd : (q ∘L T).kolmogorovNumber n ≤ T.kolmogorovNumber n :=
    (q.kolmogorovNumber_comp_le_left T n).trans
      (mul_le_of_le_one_left' SeparationQuotient.nnNorm_mkCLM_le)
  calc
    (T.singularValue n : ℝ) = ((q ∘L T).singularValue n : ℝ) := by
      rw [T.singularValue_mkCLM_comp]
    _ ≤ (1 + √n) * (q ∘L T).kolmogorovNumber n :=
      singularValue_le_one_add_sqrt_mul_kolmogorovNumber_of_normed (q ∘L T) n
    _ ≤ (1 + √n) * T.kolmogorovNumber n := by gcongr

/-- Over an `IsRCLikeNormedField`, the `n`-th Gelfand number is at most `(1 + √n)` times the
`n`-th Kolmogorov number: `cₙ(T) ≤ (1 + √n) dₙ(T)`. -/
theorem gelfandNumber_le_one_add_sqrt_mul_kolmogorovNumber (T : E →L[𝕜] F) (n : ℕ) :
    (T.gelfandNumber n : ℝ) ≤ (1 + √n) * T.kolmogorovNumber n :=
  (NNReal.coe_le_coe.mpr (T.gelfandNumber_le_singularValue n)).trans
    (T.singularValue_le_one_add_sqrt_mul_kolmogorovNumber n)

/-- **Combined projection bound.** Over an `IsRCLikeNormedField` (in particular `ℝ` or `ℂ`),
`aₙ(T) ≤ (1 + √n) min (cₙ(T), dₙ(T))`. -/
theorem singularValue_le_one_add_sqrt_mul_min_gelfandNumber_kolmogorovNumber
    (T : E →L[𝕜] F) (n : ℕ) :
    (T.singularValue n : ℝ) ≤
      (1 + √n) * min (T.gelfandNumber n : ℝ) (T.kolmogorovNumber n) := by
  rw [mul_min_of_nonneg _ _ (by positivity)]
  exact le_min (T.singularValue_le_one_add_sqrt_mul_gelfandNumber n)
    (T.singularValue_le_one_add_sqrt_mul_kolmogorovNumber n)

end IsRCLikeNormedField

end ContinuousLinearMap

universe u

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]

/-- Every s-number sequence over an `IsRCLikeNormedField` is bounded above by `(1 + √n)` times the
Gelfand numbers: `s T n ≤ (1 + √n) cₙ(T)`. -/
theorem IsSNumberSequence.le_one_add_sqrt_mul_gelfandNumber {s : SNumberFamily 𝕜}
    (hs : IsSNumberSequence s) {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) :
    (s T n : ℝ) ≤ (1 + √n) * T.gelfandNumber n :=
  (NNReal.coe_le_coe.mpr (hs.le_singularValue T n)).trans
    (T.singularValue_le_one_add_sqrt_mul_gelfandNumber n)

/-- Every s-number sequence over an `IsRCLikeNormedField` is bounded above by `(1 + √n)` times the
Kolmogorov numbers: `s T n ≤ (1 + √n) dₙ(T)`. -/
theorem IsSNumberSequence.le_one_add_sqrt_mul_kolmogorovNumber {s : SNumberFamily 𝕜}
    (hs : IsSNumberSequence s) {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) :
    (s T n : ℝ) ≤ (1 + √n) * T.kolmogorovNumber n :=
  (NNReal.coe_le_coe.mpr (hs.le_singularValue T n)).trans
    (T.singularValue_le_one_add_sqrt_mul_kolmogorovNumber n)

/-- Every s-number sequence over an `IsRCLikeNormedField` is bounded above by
`(1 + √n) min (cₙ(T), dₙ(T))`. -/
theorem IsSNumberSequence.le_one_add_sqrt_mul_min_gelfandNumber_kolmogorovNumber
    {s : SNumberFamily 𝕜} (hs : IsSNumberSequence s) {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) :
    (s T n : ℝ) ≤ (1 + √n) * min (T.gelfandNumber n : ℝ) (T.kolmogorovNumber n) :=
  (NNReal.coe_le_coe.mpr (hs.le_singularValue T n)).trans
    (T.singularValue_le_one_add_sqrt_mul_min_gelfandNumber_kolmogorovNumber n)

end TauCeti.SNumbers
