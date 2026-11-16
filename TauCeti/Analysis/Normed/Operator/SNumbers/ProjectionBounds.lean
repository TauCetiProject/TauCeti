/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Gelfand
public import TauCeti.Analysis.Normed.Operator.SNumbers.Kolmogorov
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic

import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import TauCeti.Analysis.Normed.Module.KadecSnobar
import TauCeti.Analysis.Normed.Operator.SNumbers.Approximation

/-!
# Projection bounds between approximation, Gelfand, and Kolmogorov numbers

For every bounded linear operator `T : E →L[𝕜] F` over a nontrivially normed field, the Gelfand
numbers `cₙ(T)` and the Kolmogorov numbers `dₙ(T)` are bounded above by the approximation numbers
`aₙ(T)`: for any approximant `R` of rank at most `n`, both `cₙ(R)` and `dₙ(R)` vanish, so the
perturbative triangle bounds for `T = R + (T - R)` bound `cₙ(T)` and `dₙ(T)` by `‖T - R‖`.

Reversing these inequalities requires turning a small restriction `T|_M` (on a subspace `M ≤ E` of
codimension at most `n`) or a small quotient composition `V.mkQL ∘L T` (by a subspace `V ≤ F` of
dimension at most `n`) into an actual finite-rank approximant of `T`. Any bounded operator
`P : E →L[𝕜] E` of rank at most `n` with `id - P` mapping into `M` gives the approximant `T ∘L P`
with error at most `‖id - P‖ ‖T|_M‖ ≤ (1 + ‖P‖) ‖T|_M‖`; dually, any bounded projection
`P : F →L[𝕜] V` onto `V` gives the approximant `V.subtypeL ∘L P ∘L T` with error at most
`‖id - V.subtypeL ∘L P‖ ‖V.mkQL ∘L T‖ ≤ (1 + ‖P‖) ‖V.mkQL ∘L T‖`. On Hilbert spaces, orthogonal
projections have `‖id - P‖ ≤ 1`, recovering equality; on general normed spaces, norm bounds on `P`
control the multiplicative gap.

Over an `IsRCLikeNormedField` (in particular `ℝ` or `ℂ`), the Garling–Gordon and Kadec–Snobar
theorems (`TauCeti.Analysis.Normed.Module.KadecSnobar`) supply projections of norm at most
`√n + ε` and `√n`, yielding the universal upper bounds
`aₙ(T) ≤ (1 + √n) cₙ(T)`, `aₙ(T) ≤ (1 + √n) dₙ(T)`, and
`aₙ(T) ≤ (1 + √n) min (cₙ(T), dₙ(T))`. Because the approximation numbers dominate every s-number
sequence, the same bounds hold with `aₙ(T)` replaced by an arbitrary s-number sequence `s T n`,
and in particular `cₙ(T)` and `dₙ(T)` lie within a factor of `1 + √n` of each other.

## Main results

* `ContinuousLinearMap.gelfandNumber_le_singularValue`,
  `ContinuousLinearMap.kolmogorovNumber_le_singularValue`,
  `ContinuousLinearMap.max_gelfandNumber_kolmogorovNumber_le_singularValue`:
  `max (cₙ(T), dₙ(T)) ≤ aₙ(T)` over any nontrivially normed field.
* `ContinuousLinearMap.singularValue_le_nnnorm_id_sub_mul_nnnorm_comp_subtypeL`,
  `ContinuousLinearMap.singularValue_le_one_add_nnnorm_mul_nnnorm_comp_subtypeL`, and
  `singularValue_le_one_add_nnnorm_mul_nnnorm_comp_subtypeL_of_isIdempotentElem`:
  explicit upper bounds on `aₙ(T)` from `‖T|_M‖` and an operator or projection on `E`.
* `ContinuousLinearMap.singularValue_le_nnnorm_id_sub_subtypeL_comp_mul_nnnorm_mkQL_comp`,
  `ContinuousLinearMap.singularValue_le_one_add_nnnorm_mul_nnnorm_mkQL_comp`, and
  `singularValue_le_one_add_nnnorm_mul_nnnorm_mkQL_comp_of_isIdempotentElem`:
  explicit upper bounds on `aₙ(T)` in terms of `‖V.mkQL ∘L T‖` and a projection onto `V ≤ F`.
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

/-! ### Lower bounds by Gelfand and Kolmogorov numbers -/

/-- The `n`-th Gelfand number is bounded above by the `n`-th approximation number: `cₙ(T) ≤ aₙ(T)`.
Neither completeness nor Hausdorffness of the spaces is required. -/
theorem gelfandNumber_le_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    T.gelfandNumber n ≤ T.singularValue n := by
  refine le_singularValue_iff.mpr fun R hR ↦ ?_
  have h := R.gelfandNumber_add_le (T - R) n
  simpa [gelfandNumber_eq_zero_of_rank_le hR] using h

/-- The `n`-th Kolmogorov number is bounded above by the `n`-th approximation number:
`dₙ(T) ≤ aₙ(T)`. Neither completeness nor Hausdorffness of the spaces is required. -/
theorem kolmogorovNumber_le_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    T.kolmogorovNumber n ≤ T.singularValue n := by
  refine le_singularValue_iff.mpr fun R hR ↦ ?_
  have h := R.kolmogorovNumber_add_le (T - R) n
  simpa [kolmogorovNumber_eq_zero_of_rank_le hR] using h

/-- Both the `n`-th Gelfand number and the `n`-th Kolmogorov number are bounded above by the
`n`-th approximation number: `max (cₙ(T), dₙ(T)) ≤ aₙ(T)`. -/
theorem max_gelfandNumber_kolmogorovNumber_le_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    max (T.gelfandNumber n) (T.kolmogorovNumber n) ≤ T.singularValue n :=
  max_le (T.gelfandNumber_le_singularValue n) (T.kolmogorovNumber_le_singularValue n)

/-! ### Explicit approximation bounds from bounded projections -/

/-- If `P : E →L[𝕜] E` has rank at most `n` and `id - P` maps into a submodule `M ≤ E`, then
`aₙ(T) ≤ ‖id - P‖ ‖T|_M‖`. -/
theorem singularValue_le_nnnorm_id_sub_mul_nnnorm_comp_subtypeL (T : E →L[𝕜] F)
    {M : Submodule 𝕜 E} {P : E →L[𝕜] E} {n : ℕ} (hP : P.rank ≤ n)
    (hM : ∀ x, x - P x ∈ M) :
    T.singularValue n ≤ ‖ContinuousLinearMap.id 𝕜 E - P‖₊ * ‖T ∘L M.subtypeL‖₊ := by
  have hTP : (T ∘L P).rank ≤ n := by
    have h := (LinearMap.lift_rank_comp_le_right P.toLinearMap T.toLinearMap).trans
      (Cardinal.lift_le.mpr hP)
    rwa [Cardinal.lift_natCast, Cardinal.lift_le_nat_iff] at h
  let Q : E →L[𝕜] M := (ContinuousLinearMap.id 𝕜 E - P).codRestrict M hM
  have hQ : ‖Q‖₊ ≤ ‖ContinuousLinearMap.id 𝕜 E - P‖₊ :=
    opNNNorm_le_bound _ _ fun x ↦ (ContinuousLinearMap.id 𝕜 E - P).le_opNNNorm x
  have hMQ : M.subtypeL ∘L Q = ContinuousLinearMap.id 𝕜 E - P :=
    subtypeL_comp_codRestrict _ _ _
  have hsub : T - T ∘L P = (T ∘L M.subtypeL) ∘L Q := by
    rw [comp_assoc, hMQ, comp_sub, comp_id]
  calc
    T.singularValue n ≤ ‖T - T ∘L P‖₊ := T.singularValue_le_nnnorm_sub hTP
    _ = ‖(T ∘L M.subtypeL) ∘L Q‖₊ := by rw [hsub]
    _ ≤ ‖T ∘L M.subtypeL‖₊ * ‖Q‖₊ := opNNNorm_comp_le _ _
    _ ≤ ‖T ∘L M.subtypeL‖₊ * ‖ContinuousLinearMap.id 𝕜 E - P‖₊ := by gcongr
    _ = ‖ContinuousLinearMap.id 𝕜 E - P‖₊ * ‖T ∘L M.subtypeL‖₊ := mul_comm _ _

/-- If `P : E →L[𝕜] E` has rank at most `n` and `id - P` maps into a submodule `M ≤ E`, then
`aₙ(T) ≤ (1 + ‖P‖) ‖T|_M‖`. -/
theorem singularValue_le_one_add_nnnorm_mul_nnnorm_comp_subtypeL (T : E →L[𝕜] F)
    {M : Submodule 𝕜 E} {P : E →L[𝕜] E} {n : ℕ} (hP : P.rank ≤ n)
    (hM : ∀ x, x - P x ∈ M) :
    T.singularValue n ≤ (1 + ‖P‖₊) * ‖T ∘L M.subtypeL‖₊ := by
  refine (T.singularValue_le_nnnorm_id_sub_mul_nnnorm_comp_subtypeL hP hM).trans ?_
  gcongr
  refine (nnNorm_sub_le _ _).trans ?_
  gcongr
  exact_mod_cast norm_id_le

/-- If `P : E →L[𝕜] E` is a bounded idempotent with kernel `M` of codimension at most `n`, then
`aₙ(T) ≤ (1 + ‖P‖) ‖T|_M‖`. -/
theorem singularValue_le_one_add_nnnorm_mul_nnnorm_comp_subtypeL_of_isIdempotentElem
    (T : E →L[𝕜] F) {M : Submodule 𝕜 E} {P : E →L[𝕜] E} {n : ℕ}
    (hP : IsIdempotentElem P) (hker : P.ker = M) (hrank : Module.rank 𝕜 (E ⧸ M) ≤ n) :
    T.singularValue n ≤ (1 + ‖P‖₊) * ‖T ∘L M.subtypeL‖₊ := by
  have hPrank : P.rank ≤ n := by
    rw [← hker] at hrank
    have h := P.toLinearMap.quotKerEquivRange.symm.lift_rank_eq
    exact Cardinal.lift_le_nat_iff.mp (h.trans_le (Cardinal.lift_le_nat_iff.mpr hrank))
  refine T.singularValue_le_one_add_nnnorm_mul_nnnorm_comp_subtypeL hPrank fun x ↦ ?_
  rw [← hker, LinearMap.mem_ker, coe_coe, map_sub, ← mul_apply_eq_comp, hP.eq, sub_self]

/-- If `V ≤ F` has dimension at most `n` and `P : F →L[𝕜] V` restricts to the identity on `V`, then
`aₙ(T) ≤ ‖id - V.subtypeL ∘L P‖ ‖V.mkQL ∘L T‖`. -/
theorem singularValue_le_nnnorm_id_sub_subtypeL_comp_mul_nnnorm_mkQL_comp (T : E →L[𝕜] F)
    {V : Submodule 𝕜 F} {P : F →L[𝕜] V} {n : ℕ} (hV : Module.rank 𝕜 V ≤ n)
    (hP : ∀ v : V, P v = v) :
    T.singularValue n ≤
      ‖ContinuousLinearMap.id 𝕜 F - V.subtypeL ∘L P‖₊ * ‖V.mkQL ∘L T‖₊ := by
  let R : E →L[𝕜] F := V.subtypeL ∘L P ∘L T
  have hR : R.rank ≤ n :=
    (Submodule.rank_mono (LinearMap.range_comp_le_range _ V.subtype)).trans
      ((Submodule.range_subtype V).symm ▸ hV)
  let S : F →L[𝕜] F := ContinuousLinearMap.id 𝕜 F - V.subtypeL ∘L P
  have hker : V ≤ S.ker := by
    intro y hy
    simp [S, hP ⟨y, hy⟩]
  let D : F ⧸ V →L[𝕜] F := V.liftQL S hker
  have hD : ‖D‖₊ ≤ ‖S‖₊ := by exact_mod_cast V.norm_liftQL_le S hker
  have hsub : T - R = D ∘L (V.mkQL ∘L T) := by
    ext x
    simp [R, S, D]
  calc
    T.singularValue n ≤ ‖T - R‖₊ := T.singularValue_le_nnnorm_sub hR
    _ = ‖D ∘L (V.mkQL ∘L T)‖₊ := by rw [hsub]
    _ ≤ ‖D‖₊ * ‖V.mkQL ∘L T‖₊ := opNNNorm_comp_le _ _
    _ ≤ ‖S‖₊ * ‖V.mkQL ∘L T‖₊ := by gcongr

/-- If `V ≤ F` has dimension at most `n` and `P : F →L[𝕜] V` restricts to the identity on `V`, then
`aₙ(T) ≤ (1 + ‖P‖) ‖V.mkQL ∘L T‖`. -/
theorem singularValue_le_one_add_nnnorm_mul_nnnorm_mkQL_comp (T : E →L[𝕜] F)
    {V : Submodule 𝕜 F} {P : F →L[𝕜] V} {n : ℕ} (hV : Module.rank 𝕜 V ≤ n)
    (hP : ∀ v : V, P v = v) :
    T.singularValue n ≤ (1 + ‖P‖₊) * ‖V.mkQL ∘L T‖₊ := by
  refine (T.singularValue_le_nnnorm_id_sub_subtypeL_comp_mul_nnnorm_mkQL_comp hV hP).trans ?_
  gcongr
  refine (nnNorm_sub_le _ _).trans ?_
  gcongr
  · exact_mod_cast norm_id_le
  · exact (opNNNorm_comp_le _ _).trans
      (mul_le_of_le_one_left' (by exact_mod_cast V.norm_subtypeL_le))

/-- If `P : F →L[𝕜] F` is a bounded idempotent with range `V` of dimension at most `n`, then
`aₙ(T) ≤ (1 + ‖P‖) ‖V.mkQL ∘L T‖`. -/
theorem singularValue_le_one_add_nnnorm_mul_nnnorm_mkQL_comp_of_isIdempotentElem
    (T : E →L[𝕜] F) {V : Submodule 𝕜 F} {P : F →L[𝕜] F} {n : ℕ}
    (hP : IsIdempotentElem P) (hrange : P.range = V) (hV : Module.rank 𝕜 V ≤ n) :
    T.singularValue n ≤ (1 + ‖P‖₊) * ‖V.mkQL ∘L T‖₊ := by
  let Q : F →L[𝕜] V := P.codRestrict V fun y ↦ hrange ▸ LinearMap.mem_range_self _ y
  have hQid : ∀ v : V, Q v = v := by
    rintro ⟨y, hy⟩
    ext
    exact (LinearMap.IsIdempotentElem.mem_range_iff
      (IsIdempotentElem.toLinearMap hP)).mp (hrange.symm ▸ hy)
  have hQnorm : ‖Q‖₊ ≤ ‖P‖₊ := opNNNorm_le_bound _ _ fun y ↦ P.le_opNNNorm y
  refine (T.singularValue_le_one_add_nnnorm_mul_nnnorm_mkQL_comp hV hQid).trans ?_
  gcongr

end NontriviallyNormedField

/-! ### `(1 + √n)` projection bounds over `ℝ` or `ℂ` -/

section GelfandBound

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Gelfand projection bound.** Over an `IsRCLikeNormedField` (in particular `ℝ` or `ℂ`), the
`n`-th approximation number of `T` is at most `(1 + √n)` times its `n`-th Gelfand number:
`aₙ(T) ≤ (1 + √n) cₙ(T)`. -/
theorem singularValue_le_one_add_sqrt_mul_gelfandNumber (T : E →L[𝕜] F) (n : ℕ) :
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

/-- Over an `IsRCLikeNormedField`, the `n`-th Kolmogorov number is at most `(1 + √n)` times the
`n`-th Gelfand number: `dₙ(T) ≤ (1 + √n) cₙ(T)`. -/
theorem kolmogorovNumber_le_one_add_sqrt_mul_gelfandNumber (T : E →L[𝕜] F) (n : ℕ) :
    (T.kolmogorovNumber n : ℝ) ≤ (1 + √n) * T.gelfandNumber n :=
  (NNReal.coe_le_coe.mpr (T.kolmogorovNumber_le_singularValue n)).trans
    (T.singularValue_le_one_add_sqrt_mul_gelfandNumber n)

end GelfandBound

section KolmogorovBound

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Kolmogorov projection bound.** Over an `IsRCLikeNormedField` (in particular `ℝ` or `ℂ`), the
`n`-th approximation number of `T` is at most `(1 + √n)` times its `n`-th Kolmogorov number:
`aₙ(T) ≤ (1 + √n) dₙ(T)`. -/
theorem singularValue_le_one_add_sqrt_mul_kolmogorovNumber (T : E →L[𝕜] F) (n : ℕ) :
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
  refine (T.singularValue_le_one_add_nnnorm_mul_nnnorm_mkQL_comp hV hP).trans ?_
  gcongr

/-- Over an `IsRCLikeNormedField`, the `n`-th Gelfand number is at most `(1 + √n)` times the
`n`-th Kolmogorov number: `cₙ(T) ≤ (1 + √n) dₙ(T)`. -/
theorem gelfandNumber_le_one_add_sqrt_mul_kolmogorovNumber (T : E →L[𝕜] F) (n : ℕ) :
    (T.gelfandNumber n : ℝ) ≤ (1 + √n) * T.kolmogorovNumber n :=
  (NNReal.coe_le_coe.mpr (T.gelfandNumber_le_singularValue n)).trans
    (T.singularValue_le_one_add_sqrt_mul_kolmogorovNumber n)

end KolmogorovBound

section CombinedBound

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Combined projection bound.** Over an `IsRCLikeNormedField` (in particular `ℝ` or `ℂ`),
`aₙ(T) ≤ (1 + √n) min (cₙ(T), dₙ(T))`. -/
theorem singularValue_le_one_add_sqrt_mul_min_gelfandNumber_kolmogorovNumber
    (T : E →L[𝕜] F) (n : ℕ) :
    (T.singularValue n : ℝ) ≤
      (1 + √n) * min (T.gelfandNumber n : ℝ) (T.kolmogorovNumber n) := by
  rw [mul_min_of_nonneg _ _ (by positivity)]
  exact le_min (T.singularValue_le_one_add_sqrt_mul_gelfandNumber n)
    (T.singularValue_le_one_add_sqrt_mul_kolmogorovNumber n)

end CombinedBound

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
