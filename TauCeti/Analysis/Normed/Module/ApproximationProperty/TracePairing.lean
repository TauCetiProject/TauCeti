/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.ApproximationProperty.Basic
public import TauCeti.Analysis.Normed.Module.TensorProduct.Approximable
public import TauCeti.Analysis.Normed.Module.TensorProduct.IntegralBilinearForm
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.Normed.Module.ApproximationProperty.TensorProduct
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.Basic
import TauCeti.Analysis.Normed.Module.TensorProduct.Series
import TauCeti.Analysis.Normed.Operator.Completion
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Dual

/-!
# The trace pairing and the metric approximation property

For a normed space `E` over `ℝ` or `ℂ`, the **trace pairing**
`Θ_E : E* ⊗̂π E →L[𝕜] (E ⊗̂ε E*)*` is the contraction determined on pure tensors by
`Θ_E (f ⊗ x) (y ⊗ g) = f y * g x`. Under the isometric identification of `E* ⊗ε E` with the
finite-rank operators on `E`, an algebraic tensor `w ∈ E ⊗ E*` corresponds to the finite-rank
operator `T_w`, and `Θ_E u w` is the trace `tr ((1 ⊗ T_w) u)` of `u` composed with `T_w`.
Thus `‖Θ_E u‖` is the supremum of `|tr ((1 ⊗ T) u)|` over the finite-rank contractions `T`.

This file proves Grothendieck's metric criterion for the metric approximation property (MAP):
`E` has the MAP iff `|tr u| ≤ ‖Θ_E u‖` for every `u ∈ E* ⊗̂π E`. In particular, if `Θ_E` is an
isometry, then `E` has the MAP. Conversely, when `E` is reflexive, the MAP makes `Θ_E` an
isometry: the dual of `E* ⊗̂π E` consists of the bounded bilinear forms on `E* × E`, which for
reflexive `E` are all of the form `(f, x) ↦ f (T x)` with `‖T‖` equal to the norm of the form.

The forward implication approximates `u = ∑ n, f n ⊗ x n`, with `∑ n, ‖f n‖ < ∞` and `x n → 0`,
by `(1 ⊗ R) u` for a finite-rank contraction `R` close to the identity on `{x n}`. For the
converse, Grothendieck's compactness lemma places any compact set in the closed convex hull of a
null sequence `x`. If the identity is not a limit of finite-rank contractions uniformly along `x`,
then Hahn–Banach separation in `C₀(ℕ, E)`, whose dual is `ℓ¹(ℕ, E*)`, produces
`u = ∑ n, f n ⊗ x n` with `‖Θ_E u‖ < re (tr u)`.

## Main definitions

* `TauCeti.CompletedProjectiveTensor.tracePairing 𝕜 E`: the trace pairing
  `E* ⊗̂π E →L[𝕜] (E ⊗̂ε E*)*`.

## Main results

* `TauCeti.CompletedProjectiveTensor.tracePairing_coe_tmul_coe_tmul`: the defining formula
  `Θ_E (f ⊗ x) (y ⊗ g) = f y * g x`.
* `TauCeti.CompletedProjectiveTensor.norm_tracePairing_le`: `Θ_E` is a contraction.
* `TauCeti.CompletedProjectiveTensor.tracePairing_apply_coe_comm`: on algebraic tensors, `Θ_E u` is
  the trace of `u` composed with the corresponding finite-rank operator.
* `TauCeti.hasMetricApproximationProperty_iff_norm_trace_le`: the MAP holds iff
  `‖tr u‖ ≤ ‖Θ_E u‖` for every `u`.
* `TauCeti.hasMetricApproximationProperty_of_norm_le_norm_tracePairing`: if `Θ_E` is isometric,
  then `E` has the MAP.
* `TauCeti.HasMetricApproximationProperty.norm_tracePairing_eq`: for reflexive `E`, the MAP makes
  `Θ_E` isometric.
* `TauCeti.hasMetricApproximationProperty_iff_norm_tracePairing_eq`: for reflexive `E`, the MAP
  holds iff `Θ_E` is isometric.

## References

* A. Grothendieck, *Produits tensoriels topologiques et espaces nucléaires*, Mem. Amer. Math.
  Soc. **16** (1955), Chap. I, §5.
* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, Chapter 4.
-/

public section

open Filter Set RCLike
open scoped TensorProduct Topology ZeroAtInfty

namespace TauCeti.CompletedProjectiveTensor

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The functional on `E ⊗̂ε E*` induced by the rank-one integral form
`(y, g) ↦ f y * g x`. -/
private noncomputable def tracePairingAux (f : StrongDual 𝕜 E) (x : E) :
    StrongDual 𝕜 (CompletedInjectiveTensor 𝕜 E (StrongDual 𝕜 E)) :=
  (IntegralBilinearForm.liftIsometry 𝕜 E (StrongDual 𝕜 E)
    (IntegralBilinearForm.smulRight f (NormedSpace.inclusionInDoubleDual 𝕜 E x))).fromCompletion

@[simp]
private theorem tracePairingAux_coe_tmul (f : StrongDual 𝕜 E) (x y : E) (g : StrongDual 𝕜 E) :
    tracePairingAux f x (⟨y ⊗ₜ g⟩ : InjectiveTensor 𝕜 E (StrongDual 𝕜 E)) = f y * g x := by
  simp [tracePairingAux, ContinuousLinearMap.fromCompletion_apply_coe,
    IntegralBilinearForm.liftIsometry_apply_tmul]

private theorem norm_tracePairingAux_le (f : StrongDual 𝕜 E) (x : E) :
    ‖tracePairingAux f x‖ ≤ ‖f‖ * ‖x‖ := by
  rw [tracePairingAux, ContinuousLinearMap.norm_fromCompletion, LinearIsometryEquiv.norm_map,
    IntegralBilinearForm.norm_smulRight]
  gcongr
  exact NormedSpace.double_dual_bound 𝕜 E x

/-- The bounded bilinear map `(f, x) ↦ (y ⊗ g ↦ f y * g x)` inducing the trace pairing. -/
private noncomputable def tracePairingBilin :
    StrongDual 𝕜 E →L[𝕜] E →L[𝕜] StrongDual 𝕜 (CompletedInjectiveTensor 𝕜 E (StrongDual 𝕜 E)) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 tracePairingAux
      (fun f f' x ↦ CompletedInjectiveTensor.continuousLinearMap_ext fun y g ↦ by
        simp [add_mul])
      (fun c f x ↦ CompletedInjectiveTensor.continuousLinearMap_ext fun y g ↦ by
        simp [mul_assoc])
      (fun f x x' ↦ CompletedInjectiveTensor.continuousLinearMap_ext fun y g ↦ by
        simp [mul_add])
      (fun c f x ↦ CompletedInjectiveTensor.continuousLinearMap_ext fun y g ↦ by
        simp [mul_left_comm]))
    1 fun f x ↦ by simpa using norm_tracePairingAux_le f x

variable (𝕜 E) in
/-- **The trace pairing** `Θ_E : E* ⊗̂π E →L[𝕜] (E ⊗̂ε E*)*`, the contraction determined by
`Θ_E (f ⊗ x) (y ⊗ g) = f y * g x`. -/
noncomputable def tracePairing :
    CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E →L[𝕜]
      StrongDual 𝕜 (CompletedInjectiveTensor 𝕜 E (StrongDual 𝕜 E)) :=
  liftIsometry 𝕜 (StrongDual 𝕜 E) E _ tracePairingBilin

/-- The defining formula of the trace pairing: `Θ_E (f ⊗ x) (y ⊗ g) = f y * g x`. -/
@[simp]
theorem tracePairing_coe_tmul_coe_tmul (f : StrongDual 𝕜 E) (x y : E) (g : StrongDual 𝕜 E) :
    tracePairing 𝕜 E (⟨f ⊗ₜ x⟩ : ProjectiveTensor 𝕜 (StrongDual 𝕜 E) E)
      (⟨y ⊗ₜ g⟩ : InjectiveTensor 𝕜 E (StrongDual 𝕜 E)) = f y * g x := by
  simp [tracePairing, tracePairingBilin]

/-- The trace pairing is a contraction. -/
theorem norm_tracePairing_le : ‖tracePairing 𝕜 E‖ ≤ 1 := by
  rw [tracePairing, LinearIsometryEquiv.norm_map]
  exact LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- On the algebraic tensor `comm v ∈ E ⊗ E*`, the trace pairing evaluates the trace of `u`
composed with the finite-rank operator `T_v : x ↦ ∑ fᵢ x • yᵢ` represented by
`v = ∑ fᵢ ⊗ yᵢ ∈ E* ⊗ E`. -/
theorem tracePairing_apply_coe_comm (u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E)
    (v : StrongDual 𝕜 E ⊗[𝕜] E) :
    tracePairing 𝕜 E u
        (⟨TensorProduct.comm 𝕜 (StrongDual 𝕜 E) E v⟩ : InjectiveTensor 𝕜 E (StrongDual 𝕜 E)) =
      trace 𝕜 E (mapL (.id 𝕜 _) (TensorProduct.toOperator v) u) := by
  have h : ContinuousLinearMap.apply 𝕜 𝕜
        ((⟨TensorProduct.comm 𝕜 (StrongDual 𝕜 E) E v⟩ : InjectiveTensor 𝕜 E (StrongDual 𝕜 E)) :
          CompletedInjectiveTensor 𝕜 E (StrongDual 𝕜 E)) ∘L tracePairing 𝕜 E =
      trace 𝕜 E ∘L mapL (.id 𝕜 _) (TensorProduct.toOperator v) := by
    refine continuousLinearMap_ext fun f x ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, mapL_coe,
      ProjectiveTensor.mapL_tmul, ContinuousLinearMap.id_apply, trace_coe_tmul]
    induction v with
    | tmul g y => simp [mul_comm]
    | add v v' hv hv' =>
      simp only [map_add, InjectiveTensor.mk_add, UniformSpace.Completion.coe_add,
        _root_.add_apply, hv, hv']
  exact congr($h u)

/-- The trace of `u` composed with a finite-rank operator `T` is bounded by `‖Θ_E u‖ * ‖T‖`. -/
theorem norm_trace_mapL_le_of_hasFiniteRange
    (u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E) {T : E →L[𝕜] E}
    (hT : T.toLinearMap.HasFiniteRange) :
    ‖trace 𝕜 E (mapL (.id 𝕜 _) T u)‖ ≤ ‖tracePairing 𝕜 E u‖ * ‖T‖ := by
  obtain ⟨⟨v⟩, hv⟩ := (InjectiveTensor.mem_range_toOperator_iff T).2 hT
  simp only [LinearIsometry.coe_toLinearMap, InjectiveTensor.toOperator_mk] at hv
  subst hv
  rw [← tracePairing_apply_coe_comm]
  exact ((tracePairing 𝕜 E u).le_opNorm _).trans_eq
    (by rw [UniformSpace.Completion.norm_coe, InjectiveTensor.norm_mk_comm])

/-- A bound `C` on the real part of the trace of `u` composed with every finite-rank contraction is
nonnegative, since the zero operator is one. -/
private theorem nonneg_of_forall_re_trace_mapL_le
    {u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E} {C : ℝ}
    (h : ∀ T : E →L[𝕜] E, T.toLinearMap.HasFiniteRange → ‖T‖ ≤ 1 →
      re (trace 𝕜 E (mapL (.id 𝕜 _) T u)) ≤ C) :
    0 ≤ C := by
  simpa using h 0 LinearMap.HasFiniteRange.zero (by simp)

/-- Rescaling: if the real part of the trace of `u` composed with every finite-rank contraction
is at most `C`, then `|tr ((1 ⊗ T) u)| ≤ C * ‖T‖` for every finite-rank `T`. -/
private theorem norm_trace_mapL_le_of_forall_re_le
    {u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E} {C : ℝ}
    (h : ∀ T : E →L[𝕜] E, T.toLinearMap.HasFiniteRange → ‖T‖ ≤ 1 →
      re (trace 𝕜 E (mapL (.id 𝕜 _) T u)) ≤ C)
    {T : E →L[𝕜] E} (hT : T.toLinearMap.HasFiniteRange) :
    ‖trace 𝕜 E (mapL (.id 𝕜 _) T u)‖ ≤ C * ‖T‖ := by
  set z := trace 𝕜 E (mapL (.id 𝕜 _) T u) with hz_def
  rcases eq_or_ne z 0 with hz | hz
  · rw [hz, norm_zero]
    exact mul_nonneg (nonneg_of_forall_re_trace_mapL_le h) (norm_nonneg _)
  rcases eq_or_ne T 0 with rfl | hT0
  · simp [z] at hz
  -- Rescale `T` to a contraction `c • T` with `tr ((1 ⊗ c • T) u) = ‖z‖ / ‖T‖ ≥ 0`.
  have hTn : 0 < ‖T‖ := norm_pos_iff.2 hT0
  set c : 𝕜 := (starRingEnd 𝕜) z / ((‖z‖ * ‖T‖ : ℝ) : 𝕜)
  have hc : ‖c‖ * ‖T‖ = 1 := by
    simp only [c, norm_div, RCLike.norm_conj, RCLike.norm_ofReal,
      abs_of_pos (mul_pos (norm_pos_iff.2 hz) hTn)]
    field_simp
  have hcz : c * z = ((‖z‖ / ‖T‖ : ℝ) : 𝕜) := by
    simp only [c, div_mul_eq_mul_div, RCLike.conj_mul]
    push_cast
    field_simp
  have hS := h (c • T) (by simpa using hT.smul c) (by rw [norm_smul, hc])
  simp only [mapL_smul_right, _root_.smul_apply, map_smul, smul_eq_mul, ← hz_def, hcz,
    RCLike.ofReal_re] at hS
  rwa [div_le_iff₀ hTn] at hS

/-- If the real part of the trace of `u` composed with every finite-rank contraction is at most
`C`, then `‖Θ_E u‖ ≤ C`. -/
theorem norm_tracePairing_le_of_forall_re_le
    {u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E} {C : ℝ}
    (h : ∀ T : E →L[𝕜] E, T.toLinearMap.HasFiniteRange → ‖T‖ ≤ 1 →
      re (trace 𝕜 E (mapL (.id 𝕜 _) T u)) ≤ C) :
    ‖tracePairing 𝕜 E u‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ (nonneg_of_forall_re_trace_mapL_le h) fun w ↦ ?_
  induction w using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih w =>
    -- An algebraic tensor `w = comm v` pairs with `u` through the finite-rank operator of `v`.
    obtain ⟨w⟩ := w
    set v := TensorProduct.comm 𝕜 E (StrongDual 𝕜 E) w
    have hw : TensorProduct.comm 𝕜 (StrongDual 𝕜 E) E v = w := by simp [v]
    rw [← hw, UniformSpace.Completion.norm_coe, InjectiveTensor.norm_mk_comm,
      tracePairing_apply_coe_comm]
    exact norm_trace_mapL_le_of_forall_re_le h (by
      simpa using InjectiveTensor.hasFiniteRange_toOperator (E := E) (F := E) ⟨v⟩)

end TauCeti.CompletedProjectiveTensor

/-! ### The metric criterion -/

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open CompletedProjectiveTensor

/-- Under the metric approximation property, the trace of `u` composed with any bounded operator
`T` is bounded by `‖Θ_E u‖ * ‖T‖`; without it, this holds for finite-rank `T`
(`CompletedProjectiveTensor.norm_trace_mapL_le_of_hasFiniteRange`). -/
theorem HasMetricApproximationProperty.norm_trace_mapL_le
    (hE : HasMetricApproximationProperty 𝕜 E)
    (u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E) (T : E →L[𝕜] E) :
    ‖trace 𝕜 E (mapL (.id 𝕜 _) T u)‖ ≤ ‖tracePairing 𝕜 E u‖ * ‖T‖ := by
  obtain ⟨f, x, hu, hf, hx⟩ := exists_hasSum_tmul_tendsto_zero u
  have hTx : Tendsto (fun n ↦ T (x n)) atTop (𝓝 0) := by
    rw [← map_zero T]
    exact (T.continuous.tendsto 0).comp hx
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  set S := ∑' n, ‖f n‖
  set δ := ε / (S + 1) with hδ_def
  have hδ : 0 < δ := by positivity
  -- A finite-rank contraction `R` within `δ` of the identity on `{T (x n)} ∪ {0}`.
  obtain ⟨R, hR, hR1, hRx⟩ :=
    hasBoundedApproximationPropertyWith_iff.1 (hasMetricApproximationProperty_iff.1 hE) _
      hTx.isCompact_insert_range δ hδ
  have hsum : HasSum (fun n ↦ f n (T (x n) - R (T (x n))))
      (trace 𝕜 E (mapL (.id 𝕜 _) T u) - trace 𝕜 E (mapL (.id 𝕜 _) (R ∘L T) u)) := by
    simpa using (hasSum_trace_mapL hu T).sub (hasSum_trace_mapL hu (R ∘L T))
  have hbound (n : ℕ) : ‖f n (T (x n) - R (T (x n)))‖ ≤ δ * ‖f n‖ := by
    have hn : ‖T (x n) - R (T (x n))‖ ≤ δ := by
      rw [norm_sub_rev]
      exact (hRx _ (mem_insert_of_mem _ (mem_range_self n))).le
    calc ‖f n (T (x n) - R (T (x n)))‖ ≤ ‖f n‖ * ‖T (x n) - R (T (x n))‖ := (f n).le_opNorm _
      _ ≤ ‖f n‖ * δ := by gcongr
      _ = δ * ‖f n‖ := mul_comm _ _
  have hdiff := hsum.norm_le_of_bounded (hf.hasSum.mul_left δ) hbound
  have hRT : ‖trace 𝕜 E (mapL (.id 𝕜 _) (R ∘L T) u)‖ ≤ ‖tracePairing 𝕜 E u‖ * ‖T‖ := by
    refine (norm_trace_mapL_le_of_hasFiniteRange u
      (by simpa using hR.comp_right T.toLinearMap)).trans ?_
    gcongr
    have hR1' : ‖R‖ ≤ 1 := by simpa using hR1
    exact (R.opNorm_comp_le T).trans (mul_le_of_le_one_left (norm_nonneg _) hR1')
  have hδS : δ * S < ε := by
    rw [hδ_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [(tsum_nonneg fun n ↦ norm_nonneg (f n) : 0 ≤ S)]
  calc ‖trace 𝕜 E (mapL (.id 𝕜 _) T u)‖
      ≤ ‖trace 𝕜 E (mapL (.id 𝕜 _) (R ∘L T) u)‖ +
          ‖trace 𝕜 E (mapL (.id 𝕜 _) T u) - trace 𝕜 E (mapL (.id 𝕜 _) (R ∘L T) u)‖ :=
        norm_le_insert' _ _
    _ < ‖tracePairing 𝕜 E u‖ * ‖T‖ + ε := add_lt_add_of_le_of_lt hRT (hdiff.trans_lt hδS)

/-- Along a null sequence `x`, every functional `Λ` on `C₀(ℕ, E)` is a trace functional: there is
`u ∈ E* ⊗̂π E` with `tr ((1 ⊗ T) u) = Λ (T ∘ x)` for every operator `T`. Here `u = ∑ n, fₙ ⊗ x n`
for the coordinate functionals `fₙ` of `Λ`. -/
private theorem exists_trace_mapL_eq_of_tendsto_zero {x : ℕ → E} (hx : Tendsto x atTop (𝓝 0))
    (Λ : StrongDual 𝕜 C₀(ℕ, E)) :
    ∃ u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E, ∀ T : E →L[𝕜] E,
      trace 𝕜 E (mapL (.id 𝕜 _) T u) = Λ (evalNullSeq 𝕜 E hx T) := by
  obtain ⟨u, hu⟩ := summable_coe_comp_singleCLM_tmul hx Λ
  refine ⟨u, fun T ↦ (hasSum_trace_mapL hu T).unique ?_⟩
  simpa using ZeroAtInftyContinuousMap.hasSum_comp_singleCLM Λ (evalNullSeq 𝕜 E hx T)

/-- If the tensor trace is dominated by the trace pairing, `‖tr u‖ ≤ ‖Θ_E u‖`, then the identity
of `E` can be approximated uniformly along any null sequence by finite-rank contractions. -/
private theorem exists_hasFiniteRange_norm_le_one_forall_norm_sub_lt
    (htrace : ∀ u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E,
      ‖trace 𝕜 E u‖ ≤ ‖tracePairing 𝕜 E u‖)
    {x : ℕ → E} (hx : Tendsto x atTop (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R ∈ {R : E →L[𝕜] E | R.toLinearMap.HasFiniteRange ∧ ‖R‖ ≤ 1},
      ∀ n, ‖R (x n) - x n‖ < δ := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
  set L := evalNullSeq 𝕜 E hx
  -- The finite-rank contractions, evaluated along `x`.
  set C : Set C₀(ℕ, E) := L '' {T | T.toLinearMap.HasFiniteRange ∧ ‖T‖ ≤ 1}
  have hC : Convex ℝ C := (convex_setOf_hasFiniteRange_norm_le 1).linear_image (L.restrictScalars ℝ)
  refine exists_mem_forall_norm_sub_lt_of_mem_closure hx (by_contra fun hnot ↦ ?_) hδ
  obtain ⟨Λ, s, hΛC, hΛid⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) hC.closure isClosed_closure hnot
  -- The functional `Λ` is the trace pairing with some `u ∈ E* ⊗̂π E` along `x`.
  obtain ⟨u, hu⟩ := exists_trace_mapL_eq_of_tendsto_zero hx Λ
  have hnorm : ‖tracePairing 𝕜 E u‖ ≤ s :=
    norm_tracePairing_le_of_forall_re_le fun T hT hT1 ↦ by
      rw [hu]
      exact (hΛC _ (subset_closure ⟨T, ⟨hT, hT1⟩, rfl⟩)).le
  have htr : trace 𝕜 E u = Λ (L (ContinuousLinearMap.id 𝕜 E)) := by
    simpa [mapL_id] using hu (ContinuousLinearMap.id 𝕜 E)
  have := (htrace u).trans hnorm
  rw [htr] at this
  exact (hΛid.trans_le ((RCLike.re_le_norm _).trans this)).false

/-- **Grothendieck's metric criterion.** A normed space `E` over `ℝ` or `ℂ` has the metric
approximation property iff the tensor trace is dominated by the trace pairing:
`‖tr u‖ ≤ ‖Θ_E u‖` for every `u ∈ E* ⊗̂π E`. -/
theorem hasMetricApproximationProperty_iff_norm_trace_le :
    HasMetricApproximationProperty 𝕜 E ↔
      ∀ u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E,
        ‖trace 𝕜 E u‖ ≤ ‖tracePairing 𝕜 E u‖ := by
  refine ⟨fun hE u ↦ by
    simpa [mapL_id] using (hE.norm_trace_mapL_le u (.id 𝕜 E)).trans
      (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le),
    fun htrace ↦ ?_⟩
  refine hasMetricApproximationProperty_iff.2 <|
    hasBoundedApproximationPropertyWith_iff.2 fun K hK ε hε ↦ ?_
  obtain ⟨R, ⟨hR, hR1⟩, hRK⟩ := exists_mem_forall_norm_sub_lt_of_forall_tendsto_zero
    (fun _ hx _ hδ ↦ exists_hasFiniteRange_norm_le_one_forall_norm_sub_lt htrace hx hδ)
    hK.totallyBounded hε
  exact ⟨R, hR, by simpa using hR1, hRK⟩

/-- If the trace pairing `Θ_E : E* ⊗̂π E → (E ⊗̂ε E*)*` is isometric, then `E` has the metric
approximation property. Since `Θ_E` is a contraction, it suffices that `‖u‖ ≤ ‖Θ_E u‖` for
every `u`. -/
theorem hasMetricApproximationProperty_of_norm_le_norm_tracePairing
    (h : ∀ u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E, ‖u‖ ≤ ‖tracePairing 𝕜 E u‖) :
    HasMetricApproximationProperty 𝕜 E :=
  hasMetricApproximationProperty_iff_norm_trace_le.2 fun u ↦
    ((trace 𝕜 E).le_of_opNorm_le norm_trace_le u).trans (by rw [one_mul]; exact h u)

/-- For a reflexive space `E`, the metric approximation property makes the trace pairing
`Θ_E : E* ⊗̂π E → (E ⊗̂ε E*)*` isometric. -/
theorem HasMetricApproximationProperty.norm_tracePairing_eq
    (hJ : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E))
    (hE : HasMetricApproximationProperty 𝕜 E)
    (u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E) :
    ‖tracePairing 𝕜 E u‖ = ‖u‖ := by
  refine le_antisymm (((tracePairing 𝕜 E).le_of_opNorm_le norm_tracePairing_le u).trans_eq
    (one_mul _)) ?_
  -- A norming functional on `E* ⊗̂π E` is a bilinear form `B` of norm at most one, and
  -- reflexivity writes it as `(f, x) ↦ f (T x)` with `‖T‖ ≤ 1`.
  obtain ⟨φ, hφ1, hφu⟩ := exists_dual_vector'' 𝕜 u
  set B := (liftIsometry 𝕜 (StrongDual 𝕜 E) E 𝕜).symm φ
  have hB : ‖B‖ ≤ 1 := by rwa [LinearIsometryEquiv.norm_map]
  obtain ⟨T, hTx, hTB⟩ := exists_apply_eq_and_norm_le_of_surjective_inclusionInDoubleDual hJ B
  have hT : ‖T‖ ≤ 1 := hTB.trans hB
  have hφ : φ = trace 𝕜 E ∘L mapL (.id 𝕜 _) T :=
    continuousLinearMap_ext fun f x ↦ by simp [hTx, B, liftIsometry_symm_apply_apply]
  have h := (hE.norm_trace_mapL_le u T).trans (mul_le_of_le_one_right (norm_nonneg _) hT)
  rwa [← ContinuousLinearMap.comp_apply, ← hφ, hφu, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg u)] at h

/-- **Grothendieck's metric criterion for reflexive spaces.** A reflexive normed space `E` over
`ℝ` or `ℂ` has the metric approximation property iff the trace pairing
`Θ_E : E* ⊗̂π E → (E ⊗̂ε E*)*` is isometric. -/
theorem hasMetricApproximationProperty_iff_norm_tracePairing_eq
    (hJ : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E)) :
    HasMetricApproximationProperty 𝕜 E ↔
      ∀ u : CompletedProjectiveTensor 𝕜 (StrongDual 𝕜 E) E, ‖tracePairing 𝕜 E u‖ = ‖u‖ :=
  ⟨fun hE ↦ hE.norm_tracePairing_eq hJ,
    fun h ↦ hasMetricApproximationProperty_of_norm_le_norm_tracePairing fun u ↦ (h u).ge⟩

end TauCeti
