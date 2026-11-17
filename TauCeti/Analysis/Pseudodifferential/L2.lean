/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.CalderonVaillancourt
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Sobolev.BesselPotential.Extension
public import TauCeti.Analysis.Sobolev.BesselPotential.Postcomp
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Measure

/-!
# The bounded extension of uniform symbols of order zero to `L²`

Let `a` be a symbol of order `0` on `ℝⁿ` whose estimates
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(-|β|)` hold with constants independent of the position `x`
(`TauCeti.Symbol.IsUniform`). By the Calderón–Vaillancourt theorem
(`TauCeti.Symbol.exists_quantizeUniformOrderZeroLp`,
`TauCeti.Symbol.exists_quantizeUniformOrderZero`) its Kohn–Nirenberg quantization `Op(a)`
extends to a bounded operator on `L²` when the coefficient spaces are complex Hilbert spaces or
finite-dimensional. This file records the resulting `L²` estimate on Schwartz functions and names
the extension, as an operator on the Bessel-potential space `H^0 = L²`, so that it can be compared
across symbols. The extension is defined for normed coefficient spaces; its API assumes the `L²`
estimate on Schwartz functions.

## Main declarations

* `TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le`,
  `TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_finiteDimensional`: there is
  a constant `C` with `‖Op(a) u‖_{L²} ≤ C ‖u‖_{L²}` for every Schwartz function `u`.
* `TauCeti.Symbol.quantizeUniformOrderZero`: the bounded extension `H^0(ℝⁿ; V) → H^0(ℝⁿ; W)`,
  with `TauCeti.Symbol.toDistr_quantizeUniformOrderZero_toBesselPotentialSpaceCLM_apply`
  identifying its values on Schwartz functions, its norm bound
  `TauCeti.Symbol.norm_quantizeUniformOrderZero_le` and its linearity in the symbol.
* `TauCeti.Symbol.quantizeUniformOrderZero_const`,
  `TauCeti.Symbol.quantizeUniformOrderZero_const_id`,
  `TauCeti.Symbol.norm_quantizeUniformOrderZero_const_id`: explicit action and operator norm of
  constant symbols on `H^0 = L²`.
* `TauCeti.Symbol.not_exists_eLpNorm_quantizeSchwartzValue_ofSpatial_smul_le`: failure of `L²`
  boundedness for the non-uniform order-zero symbol `x ↦ x_j • T`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap BesselPotentialSpace ContDiff

namespace TauCeti

namespace Symbol

section InnerProductSpace

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {a : Symbol n V W 0}

/-- **`L²` boundedness of uniform symbols of order zero.** For a symbol `a` of order `0` between
complex Hilbert spaces whose estimates are uniform in the position, there is a constant `C` with
`‖Op(a) u‖_{L²} ≤ C ‖u‖_{L²}` for every Schwartz function `u`. -/
theorem IsUniform.exists_eLpNorm_quantizeSchwartzValue_le (ha : a.IsUniform) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume := by
  obtain ⟨T, hT⟩ := a.exists_quantizeUniformOrderZeroLp ha
  refine ⟨‖T‖, norm_nonneg T, fun u ↦ ?_⟩
  have hTu : eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume = ‖T (u.toLp 2)‖ₑ := by
    rw [Lp.eNorm_def]
    exact eLpNorm_congr_ae (hT u).symm
  have hu : ‖u.toLp 2‖ₑ = eLpNorm u 2 volume := by
    rw [Lp.eNorm_def]
    exact eLpNorm_congr_ae (u.coeFn_toLp 2 volume)
  rw [hTu, ← hu, ofReal_norm T]
  exact T.le_opENorm _

end InnerProductSpace

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {a : Symbol n V W 0}

/-- **`L²` boundedness of uniform symbols of order zero** for finite-dimensional coefficient
spaces: there is a constant `C` with `‖Op(a) u‖_{L²} ≤ C ‖u‖_{L²}` for every Schwartz
function `u`. -/
theorem IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_finiteDimensional
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (ha : a.IsUniform) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume := by
  obtain ⟨T, hT⟩ := a.exists_quantizeUniformOrderZero ha
  refine ⟨‖T‖, norm_nonneg T, fun u ↦ ?_⟩
  have hTu : T (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM a ha u) := by
    ext φ
    rw [hT, SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply,
      coe_quantizeUniformCLM]
  have hle := T.le_opNorm (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u)
  rw [hTu, SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
    SchwartzMap.norm_toBesselPotentialSpaceCLM_zero, coe_quantizeUniformCLM] at hle
  have hfin := ((quantizeUniformCLM a ha u).memLp 2).eLpNorm_ne_top
  rw [coe_quantizeUniformCLM] at hfin
  rw [← ENNReal.ofReal_toReal hfin]
  refine (ENNReal.ofReal_le_ofReal hle).trans ?_
  rw [ENNReal.ofReal_mul (norm_nonneg T)]
  gcongr
  exact ENNReal.ofReal_toReal_le

/-- An `L²` estimate for `Op(a)` on Schwartz functions, in `H^0` norms. -/
private theorem norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le (ha : a.IsUniform) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ u : 𝓢(CoordinateSpace n, V), eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
      ENNReal.ofReal C * eLpNorm u 2 volume) (u : 𝓢(CoordinateSpace n, V)) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM a ha u)‖ ≤
      C * ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 u‖ := by
  rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
    SchwartzMap.norm_toBesselPotentialSpaceCLM_zero, coe_quantizeUniformCLM,
    ← ENNReal.toReal_ofReal hC0, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (u.memLp 2).eLpNorm_ne_top) (hC u)

/-- **The bounded extension of `Op(a)` to `L²`**, for a uniform symbol `a` of order `0`, as an
operator on the Bessel-potential space `H^0 = L²`. When `Op(a)` satisfies an `L²` estimate on
Schwartz functions (for instance for complex Hilbert spaces,
`TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le`, or finite-dimensional ones,
`TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_finiteDimensional`), it
extends the quantization of Schwartz functions
(`TauCeti.Symbol.toDistr_quantizeUniformOrderZero_toBesselPotentialSpaceCLM_apply`), and it is the
unique continuous linear map with this property (`BesselPotentialSpace.continuousLinearMap_ext`).
Without such an estimate it is `0`. -/
def quantizeUniformOrderZero (a : Symbol n V W 0) (ha : a.IsUniform) :
    H^{0}(CoordinateSpace n, V) →L[ℂ] H^{0}(CoordinateSpace n, W) :=
  SchwartzMap.extendBesselPotentialSpace (quantizeUniformCLM a ha) 0 0 2

/-- Defining formula for `Symbol.quantizeUniformOrderZero`. -/
theorem quantizeUniformOrderZero_def (a : Symbol n V W 0) (ha : a.IsUniform) :
    a.quantizeUniformOrderZero ha =
      SchwartzMap.extendBesselPotentialSpace (quantizeUniformCLM a ha) 0 0 2 :=
  (rfl)

/-- An `L²` estimate for `Op(a)` on Schwartz functions gives one in `H^0` norms. -/
private theorem exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le (ha : a.IsUniform)
    (hC : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume) :
    ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 u‖ :=
  let ⟨C, hC0, hC⟩ := hC; ⟨C, norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le ha hC0 hC⟩

/-- On Schwartz functions, the bounded extension of `Op(a)` is `Op(a)`, provided `Op(a)` satisfies
an `L²` estimate on Schwartz functions. -/
@[simp]
theorem quantizeUniformOrderZero_toBesselPotentialSpaceCLM (ha : a.IsUniform)
    (hC : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume)
    (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniformOrderZero ha (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM a ha u) :=
  SchwartzMap.extendBesselPotentialSpace_toBesselPotentialSpaceCLM ENNReal.ofNat_ne_top
    (exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le ha hC) u

/-- On a Schwartz function `u`, the bounded extension of `Op(a)` to `H^0` gives the tempered
distribution of the function `Op(a) u = quantizeSchwartzValue a.coefficient u`, provided `Op(a)`
satisfies an `L²` estimate on Schwartz functions. -/
theorem toDistr_quantizeUniformOrderZero_toBesselPotentialSpaceCLM_apply (ha : a.IsUniform)
    (hC : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume)
    (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    (a.quantizeUniformOrderZero ha (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u)).toDistr φ =
      ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  rw [quantizeUniformOrderZero_toBesselPotentialSpaceCLM ha hC,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply, coe_quantizeUniformCLM]

/-- The operator norm of the bounded extension of `Op(a)` is at most any constant of the `L²`
estimate on Schwartz functions. -/
theorem norm_quantizeUniformOrderZero_le (ha : a.IsUniform) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : 𝓢(CoordinateSpace n, V), eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
      ENNReal.ofReal C * eLpNorm u 2 volume) :
    ‖a.quantizeUniformOrderZero ha‖ ≤ C :=
  SchwartzMap.norm_extendBesselPotentialSpace_le ENNReal.ofNat_ne_top hC0
    (norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le ha hC0 hC)

/-- The bounded extension of `Op(a)` is additive in the symbol, for symbols satisfying `L²`
estimates on Schwartz functions. -/
theorem quantizeUniformOrderZero_add {b : Symbol n V W 0} (ha : a.IsUniform) (hb : b.IsUniform)
    (hCa : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume)
    (hCb : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue b.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume) :
    (a + b).quantizeUniformOrderZero (ha.add hb) =
      a.quantizeUniformOrderZero ha + b.quantizeUniformOrderZero hb := by
  simp only [quantizeUniformOrderZero, quantizeUniformCLM_add ha hb]
  exact SchwartzMap.extendBesselPotentialSpace_add ENNReal.ofNat_ne_top
    (exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le ha hCa)
    (exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le hb hCb)

/-- The bounded extension of `Op(a)` is homogeneous in the symbol, for a symbol satisfying an `L²`
estimate on Schwartz functions. -/
theorem quantizeUniformOrderZero_smul (ha : a.IsUniform)
    (hC : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume) (c : ℂ) :
    (c • a).quantizeUniformOrderZero (ha.smul c) = c • a.quantizeUniformOrderZero ha := by
  simp only [quantizeUniformOrderZero, quantizeUniformCLM_smul ha c]
  exact SchwartzMap.extendBesselPotentialSpace_smul ENNReal.ofNat_ne_top
    (exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le ha hC) c

/-- A constant symbol `T : V →L[ℂ] W` quantizes on `H^0 = L²` to `BesselPotentialSpace.postcomp`. -/
theorem quantizeUniformOrderZero_const (T : V →L[ℂ] W) :
    (const T : Symbol n V W 0).quantizeUniformOrderZero (isUniform_const T) =
      BesselPotentialSpace.postcomp (CoordinateSpace n) 0 2 T :=
  SchwartzMap.extendBesselPotentialSpace_eq_of_forall ENNReal.ofNat_ne_top fun u ↦ by
    rw [quantizeUniformCLM_const, SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM]

/-- The constant identity symbol quantizes on `H^0 = L²` to the identity operator. -/
@[simp] theorem quantizeUniformOrderZero_const_id :
    (const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).quantizeUniformOrderZero
        (isUniform_const _) = ContinuousLinearMap.id ℂ H^{0}(CoordinateSpace n, V) := by
  rw [quantizeUniformOrderZero_const]
  exact BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top
    fun _ ↦ by ext φ; simp

/-- On a nontrivial fibre `V`, the `H^0` quantization of the constant identity symbol has operator
norm `1`. -/
theorem norm_quantizeUniformOrderZero_const_id [Nontrivial V] :
    ‖(const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).quantizeUniformOrderZero
        (isUniform_const _)‖ = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hpos : 0 < (volume : Measure (CoordinateSpace n)).real (Metric.ball 0 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_lt_top.ne
  let w := (BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V 0 2).symm
    (indicatorConstLp 2 (s := Metric.ball 0 1) measurableSet_ball measure_ball_lt_top.ne v)
  have hw : ‖w‖ ≠ 0 := by
    rw [LinearIsometryEquiv.norm_map, norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top]
    exact mul_ne_zero (norm_ne_zero_iff.mpr hv) (by positivity)
  rw [quantizeUniformOrderZero_const_id]
  refine le_antisymm ContinuousLinearMap.norm_id_le ?_
  simpa [hw] using (ContinuousLinearMap.id ℂ H^{0}(CoordinateSpace n, V)).ratio_le_opNorm w

omit [CompleteSpace V] [CompleteSpace W] in
private lemma exists_schwartz_unit_ball_pos_eLpNorm_postcomp {T : V →L[ℂ] W} (hT : T ≠ 0) :
    ∃ u₀ : 𝓢(CoordinateSpace n, V), (∀ y, u₀ y ≠ 0 → ‖y‖ ≤ 1) ∧
      0 < (eLpNorm (u₀.postcompCLM T) 2 volume).toReal := by
  obtain ⟨v, hv⟩ : ∃ v : V, T v ≠ 0 := by by_contra! h; exact hT (ContinuousLinearMap.ext h)
  let b : ContDiffBump (0 : CoordinateSpace n) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let u₀ := b.hasCompactSupport.smul_right.toSchwartzMap (b.contDiff.smul (contDiff_const (c := v)))
  have hu₀ (x) : u₀ x = b x • v := HasCompactSupport.toSchwartzMap_toFun _ _ x
  refine ⟨u₀, fun y hy ↦ by
      simpa [b.tsupport_eq] using subset_tsupport b fun hb0 ↦ hy (by simp [hu₀, hb0]),
    ENNReal.toReal_pos (fun h0 ↦ hv ?_) ((u₀.postcompCLM T).memLp 2).eLpNorm_ne_top⟩
  have h0' := congrFun (Measure.eq_of_ae_eq ((eLpNorm_eq_zero_iff two_ne_zero).mp h0)
    (u₀.postcompCLM T).continuous continuous_zero) 0
  have hb0 : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))
  simpa [hu₀, hb0] using h0'

private theorem le_norm_quantizeSchwartzValue_ofSpatial_smul (j : Fin n) {T : V →L[ℂ] W}
    (hf : ContDiff ℝ ∞ fun x : CoordinateSpace n ↦ x j • T) {u₀ : 𝓢(CoordinateSpace n, V)}
    (hu₀_supp : ∀ y, u₀ y ≠ 0 → ‖y‖ ≤ 1) {t : ℝ} (ht1 : 1 ≤ t) (x : CoordinateSpace n) :
    ‖(t - 1) • ((u₀.postcompCLM T).compSubConstCLM ℂ (t • EuclideanSpace.single j (1 : ℝ))) x‖ ≤
      ‖quantizeSchwartzValue (ofSpatial _ hf).coefficient
        (u₀.compSubConstCLM ℂ (t • EuclideanSpace.single j (1 : ℝ))) x‖ := by
  set eⱼ := EuclideanSpace.single j (1 : ℝ)
  have hq : quantizeSchwartzValue (ofSpatial _ hf).coefficient
      (u₀.compSubConstCLM ℂ (t • eⱼ)) x = x j • T (u₀ (x - t • eⱼ)) := by
    rw [funext (coefficient_ofSpatial _ hf),
      quantizeSchwartzValue_comp_fst (fun y : CoordinateSpace n ↦ y j • T), smul_apply]; rfl
  rw [hq, SchwartzMap.compSubConstCLM_apply, SchwartzMap.postcompCLM_apply,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  by_cases hbx : T (u₀ (x - t • eⱼ)) = 0
  · simp [hbx]
  · have hxj : |x j - t| ≤ 1 := by
      simpa [eⱼ] using (PiLp.norm_apply_le (x - t • eⱼ) j).trans
        (hu₀_supp _ fun h0 ↦ hbx (by simp [h0]))
    exact mul_le_mul_of_nonneg_right (by linarith [abs_le.mp hxj, le_abs_self (x j)])
      (norm_nonneg _)

/-- **Necessity of spatial uniformity for `L²` boundedness.** For `j : Fin n` and `T ≠ 0`, the
non-uniform order-zero symbol `x ↦ x_j • T` has no `L² → L²` bound over Schwartz functions. -/
theorem not_exists_eLpNorm_quantizeSchwartzValue_ofSpatial_smul_le (j : Fin n) {T : V →L[ℂ] W}
    (hT : T ≠ 0) (hf : ContDiff ℝ ∞ fun x : CoordinateSpace n ↦ x j • T) :
    ¬ ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue (ofSpatial _ hf).coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume := by
  rintro ⟨C, hC⟩
  obtain ⟨u₀, hu₀_supp, hB0⟩ := exists_schwartz_unit_ball_pos_eLpNorm_postcomp (n := n) hT
  set A := (eLpNorm u₀ 2 volume).toReal; set B := (eLpNorm (u₀.postcompCLM T) 2 volume).toReal
  set t : ℝ := max 2 (max C 0 * A / B + 2); set eⱼ := EuclideanSpace.single j (1 : ℝ)
  have hmp := measurePreserving_sub_right (volume : Measure (CoordinateSpace n)) (t • eⱼ)
  have ht1 : 1 ≤ t := by linarith [le_max_left 2 (max C 0 * A / B + 2)]
  set w : 𝓢(CoordinateSpace n, W) := (u₀.postcompCLM T).compSubConstCLM ℂ (t • eⱼ)
  have hlow : ENNReal.ofReal (t - 1) * eLpNorm (u₀.postcompCLM T) 2 volume ≤
      ENNReal.ofReal C * eLpNorm u₀ 2 volume := by
    have hw_eq : (w : CoordinateSpace n → W) = (u₀.postcompCLM T) ∘ fun x ↦ x - t • eⱼ :=
      funext (SchwartzMap.compSubConstCLM_apply _ _)
    rw [← eLpNorm_comp_measurePreserving (u₀.postcompCLM T).continuous.aestronglyMeasurable hmp,
      ← hw_eq, ← eLpNorm_comp_measurePreserving u₀.continuous.aestronglyMeasurable hmp]
    refine (le_of_eq (by rw [eLpNorm_const_smul, Real.eNorm_eq_ofReal (by linarith)])).trans
      ((eLpNorm_mono (w.continuous.const_smul (t - 1)).aestronglyMeasurable
        (le_norm_quantizeSchwartzValue_ofSpatial_smul j hf hu₀_supp ht1)).trans (hC _))
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (u₀.memLp 2).eLpNorm_ne_top) hlow
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal'] at hreal
  have hmul : (max C 0 * A / B + 1) * B ≤ (t - 1) * B :=
    mul_le_mul_of_nonneg_right (by linarith [le_max_right 2 (max C 0 * A / B + 2)]) hB0.le
  rw [add_mul, div_mul_cancel₀ _ hB0.ne', one_mul] at hmul; linarith [hreal]

end Symbol

end TauCeti
