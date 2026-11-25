/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.BumpFunction
public import TauCeti.Analysis.Calculus.FDeriv.NormComparison
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.Negative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.RealSmooth

/-!
# Untwisting a transverse zero of a section

Let `L → X` be a complex line bundle over a Riemann surface whose underlying real bundle is smooth,
and let `σ` be a smooth section of `L` with a transverse zero at `x`. Read in the chart `φ` of `X`
at `x` and the chart of `L` at `x`, the section is a function `g` of `w = φ z` vanishing at
`p = φ x`. Its zero is positive when the real derivative of `g` at `p` is close to a complex linear
map `u ↦ u c`, and negative when it is close to a conjugate linear map `u ↦ conj u c`, in the sense
that `‖g w - c u‖ < ‖c‖ ‖u‖`, respectively `‖g w - c conj u‖ < ‖c‖ ‖u‖`, for `u = w - p ≠ 0`
small.

Twisting `L` at a positive zero by `-x`, and at a negative zero by `x`, removes the zero: this file
constructs a smooth section of the twist `L(∓x)` with no zero near `x` which agrees with `σ` away
from a small neighbourhood of `x` (`TauCeti.exists_untwist_section`).

The twisted section reads `g / u` in the chart of `L(-x)` at `x`, and `u g` in that of `L(x)`.
Near a positive zero, `g / u` lies in the open disc of radius `‖c‖` about `c`; near a negative
zero, `u g` is `‖u‖²` times a point of that disc, because `u conj u = ‖u‖²`. In both cases the
segment from the twisted reading to the constant `c` avoids `0`, so interpolating with a smooth
bump function `f` that is `1` near `x` (`TauCeti.untwistSection`) gives a section which is the
constant `c` near `x`, hence smooth there, and has no zero on the support of `f`. Off the support of
`f` it is the twist of `σ`, whose only zero near `x` was `x` itself.

In the proof of the Riemann–Roch formula for real Cauchy–Riemann operators (McDuff–Salamon,
Theorem C.1.10), a smooth line bundle `L` is twisted at the zeros of a generic section `σ`, by
`-xᵢ` at the positive and by `xᵢ` at the negative zeros. Untwisting the zeros one at a time gives a
nowhere-zero section of the resulting twist, which is therefore trivial.

## Main definitions

* `TauCeti.untwistSection`: the interpolation, with weight `f`, between the twist of a section and
  the section which is constant in the chart of the twist at `x`.

## Main results

* `TauCeti.contMDiff_untwistSection`: the interpolation is smooth when `f` is a smooth function
  equal to `1` near `x` and supported in the chart of the twist at `x`.
* `TauCeti.exists_untwist_section`: untwisting a zero satisfying the estimate above.
* `TauCeti.exists_negPointTwist_section_of_hasFDerivAt` and
  `TauCeti.exists_pointTwist_section_of_hasFDerivAt`: untwisting a positive zero in `L(-x)`, and a
  negative zero in `L(x)`, from the derivative of the chart reading.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10.
-/

public section

noncomputable section

open Bundle Set Topology Filter ComplexConjugate
open scoped Manifold ContDiff

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {L : X → Type*} [∀ z, AddCommGroup (L z)] [∀ z, Module ℂ (L z)]
  [∀ z, TopologicalSpace (L z)] [TopologicalSpace (TotalSpace ℂ L)]
  [FiberBundle ℂ L] [VectorBundle ℂ ℂ L]

local instance instVectorBundleRealUntwist {L : X → Type*} [∀ z, AddCommGroup (L z)]
    [∀ z, Module ℂ (L z)] [∀ z, Module ℝ (L z)] [∀ z, IsScalarTower ℝ ℂ (L z)]
    [∀ z, TopologicalSpace (L z)] [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L]
    [VectorBundle ℂ ℂ L] : VectorBundle ℝ ℂ L :=
  VectorBundle.restrictScalars ℝ ℂ ℂ L

local instance instVectorBundleRealSignedPointTwistCoreUntwist (x : X) (s : Bool) :
    VectorBundle ℝ ℂ (signedPointTwistCore ℂ L x s).Fiber :=
  VectorBundle.restrictScalars ℝ ℂ ℂ _

/-! ### The interpolating section -/

variable (L) in
/-- The section of the signed point twist `L(±x)` interpolating, with weight `1 - f z`, the section
`σ` of `L` read in the preferred chart of `L` at `z`, which is the twist of `σ` off `x`, and, with
weight `f z`, the section which is the constant `c` in the chart of the twist at `x`. -/
def untwistSection (x : X) (s : Bool) (σ : ∀ z, L z) (f : X → ℝ) (c : ℂ) (z : X) :
    (signedPointTwistCore ℂ L x s).Fiber z :=
  (1 - f z) • (show (signedPointTwistCore ℂ L x s).Fiber z from
      (trivializationAt ℂ L z ⟨z, σ z⟩).2) +
    f z • (trivializationAt ℂ (signedPointTwistCore ℂ L x s).Fiber x).symm z c

/-- Where `f` vanishes, the interpolating section is the twist of `σ`. -/
theorem untwistSection_of_eq_zero {x z : X} {s : Bool} {σ : ∀ z, L z} {f : X → ℝ} {c : ℂ}
    (hf : f z = 0) :
    untwistSection L x s σ f c z = (trivializationAt ℂ L z ⟨z, σ z⟩).2 := by
  simp only [untwistSection, hf, sub_zero, zero_smul, add_zero]
  exact one_smul ℝ _

/-- Away from `x`, where `f` vanishes, the interpolating section is `σ`, read in `L` through
`pointTwistDiv`. -/
theorem pointTwistDiv_untwistSection_of_eq_zero {x z : X} {s : Bool} {σ : ∀ z, L z} {f : X → ℝ}
    {c : ℂ} (hf : f z = 0) (hzx : z ≠ x) :
    pointTwistDiv ℂ L x z (untwistSection L x s σ f c z) = σ z := by
  rw [untwistSection_of_eq_zero hf, pointTwistDiv_apply_of_ne hzx]
  exact (trivializationAt ℂ L z).symm_apply_apply_mk (mem_baseSet_trivializationAt ℂ L z) _

/-- In the chart of the twist at `x`, the interpolating section reads as the interpolation of the
reading of the twist of `σ` and the constant `c`. -/
theorem trivializationAt_untwistSection {x z : X} {s : Bool} {σ : ∀ z, L z} {f : X → ℝ} {c : ℂ}
    (hz : z ∈ (trivializationAt ℂ (signedPointTwistCore ℂ L x s).Fiber x).baseSet) :
    (trivializationAt ℂ (signedPointTwistCore ℂ L x s).Fiber x
        ⟨z, untwistSection L x s σ f c z⟩).2 =
      (1 - f z) • (trivializationAt ℂ (signedPointTwistCore ℂ L x s).Fiber x
        ⟨z, (trivializationAt ℂ L z ⟨z, σ z⟩).2⟩).2 + f z • c := by
  have hlin := (trivializationAt ℂ (signedPointTwistCore ℂ L x s).Fiber x).linear ℝ hz
  rw [untwistSection, hlin.map_add, hlin.map_smul, hlin.map_smul,
    (trivializationAt ℂ (signedPointTwistCore ℂ L x s).Fiber x).apply_mk_symm hz]

/-! ### Smoothness -/

section Smooth

variable {n : ℕ∞ω} [∀ z, Module ℝ (L z)] [∀ z, IsScalarTower ℝ ℂ (L z)] [IsManifold 𝓘(ℂ) n X]
  [ContMDiffVectorBundle n ℂ L 𝓘(ℝ, ℂ)]

/-- **The interpolating section is smooth.** If `σ` is a real-`C^n` section of `L` and `f` is a
real-`C^n` function equal to `1` near `x` whose support has closure in the chart of the twist at
`x`, then the interpolating section is a real-`C^n` section of the twist. Near `x` it is the
constant `c` in the chart of the twist; away from `x` the twist of `σ` is `C^n`. -/
theorem contMDiff_untwistSection {x : X} {s : Bool} {σ : ∀ z, L z} {f : X → ℝ} {c : ℂ}
    (hσ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) n fun z ↦ TotalSpace.mk' ℂ z (σ z))
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) n f) (hf₁ : f =ᶠ[𝓝 x] 1)
    (hfs : tsupport f ⊆ (trivializationAt ℂ (signedPointTwistCore ℂ L x s).Fiber x).baseSet) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) n
      fun z ↦ TotalSpace.mk' ℂ z (untwistSection L x s σ f c z) := by
  have : T1Space X := ChartedSpace.t1Space ℂ X
  set e := trivializationAt ℂ (signedPointTwistCore ℂ L x s).Fiber x
  set t : ∀ z, (signedPointTwistCore ℂ L x s).Fiber z := fun z ↦
    (trivializationAt ℂ L z ⟨z, σ z⟩).2
  intro z₀
  -- A section vanishing near `z₀` is `C^n` there.
  have hzero {τ : ∀ z, (signedPointTwistCore ℂ L x s).Fiber z} (h : ∀ᶠ z in 𝓝 z₀, τ z = 0) :
      ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) n (fun z ↦ TotalSpace.mk' ℂ z (τ z)) z₀ :=
    (contMDiffAt_zeroSection ℝ _).congr_of_eventuallyEq (h.mono fun z hz ↦ by
      change TotalSpace.mk' ℂ z (τ z) = _
      rw [hz]
      rfl)
  -- The first summand: the twist of `σ` is `C^n` off `x`, and its weight vanishes near `x`.
  have h₁ : ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) n
      (fun z ↦ TotalSpace.mk' ℂ z (((1 - f) • t) z)) z₀ := by
    by_cases hz₀ : z₀ = x
    · subst hz₀
      refine hzero ?_
      filter_upwards [hf₁] with z hz
      simp [hz]
    · refine (contMDiffAt_const.sub (hf z₀)).smul_section
        ((contMDiffAt_signedPointTwist_section_iff_of_ne_real hz₀).2
          ((hσ z₀).congr_of_eventuallyEq ?_))
      filter_upwards [isOpen_compl_singleton.mem_nhds hz₀] with z hz
      rw [pointTwistDiv_apply_of_ne hz]
      exact congrArg _
        ((trivializationAt ℂ L z).symm_apply_apply_mk (mem_baseSet_trivializationAt ℂ L z) _)
  -- The second summand: constant in the chart `e`, with weight supported in its domain.
  have h₂ : ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) n
      (fun z ↦ TotalSpace.mk' ℂ z ((f • fun z ↦ e.symm z c) z)) z₀ := by
    by_cases hz₀ : z₀ ∈ e.baseSet
    · refine (hf z₀).smul_section ((e.contMDiffAt_section_iff hz₀).2
        ((contMDiffAt_const (c := c)).congr_of_eventuallyEq ?_))
      filter_upwards [e.open_baseSet.mem_nhds hz₀] with z hz
      exact congrArg Prod.snd (e.apply_mk_symm hz c)
    · refine hzero ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hz₀ (hfs h)] with z hz
      simp [hz]
  exact h₁.add_section h₂

end Smooth

/-! ### Untwisting -/

/-- Interpolating along the segment from `T` to `c` avoids `0` when `T` lies in the open disc of
radius `μ ‖c‖` about `μ c`, for some `μ > 0`. -/
private theorem sub_smul_add_smul_ne_zero {T c : ℂ} {μ t : ℝ} (hμ : 0 < μ) (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) (hT : ‖T - μ • c‖ < μ * ‖c‖) :
    (1 - t) • T + t • c ≠ 0 := by
  intro h
  have hc : 0 < ‖c‖ := pos_of_mul_pos_right ((norm_nonneg _).trans_lt hT) hμ.le
  -- The value is `((1 - t) μ + t) c` plus `(1 - t)` times the deviation `T - μ c`.
  have h' : ((1 - t) * μ + t) • c = -((1 - t) • (T - μ • c)) := by
    rw [← sub_eq_zero, sub_neg_eq_add, smul_sub, ← h]
    module
  have hn := congrArg norm h'
  rw [norm_neg, norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by linarith)] at hn
  -- So `t ‖c‖ ≤ 0`, hence `t = 0`, and then `μ ‖c‖ = ‖T - μ c‖ < μ ‖c‖`.
  have h₁ : t * ‖c‖ ≤ 0 := by nlinarith [mul_le_mul_of_nonneg_left hT.le (sub_nonneg.2 ht₁)]
  obtain rfl : t = 0 := le_antisymm (by nlinarith) ht₀
  simp only [sub_zero, one_mul, add_zero] at hn
  linarith

section Untwist

/-- **The interpolating section has no zero off `x`.** At a point `z ≠ x` of the chart of the twist
at `x`, with chart coordinate `w = φ z` and `u = w - φ x`, suppose the chart reading `g` of `σ`
satisfies `‖g w - c u‖ < ‖c‖ ‖u‖` for the twist `L(-x)`, or `‖g w - c conj u‖ < ‖c‖ ‖u‖` for the
twist `L(x)`. Then for every weight `f z ∈ [0, 1]` the interpolating section is nonzero at `z`. -/
theorem trivializationAt_untwistSection_ne_zero {x z : X} {s : Bool} {σ : ∀ z, L z}
    {f : X → ℝ} {c : ℂ}
    (hz : z ∈ (trivializationAt ℂ (signedPointTwistCore ℂ L x s).Fiber x).baseSet) (hzx : z ≠ x)
    (hf₀ : 0 ≤ f z) (hf₁ : f z ≤ 1)
    (hg : ‖negPointTwistChartReading ℂ x σ (chartAt ℂ x z) -
      (if s then conj (chartAt ℂ x z - chartAt ℂ x x) else chartAt ℂ x z - chartAt ℂ x x) * c‖ <
        ‖c‖ * ‖chartAt ℂ x z - chartAt ℂ x x‖) :
    (trivializationAt ℂ (signedPointTwistCore ℂ L x s).Fiber x
      ⟨z, untwistSection L x s σ f c z⟩).2 ≠ 0 := by
  rw [trivializationAt_untwistSection hz]
  rw [signedPointTwistCore_trivializationAt_self] at hz ⊢
  have hzs : z ∈ (chartAt ℂ x).source := by simpa using (mem_signedPointTwistCore_baseSet.1 hz).2
  have hu : 0 < ‖chartAt ℂ x z - chartAt ℂ x x‖ := by
    rw [← pointTwistCoord_apply]
    exact norm_pos_iff.2 (pointTwistCoord_ne_zero hzs hzx)
  rw [signedPointTwistCore_localTriv_trivializationAt_of_ne hz hzx,
    ← negPointTwistChartReading_chartAt ℂ σ hzs]
  set g := negPointTwistChartReading ℂ x σ (chartAt ℂ x z)
  set u := chartAt ℂ x z - chartAt ℂ x x
  cases s
  · -- In `L(-x)` the twist of `σ` reads `g / u`, which lies in the disc of radius `‖c‖` about `c`.
    simp only [Bool.false_eq_true, ite_false] at hg
    simp only [signedPointTwistFactor_false, pointTwistFactor_true_false, pointTwistCoord_apply,
      smul_eq_mul]
    refine sub_smul_add_smul_ne_zero one_pos hf₀ hf₁ ?_
    have h : u⁻¹ * g - (1 : ℝ) • c = u⁻¹ * (g - u * c) := by
      rw [one_smul, mul_sub, ← mul_assoc, inv_mul_cancel₀ (norm_pos_iff.1 hu), one_mul]
    rw [h, norm_mul, norm_inv, one_mul, inv_mul_lt_iff₀ hu, mul_comm ‖u‖]
    exact hg
  · -- In `L(x)` it reads `u g`, which is `‖u‖²` times a point of that disc.
    simp only [ite_true] at hg
    simp only [signedPointTwistFactor_true, pointTwistFactor_false_true, pointTwistCoord_apply,
      smul_eq_mul]
    refine sub_smul_add_smul_ne_zero (pow_pos hu 2) hf₀ hf₁ ?_
    have h : u * g - (‖u‖ ^ 2 : ℝ) • c = u * (g - conj u * c) := by
      rw [mul_sub, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.real_smul]
    rw [h, norm_mul]
    nlinarith

variable [∀ z, Module ℝ (L z)] [∀ z, IsScalarTower ℝ ℂ (L z)] [T2Space X] [IsManifold 𝓘(ℂ) ∞ X]
  [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℝ, ℂ)]

/-- **Untwisting a zero.** Let `σ` be a smooth section of a smooth complex line bundle `L` over a
Riemann surface, and `V` a neighbourhood of `x` containing no zero of `σ` other than `x`. Suppose
that, read in the charts at `x`, `‖g w - c u‖ < ‖c‖ ‖u‖` (for `s = false`) or
`‖g w - c conj u‖ < ‖c‖ ‖u‖` (for `s = true`) for `u = w - φ x ≠ 0` small. Then the signed point
twist `L(-x)` (for `s = false`), respectively `L(x)` (for `s = true`), has a smooth section with no
zero in `V`, which outside `V` is `σ`, read in `L` through `pointTwistDiv`. -/
theorem exists_untwist_section {x : X} {σ : ∀ z, L z}
    (hσ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ fun z ↦ TotalSpace.mk' ℂ z (σ z))
    {V : Set X} (hV : V ∈ 𝓝 x) (hVσ : ∀ z ∈ V, σ z = 0 → z = x) (s : Bool) {c : ℂ}
    (hg : ∀ᶠ w in 𝓝[≠] chartAt ℂ x x, ‖negPointTwistChartReading ℂ x σ w -
      (if s then conj (w - chartAt ℂ x x) else w - chartAt ℂ x x) * c‖ <
        ‖c‖ * ‖w - chartAt ℂ x x‖) :
    ∃ τ : ∀ z, (signedPointTwistCore ℂ L x s).Fiber z,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ (fun z ↦ TotalSpace.mk' ℂ z (τ z)) ∧
        (∀ z ∈ V, τ z ≠ 0) ∧ ∀ z ∉ V, pointTwistDiv ℂ L x z (τ z) = σ z := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ X := IsManifold.restrictScalars ℝ ‹_›
  set e := trivializationAt ℂ (signedPointTwistCore ℂ L x s).Fiber x
  have hc : c ≠ 0 := by
    rintro rfl
    obtain ⟨w, hw⟩ := hg.exists
    simp only [mul_zero, sub_zero, norm_zero, zero_mul] at hw
    exact (norm_nonneg _).not_gt hw
  rw [eventually_nhdsWithin_iff] at hg
  -- A bump function `f` at `x` supported where the estimate holds, in `V` and in the chart `e`.
  have hS : e.baseSet ∩ V ∩ chartAt ℂ x ⁻¹' {w | w ∈ ({chartAt ℂ x x}ᶜ : Set ℂ) →
      ‖negPointTwistChartReading ℂ x σ w -
        (if s then conj (w - chartAt ℂ x x) else w - chartAt ℂ x x) * c‖ <
          ‖c‖ * ‖w - chartAt ℂ x x‖} ∈ 𝓝 x :=
    inter_mem (inter_mem (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt ℂ _ x)) hV)
      ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x) hg)
  obtain ⟨f, -, hfS⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, ℂ)) x).mem_iff.1 hS
  have hx : x ∈ V := mem_of_mem_nhds hV
  refine ⟨untwistSection L x s σ f c, contMDiff_untwistSection hσ f.contMDiff f.eventuallyEq_one
    (hfS.trans (inter_subset_left.trans inter_subset_left)), fun z hz hτ ↦ ?_, fun z hz ↦ ?_⟩
  · by_cases hfz : f z = 0
    · -- Off the support of `f` the section is the twist of `σ`, which vanishes only at `x`.
      have hzx : z ≠ x := by rintro rfl; exact one_ne_zero (f.eq_one ▸ hfz)
      have h₀ : (trivializationAt ℂ L z ⟨z, σ z⟩).2 = (0 : ℂ) :=
        (untwistSection_of_eq_zero hfz).symm.trans hτ
      refine hzx (hVσ z hz ?_)
      rw [← (trivializationAt ℂ L z).symm_apply_apply_mk (mem_baseSet_trivializationAt ℂ L z) (σ z),
        h₀, ← (trivializationAt ℂ L z).symmL_apply (R := ℂ) (mem_baseSet_trivializationAt ℂ L z),
        map_zero]
    · obtain ⟨⟨hze, -⟩, hzg⟩ := hfS (subset_tsupport _ hfz)
      have h0 : (e ⟨z, untwistSection L x s σ f c z⟩).2 = 0 := by
        rw [hτ]
        exact congrArg Prod.snd (e.zeroSection ℝ hze)
      by_cases hzx : z = x
      · subst hzx
        rw [trivializationAt_untwistSection hze, f.eq_one] at h0
        simp [hc] at h0
      · have hzs : z ∈ (chartAt ℂ x).source := by
          have hze' : z ∈ ((signedPointTwistCore ℂ L x s).localTriv (x, true)).baseSet := by
            rw [← signedPointTwistCore_trivializationAt_self]
            exact hze
          simpa using (mem_signedPointTwistCore_baseSet.1 hze').2
        exact trivializationAt_untwistSection_ne_zero hze hzx f.nonneg f.le_one
          (hzg fun h ↦ hzx ((chartAt ℂ x).injOn hzs (mem_chart_source ℂ x) h)) h0
  · have hfz : f z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hz (hfS h).1.2
    exact pointTwistDiv_untwistSection_of_eq_zero hfz fun h ↦ hz (h ▸ hx)

/-- **Untwisting a positive zero.** Let `σ` be a smooth section of `L` vanishing at `x`, and `V` a
neighbourhood of `x` containing no other zero of `σ`. If the real derivative `D` of the chart
reading of `σ` at `x` is within `‖c‖` of multiplication by `c`, so that `x` is a positive transverse
zero, then the negative point twist `L(-x)` has a smooth section with no zero in `V`, which outside
`V` is `σ`, read in `L` through `pointTwistDiv`. -/
theorem exists_negPointTwist_section_of_hasFDerivAt {x : X} {σ : ∀ z, L z}
    (hσ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ fun z ↦ TotalSpace.mk' ℂ z (σ z))
    (hσx : σ x = 0) {V : Set X} (hV : V ∈ 𝓝 x) (hVσ : ∀ z ∈ V, σ z = 0 → z = x)
    {D : ℂ →L[ℝ] ℂ} (hD : HasFDerivAt (negPointTwistChartReading ℂ x σ) D (chartAt ℂ x x))
    {c : ℂ} (hDc : ‖D - (ContinuousLinearMap.id ℝ ℂ).smulRight c‖ < ‖c‖) :
    ∃ τ : ∀ z, (negPointTwistCore ℂ L x).Fiber z,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ (fun z ↦ TotalSpace.mk' ℂ z (τ z)) ∧
        (∀ z ∈ V, τ z ≠ 0) ∧ ∀ z ∉ V, pointTwistDiv ℂ L x z (τ z) = σ z := by
  refine exists_untwist_section hσ hV hVσ false (c := c) ?_
  filter_upwards [hD.eventually_norm_sub_sub_apply_lt hDc] with w hw
  simpa [negPointTwistChartReading_chartAt_self ℂ hσx] using hw

/-- **Untwisting a negative zero.** Let `σ` be a smooth section of `L` vanishing at `x`, and `V` a
neighbourhood of `x` containing no other zero of `σ`. If the real derivative `D` of the chart
reading of `σ` at `x` is within `‖c‖` of `u ↦ conj u * c`, so that `x` is a negative transverse
zero, then the point twist `L(x)` has a smooth section with no zero in `V`, which outside `V` is
`σ`, read in `L` through `pointTwistDiv`. -/
theorem exists_pointTwist_section_of_hasFDerivAt {x : X} {σ : ∀ z, L z}
    (hσ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ fun z ↦ TotalSpace.mk' ℂ z (σ z))
    (hσx : σ x = 0) {V : Set X} (hV : V ∈ 𝓝 x) (hVσ : ∀ z ∈ V, σ z = 0 → z = x)
    {D : ℂ →L[ℝ] ℂ} (hD : HasFDerivAt (negPointTwistChartReading ℂ x σ) D (chartAt ℂ x x))
    {c : ℂ} (hDc : ‖D - Complex.conjCLE.toContinuousLinearMap.smulRight c‖ < ‖c‖) :
    ∃ τ : ∀ z, (pointTwistCore ℂ L x).Fiber z,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) ∞ (fun z ↦ TotalSpace.mk' ℂ z (τ z)) ∧
        (∀ z ∈ V, τ z ≠ 0) ∧ ∀ z ∉ V, pointTwistDiv ℂ L x z (τ z) = σ z := by
  refine exists_untwist_section hσ hV hVσ true (c := c) ?_
  filter_upwards [hD.eventually_norm_sub_sub_apply_lt hDc] with w hw
  simpa [negPointTwistChartReading_chartAt_self ℂ hσx] using hw

end Untwist

end TauCeti
