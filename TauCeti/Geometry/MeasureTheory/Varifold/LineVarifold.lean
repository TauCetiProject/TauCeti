/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Varifold.FirstVariation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.LinearAlgebra.Trace
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# A varifold on a line with a constant plane, and the vertical lift

Let `E` be a finite-dimensional real inner product space. For `a, u ∈ E` with `u ≠ 0` and a plane
`P ∈ G(E, k)`, the varifold `Euclidean.lineVarifold a u P` is the image of Lebesgue measure on `ℝ`
under `t ↦ (a + t u, P)`: its weight is carried by the line `a + ℝu`, and every point carries the
same plane `P`. Its first variation is `δV(X) = ∫ tr (P ∘ DX(a + t u)) dt`
(`Euclidean.firstVariation_lineVarifold_apply`).

The *vertical lift* `Euclidean.verticalLift a u w` of the line is the case where `P` is the line
spanned by a unit vector `w` orthogonal to `u`. It does not have locally bounded first variation:
for a smooth `ψ` of compact support, the fields `X_n(y) = n⁻¹ ψ(y) sin(n ⟪w, y - a⟫) w` satisfy
`‖X_n‖ ≤ n⁻¹ sup |ψ|` while `δV(X_n) = ∫ ψ(a + t u) dt` for every `n`
(`Euclidean.firstVariation_verticalLift_verticalField`).
Hence no bound `|δV(X)| ≤ C sup |X|` holds for the fields supported in any closed ball centred on
the line (`Euclidean.not_exists_abs_firstVariation_verticalLift_le`).

## Main definitions

* `Euclidean.lineVarifold a u P`: the line `a + ℝu`, parametrized by Lebesgue measure, with the
  constant plane `P`.
* `Euclidean.verticalLift a u w`: the line `a + ℝu` with the constant plane `span {w}`.

## Main results

* `Euclidean.firstVariation_lineVarifold_apply`: `δV(X) = ∫ tr (P ∘ DX(a + t u)) dt`.
* `Euclidean.firstVariation_verticalLift_verticalField`: `δV(X_n) = ∫ ψ(a + t u) dt`.
* `Euclidean.not_exists_abs_firstVariation_verticalLift_le`: the vertical lift does not have
  locally bounded first variation.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §39.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Module Metric
open scoped Distributions RealInnerProductSpace ContDiff

namespace Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

/-! ### The vertical fields -/

/-- The vertical field `X_n(y) = n⁻¹ ψ(y) sin(n ⟪w, y - a⟫) w` of a smooth `ψ` is smooth. -/
private theorem contDiff_verticalField {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (a w : E) (n : ℝ) :
    ContDiff ℝ ∞ fun y => (n⁻¹ * ψ y * Real.sin (n * ⟪w, y - a⟫)) • w :=
  ((contDiff_const.mul hψ).mul (Real.contDiff_sin.comp
    (contDiff_const.mul ((innerSL ℝ w).contDiff.comp (contDiff_id.sub contDiff_const))))).smul
    contDiff_const

/-- The vertical field `X_n` as a test vector field, for `ψ` smooth with compact support. -/
def verticalField {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (a w : E)
    (n : ℝ) : 𝓓^{1}((⊤ : Opens E), E) :=
  ⟨fun y => (n⁻¹ * ψ y * Real.sin (n * ⟪w, y - a⟫)) • w,
    (contDiff_verticalField hψ a w n).of_le (by exact_mod_cast le_top),
    (hψc.mul_left.mul_right).smul_right, by simp⟩

/-- The vertical field evaluates to `n⁻¹ ψ(y) sin(n ⟪w, y - a⟫) w`. -/
@[simp]
theorem verticalField_apply {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (a w : E) (n : ℝ) (y : E) :
    verticalField hψ hψc a w n y = (n⁻¹ * ψ y * Real.sin (n * ⟪w, y - a⟫)) • w :=
  (rfl)

/-- As a function, the vertical field is `y ↦ n⁻¹ ψ(y) sin(n ⟪w, y - a⟫) w`. -/
theorem coe_verticalField {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (a w : E) (n : ℝ) :
    ⇑(verticalField hψ hψc a w n) = fun y => (n⁻¹ * ψ y * Real.sin (n * ⟪w, y - a⟫)) • w :=
  funext (verticalField_apply hψ hψc a w n)

/-- The vertical field is small: `‖X_n(y)‖ ≤ |n|⁻¹ |ψ(y)| ‖w‖`. -/
theorem norm_verticalField_le {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (a w : E) (n : ℝ) (y : E) :
    ‖verticalField hψ hψc a w n y‖ ≤ |n|⁻¹ * |ψ y| * ‖w‖ := by
  rw [verticalField_apply, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_inv]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)) (norm_nonneg w)

/-- Along the line `a + ℝu` with `u ⊥ w`, the tangential divergence of the vertical field along
the line spanned by `w` is `ψ`. -/
private theorem tangentialDivergence_verticalField [FiniteDimensional ℝ E] {ψ : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) {a u w : E} (huw : ⟪w, u⟫ = 0) (hw : ‖w‖ = 1) {n : ℝ}
    (hn : n ≠ 0) (t : ℝ) :
    tangentialDivergence (verticalField hψ hψc a w n) (a + t • u) (ℝ ∙ w).starProjection =
      ψ (a + t • u) := by
  set y := a + t • u
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ y) y :=
    (hψ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hin : HasFDerivAt (fun y => n * ⟪w, y - a⟫) (n • innerSL ℝ w) y :=
    (((innerSL ℝ w).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const a))).const_mul n
  have hc := ((hψd.const_mul n⁻¹).mul (Real.hasDerivAt_sin _ |>.comp_hasFDerivAt y hin))
  set c' : E →L[ℝ] ℝ := (n⁻¹ * ψ y) • (Real.cos (n * ⟪w, y - a⟫) • n • innerSL ℝ w) +
    Real.sin (n * ⟪w, y - a⟫) • n⁻¹ • fderiv ℝ ψ y
  have hX : HasFDerivAt (fun y => (n⁻¹ * ψ y * Real.sin (n * ⟪w, y - a⟫)) • w)
      (c'.smulRight w) y := hc.smul_const w
  have hya : ⟪w, y - a⟫ = 0 := by simp [y, inner_smul_right, huw]
  have hPw : (ℝ ∙ w).starProjection w = w :=
    Submodule.starProjection_eq_self_iff.2 (Submodule.mem_span_singleton_self w)
  rw [tangentialDivergence_def, coe_verticalField, hX.fderiv]
  have hlin : (((ℝ ∙ w).starProjection ∘L c'.smulRight w : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      (c' : E →ₗ[ℝ] ℝ).smulRight w := by
    ext v
    simp [hPw]
  rw [hlin, LinearMap.trace_smulRight]
  simp only [c', hya, mul_zero, Real.cos_zero, Real.sin_zero, ContinuousLinearMap.coe_coe,
    add_apply, smul_apply, innerSL_apply_apply,
    real_inner_self_eq_norm_sq, hw, smul_eq_mul, zero_mul, add_zero, one_pow, one_mul, mul_one]
  field_simp

/-! ### The line varifold -/

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


/-- The varifold of the line `a + ℝu`, parametrized by Lebesgue measure, carrying the constant
plane `P` at every point: the image of Lebesgue measure under `t ↦ (a + t u, P)`. -/
def lineVarifold (a u : E) (P : grassmannian ℝ E k) :
    Measure ((⊤ : Opens E) × grassmannian ℝ E k) :=
  (volume : Measure ℝ).map fun t => (⟨a + t • u, by simp⟩, P)

omit [BorelSpace E] in
/-- The defining formula of `Euclidean.lineVarifold`. -/
theorem lineVarifold_def (a u : E) (P : grassmannian ℝ E k) :
    lineVarifold a u P = (volume : Measure ℝ).map fun t => (⟨a + t • u, by simp⟩, P) := by
  rw [lineVarifold]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The parametrization `t ↦ (a + t u, P)` of the line varifold is continuous. -/
private theorem continuous_lineVarifold_param (a u : E) (P : grassmannian ℝ E k) :
    Continuous fun t : ℝ => ((⟨a + t • u, by simp⟩ : (⊤ : Opens E)), P) :=
  ((continuous_const.add (continuous_id.smul continuous_const)).subtype_mk fun _ => by
    simp).prodMk continuous_const

/-- The line varifold is finite on compact sets. -/
theorem isFiniteMeasureOnCompacts_lineVarifold {a u : E} (hu : u ≠ 0) (P : grassmannian ℝ E k) :
    IsFiniteMeasureOnCompacts (lineVarifold a u P) := by
  refine ⟨fun K hK => ?_⟩
  rw [lineVarifold_def, Measure.map_apply (continuous_lineVarifold_param a u P).measurable
    hK.isClosed.measurableSet]
  refine (measure_mono fun t ht => ?_).trans_lt
    ((TauCeti.isClosedEmbedding_add_smul_left a hu).isCompact_preimage
      ((hK.image continuous_fst).image continuous_subtypeVal)).measure_lt_top
  exact ⟨_, ⟨_, ht, rfl⟩, rfl⟩

/-- **The first variation of a line varifold** is `δV(X) = ∫ tr (P ∘ DX(a + t u)) dt`. -/
theorem firstVariation_lineVarifold_apply {a u : E} (hu : u ≠ 0) (P : grassmannian ℝ E k)
    (X : 𝓓^{1}((⊤ : Opens E), E)) :
    firstVariation (lineVarifold a u P) X = ∫ t : ℝ, tangentialDivergence X (a + t • u) P := by
  have := isFiniteMeasureOnCompacts_lineVarifold (a := a) hu P
  rw [firstVariation_apply, lineVarifold_def,
    integral_map (continuous_lineVarifold_param a u P).aemeasurable (by
    simpa using (tangentialDivergenceCc (k := k) X).continuous.aestronglyMeasurable)]

/-- The *vertical lift* of the line `a + ℝu` along `w ≠ 0`: the line varifold carrying the
constant plane `span {w}` at every point. -/
def verticalLift (a u w : E) (hw : w ≠ 0) : Measure ((⊤ : Opens E) × grassmannian ℝ E 1) :=
  lineVarifold a u
    ⟨(ℝ ∙ w).starProjection, grassmannian.starProjection_mem (finrank_span_singleton hw)⟩

/-- **The first variation of the vertical lift on the vertical fields.** For the line `a + ℝu`
with the constant plane `span {w}`, `w` a unit vector orthogonal to `u ≠ 0`, the vertical field
`X_n` has `δV(X_n) = ∫ ψ(a + t u) dt` for every `n ≠ 0`, although `‖X_n‖ ≤ |n|⁻¹ sup |ψ|`. -/
theorem firstVariation_verticalLift_verticalField {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) {a u w : E} (hu : u ≠ 0) (huw : ⟪w, u⟫ = 0) (hw : ‖w‖ = 1)
    {n : ℝ} (hn : n ≠ 0) :
    firstVariation (verticalLift a u w (norm_ne_zero_iff.1 (hw ▸ one_ne_zero)))
      (verticalField hψ hψc a w n) = ∫ t : ℝ, ψ (a + t • u) := by
  rw [verticalLift, firstVariation_lineVarifold_apply hu]
  exact integral_congr_ae (ae_of_all _ fun t =>
    tangentialDivergence_verticalField hψ hψc huw hw hn t)

/-- **The vertical lift does not have locally bounded first variation.** For the line `a + ℝu`
with the constant plane `span {w}`, `w` a unit vector orthogonal to `u ≠ 0`, and any `r > 0`,
there is no constant `C` with `|δV(X)| ≤ C M` for every `C¹` field `X` supported in
`closedBall a r` with `‖X‖ ≤ M`. -/
theorem not_exists_abs_firstVariation_verticalLift_le {a u w : E} (hu : u ≠ 0)
    (huw : ⟪w, u⟫ = 0) (hw : ‖w‖ = 1) {r : ℝ} (hr : 0 < r) :
    ¬∃ C : ℝ, ∀ X : 𝓓^{1}((⊤ : Opens E), E), tsupport X ⊆ closedBall a r → ∀ M : ℝ,
      (∀ y, ‖X y‖ ≤ M) →
        |firstVariation (verticalLift a u w (norm_ne_zero_iff.1 (hw ▸ one_ne_zero))) X| ≤
          C * M := by
  rintro ⟨C, hC⟩
  -- Test against the vertical fields of a bump `θ` equal to one near `a`.
  let θ : ContDiffBump a := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  -- The integral of the bump along the line is positive.
  set I := ∫ t : ℝ, θ (a + t • u)
  have hI : 0 < I := Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := 0)
    (θ.continuous.comp (continuous_const.add (continuous_id.smul continuous_const)))
    (θ.hasCompactSupport.comp_isClosedEmbedding (TauCeti.isClosedEmbedding_add_smul_left a hu))
    (fun t => θ.nonneg)
    (by simp [θ.one_of_mem_closedBall (mem_closedBall_self (half_pos hr).le)])
  -- The vertical field with `n = |C| / I + 1` breaks the bound.
  set n : ℝ := |C| / I + 1
  have hn : 0 < n := by positivity
  have h := hC (verticalField θ.contDiff θ.hasCompactSupport a w n)
    ((closure_mono fun y hy => ?_).trans θ.tsupport_eq.subset) n⁻¹ fun y =>
      (norm_verticalField_le θ.contDiff θ.hasCompactSupport a w n y).trans (by
        rw [hw, mul_one, abs_of_pos hn, abs_of_nonneg θ.nonneg]
        exact mul_le_of_le_one_right (by positivity) θ.le_one)
  · rw [firstVariation_verticalLift_verticalField θ.contDiff θ.hasCompactSupport hu huw hw
      hn.ne', abs_of_pos hI, ← div_eq_mul_inv, le_div_iff₀ hn] at h
    have : C < I * n := by
      rw [mul_add, mul_div_cancel₀ _ hI.ne', mul_one]
      linarith [le_abs_self C]
    linarith
  · by_contra hθ
    exact hy (by simp [Function.notMem_support.1 hθ])

end Euclidean
