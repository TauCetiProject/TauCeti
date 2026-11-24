/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Manifold.IntegralCurve.Reparam
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Damping a vector field to make it complete

The negative gradient flow of a proper function bounded below need not be complete: for
`f x = x² + x⁴` on `ℝ` with the Euclidean metric, the trajectory through `1` escapes to infinity in
finite backward time (`TauCeti.NoncompactLineExample.exists_isIntegralCurveOn_Icc_iff`).
Completeness is restored by slowing the field down where `f` changes fast along it. This file does
so without changing the field near its zeros.

The **damping factor** `TauCeti.rateDamping s = (1 + τ(s² - 1) s²)⁻¹`, where `τ` is Mathlib's
smooth transition function `Real.smoothTransition`, is a smooth function of `s` with values in
`(0, 1]`, equal to `1` for `|s| ≤ 1`, and such that `|s · rateDamping s| ≤ 2`. For a function
`f : M → ℝ` and a vector field `v`, the **damped field**

`TauCeti.rateDampedField f v x = rateDamping (df_x (v x)) • v x`

is a positive multiple of `v`, equal to `v` wherever `|df(v)| ≤ 1`, in particular near the zeros
of `v` and near the critical points of `f`. Along it `f` changes at rate at most `2`, so it is
complete as soon as `f` is proper (`TauCeti.isCompleteVectorField_rateDampedField`), by the
completeness criterion `TauCeti.isCompleteVectorField_of_isProperMap_of_abs_mvfderiv_le`. It is
`C^n` when `f` is `C^(n+1)` and `v` is `C^n`. Since it is a positive multiple of `v` with factor
at most `1`, every global integral curve of `v` is reparametrized by an order automorphism of `ℝ`
into an integral curve of the damped field
(`IsMIntegralCurve.exists_orderIso_isMIntegralCurve_comp_rateDampedField`), with the same image
run in the same direction and the same limits at `±∞`.

This is the rescaling to a complete pseudo-gradient used to run Morse theory on noncompact
manifolds with a proper Morse function.

## Main declarations

* `TauCeti.rateDamping`: the damping factor, with `rateDamping_pos`, `rateDamping_le_one`,
  `rateDamping_of_abs_le_one`, `abs_mul_rateDamping_le_two` and `contDiff_rateDamping`.
* `TauCeti.rateDampedField`: the damped field `rateDamping (df(v)) • v`.
* `TauCeti.rateDampedField_of_abs_le_one`: it agrees with `v` where `|df(v)| ≤ 1`.
* `TauCeti.mvfderiv_rateDampedField`, `TauCeti.abs_mvfderiv_rateDampedField_le_two`: the rate
  of change of `f` along it is `rateDamping (df(v)) · df(v)`, at most `2` in absolute value.
* `TauCeti.contMDiff_rateDampedField`: it is `C^n` when `f` is `C^(n+1)` and `v` is `C^n`.
* `TauCeti.isCompleteVectorField_rateDampedField`: it is complete when `f` is proper.
* `IsMIntegralCurve.exists_orderIso_isMIntegralCurve_comp_rateDampedField`: global integral
  curves of `v` are reparametrized integral curves of the damped field.

## References

* J. Milnor, *Morse theory*, Annals of Mathematics Studies **51**, Princeton University Press,
  1963, Lemma 2.4 and the proof of Theorem 3.1 (multiplying a gradient field by a function to
  control its flow, and completeness of compactly supported fields).
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti

/-! ### The damping factor -/

/-- The **damping factor** `s ↦ (1 + τ(s² - 1) s²)⁻¹`, where `τ = Real.smoothTransition` vanishes
on `(-∞, 0]` and equals `1` on `[1, ∞)`. It is smooth, takes values in `(0, 1]`, equals `1` for
`|s| ≤ 1` and equals `(1 + s²)⁻¹` for `s² ≥ 2`, so that `|s · rateDamping s| ≤ 2`. -/
def rateDamping (s : ℝ) : ℝ :=
  (1 + Real.smoothTransition (s ^ 2 - 1) * s ^ 2)⁻¹

theorem rateDamping_def (s : ℝ) :
    rateDamping s = (1 + Real.smoothTransition (s ^ 2 - 1) * s ^ 2)⁻¹ :=
  (rfl)

/-- The denominator of the damping factor is at least `1`. -/
private theorem one_le_one_add_smoothTransition_mul (s : ℝ) :
    1 ≤ 1 + Real.smoothTransition (s ^ 2 - 1) * s ^ 2 :=
  le_add_of_nonneg_right (mul_nonneg (Real.smoothTransition.nonneg _) (sq_nonneg s))

theorem rateDamping_pos (s : ℝ) : 0 < rateDamping s :=
  inv_pos.2 (zero_lt_one.trans_le (one_le_one_add_smoothTransition_mul s))

theorem rateDamping_le_one (s : ℝ) : rateDamping s ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_one_add_smoothTransition_mul s)

/-- The damping factor is `1` on `[-1, 1]`. -/
theorem rateDamping_of_abs_le_one {s : ℝ} (hs : |s| ≤ 1) : rateDamping s = 1 := by
  have hs2 : s ^ 2 - 1 ≤ 0 := by
    rw [sub_nonpos, ← sq_abs]
    exact pow_le_one₀ (abs_nonneg s) hs
  rw [rateDamping, Real.smoothTransition.zero_of_nonpos hs2, zero_mul, add_zero, inv_one]

/-- **The damping bound** `|s · rateDamping s| ≤ 2`. For `s² ≤ 4` this follows from
`rateDamping s ≤ 1`, and for `s² ≥ 2` the factor is `(1 + s²)⁻¹`. -/
theorem abs_mul_rateDamping_le_two (s : ℝ) : |s * rateDamping s| ≤ 2 := by
  rw [abs_mul, abs_of_pos (rateDamping_pos s)]
  rcases le_or_gt (s ^ 2) 4 with hs | hs
  · have hs' : |s| ≤ 2 := by nlinarith [sq_abs s, abs_nonneg s]
    nlinarith [rateDamping_le_one s, rateDamping_pos s, abs_nonneg s]
  · rw [rateDamping, Real.smoothTransition.one_of_one_le (by linarith), one_mul,
      ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith [sq_abs s, abs_nonneg s]

theorem contDiff_rateDamping {n : ℕ∞} : ContDiff ℝ n rateDamping :=
  (contDiff_const.add ((Real.smoothTransition.contDiff.comp
    ((contDiff_id.pow 2).sub contDiff_const)).mul (contDiff_id.pow 2))).inv
    fun s ↦ (zero_lt_one.trans_le (one_le_one_add_smoothTransition_mul s)).ne'

/-! ### The damped field -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {f : M → ℝ} {v : (x : M) → TangentSpace I x}

variable (I) in
/-- The **damped field** `rateDamping (df(v)) • v` of a vector field `v` with respect to a function
`f`: a positive multiple of `v`, equal to `v` where `|df(v)| ≤ 1`, along which `f` changes at rate
at most `2`. -/
def rateDampedField (f : M → ℝ) (v : (x : M) → TangentSpace I x) (x : M) : TangentSpace I x :=
  rateDamping (mvfderiv I f x (v x)) • v x

theorem rateDampedField_apply (x : M) :
    rateDampedField I f v x = rateDamping (mvfderiv I f x (v x)) • v x :=
  (rfl)

/-- The damped field agrees with `v` where `|df(v)| ≤ 1`, in particular at the zeros of `v` and
at the critical points of `f`. -/
theorem rateDampedField_of_abs_le_one {x : M} (hx : |mvfderiv I f x (v x)| ≤ 1) :
    rateDampedField I f v x = v x := by
  rw [rateDampedField_apply, rateDamping_of_abs_le_one hx, one_smul]

/-- The damped field vanishes exactly where `v` does. -/
@[simp]
theorem rateDampedField_eq_zero_iff {x : M} : rateDampedField I f v x = 0 ↔ v x = 0 := by
  rw [rateDampedField_apply, smul_eq_zero, or_iff_right (rateDamping_pos _).ne']

/-- The derivative of `f` along the damped field is the damped derivative along `v`. -/
theorem mvfderiv_rateDampedField (x : M) :
    mvfderiv I f x (rateDampedField I f v x) =
      rateDamping (mvfderiv I f x (v x)) * mvfderiv I f x (v x) := by
  rw [rateDampedField_apply, map_smul, smul_eq_mul]

/-- `f` changes at rate at most `2` along the damped field. -/
theorem abs_mvfderiv_rateDampedField_le_two (x : M) :
    |mvfderiv I f x (rateDampedField I f v x)| ≤ 2 := by
  rw [mvfderiv_rateDampedField, mul_comm]
  exact abs_mul_rateDamping_le_two _

/-- The damped field is `C^n` when `f` is `C^(n+1)` and `v` is `C^n`. -/
theorem contMDiff_rateDampedField [IsManifold I 1 M] {n : ℕ∞}
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f)
    (hv : ContMDiff I I.tangent n (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    ContMDiff I I.tangent n (fun x ↦ (⟨x, rateDampedField I f v x⟩ : TangentBundle I M)) := by
  have hdf : ContMDiff I 𝓘(ℝ) n (fun x ↦ mvfderiv I f x (v x)) :=
    (hf.contMDiff_mvfderiv_apply le_rfl).comp hv
  exact (contDiff_rateDamping.comp_contMDiff hdf).smul_section hv

/-- **The damped field of a proper function is complete.** If `f` is proper and `C²` and `v` is
`C¹`, then `f` changes at rate at most `2` along `rateDamping (df(v)) • v`, so this field is
complete by `TauCeti.isCompleteVectorField_of_isProperMap_of_abs_mvfderiv_le`. No lower bound on
`f` and no growth condition on `v` is needed. -/
theorem isCompleteVectorField_rateDampedField [T2Space M]
    [BoundarylessManifold I M] [IsManifold I 1 M] (hfp : IsProperMap f)
    (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    IsCompleteVectorField (rateDampedField I f v) :=
  isCompleteVectorField_of_isProperMap_of_abs_mvfderiv_le
    (contMDiff_rateDampedField (n := 1) hf hv) hfp (hf.mdifferentiable (by norm_num))
    abs_mvfderiv_rateDampedField_le_two

end TauCeti

open TauCeti in
/-- **The damped field has the trajectories of `v`.** If `f` is `C¹` and `v` is continuous, every
global integral curve `γ` of `v` becomes an integral curve of the damped field
`rateDamping (df(v)) • v` after an increasing change of time `ψ : ℝ ≃o ℝ` fixing `0`. So `γ ∘ ψ`
has the image of `γ`, runs in the same direction, and has the same limits at `±∞`. -/
theorem IsMIntegralCurve.exists_orderIso_isMIntegralCurve_comp_rateDampedField
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {f : M → ℝ} {v : (x : M) → TangentSpace I x} {γ : ℝ → M}
    (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hv : ContMDiff I I.tangent 0 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurve γ v) :
    ∃ ψ : ℝ ≃o ℝ, ψ 0 = 0 ∧ IsMIntegralCurve (γ ∘ ψ) (rateDampedField I f v) :=
  hγ.exists_orderIso_isMIntegralCurve_comp
    ((contDiff_rateDamping (n := 0)).continuous.comp
      (((hf.contMDiff_mvfderiv_apply (m := 0) (by simp)).comp hv).continuous.comp hγ.continuous))
    (fun _ ↦ rateDamping_pos _) (fun _ ↦ rateDamping_le_one _) fun _ ↦ rateDampedField_apply _
