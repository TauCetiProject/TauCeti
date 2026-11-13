/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.RieszTransform.Kernel
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import TauCeti.Analysis.SpecialFunctions.Log.DivSub
public import Mathlib.Basic.Real.Sign

/-!
# The Hilbert transform

On the real line the Riesz transform in the direction `v`, `R_v = rieszTransform F v`, is `v`
times the **Hilbert transform** `H = R_1`. Its symbol is `ξ ↦ -i v sign ξ`
(`TauCeti.rieszSymbol_real`) and its kernel is `v / (π z)` (`TauCeti.rieszKernel_real`), so off
the support of its argument

`R_v f (x) = (v / π) ∫ f(y) / (x - y) dy`.

The Hilbert transform is the model Calderón–Zygmund operator. This file computes its exact `L²`
norm and shows, on an explicit example, that it is not bounded on `L¹`:

* `H` is an isometry of `L²(ℝ)`, and more generally `‖R_v f‖ = |v| ‖f‖`
  (`TauCeti.norm_rieszTransform_real_apply`), so `‖R_v‖ = |v|`
  (`TauCeti.norm_rieszTransform_real`). In higher dimensions only the sum
  `∑ⱼ ‖Rⱼ f‖² = ‖f‖²` survives.
* The Hilbert transform of the indicator of an interval `[a, b]` is
  `H 1_{[a, b]} (x) = π⁻¹ log |(x - a) / (x - b)|` off `[a, b]`
  (`TauCeti.ae_rieszTransform_indicatorConstLp_eq_log_smul`). This decays like
  `(b - a) / (π |x|)` at infinity, so it is not integrable
  (`TauCeti.not_integrable_rieszTransform_indicatorConstLp`).
* Hence `R_v` is not bounded on `L¹` for `v ≠ 0`: no estimate `‖R_v f‖₁ ≤ C ‖f‖₁` holds on
  `L² ∩ L¹` (`TauCeti.not_exists_eLpNorm_one_rieszTransform_real_le`). At `p = 1` the weak type
  `(1, 1)` bound `TauCeti.exists_mul_volume_lt_enorm_rieszTransform_le` cannot be upgraded to a
  strong type bound.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter II,
  §1 and Chapter III, §1.
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 5.1.
-/

public section

noncomputable section

open scoped ENNReal NNReal Real
open MeasureTheory Set

namespace TauCeti

/-! ### The symbol and the kernel on the real line -/

/-- On the real line the constant of the Riesz kernel is `c₁ = Γ(1) / π = π⁻¹`. -/
@[simp]
theorem rieszConst_real : rieszConst ℝ = π⁻¹ := by
  simp [rieszConst_def]

/-- On the real line the Riesz symbol in the direction `v` is `ξ ↦ -i v sign ξ`. For `v = 1` this
is the symbol of the Hilbert transform. -/
@[simp]
theorem rieszSymbol_real (v ξ : ℝ) :
    rieszSymbol v ξ = -Complex.I * ((v * Real.sign ξ : ℝ) : ℂ) := by
  rw [rieszSymbol_apply]
  congr 2
  rcases lt_trichotomy ξ 0 with h | rfl | h
  · simp [Real.sign_of_neg h, abs_of_neg h]
    field_simp [h.ne]
  · simp
  · simp [Real.sign_of_pos h, abs_of_pos h]
    field_simp [h.ne']

/-- On the real line the Riesz kernel in the direction `v` is `z ↦ v / (π z)`. For `v = 1` this is
the kernel of the Hilbert transform. -/
@[simp]
theorem rieszKernel_real (v z : ℝ) : rieszKernel v z = v / (π * z) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [rieszKernel_apply, rieszConst_real]
  simp
  field_simp

/-! ### The Hilbert transform is an isometry of `L²` -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- On the real line the Riesz transform in the direction `v` scales the `L²` norm by `|v|`:
`‖R_v f‖ = |v| ‖f‖`. In particular the Hilbert transform `R_1` is an isometry of `L²(ℝ)`. -/
@[simp]
theorem norm_rieszTransform_real_apply (v : ℝ) (f : Lp F 2 (volume : Measure ℝ)) :
    ‖rieszTransform F v f‖ = |v| * ‖f‖ := by
  have h1 : ‖rieszTransform F (1 : ℝ) f‖ = ‖f‖ := by
    have := sum_norm_rieszTransform_apply_sq (F := F) (OrthonormalBasis.singleton (Fin 1) ℝ) f
    simp only [Finset.univ_unique, Finset.sum_singleton, OrthonormalBasis.singleton_apply] at this
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  -- On `ℝ` the direction `v` is the scalar multiple `v • 1` of the unit direction.
  have hv : rieszTransform F v = (v : ℂ) • rieszTransform F (1 : ℝ) := by
    simpa using rieszTransform_smul (F := F) v (1 : ℝ)
  rw [hv, smul_apply, norm_smul, h1]
  simp

/-- On the real line the Riesz transform in the direction `v` has operator norm `|v|` on
`L²(ℝ, F)` for nonzero `F`. In particular the Hilbert transform has norm `1`. -/
theorem norm_rieszTransform_real [Nontrivial F] (v : ℝ) :
    ‖rieszTransform (E := ℝ) F v‖ = |v| := by
  refine le_antisymm (by simpa using norm_rieszTransform_le (F := F) v) ?_
  obtain ⟨c, hc⟩ := exists_ne (0 : F)
  set f : Lp F 2 (volume : Measure ℝ) :=
    indicatorConstLp 2 measurableSet_Icc (by simp : volume (Icc (0 : ℝ) 1) ≠ ∞) c
  have hf : ‖f‖ ≠ 0 := by
    simp [f, norm_indicatorConstLp, hc]
  have := (rieszTransform (E := ℝ) F v).le_opNorm f
  rw [norm_rieszTransform_real_apply] at this
  exact le_of_mul_le_mul_right this ((norm_nonneg f).lt_of_ne' hf)

/-! ### The Hilbert transform of an interval -/

/-- **The Hilbert transform of an interval.** On the real line, the Riesz transform in the
direction `v` of `c` times the indicator of `[a, b]` is

`R_v (c 1_{[a, b]}) (x) = (v / π) log |(x - a) / (x - b)| · c`

for almost every `x ∉ [a, b]`. (`Real.log` takes the logarithm of the absolute value.) -/
theorem ae_rieszTransform_indicatorConstLp_eq_log_smul (v : ℝ) {a b : ℝ} (hab : a ≤ b)
    (c : F) :
    ∀ᵐ x, x ∉ Icc a b →
      rieszTransform F v
          (indicatorConstLp (s := Icc a b) 2 measurableSet_Icc measure_Icc_lt_top.ne c) x =
        (v / π * Real.log ((x - a) / (x - b))) • c := by
  set f : Lp F 2 (volume : Measure ℝ) :=
    indicatorConstLp (s := Icc a b) 2 measurableSet_Icc measure_Icc_lt_top.ne c
  have hf : (f : ℝ → F) =ᵐ[volume] (Icc a b).indicator fun _ ↦ c := indicatorConstLp_coeFn
  have hf0 : ∀ᵐ x, x ∉ Icc a b → f x = 0 := by
    filter_upwards [hf] with x hx hxs
    rw [hx, indicator_of_notMem hxs]
  filter_upwards [ae_rieszTransform_eq_integral v f isCompact_Icc hf0] with x hx hxs
  rw [hx hxs, integral_congr_ae (hf.mono fun y hy ↦ by rw [hy])]
  rw [← indicator_smul (Icc a b) (fun y ↦ rieszKernel v (x - y)) fun _ ↦ c,
    integral_indicator measurableSet_Icc, integral_smul_const, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  congr 1
  simp_rw [rieszKernel_real, div_eq_mul_inv v, mul_inv, ← mul_assoc]
  -- `∫_a^b (x - y)⁻¹ dy = ∫_{x - b}^{x - a} u⁻¹ du`, and `0 ∉ [x - b, x - a]` since `x ∉ [a, b]`.
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left (·⁻¹),
    integral_inv]
  rw [uIcc_of_le (by linarith)]
  exact fun h ↦ hxs ⟨by linarith [h.2], by linarith [h.1]⟩

/-- **The Hilbert transform of an interval is not integrable.** On the real line, for `v ≠ 0`,
`a < b` and `c ≠ 0`, the Riesz transform `R_v (c 1_{[a, b]})` is not integrable: for large `x` its
norm is at least `|v| (b - a) ‖c‖ / (2 π x)`. -/
theorem not_integrable_rieszTransform_indicatorConstLp {v : ℝ} (hv : v ≠ 0) {a b : ℝ}
    (hab : a < b) {c : F} (hc : c ≠ 0) :
    ¬ Integrable (rieszTransform F v
      (indicatorConstLp (s := Icc a b) 2 measurableSet_Icc measure_Icc_lt_top.ne c)) := by
  intro hint
  set g := rieszTransform F v
    (indicatorConstLp (s := Icc a b) 2 measurableSet_Icc measure_Icc_lt_top.ne c)
  set m := max b |a|
  set C := |v| * (b - a) * ‖c‖ / (2 * π)
  have hC : 0 < C := by
    have := norm_pos_iff.2 hc
    have := abs_pos.2 hv
    have : 0 < b - a := sub_pos.2 hab
    positivity
  refine not_integrableOn_Ioi_inv (a := m) ((hint.norm.const_mul C⁻¹).integrableOn.mono'
    measurable_inv.aestronglyMeasurable ?_)
  filter_upwards [ae_restrict_of_ae
      (ae_rieszTransform_indicatorConstLp_eq_log_smul (F := F) v hab.le c),
    ae_restrict_mem measurableSet_Ioi] with x hx hxm
  have hxm : m < x := hxm
  have hxb : b < x := (le_max_left _ _).trans_lt hxm
  have hax : |a| < x := (le_max_right _ _).trans_lt hxm
  have hx0 : 0 < x := (abs_nonneg a).trans_lt hax
  have hxs : x ∉ Icc a b := fun h ↦ hxb.not_ge h.2
  -- For `x > max b |a|`, `log ((x - a) / (x - b)) ≥ (b - a) / (x - a) ≥ (b - a) / (2 x)`.
  have hlog : (b - a) / (2 * x) ≤ Real.log ((x - a) / (x - b)) :=
    calc (b - a) / (2 * x) ≤ (b - a) / (x - a) := by gcongr <;> linarith [neg_abs_le a]
      _ ≤ _ := Real.sub_div_sub_le_log_div_sub (by linarith [neg_abs_le a]) hxb
  have hlog0 : 0 ≤ Real.log ((x - a) / (x - b)) :=
    (div_nonneg (by linarith) (by linarith)).trans hlog
  have hg : ‖g x‖ = |v| / π * Real.log ((x - a) / (x - b)) * ‖c‖ := by
    rw [hx hxs, norm_smul]
    simp [abs_of_nonneg hlog0, abs_of_pos Real.pi_pos]
  rw [hg, norm_inv, Real.norm_of_nonneg hx0.le, le_inv_mul_iff₀ hC]
  calc C * x⁻¹ = |v| / π * ((b - a) / (2 * x)) * ‖c‖ := by
        simp only [C]; field_simp
    _ ≤ |v| / π * Real.log ((x - a) / (x - b)) * ‖c‖ := by gcongr

/-- **The Hilbert transform is not bounded on `L¹`.** On the real line, for `v ≠ 0` and nonzero
`F`, there is no constant `C` with `‖R_v f‖₁ ≤ C ‖f‖₁` for every `f ∈ L²`: the indicator of
`[0, 1]` is integrable while its Riesz transform is not. The weak type `(1, 1)` bound
`TauCeti.exists_mul_volume_lt_enorm_rieszTransform_le` is the substitute at this endpoint. -/
theorem not_exists_eLpNorm_one_rieszTransform_real_le [Nontrivial F] {v : ℝ} (hv : v ≠ 0) :
    ¬ ∃ C : ℝ≥0, ∀ f : Lp F 2 (volume : Measure ℝ),
      eLpNorm (rieszTransform F v f) 1 volume ≤ C * eLpNorm f 1 volume := by
  rintro ⟨C, hC⟩
  obtain ⟨c, hc⟩ := exists_ne (0 : F)
  set f : Lp F 2 (volume : Measure ℝ) :=
    indicatorConstLp (s := Icc 0 1) 2 measurableSet_Icc measure_Icc_lt_top.ne c
  have hf : eLpNorm f 1 volume < ∞ := by
    rw [eLpNorm_congr_ae indicatorConstLp_coeFn]
    exact memLp_indicator_const 1 measurableSet_Icc.nullMeasurableSet c
      (Or.inr measure_Icc_lt_top.ne)
  exact not_integrable_rieszTransform_indicatorConstLp hv zero_lt_one hc
    (memLp_one_iff_integrable.1 ((hC f).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf)))

end TauCeti
