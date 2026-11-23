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
  (`TauCeti.norm_rieszTransform_real_apply`). In higher dimensions a single Riesz transform is
  not a multiple of an isometry: only the operator norm `‖R_v‖ = ‖v‖`
  (`TauCeti.norm_rieszTransform`) and the sum `∑ⱼ ‖Rⱼ f‖² = ‖f‖²` survive.
* The Hilbert transform of the indicator of an interval `[a, b]` is
  `H 1_{[a, b]} (x) = π⁻¹ log |(x - a) / (x - b)|` off `[a, b]`
  (`TauCeti.ae_rieszTransform_indicatorConstLp_eq_log_smul`). This decays like
  `(b - a) / (π |x|)` at infinity, so it is not integrable
  (`TauCeti.not_integrable_rieszTransform_indicatorConstLp`).
* Hence `R_v` is not bounded on `L¹` for `v ≠ 0`: no estimate `‖R_v f‖₁ ≤ C ‖f‖₁` holds on
  `L² ∩ L¹` (`TauCeti.not_exists_eLpNorm_one_rieszTransform_real_le`). At `p = 1` the weak type
  `(1, 1)` bound, `TauCeti.HasStandardKernel.exists_mul_volume_lt_enorm_le` applied to
  `TauCeti.hasStandardKernel_rieszTransform`, cannot be upgraded to a strong type bound.
* The commutator of `R_v` with multiplication by `x` is constant off the support of its argument:
  if `f` vanishes off a compact set `s`, then `x • R_v f (x) - R_v (x • f) (x) = (v / π) • ∫ f`
  for almost every `x ∉ s`
  (`TauCeti.ae_smul_rieszTransform_sub_rieszTransform_eq_smul_integral`). Hence this commutator
  is not bounded on any `Lᵖ`, `0 < p < ∞`
  (`TauCeti.not_exists_eLpNorm_smul_rieszTransform_sub_rieszTransform_le`). The
  Coifman–Rochberg–Weiss theorem bounds the commutator `[b, R_v]` for `b` of bounded mean
  oscillation, and `x` is not of bounded mean oscillation
  (`ContinuousLinearMap.bmoSeminorm_eq_top`), so the hypothesis on `b` cannot be dropped.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter II,
  §1 and Chapter III, §1.
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 5.1.
* R. R. Coifman, R. Rochberg and G. Weiss, *Factorization theorems for Hardy spaces in several
  variables*, Ann. of Math. **103** (1976), 611–635 (the commutator theorem).
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
(`TauCeti.HasStandardKernel.exists_mul_volume_lt_enorm_le` applied to
`TauCeti.hasStandardKernel_rieszTransform`) is the substitute at this endpoint. -/
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

/-! ### The commutator with multiplication by `x` -/

/-- **The commutator of the Hilbert transform with `x`.** On the real line let `f ∈ L²` vanish
almost everywhere off a compact set `s`, and let `g ∈ L²` be `x • f`. Off `s` the commutator of
the Riesz transform `R_v` with multiplication by `x` is the constant

`x • R_v f (x) - R_v g (x) = (v / π) • ∫ f`

for almost every `x ∉ s`. -/
theorem ae_smul_rieszTransform_sub_rieszTransform_eq_smul_integral (v : ℝ)
    {f g : Lp F 2 (volume : Measure ℝ)} {s : Set ℝ} (hs : IsCompact s)
    (hf : ∀ᵐ x, x ∉ s → f x = 0) (hg : ∀ᵐ x, g x = x • f x) :
    ∀ᵐ x, x ∉ s → x • rieszTransform F v f x - rieszTransform F v g x = (v / π) • ∫ y, f y := by
  have hg0 : ∀ᵐ x, x ∉ s → g x = 0 := by
    filter_upwards [hf, hg] with x hfx hgx hxs
    rw [hgx, hfx hxs, smul_zero]
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.2 hs.measure_lt_top.ne
  have hfi : Integrable f :=
    IntegrableOn.integrable_of_ae_notMem_eq_zero (s := s)
      (((Lp.memLp f).restrict s).integrable one_le_two) hf
  filter_upwards [ae_rieszTransform_eq_integral v f hs hf,
    ae_rieszTransform_eq_integral v g hs hg0] with x hRf hRg hxs
  rw [hRf hxs, hRg hxs]
  have hKf : Integrable fun y ↦ rieszKernel v (x - y) • f y :=
    integrable_rieszKernel_sub_smul_of_notMem v one_le_two (Lp.memLp f) hs hf hxs
  -- Almost everywhere `K(x - y) • g y = x • (K(x - y) • f y) - (v / π) • f y`.
  have hpt : (fun y ↦ rieszKernel v (x - y) • g y) =ᵐ[volume]
      fun y ↦ x • (rieszKernel v (x - y) • f y) - (v / π) • f y := by
    filter_upwards [hf, hg] with y hfy hgy
    rw [hgy]
    by_cases hys : y ∈ s
    · have hxy : x - y ≠ 0 := sub_ne_zero.2 fun h ↦ hxs (h ▸ hys)
      rw [smul_smul, smul_smul, ← sub_smul, rieszKernel_real]
      congr 1
      field_simp
      ring
    · simp [hfy hys]
  have h₁ : Integrable fun y ↦ x • (rieszKernel v (x - y) • f y) := hKf.smul x
  have h₂ : Integrable fun y ↦ (v / π) • f y := hfi.smul (v / π)
  rw [integral_congr_ae hpt, integral_sub h₁ h₂, integral_smul, integral_smul, sub_sub_cancel]

/-- **The commutator of the Hilbert transform with `x` is unbounded.** On the real line, for
`v ≠ 0`, nonzero `F` and `0 < p < ∞`, there is no constant `C` with

`‖x • R_v f - R_v (x • f)‖_p ≤ C ‖f‖_p`

for all `f ∈ L²` with `x • f ∈ L²`. This is consistent with the
Coifman–Rochberg–Weiss theorem `TauCeti.exists_eLpNorm_smul_sub_le_of_norm_sub_le_mul_rpow`, which
bounds `[b, T]` for `b` of bounded mean oscillation, since `x` does not have bounded mean
oscillation (`ContinuousLinearMap.bmoSeminorm_eq_top`). -/
theorem not_exists_eLpNorm_smul_rieszTransform_sub_rieszTransform_le [Nontrivial F] {v : ℝ}
    (hv : v ≠ 0) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    ¬ ∃ C : ℝ≥0, ∀ f g : Lp F 2 (volume : Measure ℝ), (∀ᵐ x, g x = x • f x) →
      eLpNorm (fun x ↦ x • rieszTransform F v f x - rieszTransform F v g x) p volume ≤
        C * eLpNorm f p volume := by
  -- Test against `f`, the indicator of `[0, 1]` times `c ≠ 0`: by
  -- `ae_smul_rieszTransform_sub_rieszTransform_eq_smul_integral`, the commutator is the nonzero
  -- constant `(v / π) • c` on `(1, ∞)`, so its `Lᵖ` norm is infinite while `‖f‖_p` is finite.
  rintro ⟨C, hC⟩
  obtain ⟨c, hc⟩ := exists_ne (0 : F)
  set f : Lp F 2 (volume : Measure ℝ) :=
    indicatorConstLp (s := Icc 0 1) 2 measurableSet_Icc measure_Icc_lt_top.ne c
  have hf : (f : ℝ → F) =ᵐ[volume] (Icc 0 1).indicator fun _ ↦ c := indicatorConstLp_coeFn
  -- The function `x • f`, bounded by `‖c‖` and supported in `[0, 1]`, is in `L²`.
  have hg : MemLp ((Icc (0 : ℝ) 1).indicator fun x ↦ x • c) 2 volume := by
    rw [memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
    have : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
      isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
    refine MemLp.of_bound (continuous_id.smul continuous_const).aestronglyMeasurable ‖c‖
      (ae_restrict_of_forall_mem measurableSet_Icc fun x hx ↦ ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact mul_le_of_le_one_left (norm_nonneg c) hx.2
  have hgf : ∀ᵐ x, hg.toLp _ x = x • f x := by
    filter_upwards [hg.coeFn_toLp, hf] with x hgx hfx
    rw [hgx, hfx]
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [hx]
  have hint : ∫ y, f y = c := by
    rw [integral_indicatorConstLp, Real.volume_real_Icc_of_le zero_le_one, sub_zero, one_smul]
  set w : F := (v / π) • c
  have hw : w ≠ 0 := smul_ne_zero (div_ne_zero hv Real.pi_ne_zero) hc
  -- On `(1, ∞)` the commutator is the nonzero constant `w`, so its `Lᵖ` norm is infinite.
  have hcomm : ∀ᵐ x ∂volume.restrict (Ioi 1),
      x • rieszTransform F v f x - rieszTransform F v (hg.toLp _) x = w := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [ae_smul_rieszTransform_sub_rieszTransform_eq_smul_integral v isCompact_Icc
      (hf.mono fun x hx hxs ↦ by rw [hx, indicator_of_notMem hxs]) hgf] with x hx hx1
    rw [hx fun h ↦ (not_le.2 (mem_Ioi.1 hx1)) h.2, hint]
  have htop : eLpNorm (fun x ↦ x • rieszTransform F v f x - rieszTransform F v (hg.toLp _) x) p
      volume = ∞ := by
    refine top_le_iff.1 ((le_of_eq ?_).trans
      (eLpNorm_mono_measure _ (Measure.restrict_le_self (s := Ioi 1))))
    rw [eLpNorm_congr_ae hcomm, eLpNorm_const' w hp0 hp, Measure.restrict_apply_univ,
      Real.volume_Ioi, ENNReal.top_rpow_of_pos (by simp [ENNReal.toReal_pos hp0 hp]),
      ENNReal.mul_top (by simpa using hw)]
  have hfp : eLpNorm f p volume ≠ ∞ := by
    rw [eLpNorm_congr_ae hf]
    exact (memLp_indicator_const p measurableSet_Icc.nullMeasurableSet c
      (Or.inr measure_Icc_lt_top.ne)).eLpNorm_ne_top
  exact (ENNReal.mul_ne_top ENNReal.coe_ne_top hfp) (top_le_iff.1 (htop ▸ hC f _ hgf))

end TauCeti
