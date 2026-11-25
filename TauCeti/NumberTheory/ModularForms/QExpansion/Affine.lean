/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.QExpansion.Laurent
public import TauCeti.RingTheory.LaurentSeries.Rescale
public import TauCeti.Analysis.Complex.UpperHalfPlane.FixedDetMatrices
import TauCeti.NumberTheory.ModularForms.QExpansion.Order
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Laurent `q`-expansions under real translations and positive scalings

For a function `f` on the upper half-plane, the translate `τ ↦ f (x + τ)` by a real number `x`
and the rescaling `τ ↦ f (c τ)` by a positive real number `c` again have Laurent
`q`-expansions, read off from that of `f`:

* if `f` is `h`-periodic, then the Laurent `q`-expansion of `τ ↦ f (x + τ)` at period `h` is
  that of `f` rescaled by the unit `𝕢 h x = exp (2 π i x / h)`: the coefficient of `qᵐ` is
  multiplied by `(𝕢 h x) ^ m`;
* the Laurent `q`-expansion of `τ ↦ f (c τ)` at period `h / c` is that of `f` at period `h`,
  because `exp (2 π i τ c / h) = exp (2 π i (c τ) / h)`.

Combined with the change of period `TauCeti.UpperHalfPlane.laurentQExpansion_pnat_mul`, these
compute the expansion of `τ ↦ f ((a τ + b) / d)` at period `a d` for an upper-triangular integral
representative `(a b; 0 d)` and a `1`-periodic `f`: it is the expansion of `f` rescaled by
`exp (2 π i b / d)` and expanded by `q ↦ q^{a²}`. For `f = j` these are the values of the modular
invariant along the cyclic isogenies of degree `a d`.

## Main results

* `TauCeti.UpperHalfPlane.qExpansion_vadd`: the `q`-expansion of a translate.
* `TauCeti.UpperHalfPlane.laurentQExpansion_vadd`: the Laurent `q`-expansion of a translate.
* `TauCeti.UpperHalfPlane.laurentQExpansion_pos_real_smul`: the Laurent `q`-expansion of a
  rescaling.
* `TauCeti.UpperHalfPlane.laurentQExpansion_comp_toGLReal_smul`: the Laurent `q`-expansion along
  an upper-triangular integral matrix.
-/

public section

open UpperHalfPlane Filter Function Topology
open scoped Manifold

local notation "𝕢" => Function.Periodic.qParam

namespace TauCeti.UpperHalfPlane

variable {h : ℝ} {f : ℍ → ℂ}

/-- The local parameter of a translate: `𝕢 h (x + τ) = 𝕢 h x * 𝕢 h τ`. -/
theorem qParam_vadd (h x : ℝ) (τ : ℍ) : 𝕢 h ↑(x +ᵥ τ) = 𝕢 h x * 𝕢 h τ := by
  simp only [coe_vadd, Periodic.qParam, mul_add, add_div, Complex.exp_add]

/-! ### Translations -/

/-- Off `q = 0` and inside the unit disc, the cusp function of a translate `τ ↦ f (x + τ)` of an
`h`-periodic function is the cusp function of `f` at `𝕢 h x * q`. -/
theorem cuspFunction_vadd_eventuallyEq (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (x : ℝ) :
    cuspFunction h (fun τ ↦ f (x +ᵥ τ)) =ᶠ[𝓝[≠] 0] fun q ↦ cuspFunction h f (𝕢 h x * q) := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with q hq hq1
  have hq0 : q ≠ 0 := hq
  have him := Periodic.im_invQParam_pos_of_norm_lt_one hh (mem_ball_zero_iff.mp hq1) hq0
  have hτ : 𝕢 h (⟨_, him⟩ : ℍ) = q := Periodic.qParam_right_inv hh.ne' hq0
  rw [cuspFunction_of_ne_zero hq0, ofComplex_apply_of_im_pos him]
  conv_rhs => rw [← hτ]
  rw [← qParam_vadd, eq_cuspFunction _ hh.ne' hfper]

/-- The translate of an `h`-periodic function by a real number is `h`-periodic. -/
theorem periodic_vadd_comp_ofComplex (hfper : Periodic (f ∘ ofComplex) h) (x : ℝ) :
    Periodic ((fun τ ↦ f (x +ᵥ τ)) ∘ ofComplex) h :=
  periodic_comp_ofComplex_iff.mpr fun τ ↦ by
    rw [vadd_vadd, add_comm, ← vadd_vadd]
    exact periodic_comp_ofComplex_iff.mp hfper _

/-- The cusp function of a translate of an `h`-periodic function with analytic cusp function is
analytic at `0`, and near `0` it is the cusp function of `f` at `𝕢 h x * q`. -/
theorem cuspFunction_vadd_eventuallyEq_nhds (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (x : ℝ) :
    cuspFunction h (fun τ ↦ f (x +ᵥ τ)) =ᶠ[𝓝 0] fun q ↦ cuspFunction h f (𝕢 h x * q) :=
  cuspFunction_eventuallyEq_nhds_of_continuousAt (cuspFunction_vadd_eventuallyEq hh hfper x)
    (hf.continuousAt.comp_of_eq (by fun_prop) (mul_zero _))

/-- The cusp function of a translate of an `h`-periodic function with analytic cusp function is
analytic at `0`. -/
theorem analyticAt_cuspFunction_vadd (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (x : ℝ) :
    AnalyticAt ℂ (cuspFunction h fun τ ↦ f (x +ᵥ τ)) 0 :=
  (hf.comp_of_eq (by fun_prop) (mul_zero _)).congr
    (cuspFunction_vadd_eventuallyEq_nhds hh hfper hf x).symm

/-- **The `q`-expansion of a translate.** For an `h`-periodic function `f` with analytic cusp
function, the `q`-expansion of `τ ↦ f (x + τ)` is that of `f` rescaled by `𝕢 h x`: its `m`-th
coefficient is `(𝕢 h x) ^ m` times that of `f`. -/
theorem qExpansion_vadd (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (x : ℝ) :
    qExpansion h (fun τ ↦ f (x +ᵥ τ)) = PowerSeries.rescale (𝕢 h x) (qExpansion h f) := by
  set L : ℂ →L[ℂ] ℂ := 𝕢 h x • ContinuousLinearMap.id ℂ ℂ
  have hL : (fun q ↦ cuspFunction h f (𝕢 h x * q)) = cuspFunction h f ∘ L := by
    funext q
    simp [L]
  have heq := cuspFunction_vadd_eventuallyEq_nhds hh hfper hf x
  rw [hL] at heq
  have hcomp : HasFPowerSeriesAt (cuspFunction h f ∘ L)
      ((FormalMultilinearSeries.ofScalars ℂ fun m ↦
        (qExpansion h f).coeff m).compContinuousLinearMap L) 0 :=
    HasFPowerSeriesAt.compContinuousLinearMap (u := L) (x := 0)
      (by simpa using hasFPowerSeriesAt_cuspFunction hf)
  have huniq := (hasFPowerSeriesAt_cuspFunction
    (analyticAt_cuspFunction_vadd hh hfper hf x)).eq_formalMultilinearSeries (hcomp.congr heq.symm)
  ext m
  have hm := congrArg (FormalMultilinearSeries.coeff · m) huniq
  simp only [FormalMultilinearSeries.coeff_ofScalars] at hm
  rw [hm, PowerSeries.coeff_rescale, FormalMultilinearSeries.coeff,
    FormalMultilinearSeries.compContinuousLinearMap_apply]
  simp [L]

/-- The cusp function of a translate of an `h`-periodic function with meromorphic cusp function
is meromorphic at `0`. -/
theorem meromorphicAt_cuspFunction_vadd (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hf : MeromorphicAt (cuspFunction h f) 0) (x : ℝ) :
    MeromorphicAt (cuspFunction h fun τ ↦ f (x +ᵥ τ)) 0 :=
  (MeromorphicAt.comp_analyticAt (g := (𝕢 h x * ·)) (by rwa [mul_zero]) (by fun_prop)).congr
    (cuspFunction_vadd_eventuallyEq hh hfper x).symm

/-- **The Laurent `q`-expansion of a translate.** For an `h`-periodic function `f` with
meromorphic cusp function, the Laurent `q`-expansion of `τ ↦ f (x + τ)` is that of `f` rescaled
by the unit `𝕢 h x`: its coefficient of `qᵐ` is `(𝕢 h x) ^ m` times that of `f`, for every
integer `m`. -/
theorem laurentQExpansion_vadd (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hf : MeromorphicAt (cuspFunction h f) 0) (x : ℝ) :
    laurentQExpansion h (fun τ ↦ f (x +ᵥ τ)) =
      LaurentSeries.rescale (Units.mk0 (𝕢 h x) (Periodic.qParam_ne_zero _))
        (laurentQExpansion h f) := by
  set u := Units.mk0 (𝕢 h x) (Periodic.qParam_ne_zero _)
  obtain ⟨k, hk⟩ := exists_neg_le_meromorphicOrderAt_cuspFunction h f
  set F : ℍ → ℂ := fun τ ↦ 𝕢 h τ ^ k * f τ
  have hFper : Periodic (F ∘ ofComplex) h := periodic_qParam_pow_mul_comp_ofComplex hfper k
  have hF : AnalyticAt ℂ (cuspFunction h F) 0 := analyticAt_cuspFunction_qParam_pow_mul hf hk
  -- twisting the translate by `𝕢 ^ k` is the translate of `F`, up to the constant `(𝕢 h x)⁻ᵏ`
  have htw : (fun τ : ℍ ↦ 𝕢 h τ ^ k * f (x +ᵥ τ)) =
      ((u ^ k)⁻¹ : ℂˣ).val • fun τ : ℍ ↦ F (x +ᵥ τ) := by
    funext τ
    simp only [F, qParam_vadd, Pi.smul_apply, smul_eq_mul, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val, Units.val_mk0, u, mul_pow]
    field_simp [Periodic.qParam_ne_zero]
  have hFT := analyticAt_cuspFunction_vadd hh hFper hF x
  have hFT' : AnalyticAt ℂ (cuspFunction h fun τ : ℍ ↦ 𝕢 h τ ^ k * f (x +ᵥ τ)) 0 := by
    rw [htw, cuspFunction_smul hFT.continuousAt]
    exact hFT.const_smul
  rw [laurentQExpansion_eq_of_analyticAt_qParam_pow_mul hh hFT', laurentQExpansion_eq hh hf hk,
    htw, qExpansion_smul hFT, qExpansion_vadd hh hFper hF, map_mul, LaurentSeries.rescale_single,
    LaurentSeries.rescale_coe]
  ext n
  simp [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe, u, F]

/-! ### Positive scalings -/

/-- The local parameter of a rescaling: `𝕢 (h / c) τ = 𝕢 h (c τ)`. -/
theorem qParam_div_pos_real (h : ℝ) (c : {x : ℝ // 0 < x}) (τ : ℍ) :
    𝕢 (h / c) τ = 𝕢 h ↑(c • τ) := by
  simp only [Periodic.qParam, coe_pos_real_smul, Complex.real_smul, Complex.ofReal_div]
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr c.property.ne']

/-- Off `q = 0` and inside the unit disc, the cusp function of a rescaling `τ ↦ f (c τ)` at
period `h / c` is the cusp function of `f` at period `h`. -/
theorem cuspFunction_pos_real_smul_eventuallyEq (hh : 0 < h) (c : {x : ℝ // 0 < x})
    (f : ℍ → ℂ) :
    cuspFunction (h / c) (fun τ ↦ f (c • τ)) =ᶠ[𝓝[≠] 0] cuspFunction h f := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with q hq hq1
  have hq0 : q ≠ 0 := hq
  have him := Periodic.im_invQParam_pos_of_norm_lt_one hh (mem_ball_zero_iff.mp hq1) hq0
  have him' := Periodic.im_invQParam_pos_of_norm_lt_one (div_pos hh c.property)
    (mem_ball_zero_iff.mp hq1) hq0
  rw [cuspFunction_of_ne_zero hq0, cuspFunction_of_ne_zero hq0, ofComplex_apply_of_im_pos him,
    ofComplex_apply_of_im_pos him']
  congr 1
  ext
  simp only [coe_pos_real_smul, Periodic.invQParam, Complex.real_smul, Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr c.property.ne']

/-- The cusp function at period `h / c` of a rescaling `τ ↦ f (c τ)` is meromorphic at `0` when
the cusp function of `f` at period `h` is. -/
theorem meromorphicAt_cuspFunction_pos_real_smul (hh : 0 < h) (c : {x : ℝ // 0 < x})
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    MeromorphicAt (cuspFunction (h / c) fun τ ↦ f (c • τ)) 0 :=
  hf.congr (cuspFunction_pos_real_smul_eventuallyEq hh c f).symm

/-- The rescaling of an `h`-periodic function by `c` is `h / c`-periodic. -/
theorem periodic_pos_real_smul_comp_ofComplex (hfper : Periodic (f ∘ ofComplex) h)
    (c : {x : ℝ // 0 < x}) :
    Periodic ((fun τ ↦ f (c • τ)) ∘ ofComplex) ((h / c : ℝ) : ℂ) :=
  periodic_comp_ofComplex_iff.mpr fun τ ↦ by
    have hc : c • ((h / c : ℝ) +ᵥ τ) = h +ᵥ c • τ := by
      ext
      simp only [coe_pos_real_smul, coe_vadd, Complex.real_smul, Complex.ofReal_div]
      field_simp [Complex.ofReal_ne_zero.mpr c.property.ne']
    rw [hc]
    exact periodic_comp_ofComplex_iff.mp hfper _

/-- **The Laurent `q`-expansion of a rescaling.** The Laurent `q`-expansion of `τ ↦ f (c τ)` at
period `h / c` is the Laurent `q`-expansion of `f` at period `h`. -/
theorem laurentQExpansion_pos_real_smul (hh : 0 < h) (c : {x : ℝ // 0 < x})
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    laurentQExpansion (h / c) (fun τ ↦ f (c • τ)) = laurentQExpansion h f := by
  obtain ⟨k, hk⟩ := exists_neg_le_meromorphicOrderAt_cuspFunction h f
  set F : ℍ → ℂ := fun τ ↦ 𝕢 h τ ^ k * f τ
  have hF : AnalyticAt ℂ (cuspFunction h F) 0 := analyticAt_cuspFunction_qParam_pow_mul hf hk
  have htw : (fun τ : ℍ ↦ 𝕢 (h / c) τ ^ k * f (c • τ)) = fun τ ↦ F (c • τ) := by
    funext τ
    rw [qParam_div_pos_real]
  have heq : cuspFunction (h / c) (fun τ : ℍ ↦ 𝕢 (h / c) τ ^ k * f (c • τ)) =ᶠ[𝓝 0]
      cuspFunction h F := by
    rw [htw]
    exact cuspFunction_eventuallyEq_nhds_of_continuousAt
      (cuspFunction_pos_real_smul_eventuallyEq hh c F) hF.continuousAt
  rw [laurentQExpansion_eq_of_analyticAt_qParam_pow_mul (div_pos hh c.property) (hF.congr heq.symm),
    laurentQExpansion_eq_of_analyticAt_qParam_pow_mul hh hF]
  congr 2
  ext m
  rw [qExpansion_coeff, qExpansion_coeff, heq.iteratedDeriv_eq]

/-! ### Upper-triangular integral matrices -/

section Reps

open FixedDetMatrices

variable {m : ℤ} {A : FixedDetMatrix (Fin 2) ℤ m}

/-- The width bookkeeping for a representative `(a b; 0 d)`: `a ^ 2 * (d / a) = m`. -/
private theorem natAbs_sq_mul_inv_repsScale (hm : 0 < m) (hA : A ∈ reps m) :
    ((((A.val 0 0).natAbs ^ 2).toPNat' : ℕ) : ℝ) * (repsScale hm hA : ℝ)⁻¹ = m := by
  have ha : 0 < (A.val 0 0).natAbs ^ 2 := pow_pos (Int.natAbs_pos.mpr hA.2.1.ne') 2
  have had : (A.val 0 0 : ℝ) * A.val 1 1 = m := by
    exact_mod_cast apply_zero_zero_mul_apply_one_one hA.1
  have ha' : (A.val 0 0 : ℝ) ≠ 0 := by exact_mod_cast hA.2.1.ne'
  rw [PNat.toPNat'_coe ha, coe_repsScale, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs,
    sq_abs, inv_div, ← had]
  field_simp

private theorem meromorphicAt_cuspFunction_and_laurentQExpansion_comp_toGLReal_smul
    (hm : 0 < m) (hA : A ∈ reps m) (hfper : Periodic (f ∘ ofComplex) 1)
    (hf : MeromorphicAt (cuspFunction 1 f) 0) :
    MeromorphicAt (cuspFunction m fun τ ↦ f (toGLReal hm.ne' A • τ)) 0 ∧
      laurentQExpansion m (fun τ ↦ f (toGLReal hm.ne' A • τ)) =
        LaurentSeries.expand ℂ ((A.val 0 0).natAbs ^ 2).toPNat'
          (LaurentSeries.rescale
            (Units.mk0 (𝕢 1 ((A.val 0 1 / A.val 1 1 : ℝ) : ℂ)) (Periodic.qParam_ne_zero _))
            (laurentQExpansion 1 f)) := by
  set c := repsScale hm hA
  set x : ℝ := A.val 0 1 / A.val 1 1
  have hfun : (fun τ ↦ f (toGLReal hm.ne' A • τ)) = fun τ ↦ f (x +ᵥ c • τ) := by
    funext τ
    rw [toGLReal_smul_eq_vadd_smul hm hA]
  have hmer := meromorphicAt_cuspFunction_vadd one_pos hfper hf x
  have hper := periodic_vadd_comp_ofComplex hfper x
  have hmer' := meromorphicAt_cuspFunction_pos_real_smul (f := fun σ ↦ f (x +ᵥ σ)) one_pos c hmer
  have hper' := periodic_pos_real_smul_comp_ofComplex hper c
  have hw := natAbs_sq_mul_inv_repsScale hm hA
  rw [← one_div] at hw
  rw [hfun, ← hw]
  refine ⟨meromorphicAt_cuspFunction_pnat_mul (div_pos one_pos c.property) hper' hmer' _, ?_⟩
  rw [laurentQExpansion_pnat_mul hper' hmer', laurentQExpansion_pos_real_smul one_pos c hmer,
    laurentQExpansion_vadd one_pos hfper hf]

/-- Along an upper-triangular representative `(a b; 0 d)` of positive determinant `m`, the
function `τ ↦ f ((a τ + b) / d)` of a `1`-periodic `f` with meromorphic cusp function has a
meromorphic cusp function at period `m`. -/
theorem meromorphicAt_cuspFunction_comp_toGLReal_smul (hm : 0 < m) (hA : A ∈ reps m)
    (hfper : Periodic (f ∘ ofComplex) 1) (hf : MeromorphicAt (cuspFunction 1 f) 0) :
    MeromorphicAt (cuspFunction m fun τ ↦ f (toGLReal hm.ne' A • τ)) 0 :=
  (meromorphicAt_cuspFunction_and_laurentQExpansion_comp_toGLReal_smul hm hA hfper hf).1

/-- **The Laurent `q`-expansion along an upper-triangular matrix.** For a representative
`(a b; 0 d)` of positive determinant `m` and a `1`-periodic `f` with meromorphic cusp function,
the Laurent expansion of `τ ↦ f ((a τ + b) / d)` at period `m` is that of `f` rescaled by
`exp (2 π i b / d)` and expanded by `X ↦ X ^ (a ^ 2)`: if `f = ∑ₖ cₖ qᵏ`, then
`f ((a τ + b) / d) = ∑ₖ cₖ e^{2πibk/d} q_m^{a² k}` with `q_m = e^{2πiτ/m}`. -/
theorem laurentQExpansion_comp_toGLReal_smul (hm : 0 < m) (hA : A ∈ reps m)
    (hfper : Periodic (f ∘ ofComplex) 1) (hf : MeromorphicAt (cuspFunction 1 f) 0) :
    laurentQExpansion m (fun τ ↦ f (toGLReal hm.ne' A • τ)) =
      LaurentSeries.expand ℂ ((A.val 0 0).natAbs ^ 2).toPNat'
        (LaurentSeries.rescale
          (Units.mk0 (𝕢 1 ((A.val 0 1 / A.val 1 1 : ℝ) : ℂ)) (Periodic.qParam_ne_zero _))
          (laurentQExpansion 1 f)) :=
  (meromorphicAt_cuspFunction_and_laurentQExpansion_comp_toGLReal_smul hm hA hfper hf).2

end Reps

end TauCeti.UpperHalfPlane
