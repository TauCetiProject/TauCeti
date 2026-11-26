/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.JetOperator
public import TauCeti.Analysis.Sobolev.Strip.Basic
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The slice average on `L²` of the strip

The zero Fourier mode of a section `f : ℝ × ℝ → E` over the strip `ℝ × [0, 1]` is its slice
average `s ↦ ∫₀¹ f(s, t) dt` (`TauCeti.StripSobolev.sliceAverage`), read as a section that does not
depend on `t`. By Jensen's inequality on the slices `{s} × [0, 1]`, the slice average does not
increase the `L²` norm on the strip (`TauCeti.StripSobolev.eLpNorm_sliceAverage_le`). It therefore
induces a bounded operator of norm at most `1`, `TauCeti.StripSobolev.sliceAverageLp`, which is
idempotent (`TauCeti.StripSobolev.sliceAverageLp_sliceAverageLp`). It commutes with every
first-order operator `TauCeti.jetOperator` whose coefficient field does not depend on `t`
(`TauCeti.StripSobolev.sliceAverageLp_jetOperator`), and with every constant operator
(`TauCeti.StripSobolev.sliceAverageLp_compLpL`).

The restriction of the slice average to the Sobolev space `W^{1,2}(ℝ × S¹, V)` of the cylinder is
in `TauCeti.Analysis.Sobolev.Cylinder.Slice.Average`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Chapter 10, on the Fourier decomposition of operators on
  cylindrical ends.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace TauCeti.StripSobolev

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f g : ℝ × ℝ → E}

/-- The slice average `∫₀¹ f(s, t) dt` of `f : ℝ × ℝ → E` over the slice `{s} × [0, 1]` through
`z = (s, t)`: the zero Fourier mode of `f`, as a section that does not depend on `t`. -/
def sliceAverage (f : ℝ × ℝ → E) (z : ℝ × ℝ) : E :=
  ∫ t in (0 : ℝ)..1, f (z.1, t)

/-- The slice average at `z = (s, t)` is the integral of `f(s, ·)` over `[0, 1]`. -/
theorem sliceAverage_apply (f : ℝ × ℝ → E) (z : ℝ × ℝ) :
    sliceAverage f z = ∫ t in (0 : ℝ)..1, f (z.1, t) :=
  (rfl)

/-- The slice average does not depend on `t`. -/
theorem sliceAverage_mk (f : ℝ × ℝ → E) (s t : ℝ) : sliceAverage f (s, t) = sliceAverage f (s, 0) :=
  (rfl)

/-- The slice average is the integral over the slice for the measure `volume.restrict (Icc 0 1)`,
the second factor of the strip measure. -/
theorem sliceAverage_eq_integral (f : ℝ × ℝ → E) (z : ℝ × ℝ) :
    sliceAverage f z = ∫ t, f (z.1, t) ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
  rw [sliceAverage_apply, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc]

/-- The slice average of a slice average is itself: a section that does not depend on `t` is its
own average. -/
@[simp]
theorem sliceAverage_sliceAverage [CompleteSpace E] (f : ℝ × ℝ → E) :
    sliceAverage (sliceAverage f) = sliceAverage f := by
  funext z
  simp only [sliceAverage_apply]
  rw [intervalIntegral.integral_const, sub_zero, one_smul]

/-- Removing the slice average leaves a section with mean zero on each slice whose restriction of
`f` is interval integrable: the nonzero-mode part `f - sliceAverage f` has vanishing slice
average. -/
theorem sliceAverage_sub_sliceAverage [CompleteSpace E] {z : ℝ × ℝ}
    (hf : IntervalIntegrable (fun t ↦ f (z.1, t)) volume 0 1) :
    sliceAverage (f - sliceAverage f) z = 0 := by
  simp only [sliceAverage_apply, Pi.sub_apply]
  rw [intervalIntegral.integral_sub hf intervalIntegrable_const, intervalIntegral.integral_const,
    sub_zero, one_smul, sub_self]

/-- **Jensen's inequality on a slice.** The squared norm of the slice average is at most the
integral of the squared norm over the slice. -/
private theorem enorm_sliceAverage_rpow_le {s : ℝ}
    (hf : AEStronglyMeasurable (fun t ↦ f (s, t)) (volume.restrict (Icc (0 : ℝ) 1))) (t : ℝ) :
    ‖sliceAverage f (s, t)‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ t, ‖f (s, t)‖ₑ ^ (2 : ℝ) ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
  have h₁ : ‖sliceAverage f (s, t)‖ₑ ≤ eLpNorm (fun t ↦ f (s, t)) 2
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    rw [sliceAverage_eq_integral]
    exact (eNorm_integral_le_lintegral_eNorm _).trans
      ((eLpNorm_one_eq_lintegral_eNorm hf).symm.trans_le
        (eLpNorm_le_eLpNorm_of_exponent_le one_le_two))
  have h₂ := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hf
  push_cast at h₂
  exact (ENNReal.rpow_le_rpow h₁ zero_le_two).trans_eq h₂

/-- The slice average of a section that is a.e. strongly measurable on the strip is a.e. strongly
measurable on the strip. -/
theorem aestronglyMeasurable_sliceAverage (hf : AEStronglyMeasurable f stripMeasure) :
    AEStronglyMeasurable (sliceAverage f) stripMeasure := by
  rw [stripMeasure_eq_prod] at hf ⊢
  have h := hf.integral_prod_right'.comp_fst (ν := volume.restrict (Icc (0 : ℝ) 1))
  exact h.congr (.of_forall fun z ↦ (sliceAverage_eq_integral f z).symm)

/-- **The slice average is an `L²` contraction.** On the strip, the `L²` norm of the slice average
of `f` is at most that of `f`. -/
theorem eLpNorm_sliceAverage_le (hf : AEStronglyMeasurable f stripMeasure) :
    eLpNorm (sliceAverage f) 2 stripMeasure ≤ eLpNorm f 2 stripMeasure := by
  have hf' := hf
  rw [stripMeasure_eq_prod] at hf'
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (aestronglyMeasurable_sliceAverage hf),
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf,
    ENNReal.toReal_ofNat]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [stripMeasure_eq_prod,
    lintegral_prod _ (((aestronglyMeasurable_sliceAverage hf).eNorm.pow_const _).mono_ac
      (by rw [stripMeasure_eq_prod])),
    lintegral_prod _ (hf'.eNorm.pow_const _)]
  refine lintegral_mono_ae ?_
  filter_upwards [hf'.prodMk_left] with s hs
  calc ∫⁻ t, ‖sliceAverage f (s, t)‖ₑ ^ (2 : ℝ) ∂(volume.restrict (Icc (0 : ℝ) 1))
      ≤ ∫⁻ _, (∫⁻ t, ‖f (s, t)‖ₑ ^ (2 : ℝ) ∂(volume.restrict (Icc (0 : ℝ) 1)))
          ∂(volume.restrict (Icc (0 : ℝ) 1)) :=
        lintegral_mono fun t ↦ enorm_sliceAverage_rpow_le hs t
    _ = ∫⁻ t, ‖f (s, t)‖ₑ ^ (2 : ℝ) ∂(volume.restrict (Icc (0 : ℝ) 1)) := by
        rw [lintegral_const, measure_univ, mul_one]

/-- The slice average of a square integrable section on the strip is square integrable. -/
theorem memLp_sliceAverage (hf : MemLp f 2 stripMeasure) :
    MemLp (sliceAverage f) 2 stripMeasure :=
  memLp_iff.2 ((eLpNorm_sliceAverage_le hf.aestronglyMeasurable).trans_lt (memLp_iff.1 hf))

/-- Sections that agree almost everywhere on the strip have slice averages that agree almost
everywhere on the strip. -/
theorem sliceAverage_congr_ae (h : f =ᵐ[stripMeasure] g) :
    sliceAverage f =ᵐ[stripMeasure] sliceAverage g := by
  rw [stripMeasure_eq_prod] at h
  have hs : ∀ᵐ s, sliceAverage f (s, 0) = sliceAverage g (s, 0) := by
    filter_upwards [Measure.ae_ae_of_ae_prod h] with s hs
    rw [sliceAverage_eq_integral, sliceAverage_eq_integral]
    exact integral_congr_ae hs
  filter_upwards [ae_stripMeasure_of_ae_fst hs] with z hz
  rw [sliceAverage_mk f z.1 z.2, sliceAverage_mk g z.1 z.2]
  exact hz

/-- The slice average is additive on square integrable sections, almost everywhere. -/
theorem sliceAverage_add_ae (hf : MemLp f 2 stripMeasure) (hg : MemLp g 2 stripMeasure) :
    sliceAverage (f + g) =ᵐ[stripMeasure] sliceAverage f + sliceAverage g := by
  filter_upwards [ae_stripMeasure_of_ae_fst (ae_intervalIntegrable_slice hf),
    ae_stripMeasure_of_ae_fst (ae_intervalIntegrable_slice hg)] with z hfz hgz
  exact intervalIntegral.integral_add hfz hgz

/-- The slice average is homogeneous. -/
theorem sliceAverage_smul (c : ℝ) (f : ℝ × ℝ → E) : sliceAverage (c • f) = c • sliceAverage f := by
  funext z
  exact intervalIntegral.integral_smul c _

/-- The slice average as a bounded operator on `L²` of the strip, of norm at most `1`
(`TauCeti.StripSobolev.opNorm_sliceAverageLp_le`): the projection onto the sections that do not
depend on `t`, the zero Fourier mode. -/
def sliceAverageLp : Lp E 2 stripMeasure →L[ℝ] Lp E 2 stripMeasure :=
  LinearMap.mkContinuous
    { toFun x := (memLp_sliceAverage (Lp.memLp x)).toLp _
      map_add' x y := by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [sliceAverage_congr_ae (Lp.coeFn_add x y),
          sliceAverage_add_ae (Lp.memLp x) (Lp.memLp y)] with z h₁ h₂
        rw [h₁, h₂]
      map_smul' c x := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [sliceAverage_congr_ae (Lp.coeFn_smul c x)] with z hz
        rw [hz, sliceAverage_smul] }
    1 fun x ↦ by
      rw [one_mul, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top x)
        (eLpNorm_sliceAverage_le (Lp.memLp x).aestronglyMeasurable)

/-- The `L²` slice average of `x` is the class of the slice average of a representative of `x`. -/
theorem sliceAverageLp_apply (x : Lp E 2 stripMeasure) :
    sliceAverageLp x = (memLp_sliceAverage (Lp.memLp x)).toLp _ := by
  rw [sliceAverageLp, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]

/-- The `L²` slice average is represented by the slice average of a representative. -/
theorem coeFn_sliceAverageLp (x : Lp E 2 stripMeasure) :
    sliceAverageLp x =ᵐ[stripMeasure] sliceAverage x := by
  rw [sliceAverageLp_apply]
  exact MemLp.coeFn_toLp _

/-- The `L²` slice average of the class of a square integrable section is the class of its slice
average. -/
theorem sliceAverageLp_toLp (hf : MemLp f 2 stripMeasure) :
    sliceAverageLp (hf.toLp f) = (memLp_sliceAverage hf).toLp _ := by
  rw [sliceAverageLp_apply]
  exact MemLp.toLp_congr _ _ (sliceAverage_congr_ae hf.coeFn_toLp)

/-- The `L²` slice average has operator norm at most `1`. -/
theorem opNorm_sliceAverageLp_le : ‖(sliceAverageLp : Lp E 2 stripMeasure →L[ℝ] _)‖ ≤ 1 := by
  unfold sliceAverageLp
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The slice average does not increase the `L²` norm. -/
theorem norm_sliceAverageLp_le (x : Lp E 2 stripMeasure) : ‖sliceAverageLp x‖ ≤ ‖x‖ :=
  ((sliceAverageLp (E := E)).le_of_opNorm_le opNorm_sliceAverageLp_le x).trans_eq (one_mul _)

/-- The `L²` slice average is idempotent. -/
@[simp]
theorem sliceAverageLp_sliceAverageLp [CompleteSpace E] (x : Lp E 2 stripMeasure) :
    sliceAverageLp (sliceAverageLp x) = sliceAverageLp x := by
  refine Lp.ext ?_
  filter_upwards [coeFn_sliceAverageLp (sliceAverageLp x),
    sliceAverage_congr_ae (coeFn_sliceAverageLp x), coeFn_sliceAverageLp x] with z h₁ h₂ h₃
  rw [h₁, h₂, sliceAverage_sliceAverage, h₃]

/-- The slice average of a pointwise operator field that does not depend on `t` is the operator
applied to the slice average, on the slices where the section is integrable. -/
private theorem sliceAverage_apply_apply [CompleteSpace E] [CompleteSpace F]
    {M : ℝ × ℝ → E →L[ℝ] F}
    (hM : ∀ s t, M (s, t) = M (s, 0)) {z : ℝ × ℝ}
    (hf : IntervalIntegrable (fun t ↦ f (z.1, t)) volume 0 1) :
    sliceAverage (fun w ↦ M w (f w)) z = M z (sliceAverage f z) := by
  rw [sliceAverage_apply, sliceAverage_apply, hM z.1 z.2]
  simp_rw [hM z.1]
  exact (M (z.1, 0)).intervalIntegral_comp_comm hf

/-- The slice average commutes with a first-order operator whose coefficient field does not depend
on `t`. -/
theorem sliceAverageLp_jetOperator {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace V] [CompleteSpace W]
    {M : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : ∀ s t, M (s, t) = M (s, 0)) (x : Lp (V × V × V) 2 stripMeasure) :
    sliceAverageLp (jetOperator 2 stripMeasure M x) =
      jetOperator 2 stripMeasure M (sliceAverageLp x) := by
  by_cases hMb : MemLp M ∞ stripMeasure
  · refine Lp.ext ?_
    filter_upwards [coeFn_sliceAverageLp (jetOperator 2 stripMeasure M x),
      sliceAverage_congr_ae (coeFn_jetOperator hMb x), coeFn_jetOperator hMb (sliceAverageLp x),
      coeFn_sliceAverageLp x,
      ae_stripMeasure_of_ae_fst (ae_intervalIntegrable_slice (Lp.memLp x))]
      with z h₁ h₂ h₃ h₄ hz
    rw [h₁, h₂, h₃, h₄, sliceAverage_apply_apply hM hz]
  · simp [jetOperator_of_not_memLp hMb]

/-- The slice average commutes with a constant operator acting pointwise. -/
theorem sliceAverageLp_compLpL [CompleteSpace E] [CompleteSpace F] (L : E →L[ℝ] F)
    (x : Lp E 2 stripMeasure) :
    sliceAverageLp (L.compLpL 2 stripMeasure x) =
      L.compLpL 2 stripMeasure (sliceAverageLp x) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_sliceAverageLp (L.compLpL 2 stripMeasure x),
    sliceAverage_congr_ae (L.coeFn_compLpL x), L.coeFn_compLpL (sliceAverageLp x),
    coeFn_sliceAverageLp x,
    ae_stripMeasure_of_ae_fst (ae_intervalIntegrable_slice (Lp.memLp x))]
    with z h₁ h₂ h₃ h₄ hz
  rw [h₁, h₂, h₃, h₄]
  exact sliceAverage_apply_apply (M := fun _ ↦ L) (fun _ _ ↦ rfl) hz

end TauCeti.StripSobolev
