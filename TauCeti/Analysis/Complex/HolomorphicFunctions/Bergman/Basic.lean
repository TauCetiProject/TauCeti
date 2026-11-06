/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Bergman spaces on open subsets of the complex plane

The Bergman space is the subspace of native `L²` classes with a holomorphic representative.
Its norm is the actual `L²` norm, rather than an auxiliary supremum norm. Values may lie in a
complete complex normed space; in particular, scalar values give the classical Bergman space.

These are the analytic Banach stages used for holomorphic Čech cochains in the finiteness
argument for compact Riemann-surface cohomology. Sheaf/cochain comparison and the finiteness
conclusion require additional arguments.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §14.
* J. B. Conway, *Functions of One Complex Variable II*, Chapter I.
-/

public noncomputable section

open MeasureTheory Filter Metric Set TopologicalSpace Topology InnerProductSpace
open scoped ENNReal

namespace TauCeti

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] (U : Opens ℂ)

/-- The native `L²` subspace of classes admitting a holomorphic representative on `U`. -/
def bergmanSpace : Submodule ℂ (Lp F 2 (volume.restrict (U : Set ℂ))) where
  carrier := {u | ∃ f : ℂ → F, DifferentiableOn ℂ f U ∧ u =ᵐ[volume.restrict (U : Set ℂ)] f}
  zero_mem' := ⟨0, differentiableOn_const 0, by
    simpa using Lp.coeFn_zero F 2 (volume.restrict (U : Set ℂ))⟩
  add_mem' := by
    rintro u v ⟨f, hf, hu⟩ ⟨g, hg, hv⟩
    exact ⟨f + g, hf.add hg, (Lp.coeFn_add u v).trans (hu.add hv)⟩
  smul_mem' := by
    rintro c u ⟨f, hf, hu⟩
    exact ⟨c • f, hf.const_smul c, (Lp.coeFn_smul c u).trans (hu.const_smul c)⟩

/-- Membership in the Bergman space means that the class has a holomorphic representative. -/
@[simp]
theorem mem_bergmanSpace_iff {u : Lp F 2 (volume.restrict (U : Set ℂ))} :
    u ∈ bergmanSpace F U ↔
      ∃ f : ℂ → F, DifferentiableOn ℂ f U ∧ u =ᵐ[volume.restrict (U : Set ℂ)] f := Iff.rfl

namespace BergmanSpace

variable {F U} [CompleteSpace F]

private theorem norm_le_ball_integral {f : ℂ → F} (hf : DifferentiableOn ℂ f U)
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hball : closedBall x r ⊆ U) :
    ‖f x‖ ≤ (volume.real (ball (0 : ℂ) r))⁻¹ * ∫ y in ball x r, ‖f y‖ := by
  have hh : HarmonicOnNhd f (closedBall x r) := fun y hy ↦
    (hf.analyticAt (U.isOpen.mem_nhds (hball hy))).harmonicAt
  have hpos : 0 < volume.real (ball x r) :=
    ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne
  have heq := hh.setIntegral_ball_eq (μ := volume)
  calc
    ‖f x‖ = (volume.real (ball x r))⁻¹ * ‖∫ y in ball x r, f y‖ := by
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hpos, ← mul_assoc,
        inv_mul_cancel₀ hpos.ne', one_mul]
    _ ≤ (volume.real (ball x r))⁻¹ * ∫ y in ball x r, ‖f y‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.2 hpos.le)
    _ = _ := by rw [Measure.addHaar_real_ball_center]

private theorem norm_le_Lp_norm {u : Lp F 2 (volume.restrict (U : Set ℂ))}
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U)
    (hu : u =ᵐ[volume.restrict (U : Set ℂ)] f) {x : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : closedBall x r ⊆ U) :
    ‖f x‖ ≤ ((volume.real (ball (0 : ℂ) r))⁻¹ *
      ((volume (ball (0 : ℂ) r)) ^ (1 / 2 : ℝ)).toReal) * ‖u‖ := by
  have hle : volume.restrict (ball x r) ≤ volume.restrict (U : Set ℂ) :=
    Measure.restrict_mono_set volume (ball_subset_closedBall.trans hball)
  have hm := (Lp.aestronglyMeasurable u).mono_measure hle
  have hae := hu.filter_mono (ae_mono hle)
  have hfm := hm.congr hae
  have htwo : eLpNorm f 2 (volume.restrict (ball x r)) ≤
      eLpNorm u 2 (volume.restrict (U : Set ℂ)) := by
    rw [← eLpNorm_congr_ae hae]
    exact eLpNorm_mono_measure _ hle
  have hbound := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
    one_le_two hfm
  have hpow : ((volume.restrict (ball x r)) univ) ^
      (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) =
      volume (ball (0 : ℂ) r) ^ (1 / 2 : ℝ) := by
    simp [Measure.addHaar_ball_center]
    norm_num
  rw [hpow] at hbound
  have hfin : eLpNorm u 2 (volume.restrict (U : Set ℂ)) *
      volume (ball (0 : ℂ) r) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top u)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne)
  have hone := ENNReal.toReal_mono hfin (hbound.trans
    (mul_le_mul htwo le_rfl (by positivity) (by positivity)))
  rw [ENNReal.toReal_mul, ← Lp.norm_def] at hone
  have hint : ∫ y in ball x r, ‖f y‖ =
      (eLpNorm f 1 (volume.restrict (ball x r))).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm hfm]
    exact integral_norm_eq_lintegral_enorm hfm
  refine (norm_le_ball_integral hf hr hball).trans ?_
  rw [hint, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by simpa [mul_comm] using hone) (by positivity)

private theorem uniformCauchySeqOn_of_cauchySeq
    {u : ℕ → Lp F 2 (volume.restrict (U : Set ℂ))} {f : ℕ → ℂ → F}
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hu : ∀ n, u n =ᵐ[volume.restrict (U : Set ℂ)] f n) (hc : CauchySeq u)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    UniformCauchySeqOn f atTop K := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open U.isOpen hKU
  let C := (volume.real (ball (0 : ℂ) r))⁻¹ *
    ((volume (ball (0 : ℂ) r)) ^ (1 / 2 : ℝ)).toReal
  have hC : 0 ≤ C := by positivity
  refine Metric.uniformCauchySeqOn_iff.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hc (ε / (C + 1))
    (div_pos hε (by positivity))
  refine ⟨N, fun m hm n hn x hx ↦ ?_⟩
  have hae : u m - u n =ᵐ[volume.restrict (U : Set ℂ)] f m - f n :=
    (Lp.coeFn_sub _ _).trans ((hu m).sub (hu n))
  have hbound := norm_le_Lp_norm ((hf m).sub (hf n)) hae hr
    ((closedBall_subset_cthickening hx r).trans hrU)
  rw [Pi.sub_apply, ← dist_eq_norm] at hbound
  calc
    dist (f m x) (f n x) ≤ C * ‖u m - u n‖ := hbound
    _ ≤ (C + 1) * dist (u m) (u n) := by
      rw [dist_eq_norm]
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (C + 1) * (ε / (C + 1)) :=
      mul_lt_mul_of_pos_left (hN m hm n hn) (by positivity)
    _ = ε := mul_div_cancel₀ ε (by positivity)

/-- A sequence of holomorphic representatives that is Cauchy in native `L²` converges
locally uniformly to a holomorphic function. No finite measure assumption on `U` is needed. -/
theorem exists_tendstoLocallyUniformlyOn_of_cauchySeq
    {u : ℕ → Lp F 2 (volume.restrict (U : Set ℂ))} {f : ℕ → ℂ → F}
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hu : ∀ n, u n =ᵐ[volume.restrict (U : Set ℂ)] f n) (hc : CauchySeq u) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g U ∧ TendstoLocallyUniformlyOn f g atTop U := by
  let g := fun x ↦ limUnder atTop (fun n ↦ f n x)
  have hpoint : ∀ x ∈ U, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) := by
    intro x hx
    exact ((uniformCauchySeqOn_of_cauchySeq hf hu hc isCompact_singleton
      (singleton_subset_iff.2 hx)).cauchySeq (mem_singleton x)).tendsto_limUnder
  have hlocal : TendstoLocallyUniformlyOn f g atTop U := by
    refine (tendstoLocallyUniformlyOn_iff_forall_isCompact U.isOpen).2 fun K hKU hK ↦ ?_
    exact (uniformCauchySeqOn_of_cauchySeq hf hu hc hK hKU).tendstoUniformlyOn_of_tendsto
      fun x hx ↦ hpoint x (hKU hx)
  exact ⟨g, hlocal.differentiableOn (Eventually.of_forall hf) U.isOpen, hlocal⟩

/-- The holomorphic classes form a closed subspace of native `L²`. -/
theorem isClosed : IsClosed (bergmanSpace F U : Set (Lp F 2 (volume.restrict (U : Set ℂ)))) := by
  refine IsSeqClosed.isClosed fun v u hv hlim ↦ ?_
  choose f hf hu using hv
  obtain ⟨g, hg, hfg⟩ := exists_tendstoLocallyUniformlyOn_of_cauchySeq hf hu hlim.cauchySeq
  refine ⟨g, hg, ?_⟩
  obtain ⟨ns, hns, hns_lim⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hae : ∀ᵐ x ∂volume.restrict (U : Set ℂ), ∀ n, (v n : ℂ → F) x = f n x :=
    ae_all_iff.2 hu
  filter_upwards [hns_lim, hae, ae_restrict_mem U.isOpen.measurableSet] with x hx hxu hxU
  exact tendsto_nhds_unique hx ((hfg.tendsto_at hxU).comp hns.tendsto_atTop |>.congr
    (fun n ↦ (hxu (ns n)).symm))

/-- Native Bergman spaces with complete values are Banach spaces. -/
instance : CompleteSpace (bergmanSpace F U) := isClosed.completeSpace_coe

section Representatives

omit [CompleteSpace F]

/-- An ambient representative, holomorphic on `U`; its values there are unique. -/
def representative (u : bergmanSpace F U) : ℂ → F := u.property.choose

/-- The chosen representative is holomorphic on the defining open set. -/
theorem differentiableOn_representative (u : bergmanSpace F U) :
    DifferentiableOn ℂ (representative u) U := u.property.choose_spec.1

/-- The chosen representative represents the original native `L²` class. -/
theorem coeFn_ae_eq_representative (u : bergmanSpace F U) :
    (u : Lp F 2 (volume.restrict (U : Set ℂ))) =ᵐ[volume.restrict (U : Set ℂ)]
      representative u := u.property.choose_spec.2

/-- Construct a Bergman class from an actual holomorphic square-integrable function. -/
def of (f : ℂ → F) (hf : DifferentiableOn ℂ f U)
    (hm : MemLp f 2 (volume.restrict (U : Set ℂ))) : bergmanSpace F U :=
  ⟨hm.toLp f, (mem_bergmanSpace_iff F U).mpr ⟨f, hf, hm.coeFn_toLp⟩⟩

/-- The constructor preserves its function almost everywhere. -/
theorem coeFn_of (f : ℂ → F) (hf : DifferentiableOn ℂ f U)
    (hm : MemLp f 2 (volume.restrict (U : Set ℂ))) :
    (of f hf hm : Lp F 2 (volume.restrict (U : Set ℂ))) =ᵐ[volume.restrict (U : Set ℂ)] f :=
  hm.coeFn_toLp

/-- The norm of a constructed Bergman class is the actual `L²` norm of its function. -/
theorem norm_of (f : ℂ → F) (hf : DifferentiableOn ℂ f U)
    (hm : MemLp f 2 (volume.restrict (U : Set ℂ))) :
    ‖of f hf hm‖ = (eLpNorm f 2 (volume.restrict (U : Set ℂ))).toReal :=
  Lp.norm_toLp f hm

/-- Any holomorphic representative agrees with the chosen one on `U`. -/
theorem eqOn_representative {u : bergmanSpace F U} {f : ℂ → F}
    (hf : DifferentiableOn ℂ f U)
    (hu : (u : Lp F 2 (volume.restrict (U : Set ℂ))) =ᵐ[volume.restrict (U : Set ℂ)] f) :
    EqOn (representative u) f U :=
  Measure.eqOn_open_of_ae_eq ((coeFn_ae_eq_representative u).symm.trans hu) U.isOpen
    (differentiableOn_representative u).continuousOn hf.continuousOn

/-- Bergman classes are determined by their holomorphic representatives on the open set. -/
@[ext]
theorem ext {u v : bergmanSpace F U}
    (h : ∀ x ∈ U, representative u x = representative v x) : u = v := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [coeFn_ae_eq_representative u, coeFn_ae_eq_representative v,
    ae_restrict_mem U.isOpen.measurableSet] with x h1 h2 hx
  rw [h1, h2, h x hx]

@[simp]
theorem representative_of (f : ℂ → F) (hf : DifferentiableOn ℂ f U)
    (hm : MemLp f 2 (volume.restrict (U : Set ℂ))) {x : ℂ} (hx : x ∈ U) :
    representative (of f hf hm) x = f x := eqOn_representative hf (coeFn_of f hf hm) hx

@[simp]
theorem representative_zero {x : ℂ} (hx : x ∈ U) :
    representative (0 : bergmanSpace F U) x = 0 :=
  eqOn_representative (differentiableOn_const 0) (Lp.coeFn_zero F 2 _) hx

@[simp]
theorem representative_add (u v : bergmanSpace F U) {x : ℂ} (hx : x ∈ U) :
    representative (u + v) x = representative u x + representative v x :=
  eqOn_representative ((differentiableOn_representative u).add
    (differentiableOn_representative v)) ((Lp.coeFn_add _ _).trans
      ((coeFn_ae_eq_representative u).add (coeFn_ae_eq_representative v))) hx

@[simp]
theorem representative_smul (c : ℂ) (u : bergmanSpace F U) {x : ℂ} (hx : x ∈ U) :
    representative (c • u) x = c • representative u x :=
  eqOn_representative ((differentiableOn_representative u).const_smul c)
    ((Lp.coeFn_smul c _).trans ((coeFn_ae_eq_representative u).const_smul c)) hx

@[simp]
theorem representative_neg (u : bergmanSpace F U) {x : ℂ} (hx : x ∈ U) :
    representative (-u) x = -representative u x :=
  eqOn_representative (differentiableOn_representative u).neg
    ((Lp.coeFn_neg _).trans (coeFn_ae_eq_representative u).neg) hx

@[simp]
theorem representative_sub (u v : bergmanSpace F U) {x : ℂ} (hx : x ∈ U) :
    representative (u - v) x = representative u x - representative v x :=
  eqOn_representative ((differentiableOn_representative u).sub
    (differentiableOn_representative v)) ((Lp.coeFn_sub _ _).trans
      ((coeFn_ae_eq_representative u).sub (coeFn_ae_eq_representative v))) hx

end Representatives

/-- On a compact subset, values of every holomorphic representative are uniformly controlled
by its native `L²` norm. The constant depends only on the compact set and the containing open. -/
theorem exists_norm_representative_le {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : bergmanSpace F U, ∀ x ∈ K, ‖representative u x‖ ≤ C * ‖u‖ := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open U.isOpen hKU
  refine ⟨(volume.real (ball (0 : ℂ) r))⁻¹ *
    ((volume (ball (0 : ℂ) r)) ^ (1 / 2 : ℝ)).toReal, by positivity, fun u x hx ↦ ?_⟩
  exact norm_le_Lp_norm (differentiableOn_representative u) (coeFn_ae_eq_representative u)
    hr ((closedBall_subset_cthickening hx r).trans hrU)

end BergmanSpace

end TauCeti
