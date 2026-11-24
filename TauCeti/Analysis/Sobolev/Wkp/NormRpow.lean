/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Algebra.Order.Ring.Basic
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.InnerProductSpace.Trace.OpNorm
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Second-order Sobolev regularity of norm powers

Let `E` be a real inner product space of finite dimension `d` with an additive Haar measure, and
let `s` be real. Away from the origin the power `u(x) = ‖x‖ ^ s` has the Hessian

`D²u(x) w = s ‖x‖ ^ (s - 2) w + s (s - 2) ‖x‖ ^ (s - 4) ⟪x, w⟫ x`,

of size comparable to `‖x‖ ^ (s - 2)`: its trace is `s (d + s - 2) ‖x‖ ^ (s - 2)`. This file
shows that for `s > 2 - d` the classical Hessian is the weak Hessian across the origin
(`TauCeti.Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_norm_rpow`), and that for `s ≠ 0` with
`s > 2 - d`, on a bounded open set `Ω` containing the origin, `u` lies in `W^{2,p}(Ω)`,
`1 ≤ p < ∞`, exactly when `(s - 2) p > -d` (`TauCeti.exists_wkp_two_value_ae_eq_norm_rpow_iff`).
For `s < 2` this is the range `p < d / (2 - s)`.

The weak first derivatives are the classical ones by `TauCeti.hasWeakFDerivOn_norm_rpow`. The
coordinates `s ‖x‖ ^ (s - 2) ⟪x, v⟫` of the gradient are weakly differentiable with their
classical derivatives by `TauCeti.hasWeakFDerivOn_norm_rpow_mul_inner`, which needs
`s - 2 > -d`, and uniqueness of weak derivatives identifies the weak Hessian.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set Filter TopologicalSpace
open scoped RealInnerProductSpace ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {s : ℝ}

/-- Away from the origin, the entries of the Hessian of `‖x‖ ^ s`:
`⟪D²u(x) w, v⟫ = s ‖x‖ ^ (s - 2) ⟪w, v⟫ + s (s - 2) ‖x‖ ^ (s - 4) ⟪x, w⟫ ⟪x, v⟫`. -/
private theorem inner_normRpowHessian_apply (x v w : E) :
    ⟪((s * ‖x‖ ^ (s - 2)) • ContinuousLinearMap.id ℝ E +
        (s * (s - 2) * ‖x‖ ^ (s - 4)) • (innerSL ℝ x).smulRight x) w, v⟫ =
      s * ((‖x‖ ^ (s - 2) • innerSL ℝ v +
        ((s - 2) * ‖x‖ ^ (s - 2 - 2) * ⟪x, v⟫) • innerSL ℝ x) w) := by
  have h4 : s - 2 - 2 = s - 4 := by ring
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_add_left, real_inner_smul_left, smul_eq_mul, h4]
  rw [real_inner_comm w v]
  ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {Ω : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The weak Hessian of a norm power.** For `s > 2 - dim E`, the weak Hessian of an element of
`W^{2,p}(Ω)` equal to `‖x‖ ^ s` is, almost everywhere on `Ω`, its classical Hessian
`w ↦ s ‖x‖ ^ (s - 2) w + s (s - 2) ‖x‖ ^ (s - 4) ⟪x, w⟫ x`, although that Hessian is only defined
away from the origin and, for `s < 2` with `s ≠ 0`, is unbounded there. -/
theorem Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_norm_rpow
    (hs : 2 - (Module.finrank ℝ E : ℝ) < s) (W : Wkp μ Ω p 2)
    (hW : Wkp.value 2 W =ᵐ[μ.restrict Ω] fun x => ‖x‖ ^ s) :
    Wkp.iteratedGradient 1 W =ᵐ[μ.restrict Ω] fun x =>
      (s * ‖x‖ ^ (s - 2)) • ContinuousLinearMap.id ℝ E +
        (s * (s - 2) * ‖x‖ ^ (s - 4)) • (innerSL ℝ x).smulRight x := by
  -- Each entry `⟪D²W w, v⟫` is the classical one.
  have hentry : ∀ v w : E, (fun x => ⟪Wkp.iteratedGradient 1 W x w, v⟫) =ᵐ[μ.restrict Ω]
      fun x => ⟪((s * ‖x‖ ^ (s - 2)) • ContinuousLinearMap.id ℝ E +
        (s * (s - 2) * ‖x‖ ^ (s - 4)) • (innerSL ℝ x).smulRight x) w, v⟫ := by
    intro v w
    obtain ⟨d, hdv, hdg⟩ := Wkp.exists_hasWeakLineDerivOn_value_and_inner_gradient_ae_eq W v
    -- The weak derivative of `‖x‖ ^ s` in the direction `v` is `s ‖x‖ ^ (s - 2) ⟪x, v⟫`.
    have hline : HasWeakLineDerivOn μ Ω (Wkp.value 2 W)
        (s • fun x => ‖x‖ ^ (s - 2) * ⟪x, v⟫) v :=
      (((hasWeakFDerivOn_norm_rpow (μ := μ) (by linarith) Ω).hasWeakLineDerivOn v).congr_ae
        hW.symm).congr_ae_deriv (Eventually.of_forall fun x => by
          simp only [smul_apply, innerSL_apply_apply, smul_eq_mul,
            Pi.smul_apply]
          ring)
    have hval := hdv.ae_eq hline
    -- Its weak derivative is the classical one.
    have hgrad := ((W1p.hasWeakFDerivOn d).congr_ae hval).ae_eq
      ((hasWeakFDerivOn_norm_rpow_mul_inner (μ := μ) (s := s - 2) (by linarith) v Ω).const_smul s)
    filter_upwards [hdg w, hgrad] with x h1 h2
    rw [← h1, inner_normRpowHessian_apply, ← innerSL_apply_apply ℝ (W1p.gradient d x) w, h2]
    simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
  -- Entries in an orthonormal basis determine the operator.
  set b := stdOrthonormalBasis ℝ E
  have hall := ae_all_iff.2 fun i => ae_all_iff.2 fun j => hentry (b i) (b j)
  filter_upwards [hall] with x hx
  refine ContinuousLinearMap.coe_injective (b.toBasis.ext fun j =>
    InnerProductSpace.ext_inner_right_basis b.toBasis fun i => ?_)
  simpa only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe] using hx i j

omit [MeasurableSpace E] [BorelSpace E] in
/-- The classical Hessian of `‖x‖ ^ s` has operator norm at least
`|s| (dim E + s - 2) / dim E ‖x‖ ^ (s - 2)` away from the origin, since its trace is
`s (dim E + s - 2) ‖x‖ ^ (s - 2)`. -/
private theorem le_norm_normRpowHessian (hs : 2 - (Module.finrank ℝ E : ℝ) < s) {x : E}
    (hx : x ≠ 0) :
    |s| * (Module.finrank ℝ E + s - 2) / Module.finrank ℝ E * ‖x‖ ^ (s - 2) ≤
      ‖(s * ‖x‖ ^ (s - 2)) • ContinuousLinearMap.id ℝ E +
        (s * (s - 2) * ‖x‖ ^ (s - 4)) • (innerSL ℝ x).smulRight x‖ := by
  set H := (s * ‖x‖ ^ (s - 2)) • ContinuousLinearMap.id ℝ E +
    (s * (s - 2) * ‖x‖ ^ (s - 4)) • (innerSL ℝ x).smulRight x
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  set b := stdOrthonormalBasis ℝ E
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.2 Module.finrank_pos
  -- The trace of `H` is the Laplacian of `‖x‖ ^ s`.
  have htr : ∑ i, ⟪H (b i), b i⟫ = s * (Module.finrank ℝ E + s - 2) * ‖x‖ ^ (s - 2) := by
    have hterm : ∀ i, ⟪H (b i), b i⟫ = iteratedFDeriv ℝ 2 (fun y : E => ‖y‖ ^ s) x ![b i, b i] := by
      intro i
      rw [iteratedFDeriv_two_norm_rpow_apply s hx]
      simp only [H, add_apply, smul_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_add_left,
        real_inner_smul_left]
      ring
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      ← congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b) x,
      laplacian_norm_rpow_of_ne s hx]
    ring
  have hle : |s * (Module.finrank ℝ E + s - 2) * ‖x‖ ^ (s - 2)| ≤ Module.finrank ℝ E * ‖H‖ := by
    have htrH : traceCLM ℝ E H = ∑ i, ⟪H (b i), b i⟫ := by
      rw [traceCLM_apply, LinearMap.trace_eq_sum_inner _ b]
      simp only [ContinuousLinearMap.coe_coe, real_inner_comm]
    rw [← htr, ← htrH, ← Real.norm_eq_abs]
    exact H.norm_traceCLM_le
  rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Module.finrank ℝ E + s - 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ (s - 2))] at hle
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  linarith

/-- **Norm powers in `W^{2,p}`.** Let `Ω` be a bounded open set and `1 ≤ p < ∞`. If
`(s - 2) p > -dim E`, then `x ↦ ‖x‖ ^ s` lies in `W^{2,p}(Ω)`: its derivatives of orders `0`, `1`
and `2` are bounded by multiples of `‖x‖ ^ s`, `‖x‖ ^ (s - 1)` and `‖x‖ ^ (s - 2)`. -/
theorem exists_wkp_two_value_ae_eq_norm_rpow (hb : Bornology.IsBounded (Ω : Set E))
    (hp : p ≠ ∞) (h : -(Module.finrank ℝ E : ℝ) < (s - 2) * p.toReal) :
    ∃ W : Wkp μ Ω p 2, Wkp.value 2 W =ᵐ[μ.restrict Ω] fun x => ‖x‖ ^ s := by
  have hp1 : 1 ≤ p.toReal := ENNReal.toReal_mono hp (Fact.out : (1 : ℝ≥0∞) ≤ p) |>.trans_eq'
    ENNReal.toReal_one.symm
  have hs2 : -(Module.finrank ℝ E : ℝ) < s - 2 := neg_lt_of_neg_lt_mul (Nat.cast_nonneg _) hp1 h
  -- The coordinates of the gradient, `s ‖x‖ ^ (s - 2) ⟪x, v⟫`, are in `W^{1,p}(Ω)`.
  have hcoord : ∀ v : E, ∃ D : Wkp μ Ω p 1,
      Wkp.value 1 D =ᵐ[μ.restrict Ω] s • fun x => ‖x‖ ^ (s - 2) * ⟪x, v⟫ := by
    intro v
    have hD := (hasWeakFDerivOn_norm_rpow_mul_inner (μ := μ) hs2 v Ω).const_smul s
    refine Wkp.exists_value_one_ae_eq_of_forall_hasWeakLineDerivOn
      (hb.memLp_of_norm_le_mul_norm_rpow (C := |s| * ‖v‖) (s := s - 1) hp (by nlinarith)
        (by fun_prop : Measurable _).aestronglyMeasurable fun x => ?_) _
      (fun w => hb.memLp_of_norm_le_mul_norm_rpow (C := |s| * ((1 + |s - 2|) * ‖v‖ * ‖w‖))
        (s := s - 2) hp h (by fun_prop : Measurable _).aestronglyMeasurable fun x => ?_)
      fun w => hD.hasWeakLineDerivOn w
    · rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc]
      have := abs_norm_rpow_mul_inner_le (s - 2) v x
      rw [show s - 2 + 1 = s - 1 by ring] at this
      exact mul_le_mul_of_nonneg_left this (abs_nonneg s)
    · rw [Pi.smul_apply, smul_apply, norm_smul, Real.norm_eq_abs,
        mul_assoc |s|]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)
      refine (ContinuousLinearMap.le_opNorm _ w).trans ?_
      have := norm_norm_rpow_smul_innerSL_add_le (s - 2) v x
      nlinarith [norm_nonneg w, Real.rpow_nonneg (norm_nonneg x) (s - 2)]
  choose D hD using hcoord
  refine Wkp.exists_value_ae_eq_of_forall_hasWeakLineDerivOn 1
    (hb.memLp_of_norm_le_mul_norm_rpow (C := 1) (s := s) hp (by nlinarith)
      (by fun_prop : Measurable _).aestronglyMeasurable
      fun x => by rw [Real.norm_of_nonneg (by positivity), one_mul]) D fun v => ?_
  refine ((hasWeakFDerivOn_norm_rpow (μ := μ) (by linarith) Ω).hasWeakLineDerivOn v).congr_ae_deriv
    ?_
  filter_upwards [hD v] with x hx
  rw [hx]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, Pi.smul_apply]
  ring

/-- **Norm powers in `W^{2,p}` near the origin.** Let `Ω` be a bounded open set containing the
origin, `1 ≤ p < ∞`, and `s ≠ 0` with `s > 2 - dim E`. Then `x ↦ ‖x‖ ^ s` lies in `W^{2,p}(Ω)`
exactly when `(s - 2) p > -dim E`, that is when `p < dim E / (2 - s)` for `s < 2`, and for every
`p` when `s ≥ 2`. Its weak Hessian has size comparable to `‖x‖ ^ (s - 2)`. -/
theorem exists_wkp_two_value_ae_eq_norm_rpow_iff (hb : Bornology.IsBounded (Ω : Set E))
    (hp : p ≠ ∞) (h0 : (0 : E) ∈ Ω) (hs0 : s ≠ 0) (hs : 2 - (Module.finrank ℝ E : ℝ) < s) :
    (∃ W : Wkp μ Ω p 2, Wkp.value 2 W =ᵐ[μ.restrict Ω] fun x => ‖x‖ ^ s) ↔
      -(Module.finrank ℝ E : ℝ) < (s - 2) * p.toReal := by
  refine ⟨fun ⟨W, hW⟩ => ?_, exists_wkp_two_value_ae_eq_norm_rpow hb hp⟩
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hp1 : 1 ≤ p.toReal := ENNReal.toReal_mono hp (Fact.out : (1 : ℝ≥0∞) ≤ p) |>.trans_eq'
    ENNReal.toReal_one.symm
  rcases le_or_gt 2 s with hs2 | hs2
  · nlinarith
  have hd : (0 : ℝ) < Module.finrank ℝ E := by linarith
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by exact_mod_cast hd)
  set c : ℝ := |s| * (Module.finrank ℝ E + s - 2) / Module.finrank ℝ E
  have hc : 0 < c := by
    have := abs_pos.2 hs0
    have : 0 < (Module.finrank ℝ E : ℝ) + s - 2 := by linarith
    positivity
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen 0 h0
  have hint : IntegrableOn (fun x => ‖Wkp.iteratedGradient 1 W x‖ ^ p.toReal)
      (Metric.ball 0 r) μ :=
    ((Lp.memLp (Wkp.iteratedGradient 1 W)).integrable_norm_rpow hp0 hp).mono_measure
      (Measure.restrict_mono hball le_rfl)
  -- `‖x‖ ^ ((s - 2) p) ≤ c⁻ᵖ ‖D²W‖ ^ p` almost everywhere near the origin.
  have hpow : IntegrableOn (fun x : E => ‖x‖ ^ ((s - 2) * p.toReal)) (Metric.ball 0 r) μ := by
    refine (hint.const_mul (c ^ (-p.toReal))).mono'
      (by fun_prop : Measurable fun x : E => ‖x‖ ^ ((s - 2) * p.toReal)).aestronglyMeasurable ?_
    have hH := (Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_norm_rpow hs W hW).filter_mono
      (ae_mono (Measure.restrict_mono hball le_rfl))
    filter_upwards [hH, ae_restrict_of_ae (μ.ae_ne 0)] with x hx hx0
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_mul (norm_nonneg x), Real.rpow_neg hc.le,
      le_inv_mul_iff₀ (by positivity), ← Real.mul_rpow hc.le (by positivity), hx]
    exact Real.rpow_le_rpow (by positivity) (le_norm_normRpowHessian hs hx0) (by linarith)
  exact (integrableOn_norm_rpow_ball_iff hr).1 hpow

end TauCeti
