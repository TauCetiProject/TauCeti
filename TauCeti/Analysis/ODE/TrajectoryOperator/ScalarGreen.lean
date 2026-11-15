/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.GreenIntegral.Scalar
public import TauCeti.Analysis.ODE.TrajectoryOperator.APriori
public import TauCeti.Analysis.ODE.TrajectoryOperator.Kernel
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import TauCeti.Analysis.ODE.Caratheodory

/-!
# The trajectory operator of an expanding scalar coefficient

Let `b : ℝ → ℝ` be a continuous essentially bounded scalar coefficient whose equation `v' = b v`
has a positive solution `g` that grows at a uniform exponential rate: for constants `K` and
`α > 0`,

`g s ≤ K exp (-α (t - s)) g t` whenever `s ≤ t`.

This file studies the trajectory operator `d/ds - b(s) : W^{1,p}(ℝ, E) → Lᵖ(ℝ, E)`
(`TauCeti.WeakDerivStep.trajectoryOperator` of the `L∞` class `AL` of `-b(s) • id`, which exists
because `b` is essentially bounded) through the Green integral
`G f (s) = -g s ∫_{t > s} f t / g t dt` of `TauCeti.Analysis.ODE.GreenIntegral.Scalar`.

On every real Banach space `E` and for every `1 ≤ p ≤ ∞` the operator is injective: a solution of
`u' = b u` is a multiple of `g`, and `g` is not in `Lᵖ`. For a finite-dimensional real normed
space `E` and `1 ≤ p < ∞`, it satisfies `‖u‖_{Lᵖ} ≤ 2 K / α ‖u' - b u‖_{Lᵖ}`, is bijective, and
its inverse is the Green integral: `u = G (u' - b u)` almost everywhere for every
`u ∈ W^{1,p}(ℝ, E)`. A typical coefficient is `b → 1` at both ends, as for the operator on a neck
glued from `d/ds + tanh` and `d/ds - tanh` (`TauCeti.Analysis.ODE.TrajectoryOperator.Neck`).

## Main declarations

* `TauCeti.WeakDerivStep.injective_trajectoryOperator_of_scalarGrowth`: `d/ds - b` is injective
  on `W^{1,p}(ℝ, E)` for every real Banach space `E` and every `1 ≤ p ≤ ∞`.
* `TauCeti.WeakDerivStep.norm_prev_le_mul_norm_trajectoryOperator_of_scalarGrowth` and
  `TauCeti.WeakDerivStep.norm_le_mul_norm_trajectoryOperator_of_scalarGrowth`: the a priori
  estimates for `d/ds - b` on `W^{1,p}(ℝ, E)`, for finite-dimensional `E`.
* `TauCeti.WeakDerivStep.bijective_trajectoryOperator_of_scalarGrowth`: `d/ds - b` is bijective,
  for finite-dimensional `E`.
* `TauCeti.WeakDerivStep.prev_ae_eq_scalarGreenIntegral_of_trajectoryOperator_ae_eq`: its inverse
  is the Green integral on all of `Lᵖ(ℝ, E)`, for finite-dimensional `E`.

## References

* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics **629**,
  Springer (1978) (exponential dichotomies and the Green function of `u' = A(t) u + f`).
* K. J. Palmer, *Exponential dichotomies and transversal homoclinic points*, J. Differential
  Equations **55** (1984), 225--256 (the operator `u ↦ u' - A(t) u` under exponential
  dichotomies).
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

namespace TauCeti.WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {g b : ℝ → ℝ} {K α : ℝ}
  {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

section Growth

variable (hg : ∀ s, HasDerivAt g (b s * g s) s) (hpos : ∀ s, 0 < g s)
  (hK : ∀ s t, s ≤ t → g s ≤ K * Real.exp (-α * (t - s)) * g t) (hα : 0 < α)
  (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
    fun s ↦ -b s • ContinuousLinearMap.id ℝ E)
include hg hpos hK hα hAL

/-- **The Green integral is a `W^{1,p}` solution.** If `g` is a positive solution of `v' = b v`
with `g s ≤ K exp (-α (t - s)) g t` for `s ≤ t` and `α > 0`, then for every continuous compactly
supported `f` with values in a real Banach space and `1 ≤ p ≤ ∞`, some `u ∈ W^{1,p}(ℝ, E)`
represented by the Green integral of `f` solves `u' - b u = f`. The coefficient of the trajectory
operator is any `L∞` class `AL` of `-b(s) • id`. -/
theorem exists_prev_ae_eq_scalarGreenIntegral_and_trajectoryOperator_ae_eq [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ u : WeakDerivStep volume ⊤ p
        (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] scalarGreenIntegral g f ∧
        ⇑(trajectoryOperator AL u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f := by
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun s ↦ (hg s).continuousAt
  have hfp : MemLp f p volume := hf.memLp_of_hasCompactSupport hfc
  have hvp : MemLp (scalarGreenIntegral g f) p volume :=
    (eLpNorm_scalarGreenIntegral_le hgc.aemeasurable hpos hK hα hf.aestronglyMeasurable
      Fact.out).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfp.eLpNorm_lt_top)
  obtain ⟨u, hu, hux⟩ := exists_trajectoryOperator_ae_eq_of_hasDerivAt hAL
    (fun s ↦ by simpa [add_comm] using hasDerivAt_scalarGreenIntegral hg hpos hK hα hf hM s)
    hvp hfp
  exact ⟨u, hux, hu⟩

/-- **`d/ds - b` is injective.** Let `b` be continuous and essentially bounded, so that
`-b(s) • id` has an `L∞` class `AL`, and let `g` be a positive solution of `v' = b v` with
`g s ≤ K exp (-α (t - s)) g t` for `s ≤ t` and `α > 0`. Then on every real Banach space `E` and
for every `1 ≤ p ≤ ∞`, `u' = b u` has no nonzero solution in `W^{1,p}(ℝ, E)`: a solution is a
multiple `g • x` of `g`, and `t ↦ (g t)⁻¹ • (g t • x) = x` would be integrable on `(0, ∞)`. -/
theorem injective_trajectoryOperator_of_scalarGrowth [CompleteSpace E] (hb : Continuous b) :
    Function.Injective (trajectoryOperator (p := p) AL) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu0 ↦ norm_le_zero_iff.1 ?_
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun s ↦ (hg s).continuousAt
  obtain ⟨v, hv, huv⟩ := exists_hasDerivAt_of_trajectoryOperator_eq_zero
    (hb.neg.smul continuous_const) hAL hu0
  -- The classical solution `v` is a multiple of `g`.
  have hB : Continuous fun s ↦ b s • ContinuousLinearMap.id ℝ E := hb.smul continuous_const
  have heq : v = fun s ↦ (g s / g 0) • v 0 :=
    hB.eq_of_hasDerivAt_clm_apply (fun s ↦ by simpa using hv s)
      (fun s ↦ by
        convert ((hg s).div_const (g 0)).smul_const (v 0) using 1
        rw [smul_apply, ContinuousLinearMap.id_apply, smul_smul, mul_div_assoc])
      (t₀ := 0) (by simp [(hpos 0).ne'])
  have hvp : MemLp v p (volume.restrict (Ioi 0)) := by
    have h := (Lp.memLp (prev _ u)).ae_eq huv
    rw [Opens.coe_top, Measure.restrict_univ] at h
    exact h.restrict _
  -- So `t ↦ (g t)⁻¹ • v t` is the constant `(g 0)⁻¹ • v 0`, integrable on `(0, ∞)` only if zero.
  have hint : IntegrableOn (fun _ : ℝ ↦ (g 0)⁻¹ • v 0) (Ioi 0) := by
    refine (integrableOn_inv_smul_Ioi hgc.aemeasurable hpos hK hα hvp).congr_fun
      (fun t _ ↦ ?_) measurableSet_Ioi
    dsimp only
    rw [congrFun heq t, smul_smul, ← mul_div_assoc, inv_mul_cancel₀ (hpos t).ne', one_div]
  have hv0 : v 0 = 0 := by
    rcases (integrableOn_const_iff (C := (g 0)⁻¹ • v 0)).1 hint with h | h
    · simpa [(hpos 0).ne'] using h
    · simp at h
  have hprev : prev _ u = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    refine huv.trans (Eventually.of_forall fun s ↦ ?_)
    rw [congrFun heq s, hv0, smul_zero, Pi.zero_apply]
  have h := norm_le_mul_norm_trajectoryOperator_of_norm_prev_le (A := AL) (C := 0) u
    (by rw [hprev, norm_zero, zero_mul])
  rwa [hu0, norm_zero, mul_zero] at h

variable [FiniteDimensional ℝ E]

/-- **The a priori estimate for `d/ds - b`.** Let `E` be a finite-dimensional real normed space,
let `b` be continuous and essentially bounded, so that `-b(s) • id` has an `L∞` class `AL`, and let
`g` be a positive solution of `v' = b v` with `g s ≤ K exp (-α (t - s)) g t` for `s ≤ t` and
`α > 0`. Then for `1 ≤ p < ∞` every `u ∈ W^{1,p}(ℝ, E)` satisfies
`‖u‖_{Lᵖ} ≤ 2 K / α ‖u' - b u‖_{Lᵖ}`. -/
theorem norm_prev_le_mul_norm_trajectoryOperator_of_scalarGrowth (hb : Continuous b)
    (hp : p ≠ ∞)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖prev _ u‖ ≤ 2 * K / α * ‖trajectoryOperator AL u‖ := by
  have hK0 : 0 ≤ 2 * K / α := by
    have h := hK 0 0 le_rfl
    rw [sub_self, mul_zero, Real.exp_zero, mul_one] at h
    exact div_nonneg (mul_nonneg zero_le_two
      (zero_le_one.trans ((le_mul_iff_one_le_left (hpos 0)).1 h))) hα.le
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun s ↦ (hg s).continuousAt
  -- On smooth compactly supported paths this is the `Lᵖ` bound for the Green integral.
  refine norm_prev_le_mul_norm_trajectoryOperator_of_forall_contDiff hp hAL hK0
    (fun φ hφ hφc ↦ ?_) u
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  set f : ℝ → E := fun s ↦ deriv φ s - b s • φ s with f_def
  have hfc : Continuous f := (hφ1.continuous_deriv le_rfl).sub (hb.smul hφ1.continuous)
  have hG : scalarGreenIntegral g f = φ :=
    funext (scalarGreenIntegral_deriv_sub_eq hb hg hpos hφ1 hφc)
  have key := eLpNorm_scalarGreenIntegral_le hgc.aemeasurable hpos hK hα hfc.aestronglyMeasurable
    (p := p) Fact.out
  have hf : (fun s ↦ deriv φ s + (-b s • ContinuousLinearMap.id ℝ E) (φ s)) = f := by
    funext s
    rw [f_def, smul_apply, ContinuousLinearMap.id_apply, neg_smul,
      ← sub_eq_add_neg]
  rwa [hG, ← hf] at key

/-- **The graph-norm estimate for `d/ds - b`.** Under the hypotheses of
`TauCeti.WeakDerivStep.norm_prev_le_mul_norm_trajectoryOperator_of_scalarGrowth`, including that
`E` is finite-dimensional, every `u ∈ W^{1,p}(ℝ, E)` satisfies
`‖u‖ ≤ (1 + (1 + ‖AL‖) 2 K / α) ‖u' - b u‖_{Lᵖ}`, where `AL` is the `L∞` class of `-b(s) • id`. -/
theorem norm_le_mul_norm_trajectoryOperator_of_scalarGrowth (hb : Continuous b) (hp : p ≠ ∞)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖u‖ ≤ (1 + (1 + ‖AL‖) * (2 * K / α)) * ‖trajectoryOperator AL u‖ :=
  norm_le_mul_norm_trajectoryOperator_of_norm_prev_le u
    (norm_prev_le_mul_norm_trajectoryOperator_of_scalarGrowth hg hpos hK hα hAL hb hp u)

/-- **`d/ds - b` is surjective.** Under the hypotheses of
`TauCeti.WeakDerivStep.norm_prev_le_mul_norm_trajectoryOperator_of_scalarGrowth`, including that
`E` is finite-dimensional, the equation `u' - b u = f` has a solution `u ∈ W^{1,p}(ℝ, E)` for
every `f ∈ Lᵖ(ℝ, E)`. -/
theorem surjective_trajectoryOperator_of_scalarGrowth (hb : Continuous b) (hp : p ≠ ∞) :
    Function.Surjective (trajectoryOperator (p := p) AL) :=
  surjective_trajectoryOperator_of_forall_norm_le hp
    (norm_le_mul_norm_trajectoryOperator_of_scalarGrowth hg hpos hK hα hAL hb hp) fun _ hf hfc ↦
      (exists_prev_ae_eq_scalarGreenIntegral_and_trajectoryOperator_ae_eq hg hpos hK hα hAL
        hf.continuous hfc).imp fun _ h ↦ h.2

/-- **`d/ds - b` is bijective.** Let `E` be a finite-dimensional real normed space, let `b` be
continuous and essentially bounded, so that `-b(s) • id` has an `L∞` class `AL`, and let `g` be a
positive solution of `v' = b v` with `g s ≤ K exp (-α (t - s)) g t` for `s ≤ t` and `α > 0`. Then
for `1 ≤ p < ∞` the trajectory operator `u ↦ u' - b u` with coefficient `AL` is a bijection from
`W^{1,p}(ℝ, E)` onto `Lᵖ(ℝ, E)`. -/
theorem bijective_trajectoryOperator_of_scalarGrowth (hb : Continuous b) (hp : p ≠ ∞) :
    Function.Bijective (trajectoryOperator (p := p) AL) :=
  ⟨injective_trajectoryOperator_of_scalarGrowth hg hpos hK hα hAL hb,
    surjective_trajectoryOperator_of_scalarGrowth hg hpos hK hα hAL hb hp⟩

/-- **The inverse of `d/ds - b` is the Green integral.** Under the hypotheses of
`TauCeti.WeakDerivStep.bijective_trajectoryOperator_of_scalarGrowth`, including that `E` is
finite-dimensional, if `u ∈ W^{1,p}(ℝ, E)` solves `u' - b u = f`, then
`u s = -g s ∫_{t > s} f t / g t dt` for almost every `s`. The forcing term `f` is any
representative of an element of `Lᵖ(ℝ, E)`: the formula holds for continuous compactly supported
`f` by construction, and extends to all of `Lᵖ` by density, since both sides are bounded in `f`. -/
theorem prev_ae_eq_scalarGreenIntegral_of_trajectoryOperator_ae_eq (hb : Continuous b)
    (hp : p ≠ ∞) {f : ℝ → E}
    {u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    (hu : ⇑(trajectoryOperator AL u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f) :
    ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] scalarGreenIntegral g f := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun s ↦ (hg s).continuousAt
  have hC := norm_prev_le_mul_norm_trajectoryOperator_of_scalarGrowth hg hpos hK hα hAL hb hp
  -- On the whole line the restricted measure is `volume`.
  have hae {F G : ℝ → E} (h : F =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] G) : F =ᵐ[volume] G :=
    by simpa using h
  have hnorm {F : ℝ → E} :
      eLpNorm F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) = eLpNorm F p volume := by simp
  have hfp : MemLp f p volume := by
    have h := (Lp.memLp (trajectoryOperator AL u)).ae_eq hu
    rwa [Opens.coe_top, Measure.restrict_univ] at h
  have hint {φ : ℝ → E} (hφ : MemLp φ p volume) (s : ℝ) :
      IntegrableOn (fun t ↦ (g t)⁻¹ • φ t) (Ioi s) :=
    integrableOn_inv_smul_Ioi hgc.aemeasurable hpos hK hα (hφ.restrict _)
  set c := ENNReal.ofReal (2 * K / α)
  -- Compare with the solution `v` for a continuous compactly supported `φ` close to `f`.
  have key (ε : ℝ≥0∞) (hε : ε ≠ 0) :
      eLpNorm (⇑(prev _ u) - scalarGreenIntegral g f) p volume ≤ (c + c) * ε := by
    obtain ⟨φ, hφc, hfφ, hφ, hφp⟩ := hfp.exists_hasCompactSupport_eLpNorm_sub_le hp hε
    obtain ⟨v, hv, hTv⟩ :=
      exists_prev_ae_eq_scalarGreenIntegral_and_trajectoryOperator_ae_eq (p := p) hg hpos hK hα
        hAL hφ hφc
    have hTuv : eLpNorm (⇑(trajectoryOperator AL (u - v))) p volume = eLpNorm (f - φ) p volume :=
      eLpNorm_congr_ae <| by
        rw [map_sub]
        filter_upwards [hae (Lp.coeFn_sub (trajectoryOperator AL u) (trajectoryOperator AL v)),
          hae hu, hae hTv] with s hs hus hvs
        rw [hs, Pi.sub_apply, hus, hvs, Pi.sub_apply]
    -- The value part: the a priori estimate for `u - v`.
    have h₁ : eLpNorm (⇑(prev _ (u - v))) p volume ≤ c * ε := by
      rw [← hnorm, ← Lp.eNorm_def, ← ofReal_norm]
      calc ENNReal.ofReal ‖prev _ (u - v)‖
          ≤ ENNReal.ofReal (2 * K / α * ‖trajectoryOperator AL (u - v)‖) :=
            ENNReal.ofReal_le_ofReal (hC (u - v))
        _ = c * eLpNorm (f - φ) p volume := by
          rw [ENNReal.ofReal_mul' (norm_nonneg _), ofReal_norm, Lp.eNorm_def, hnorm,
            hTuv]
        _ ≤ c * ε := by gcongr
    -- The forcing part: the `Lᵖ` bound for the Green integral of `φ - f`.
    have h₂ : eLpNorm (scalarGreenIntegral g (φ - f)) p volume ≤ c * ε :=
      (eLpNorm_scalarGreenIntegral_le hgc.aemeasurable hpos hK hα
        (hφ.aestronglyMeasurable.sub hfp.aestronglyMeasurable) Fact.out).trans
        (by rw [eLpNorm_sub_comm]; gcongr)
    have hsplit : ⇑(prev _ u) - scalarGreenIntegral g f =ᵐ[volume]
        ⇑(prev _ (u - v)) + scalarGreenIntegral g (φ - f) := by
      filter_upwards [hae (Lp.coeFn_sub (prev _ u) (prev _ v)), hae hv] with s hs hvs
      rw [Pi.sub_apply, Pi.add_apply,
        show prev _ (u - v) = prev _ u - prev _ v by simp only [← prevL_apply, map_sub], hs,
        Pi.sub_apply, hvs,
        scalarGreenIntegral_sub (hint hφp s) (hint hfp s)]
      abel
    calc eLpNorm (⇑(prev _ u) - scalarGreenIntegral g f) p volume
        = eLpNorm (⇑(prev _ (u - v)) + scalarGreenIntegral g (φ - f)) p volume :=
          eLpNorm_congr_ae hsplit
      _ ≤ eLpNorm (⇑(prev _ (u - v))) p volume +
            eLpNorm (scalarGreenIntegral g (φ - f)) p volume :=
          eLpNorm_add_le Fact.out
      _ ≤ c * ε + c * ε := add_le_add h₁ h₂
      _ = (c + c) * ε := (add_mul _ _ _).symm
  -- Letting `ε → 0`, the `Lᵖ` distance between `u` and the Green integral of `f` vanishes.
  have hzero : eLpNorm (⇑(prev _ u) - scalarGreenIntegral g f) p volume = 0 := by
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_) zero_le
    rw [zero_add]
    rcases eq_or_ne (c + c) 0 with h0 | h0
    · calc _ ≤ (c + c) * 1 := key 1 one_ne_zero
        _ = 0 := by rw [h0, zero_mul]
        _ ≤ δ := zero_le
    · have hctop : c + c ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
      calc _ ≤ (c + c) * (δ / (c + c)) :=
            key _ (ENNReal.div_ne_zero.2 ⟨by exact_mod_cast hδ.ne', hctop⟩)
        _ = δ := ENNReal.mul_div_cancel h0 hctop
  exact ae_restrict_of_ae ((sub_ae_eq_zero _ _).1
    ((eLpNorm_eq_zero_iff (zero_lt_one.trans_le Fact.out).ne').1 hzero))

end Growth

end TauCeti.WeakDerivStep
