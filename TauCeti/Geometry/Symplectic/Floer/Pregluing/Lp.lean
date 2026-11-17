/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Pregluing
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The `Lᵖ` norm of the pre-gluing error

Let `(V, ω)` be a symplectic vector space, `H_t` a `C²` Hamiltonian, `J_t(y)` a continuous family
of endomorphisms, and `F` the Floer operator of the cylindrical datum `K = H_t dt`
(`TauCeti.SymplecticForm.floerOperator`). Let `u` and `v` be `C¹` solutions of `F = 0` on the
strip `ℝ × [0, 1]` converging in `C¹` at the exponential rate `κ > 0` to the same orbit `x`, `u` as
`s → +∞` and `v` as `s → -∞`. The gluing theorem corrects the pre-glued map
`w_R = TauCeti.Floer.preglue x u v R` to a solution by the Newton iteration
`TauCeti.exists_mem_range_norm_le_add_add_eq_zero`, for the Floer operator as a map from
`W^{1,p}` to `Lᵖ`. Its input `e` is the error `F(w_R)` as an element of `Lᵖ`, and the iteration
converges once `‖e‖_{Lᵖ}` is small compared with the norm of a right inverse of the linearized
operator and the constant of the quadratic estimate. This file proves that bound on `‖e‖_{Lᵖ}`.

The error is supported in the neck `[-1, 1] × [0, 1]` of the strip
(`TauCeti.SymplecticForm.floerOperator_preglue_eq_zero`), and there it is at most `C' e^{-κ R}`
for every large `R`
(`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglue_le_of_floerOperator_eq_zero`).
The neck has area `2`, so for every exponent `p ∈ [0, ∞]` and every large `R`

`‖F(w_R)‖_{Lᵖ(ℝ × [0, 1])} ≤ 2^{1/p} C' e^{-κ R}`

with `1/∞ = 0` (`TauCeti.SymplecticForm.exists_eventually_eLpNorm_floerOperator_preglue_le`). The
strip has infinite area; the error vanishes outside the neck because `u` and `v` are exact
solutions, so only the area of the neck enters the constant.

## Main results

* `TauCeti.SymplecticForm.exists_eventually_eLpNorm_floerOperator_preglue_le`: the
  pre-gluing error of two Floer solutions converging exponentially to the same orbit has `Lᵖ` norm
  `O(e^{-κ R})` on the strip.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), on gluing Floer trajectories.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Chapter 10, on the
  `Lᵖ` estimate of the pre-gluing error in the gluing theorem.
-/

public section

open Filter MeasureTheory Set Function ContinuousLinearMap
open scoped ENNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The pre-gluing error is exponentially small in `Lᵖ`.** Let `H` be a `C²`
Hamiltonian, `J_t(y)` a continuous family of endomorphisms, and `x` an orbit of `X_{H_t}`. Let `u`
and `v` be `C¹` solutions of the Floer equation on the strip `ℝ × [0, 1]` converging to `x` in
`C¹` at the exponential rate `κ > 0`, `u` as `s → +∞` and `v` as `s → -∞`. Then for every exponent
`p` there is a constant `C'` such that for every large gluing parameter `R`, the Floer operator of
the pre-glued map `w_R` has `Lᵖ` norm at most `C' e^{-κ R}` on the strip. In particular it lies in
`Lᵖ` of the strip (`MeasureTheory.MemLp` is the finiteness of this norm). -/
theorem exists_eventually_eLpNorm_floerOperator_preglue_le (ω : SymplecticForm V)
    {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {x : ℝ → V} {u v : ℝ × ℝ → V} {C κ : ℝ}
    (p : ℝ≥0∞) (hH : ContDiff ℝ 2 (uncurry H)) (hJ : Continuous (uncurry J))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hκ : 0 < κ)
    (huc : ContDiff ℝ 1 u) (hvc : ContDiff ℝ 1 v)
    (hu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1, ‖u (s, t) - x t‖ ≤ C * Real.exp (-(κ * s)))
    (hdu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ u (s, t) - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (-(κ * s)))
    (hv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, ‖v (s, t) - x t‖ ≤ C * Real.exp (κ * s))
    (hdv : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ v (s, t) - (snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (κ * s))
    (huF : ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1,
      ω.floerOperator (fun w ↦ J w.2) (fun _ _ ↦ 0) (fun w ↦ H w.2) u z = 0)
    (hvF : ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1,
      ω.floerOperator (fun w ↦ J w.2) (fun _ _ ↦ 0) (fun w ↦ H w.2) v z = 0) :
    ∃ C', ∀ᶠ R in atTop,
      eLpNorm (ω.floerOperator (fun w ↦ J w.2) (fun _ _ ↦ 0) (fun w ↦ H w.2)
        (Floer.preglue x u v R)) p (volume.restrict (univ ×ˢ Icc (0 : ℝ) 1)) ≤
        ENNReal.ofReal (C' * Real.exp (-(κ * R))) := by
  set S : Set (ℝ × ℝ) := univ ×ˢ Icc (0 : ℝ) 1
  set N : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hS : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Icc
  have hN : MeasurableSet N := measurableSet_Icc.prod measurableSet_Icc
  have hNS : N ⊆ S := prod_mono (subset_univ _) subset_rfl
  have hvolN : volume N = 2 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    norm_num
  obtain ⟨C', hC'⟩ := ω.exists_eventually_norm_floerOperator_preglue_le_of_floerOperator_eq_zero
    hH hJ hx hκ (.of_forall fun _ _ _ ↦ huc.differentiable one_ne_zero _) hu hdu
    (.of_forall fun _ _ _ ↦ hvc.differentiable one_ne_zero _) hv hdv huF hvF
  -- The neck has area `2`, which contributes the factor `2^{1/p}` to the constant.
  set c : ℝ := (2 : ℝ) ^ p.toReal⁻¹
  have hc : 0 ≤ c := by positivity
  refine ⟨c * C', hC'.mono fun R hR ↦ ?_⟩
  set F := ω.floerOperator (fun w ↦ J w.2) (fun _ _ ↦ 0) (fun w ↦ H w.2) (Floer.preglue x u v R)
  -- The orbit `x` is `C¹`, as its derivative `X_{H_t}(x(t))` is continuous, so `F` is continuous.
  have hxd : Differentiable ℝ x := fun t ↦ (hx t).differentiableAt
  have hxc : ContDiff ℝ 1 x := contDiff_one_iff_deriv.2 ⟨hxd,
    (continuous_congr fun t ↦ (hx t).deriv.symm).1
      ((ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH).continuous.comp
        (continuous_id.prodMk hxd.continuous))⟩
  have hF : Continuous F := ω.continuous_floerOperator
    (hJ.comp (continuous_fst.snd.prodMk continuous_snd)) contDiff_const
    ((hH.of_le one_le_two).comp (contDiff_fst.snd.prodMk contDiff_snd))
    (Floer.contDiff_preglue hxc huc hvc)
  -- On the strip the error is its restriction to the neck, where it is bounded.
  have hFN : F =ᵐ[volume.restrict S] N.indicator F :=
    ae_restrict_of_forall_mem hS fun z hz ↦ by
      by_cases hzN : z ∈ N
      · rw [indicator_of_mem hzN]
      · rw [indicator_of_notMem hzN]
        exact ω.floerOperator_preglue_eq_zero J H x R (fun h ↦ hzN ⟨h, hz.2⟩) hz.2 huF hvF
  rw [eLpNorm_congr_ae hFN, eLpNorm_indicator_eq_eLpNorm_restrict hN.nullMeasurableSet,
    Measure.restrict_restrict hN, inter_eq_left.2 hNS]
  refine (eLpNorm_le_of_ae_bound hF.aestronglyMeasurable
    (ae_restrict_of_forall_mem hN fun z hz ↦ hR z (hNS hz))).trans_eq ?_
  rw [Measure.restrict_apply_univ, hvolN, ← ENNReal.ofReal_ofNat 2,
    ENNReal.ofReal_rpow_of_nonneg zero_le_two (inv_nonneg.2 ENNReal.toReal_nonneg),
    ← ENNReal.ofReal_mul hc, mul_assoc]

end TauCeti.SymplecticForm
