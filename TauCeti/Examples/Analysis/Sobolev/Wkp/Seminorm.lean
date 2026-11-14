/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import TauCeti.Analysis.Sobolev.Wkp.Seminorm
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Concrete evaluations of Sobolev order truncations and seminorms

This file exercises the unexposed public interface of `TauCeti.Analysis.Sobolev.Wkp.Seminorm` on
explicit one-dimensional functions:

* On `(0, 1)` at exponent `p = 2` and order `k = 1`, `u(x) = x` satisfies `toOrderL le_rfl u = u`
  with `u ≠ 0`, `|u|_{0,2} = 1 / √3`, `|u|_{1,2} = 1`, and graph norm `‖u‖ = 2 / √3`.
* On `(0, 1)` at exponent `p = 2` and order `k = 2`, `u(x) = x²` has seminorms
  `|u|_{0,2} = 1 / √5`, `|u|_{1,2} = 2 / √3`, and `|u|_{2,2} = 2`, and truncating to order `1`
  preserves `|·|_{1,2}`.
* On `(0, 2π)` at exponent `p = ∞` and order `k = 1`, `u(x) = sin x` has `|u|_{0,∞} = 1`,
  `|u|_{1,∞} = 1`, and `√(|u|_{0,∞}² + |u|_{1,∞}²) = √2`, whereas its `W^{1,∞}` graph norm is `1`
  because `sin² + cos² = 1` pointwise. This shows both that the `√2` constant in
  `TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm` is sharp and that `‖u‖` does not equal
  `√(∑_{j ≤ k} |u|_{j,p}²)` for general `p`.
* On `(0, 2)`, the constant function `1` in `W^{1,2}(0, 2)` has `|1|_{0,2} = √2`, its image in
  `W^{1,1}(0, 2)` under `TauCeti.Wkp.ofExponentLEL` has `|1|_{0,1} = 2`, and the Hölder bound
  `TauCeti.Wkp.seminorm_ofExponentLEL_le` holds with equality (`2 = √2 · √2`), while at equal
  exponents `ofExponentLEL le_rfl` preserves `1 ≠ 0`.
* On `ℝ` (`⊤ : Opens ℝ`), `x ↦ (1 + |x|)⁻¹` defines an element of `W^{0,2}(ℝ)` whose value does not
  represent any element of `W^{0,1}(ℝ)`, showing that the finite-measure hypothesis in
  `TauCeti.Wkp.ofExponentLEL` and `TauCeti.Wkp.seminorm_ofExponentLEL_le` is necessary.
-/

public section

noncomputable section

namespace TauCeti.Examples.Sobolev

open MeasureTheory TopologicalSpace TauCeti TauCeti.Wkp
open scoped ENNReal ContDiff

/-- The open interval `(a, b) ⊆ ℝ` as an element of `Opens ℝ`. -/
abbrev openInterval (a b : ℝ) : Opens ℝ :=
  ⟨Set.Ioo a b, isOpen_Ioo⟩

/-- Coercing `openInterval a b` to a set gives `Set.Ioo a b`. -/
@[simp]
theorem coe_openInterval (a b : ℝ) : ((openInterval a b : Opens ℝ) : Set ℝ) = Set.Ioo a b :=
  rfl

/-- Evaluate `seminorm k j hj u` at `p = 2` on `(a, b)` for a `C^j` representative `f` whose `j`th
scalar iterated derivative agrees on `(a, b)` with a continuous function `g`. -/
private theorem seminorm_two_eq_sqrt_intervalIntegral {a b : ℝ} (hab : a ≤ b) {j k : ℕ}
    (hj : j ≤ k) (u : Wkp volume (openInterval a b) 2 k) {f g : ℝ → ℝ} (hf : ContDiff ℝ j f)
    (hu : (value k u : ℝ → ℝ) =ᵐ[volume.restrict (openInterval a b)] f) (hg_cont : Continuous g)
    (hg : ∀ x ∈ Set.Ioo a b, |iteratedDeriv j f x| = |g x|) :
    seminorm k j hj u = √(∫ x in a..b, g x ^ 2) := by
  rw [seminorm_eq_lpNorm_iteratedFDeriv_of_contDiffOn hj u hf.contDiffOn hu]
  have hmem : MemLp g 2 (volume.restrict (Set.Ioo a b)) :=
    hg_cont.continuousOn.memLp_restrict_of_subset_isCompact isCompact_Icc isOpen_Ioo.measurableSet
      Set.Ioo_subset_Icc_self 2
  have hlp : lpNorm (iteratedFDeriv ℝ j f) 2 (volume.restrict (openInterval a b)) =
      ‖hmem.toLp g‖ := by
    rw [Lp.norm_toLp, lpNorm]
    congr 1
    have hcont :=
      ContinuousOn.continuousOn_iteratedFDeriv hf.contDiffOn (isOpen_Ioo (a := a) (b := b)) le_rfl
    refine eLpNorm_congr_norm_ae (hcont.aestronglyMeasurable isOpen_Ioo.measurableSet)
      hmem.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem isOpen_Ioo.measurableSet] with x hx
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, Real.norm_eq_abs]
    exact hg x hx
  rw [hlp, ← Real.sqrt_sq (norm_nonneg (hmem.toLp g)), hmem.norm_toLp_sq]
  congr 1
  rw [intervalIntegral.integral_of_le hab, ← setIntegral_congr_set Ioo_ae_eq_Ioc]
  exact setIntegral_congr_fun isOpen_Ioo.measurableSet fun x _ => by simp [Real.norm_eq_abs, sq_abs]

/-! ### `u(x) = x` in `W^{1,2}(0, 1)` -/

/-- On `(0, 1)`, `x ↦ x` defines a nonzero class `u ∈ W^{1,2}(0, 1)` with `toOrderL le_rfl u = u`,
`|u|_{0,2} = 1 / √3`, `|u|_{1,2} = 1`, and graph norm `‖u‖ = 2 / √3`. -/
theorem exists_linear_unitInterval_seminorms :
    ∃ u : Wkp volume (openInterval 0 1) 2 1,
      (value 1 u : ℝ → ℝ) =ᵐ[volume.restrict (openInterval 0 1)] id ∧
      toOrderL (le_rfl : 1 ≤ 1) u = u ∧
      u ≠ 0 ∧
      seminorm 1 0 (Nat.zero_le 1) u = 1 / √3 ∧
      seminorm 1 1 le_rfl u = 1 ∧
      ‖u‖ = 2 / √3 := by
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := openInterval 0 1) (p := 2) 1 isOpen_univ contDiff_id.contDiffOn
    isCompact_Icc Set.Ioo_subset_Icc_self (Set.subset_univ _)
  have hs0 : seminorm 1 0 (Nat.zero_le 1) u = 1 / √3 := by
    rw [seminorm_two_eq_sqrt_intervalIntegral zero_le_one (Nat.zero_le 1) u contDiff_id hu
      continuous_id (g := fun x => x) fun x _ => by simp]
    rw [integral_pow, Real.sqrt_div (by norm_num)]
    norm_num
  have hs1 : seminorm 1 1 le_rfl u = 1 := by
    rw [seminorm_two_eq_sqrt_intervalIntegral zero_le_one le_rfl u contDiff_id hu
      continuous_const (g := fun _ => 1) fun x _ => by simp [iteratedDeriv_one]]
    simp
  have hnorm : ‖u‖ = 2 / √3 := by
    have hsum : (∑ j : Fin 2, seminorm 1 j j.is_le u ^ 2) =
        seminorm 1 0 (Nat.zero_le 1) u ^ 2 + seminorm 1 1 le_rfl u ^ 2 :=
      Fin.sum_univ_two _
    rw [norm_eq_sqrt_sum_seminorm_sq u, hsum, hs0, hs1]
    have hsq : (1 / √3) ^ 2 + 1 ^ 2 = (2 : ℝ) ^ 2 / 3 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    rw [hsq, Real.sqrt_div (by norm_num), Real.sqrt_sq (by norm_num)]
  refine ⟨u, hu, by simp, ?_, hs0, hs1, hnorm⟩
  intro hu0
  rw [hu0, map_zero] at hs1
  norm_num at hs1

/-! ### `u(x) = x²` in `W^{2,2}(0, 1)` -/

/-- On `(0, 1)`, `x ↦ x²` defines `u ∈ W^{2,2}(0, 1)` with seminorms `1 / √5`, `2 / √3`, and `2`,
and order truncation to `W^{1,2}(0, 1)` preserves the first-order seminorm `2 / √3`. -/
theorem exists_sq_unitInterval_seminorms :
    ∃ u : Wkp volume (openInterval 0 1) 2 2,
      (value 2 u : ℝ → ℝ) =ᵐ[volume.restrict (openInterval 0 1)] (fun x => x ^ 2) ∧
      seminorm 2 0 (Nat.zero_le 2) u = 1 / √5 ∧
      seminorm 2 1 (by decide) u = 2 / √3 ∧
      seminorm 2 2 le_rfl u = 2 ∧
      seminorm 1 1 le_rfl (toOrderL (by decide : 1 ≤ 2) u) = 2 / √3 := by
  have hcd : ∀ {j : ℕ}, ContDiff ℝ j (fun x : ℝ => x ^ 2) := fun {j} => contDiff_id.pow 2
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := openInterval 0 1) (p := 2) 2 isOpen_univ hcd.contDiffOn
    isCompact_Icc Set.Ioo_subset_Icc_self (Set.subset_univ _)
  have hs0 : seminorm 2 0 (Nat.zero_le 2) u = 1 / √5 := by
    rw [seminorm_two_eq_sqrt_intervalIntegral zero_le_one (Nat.zero_le 2) u hcd hu
      (continuous_pow 2) fun x _ => by simp]
    have hint : (∫ x in (0 : ℝ)..1, (x ^ 2) ^ 2) = 1 / 5 := by
      have hpow : (fun x : ℝ => (x ^ 2) ^ 2) = fun x : ℝ => x ^ 4 := by ext x; ring
      rw [hpow, integral_pow]
      norm_num
    rw [hint, Real.sqrt_div (by norm_num)]
    norm_num
  have hs1 : seminorm 2 1 (by decide) u = 2 / √3 := by
    rw [seminorm_two_eq_sqrt_intervalIntegral zero_le_one (by decide) u hcd hu
      (continuous_const.mul continuous_id) (g := fun x => 2 * x) fun x _ => by
        rw [iteratedDeriv_one]
        have hd : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
        rw [hd.deriv]]
    have hint : (∫ x in (0 : ℝ)..1, (2 * x) ^ 2) = (2 : ℝ) ^ 2 / 3 := by
      have hpow : (fun x : ℝ => (2 * x) ^ 2) = fun x : ℝ => 4 * x ^ 2 := by ext x; ring
      rw [hpow, intervalIntegral.integral_const_mul, integral_pow]
      norm_num
    rw [hint, Real.sqrt_div (by norm_num), Real.sqrt_sq (by norm_num)]
  have hs2 : seminorm 2 2 le_rfl u = 2 := by
    rw [seminorm_two_eq_sqrt_intervalIntegral zero_le_one le_rfl u hcd hu
      continuous_const (g := fun _ => 2) fun x _ => by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
        have hd1 : deriv (fun t : ℝ => t ^ 2) = fun t : ℝ => 2 * t := by
          ext t
          exact (by simpa using hasDerivAt_pow 2 t : HasDerivAt _ (2 * t) t).deriv
        rw [hd1]
        have hd2 : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
          simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
        rw [hd2.deriv]]
    have hint : (∫ _ in (0 : ℝ)..1, (2 : ℝ) ^ 2) = 2 ^ 2 := by simp
    rw [hint, Real.sqrt_sq (by norm_num)]
  refine ⟨u, hu, hs0, hs1, hs2, ?_⟩
  rw [seminorm_toOrderL, hs1]

/-! ### Sharpness of `√2` on `(0, 2π)` at `p = ∞`: `u(x) = sin x` -/

/-- If an `L^∞` class `v` on an open set `Ω ⊆ ℝ` agrees almost everywhere with a continuous
function `g` bounded by `C` on `Ω` that attains `|g x₀| = C` at `x₀ ∈ Ω`, then `‖v‖ = C`. -/
private theorem norm_top_eq_of_ae_eq_continuous {F : Type*} [NormedAddCommGroup F] {Ω : Opens ℝ}
    (v : Lp F ∞ (volume.restrict Ω)) {g : ℝ → F} {C x₀ : ℝ} (hC : 0 ≤ C) (hg_cont : Continuous g)
    (hv : (v : ℝ → F) =ᵐ[volume.restrict Ω] g) (hle : ∀ x ∈ Ω, ‖g x‖ ≤ C)
    (hx₀ : x₀ ∈ Ω) (hmax : ‖g x₀‖ = C) :
    ‖v‖ = C := by
  refine le_antisymm (Lp.norm_top_le_of_ae_bound hC ?_) ?_
  · filter_upwards [hv, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    exact hx.symm ▸ hle x hxΩ
  · by_contra! hlt
    have hopen : IsOpen ((Ω : Set ℝ) ∩ {x : ℝ | ‖v‖ < ‖g x‖}) :=
      Ω.isOpen.inter (isOpen_lt continuous_const hg_cont.norm)
    have hpos : 0 < (volume.restrict (Ω : Set ℝ)) {x : ℝ | ‖v‖ < ‖g x‖} := by
      rw [Measure.restrict_apply' Ω.isOpen.measurableSet, Set.inter_comm]
      exact hopen.measure_pos volume ⟨x₀, hx₀, hlt.trans_eq hmax.symm⟩
    have hae : ∀ᵐ x ∂volume.restrict (Ω : Set ℝ), ‖g x‖ ≤ ‖v‖ := by
      filter_upwards [hv, Lp.ae_norm_le_norm_top v] with x hx hnx
      exact hx ▸ hnx
    exact hpos.ne' (measure_mono_null (fun _ hx => not_le_of_gt hx) (ae_iff.mp hae))

/-- On `(0, 2π)` at `p = ∞`, `sin` has `|u|_{0,∞} = 1`, `|u|_{1,∞} = 1`, and
`√(|u|_{0,∞}² + |u|_{1,∞}²) = √2`, while its `W^{1,∞}` graph norm is `1`, attaining equality in
`TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm`. -/
theorem exists_sin_twoPi_seminorms_top :
    ∃ u : Wkp volume (openInterval 0 (2 * Real.pi)) ∞ 1,
      (value 1 u : ℝ → ℝ) =ᵐ[volume.restrict (openInterval 0 (2 * Real.pi))] Real.sin ∧
      seminorm 1 0 (Nat.zero_le 1) u = 1 ∧
      seminorm 1 1 le_rfl u = 1 ∧
      ‖u‖ = 1 ∧
      √(∑ j : Fin 2, seminorm 1 j j.is_le u ^ 2) = √2 * ‖u‖ ∧
      ‖u‖ ≠ √(∑ j : Fin 2, seminorm 1 j j.is_le u ^ 2) := by
  set Ω := openInterval 0 (2 * Real.pi)
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := Ω) (p := ∞) 1 isOpen_univ Real.contDiff_sin.contDiffOn
    isCompact_Icc Set.Ioo_subset_Icc_self (Set.subset_univ _)
  have hgrad : (iteratedGradient 0 u : ℝ → ℝ) =ᵐ[volume.restrict Ω] Real.cos := by
    filter_upwards [iteratedGradient_ae_eq_of_contDiffOn 0 u Real.contDiff_sin.contDiffOn hu]
      with x hx
    rw [hx, iteratedGradientChain_zero]
    apply (InnerProductSpace.toDual ℝ ℝ).injective
    ext
    simp [gradient, Real.hasDerivAt_sin x |>.hasFDerivAt.fderiv]
  have hs0 : seminorm 1 0 (Nat.zero_le 1) u = 1 := by
    rw [seminorm_zero]
    exact norm_top_eq_of_ae_eq_continuous (value 1 u) zero_le_one Real.continuous_sin hu
      (fun x _ => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one x)
      (x₀ := Real.pi / 2) ⟨by positivity, by linarith [Real.pi_pos]⟩ (by simp [Real.sin_pi_div_two])
  have hs1 : seminorm 1 1 le_rfl u = 1 := by
    rw [seminorm_succ_self]
    exact norm_top_eq_of_ae_eq_continuous (iteratedGradient 0 u) zero_le_one Real.continuous_cos
      hgrad (fun x _ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one x)
      (x₀ := Real.pi) ⟨Real.pi_pos, by linarith [Real.pi_pos]⟩ (by simp [Real.cos_pi])
  have hnorm : ‖u‖ = 1 := by
    let w : W1p volume Ω ∞ := u
    have hjet : ∀ᵐ x ∂volume.restrict (Ω : Set ℝ), ‖(w : Sobolev1JetLp volume Ω ∞) x‖ = 1 := by
      have hwv : (W1p.value w : ℝ → ℝ) =ᵐ[volume.restrict Ω] Real.sin := by
        rwa [← value_one u]
      have hwg : (W1p.gradient w : ℝ → ℝ) =ᵐ[volume.restrict Ω] Real.cos := by
        rwa [← iteratedGradient_zero u]
      filter_upwards [W1p.norm_apply_sq_ae w, hwv, hwg] with x hsq hv hg
      have hsq1 : ‖(w : Sobolev1JetLp volume Ω ∞) x‖ ^ 2 = 1 ^ 2 := by
        rw [hsq, hv, hg, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, Real.sin_sq_add_cos_sq]
        norm_num
      exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hsq1
    have hle : ‖w‖ ≤ 1 := Lp.norm_top_le_of_ae_bound (f := (w : Sobolev1JetLp volume Ω ∞))
      zero_le_one (hjet.mono fun x hx => hx.le)
    have hne : (ae (volume.restrict (Ω : Set ℝ))).NeBot :=
      ae_neBot.mpr (Measure.restrict_eq_zero.not.mpr
        (isOpen_Ioo.measure_pos volume ⟨Real.pi, Real.pi_pos, by linarith [Real.pi_pos]⟩).ne')
    obtain ⟨x, hx1, hxn⟩ :=
      (hjet.and (Lp.ae_norm_le_norm_top (w : Sobolev1JetLp volume Ω ∞))).exists
    exact le_antisymm hle (hx1 ▸ hxn)
  have hS : √(∑ j : Fin 2, seminorm 1 j j.is_le u ^ 2) = √2 := by
    have hsum : (∑ j : Fin 2, seminorm 1 j j.is_le u ^ 2) =
        seminorm 1 0 (Nat.zero_le 1) u ^ 2 + seminorm 1 1 le_rfl u ^ 2 :=
      Fin.sum_univ_two _
    rw [hsum, hs0, hs1]
    norm_num
  refine ⟨u, hu, hs0, hs1, hnorm, by rw [hS, hnorm, mul_one], ?_⟩
  rw [hnorm, hS]
  intro h12
  have hsq := congrArg (· ^ 2) h12
  norm_num [Real.sq_sqrt] at hsq

/-! ### Exponent lowering on `(0, 2)`: `u(x) = 1` -/

/-- On `(0, 2)`, the constant `1` in `W^{1,2}(0, 2)` has `|1|_{0,2} = √2`, its image in
`W^{1,1}(0, 2)` has `|1|_{0,1} = 2`, the Hölder seminorm bound `2 ≤ √2 · √2` holds with equality,
and `ofExponentLEL le_rfl` preserves `1 ≠ 0`. -/
theorem exists_const_one_twoInterval_ofExponentLEL :
    have : IsFiniteMeasure (volume.restrict (openInterval 0 2 : Set ℝ)) :=
      ⟨by rw [Measure.restrict_apply_univ, coe_openInterval, Real.volume_Ioo]
          exact ENNReal.ofReal_lt_top⟩
    ∃ u : Wkp volume (openInterval 0 2) 2 1,
      (value 1 u : ℝ → ℝ) =ᵐ[volume.restrict (openInterval 0 2)] (fun _ => 1) ∧
      seminorm 1 0 (Nat.zero_le 1) u = √2 ∧
      seminorm 1 0 (Nat.zero_le 1) (ofExponentLEL (by norm_num : (1 : ℝ≥0∞) ≤ 2) 1 u) = 2 ∧
      seminorm 1 0 (Nat.zero_le 1) (ofExponentLEL (by norm_num : (1 : ℝ≥0∞) ≤ 2) 1 u) =
        (volume (openInterval 0 2 : Set ℝ) ^
          (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal *
          seminorm 1 0 (Nat.zero_le 1) u ∧
      ofExponentLEL le_rfl 1 u ≠ 0 := by
  have : IsFiniteMeasure (volume.restrict (openInterval 0 2 : Set ℝ)) :=
    ⟨by rw [Measure.restrict_apply_univ, coe_openInterval, Real.volume_Ioo]
        exact ENNReal.ofReal_lt_top⟩
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := openInterval 0 2) (p := 2) 1 isOpen_univ (contDiff_const (c := (1 : ℝ))).contDiffOn
    isCompact_Icc Set.Ioo_subset_Icc_self (Set.subset_univ _)
  have hs2 : seminorm 1 0 (Nat.zero_le 1) u = √2 := by
    rw [seminorm_two_eq_sqrt_intervalIntegral (by norm_num) (Nat.zero_le 1) u
      (contDiff_const (c := (1 : ℝ))) hu continuous_const (g := fun _ => 1) fun x _ => by simp]
    simp
  have hs1 : seminorm 1 0 (Nat.zero_le 1)
      (ofExponentLEL (by norm_num : (1 : ℝ≥0∞) ≤ 2) 1 u) = 2 := by
    rw [seminorm_zero, L1.norm_eq_integral_norm]
    have hae : (value 1 (ofExponentLEL (by norm_num : (1 : ℝ≥0∞) ≤ 2) 1 u) : ℝ → ℝ) =ᵐ[
        volume.restrict (openInterval 0 2)] fun _ => 1 :=
      (value_ofExponentLEL_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) 1 u).trans hu
    rw [integral_congr_ae (hae.mono fun x hx => by rw [hx, norm_one])]
    simp
  have hfac : (volume (openInterval 0 2 : Set ℝ) ^
      (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal = √2 := by
    have hexp : (1 : ℝ) / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal = 1 / 2 := by norm_num
    rw [coe_openInterval, Real.volume_Ioo, sub_zero, hexp,
      ENNReal.ofReal_rpow_of_nonneg zero_le_two (by norm_num),
      ENNReal.toReal_ofReal (by positivity), ← Real.sqrt_eq_rpow]
  refine ⟨u, hu, hs2, hs1, ?_, ?_⟩
  · rw [hs1, hfac, hs2, Real.mul_self_sqrt zero_le_two]
  · rw [ofExponentLEL_self]
    intro hu0
    rw [hu0, map_zero] at hs2
    exact (Real.sqrt_pos.mpr zero_lt_two).ne hs2

/-- On `ℝ`, `x ↦ (1 + |x|)⁻¹` represents a class in `W^{0,2}(ℝ)` whose value does not belong to
`W^{0,1}(ℝ)`, witnessing that `IsFiniteMeasure` cannot be dropped when lowering the Sobolev
exponent from `2` to `1`. -/
theorem exists_inv_one_add_abs_mem_Wkp_two_not_one :
    ∃ u : Wkp volume (⊤ : Opens ℝ) 2 0,
      (value 0 u : ℝ → ℝ) =ᵐ[volume.restrict (⊤ : Opens ℝ)] (fun x => (1 + |x|)⁻¹) ∧
      ¬ ∃ v : Wkp volume (⊤ : Opens ℝ) 1 0,
        (value 0 v : ℝ → ℝ) =ᵐ[volume.restrict (⊤ : Opens ℝ)] (value 0 u : ℝ → ℝ) := by
  have hf_cont : Continuous (fun x : ℝ => (1 + |x|)⁻¹) :=
    (continuous_const.add continuous_abs).inv₀ fun x =>
      (by linarith [abs_nonneg x] : 0 < 1 + |x|).ne'
  have hf_mem : MemLp (fun x : ℝ => (1 + |x|)⁻¹) 2 (volume.restrict (⊤ : Opens ℝ)) := by
    rw [Opens.coe_top, Measure.restrict_univ,
      memLp_two_iff_integrable_sq hf_cont.aestronglyMeasurable]
    refine integrable_inv_one_add_sq.mono' (hf_cont.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), inv_pow]
    exact inv_anti₀ (by positivity) (by nlinarith [abs_nonneg x, sq_abs x])
  refine ⟨hf_mem.toLp _, by rw [value_zero]; exact hf_mem.coeFn_toLp, ?_⟩
  rintro ⟨v, hv⟩
  have hf_int : Integrable (fun x : ℝ => (1 + |x|)⁻¹) volume := by
    have hv_int : Integrable (value 0 v) (volume.restrict (⊤ : Opens ℝ)) :=
      memLp_one_iff_integrable.mp (Lp.memLp (value 0 v))
    have hae : (value 0 v : ℝ → ℝ) =ᵐ[volume.restrict (⊤ : Opens ℝ)] fun x => (1 + |x|)⁻¹ :=
      hv.trans (by rw [value_zero]; exact hf_mem.coeFn_toLp)
    simpa only [Opens.coe_top, Measure.restrict_univ] using hv_int.congr hae
  have hhalf : IntegrableOn (fun x : ℝ => (1 / 2 : ℝ) * x⁻¹) (Set.Ioi 1) volume := by
    refine hf_int.integrableOn.mono'
      ((continuousOn_const.mul (continuousOn_id.inv₀ fun x hx =>
        (zero_lt_one.trans hx).ne')).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 1 < x)
    have hx0 : 0 < x := zero_lt_one.trans hx
    rw [Real.norm_of_nonneg (by positivity), one_div, ← mul_inv, abs_of_pos hx0]
    exact inv_anti₀ (by positivity) (by linarith)
  exact not_integrableOn_Ioi_inv (a := (1 : ℝ))
    (by simpa [IntegrableOn] using hhalf.const_mul (2 : ℝ))

end TauCeti.Examples.Sobolev
