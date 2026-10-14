/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.VariableCoefficient
public import TauCeti.Analysis.Sobolev.Wkp.Leibniz
public import TauCeti.Analysis.Sobolev.Wkp.MeyersSerrin
public import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The localized Calderón–Zygmund estimate on a domain

Let `n ≥ 3`, `1 < p < ∞`, and let `Ω ⊆ ℝⁿ` be open. This file localizes the whole-space
`W^{2,p}` estimate for coefficients of small oscillation
(`TauCeti.PDE.exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq_of_abs_sub_le`) to a
strong solution on `Ω`, by a smooth cutoff
(`TauCeti.PDE.exists_lpNorm_smul_iteratedGradient_le_of_sum_mul_inner_eq_of_abs_sub_le`).

There are `C` and `δ > 0`, depending only on `n` and `p`, with the following property. Let `A` be
a matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `0 < λ`, let `ζ` be smooth with compact support in `Ω`, with
`‖∇ζ‖ ≤ M₁` and `‖D²ζ‖ ≤ M₂`, and let `a` be a measurable matrix-valued coefficient with
`|aᵢⱼ - Aᵢⱼ| ≤ ε ≤ δ λ` and `|aᵢⱼ| ≤ Λ` almost everywhere on the support of `ζ`. Then every
`u ∈ W^{2,p}(Ω)` with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f ∈ Lᵖ(Ω)` almost everywhere on `Ω` satisfies

`‖ζ D²u‖_{Lᵖ(Ω)} ≤ (C / λ) ‖ζ f‖_{Lᵖ(Ω)} + (C n² Λ / λ + 1) (2 M₁ ‖∇u‖_{Lᵖ(Ω)} + M₂ ‖u‖_{Lᵖ(Ω)})`.

No boundary condition is imposed on `u` and no regularity of `Ω` is used: the estimate is
interior. The lower-order terms on the right are the price of localization. In the interior
`W^{2,p}` estimate for continuous coefficients, where `ζ` runs over cutoffs of balls small enough
that the oscillation of `a` is below `δ λ`, the gradient term is absorbed by an interpolation
inequality for `‖∇u‖`.

## The argument

The cutoff `ζ u` lies in `W^{2,p}_0(Ω)` (`TauCeti.Wkp.exists_mem_wkp0Submodule_value_ae_eq_mul`),
and its extension by zero lies in `W^{2,p}(ℝⁿ)` and vanishes off the support of `ζ`. By the
Leibniz rule for the weak Hessian (`TauCeti.Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul`),
`D²(ζ u) = ζ D²u + T` with `T = ∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ`, so

`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ(ζ u) = ζ f + ∑ᵢⱼ aᵢⱼ Tᵢⱼ`.

The whole-space estimate bounds `‖D²(ζ u)‖` by `(C / λ)` times the `Lᵖ` norm of the right side,
the coefficient bound gives `|∑ᵢⱼ aᵢⱼ Tᵢⱼ| ≤ n² Λ ‖T‖`, and `‖T‖ ≤ 2 M₁ ‖∇u‖ + M₂ |u|`
pointwise. Finally `ζ D²u = D²(ζ u) - T`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  proof of Theorem 9.11.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Gradient ContDiff

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The localized Calderón–Zygmund estimate for coefficients of small oscillation.**
Let `n ≥ 3` and `1 < p < ∞`. There are constants `C` and `δ > 0`, depending only on `n` and `p`,
with the following property. Let `A` be a matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `0 < λ`, let `Ω` be
open, and let `ζ` be smooth with compact support in `Ω`, `‖∇ζ‖ ≤ M₁` and `‖D²ζ‖ ≤ M₂`. Let `a` be
a measurable matrix-valued coefficient on `Ω` with `|aᵢⱼ(x) - Aᵢⱼ| ≤ ε` and `|aᵢⱼ(x)| ≤ Λ` for
almost every `x` in the support of `ζ`, where `ε ≤ δ λ` and `0 ≤ Λ`. Then every
`u ∈ W^{2,p}(Ω)` with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on `Ω`, with `f ∈ Lᵖ(Ω)`, satisfies

`‖ζ D²u‖_{Lᵖ(Ω)} ≤ (C / λ) ‖ζ f‖_{Lᵖ(Ω)} + (C n² Λ / λ + 1) (2 M₁ ‖∇u‖_{Lᵖ(Ω)} + M₂ ‖u‖_{Lᵖ(Ω)})`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u` and `∇u` is the weak gradient
`TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)`. No boundary condition on `u` and
no regularity of `Ω` is assumed. -/
theorem exists_lpNorm_smul_iteratedGradient_le_of_sum_mul_inner_eq_of_abs_sub_le (hn : 3 ≤ n)
    (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ {A : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ}, 0 < lam →
      (∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      ∀ {Omega : Opens (EuclideanSpace ℝ (Fin n))} {zeta : EuclideanSpace ℝ (Fin n) → ℝ}
        {M₁ M₂ : ℝ}, ContDiff ℝ ∞ zeta → HasCompactSupport zeta →
        tsupport zeta ⊆ Omega → (∀ x, ‖∇ zeta x‖ ≤ M₁) →
        (∀ x, ‖fderiv ℝ (∇ zeta) x‖ ≤ M₂) →
      ∀ {a : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {ε Λ : ℝ},
        AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))) →
        ε ≤ δ * lam → (∀ᵐ x, x ∈ tsupport zeta → ∀ i j, |a x i j - A i j| ≤ ε) → 0 ≤ Λ →
        (∀ᵐ x, x ∈ tsupport zeta → ∀ i j, |a x i j| ≤ Λ) →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Omega)),
        (∀ᵐ x ∂(volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))),
          ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
            EuclideanSpace.single j 1⟫_ℝ = f x) →
        lpNorm (fun x => zeta x • Wkp.iteratedGradient 1 u x) p (volume.restrict Omega) ≤
          C / lam * lpNorm (fun x => zeta x * f x) p (volume.restrict Omega) +
            (C / lam * n ^ 2 * Λ + 1) *
              (2 * M₁ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ + M₂ * ‖Wkp.value 2 u‖) := by
  obtain ⟨C, δ, hδ, hCZ⟩ :=
    exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq_of_abs_sub_le hn hp hp_top
  refine ⟨C, δ, hδ, fun {A lam} hlam hA {Omega zeta M₁ M₂} hζ hcpt hts hM₁ hM₂
    {a ε Λ} ha_meas hε ha hΛ haΛ u f hf => ?_⟩
  have hΩ : MeasurableSet (Omega : Set (EuclideanSpace ℝ (Fin n))) := Omega.isOpen.measurableSet
  have htop : ae ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)))) = ae volume := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  -- The Leibniz remainder `T = ∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ`, which vanishes off the support of `ζ`.
  set T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun x => (innerSL ℝ (∇ zeta x)).smulRight (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x)
      + (innerSL ℝ (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x)).smulRight (∇ zeta x)
      + Wkp.value 2 u x • fderiv ℝ (∇ zeta) x with hT
  have hTx : ∀ x, ‖T x‖ ≤ 2 * ‖∇ zeta x‖ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x‖
      + ‖fderiv ℝ (∇ zeta) x‖ * ‖Wkp.value 2 u x‖ := fun x => by
    refine norm_add₃_le.trans (le_of_eq ?_)
    rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_smulRight_apply,
      innerSL_apply_norm, innerSL_apply_norm, norm_smul]
    ring
  have hT0 : ∀ x, x ∉ tsupport zeta → T x = 0 := by
    intro x hx
    have hs0 := tsupport_iteratedGradientChain_subset zeta 0
    have hs1 := tsupport_iteratedGradientChain_subset zeta 1
    rw [iteratedGradientChain_zero] at hs0
    rw [iteratedGradientChain_succ, iteratedGradientChain_zero] at hs1
    have h1 : ∇ zeta x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs0 h)
    have h2 : fderiv ℝ (∇ zeta) x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs1 h)
    exact norm_le_zero_iff.1 ((hTx x).trans (by simp [h1, h2]))
  -- The cutoff `w = ζ u ∈ W^{2,p}_0(Ω)` and its weak Hessian `ζ D²u + T`.
  obtain ⟨w, hw0, hwv⟩ := Wkp.exists_mem_wkp0Submodule_value_ae_eq_mul hp_top hζ hcpt hts 2 u
  have hD := Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul hζ hwv
  obtain ⟨M₀, hM₀⟩ := hζ.continuous.bounded_above_of_compact_support hcpt
  have hζH : MemLp (fun x => zeta x • Wkp.iteratedGradient 1 u x) p (volume.restrict Omega) :=
    (Lp.memLp _).of_le_mul (c := M₀)
      (hζ.continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable _))
      (ae_of_all _ fun x => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hM₀ x) (norm_nonneg _))
  set TL := Wkp.iteratedGradient 1 w - hζH.toLp _ with hTL_def
  have hTL : ∀ᵐ x ∂volume.restrict Omega, TL x = T x := by
    filter_upwards [Lp.coeFn_sub (Wkp.iteratedGradient 1 w) (hζH.toLp _), hD,
      hζH.coeFn_toLp] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, hT]
    simp only [add_assoc, add_sub_cancel_left]
  have hTnorm : ‖TL‖ ≤ 2 * M₁ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖
      + M₂ * ‖Wkp.value 2 u‖ := by
    refine TauCeti.Lp.norm_le_add_of_ae_norm_le (by positivity) hM₂0 ?_
    filter_upwards [hTL] with x hx
    rw [hx]
    refine (hTx x).trans ?_
    gcongr
    · exact hM₁ x
    · exact hM₂ x
  -- The forcing term `ζ f + ∑ᵢⱼ aᵢⱼ Tᵢⱼ` of the equation for `ζ u`.
  have hEmeas : AEStronglyMeasurable (fun x => Matrix.contraction (a x) (T x))
      (volume.restrict Omega) := by
    have hTm : AEStronglyMeasurable T (volume.restrict Omega) :=
      (Lp.aestronglyMeasurable TL).congr hTL
    simp only [Matrix.contraction_apply]
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    exact ((continuous_id.matrix_elem i j).comp_aestronglyMeasurable ha_meas).mul
      (((ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single i 1)).continuous
        |>.comp_aestronglyMeasurable hTm).inner aestronglyMeasurable_const)
  have hEle : ∀ᵐ x ∂volume.restrict Omega,
      ‖Matrix.contraction (a x) (T x)‖ ≤ n ^ 2 * Λ * ‖TL x‖ := by
    filter_upwards [hTL, ae_restrict_of_ae haΛ] with x h1 h2
    rw [h1, Real.norm_eq_abs]
    by_cases hx : x ∈ tsupport zeta
    · exact Matrix.abs_contraction_le (h2 hx) _
    · simp [hT0 x hx]
  have hE : MemLp (fun x => Matrix.contraction (a x) (T x)) p (volume.restrict Omega) :=
    (Lp.memLp TL).of_le_mul hEmeas hEle
  have hζf : MemLp (fun x => zeta x * f x) p (volume.restrict Omega) :=
    (Lp.memLp f).of_le_mul (c := M₀)
      (hζ.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
      (ae_of_all _ fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM₀ x) (norm_nonneg _))
  set FL := hζf.toLp _ + hE.toLp _ with hFL_def
  have hFLnorm : ‖FL‖ ≤ lpNorm (fun x => zeta x * f x) p (volume.restrict Omega)
      + n ^ 2 * Λ * ‖TL‖ := by
    refine (norm_add_le _ _).trans (add_le_add (Lp.norm_toLp _ _).le ?_)
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [hE.coeFn_toLp, hEle] with x h1 h2
    rwa [h1]
  -- Extend `ζ u` and its forcing term by zero to all of `ℝⁿ`.
  have hsub : Omega ≤ ⊤ := le_top
  have hsub' : (Omega : Set (EuclideanSpace ℝ (Fin n))) ⊆
      ((⊤ : Opens (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))) :=
    SetLike.coe_subset_coe.mpr hsub
  set W : Wkp0 volume ⊤ p 2 := Wkp0.extendByZeroₗᵢ hsub 2 ⟨w, hw0⟩
  set F := extendByZeroLpₗᵢ ℝ volume hΩ hsub' FL
  have hWD : Wkp.iteratedGradient 1 (W : Wkp volume ⊤ p 2) =
      extendByZeroLpₗᵢ ℝ volume hΩ hsub' (Wkp.iteratedGradient 1 w) :=
    Wkp0.iteratedGradient_extendByZeroₗᵢ hsub 1 ⟨w, hw0⟩
  have hWv : Wkp.value 2 (W : Wkp volume ⊤ p 2) =
      extendByZeroLpₗᵢ ℝ volume hΩ hsub' (Wkp.value 2 w) :=
    Wkp0.value_extendByZeroₗᵢ hsub 2 ⟨w, hw0⟩
  have hWzero : ∀ᵐ x, x ∉ tsupport zeta → Wkp.value 2 (W : Wkp volume ⊤ p 2) x = 0 := by
    have h1 := coeFn_extendByZeroLpₗᵢ ℝ hΩ hsub' (Wkp.value 2 w)
    rw [← hWv] at h1
    rw [Filter.EventuallyEq, htop] at h1
    filter_upwards [h1, (ae_restrict_iff' hΩ).1 hwv] with x hx hx' hxs
    rw [hx]
    by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ (Fin n)))
    · rw [Set.indicator_of_mem hxΩ, hx' hxΩ, image_eq_zero_of_notMem_tsupport hxs, zero_mul]
    · exact Set.indicator_of_notMem hxΩ _
  have hf' : ∀ᵐ x ∂volume.restrict Omega,
      Matrix.contraction (a x) (Wkp.iteratedGradient 1 u x) = f x := by
    filter_upwards [hf] with x hx
    rw [Matrix.contraction_apply]
    -- `hx` applies the Hessian through the instances of `IteratedGradient`, which unfold to those
    -- of `ContinuousLinearMap` used by `Matrix.contraction_apply`.
    exact hx
  have hWeq : ∀ᵐ x, Matrix.contraction (a x) (Wkp.iteratedGradient 1 (W : Wkp volume ⊤ p 2) x)
      = F x := by
    have h1 := coeFn_extendByZeroLpₗᵢ ℝ hΩ hsub' (Wkp.iteratedGradient 1 w)
    have h2 := coeFn_extendByZeroLpₗᵢ ℝ hΩ hsub' FL
    rw [← hWD] at h1
    rw [Filter.EventuallyEq, htop] at h1 h2
    have h3 : ∀ᵐ x ∂volume.restrict Omega,
        FL x = zeta x * f x + Matrix.contraction (a x) (T x) := by
      filter_upwards [Lp.coeFn_add (hζf.toLp _) (hE.toLp _), hζf.coeFn_toLp, hE.coeFn_toLp]
        with x h h' h''
      rw [h, Pi.add_apply, h', h'']
    filter_upwards [h1, h2, (ae_restrict_iff' hΩ).1 hD, (ae_restrict_iff' hΩ).1 hf',
      (ae_restrict_iff' hΩ).1 h3] with x hx1 hx2 hxD hxf hx3
    rw [hx1, hx2]
    by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ (Fin n)))
    · rw [Set.indicator_of_mem hxΩ, Set.indicator_of_mem hxΩ, hxD hxΩ, hx3 hxΩ, ← hxf hxΩ]
      have hTx : zeta x • Wkp.iteratedGradient 1 u x
          + (innerSL ℝ (∇ zeta x)).smulRight (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x)
          + (innerSL ℝ (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x)).smulRight (∇ zeta x)
          + Wkp.value 2 u x • fderiv ℝ (∇ zeta) x = zeta x • Wkp.iteratedGradient 1 u x + T x := by
        simp only [hT, add_assoc]
      rw [hTx, map_add, map_smul, smul_eq_mul]
    · rw [Set.indicator_of_notMem hxΩ, Set.indicator_of_notMem hxΩ, map_zero]
  -- The whole-space estimate, and `ζ D²u = D²(ζ u) - T`.
  have hkey := hCZ hlam hA (isClosed_tsupport zeta) hε ha (W : Wkp volume ⊤ p 2) F hWzero
    (by
      -- As for `hf'`, the two sides differ only by unfolding the instances of `IteratedGradient`.
      filter_upwards [hWeq] with x hx
      rw [← Matrix.contraction_apply]
      exact hx)
  rw [hWD, LinearIsometry.norm_map, LinearIsometry.norm_map] at hkey
  have hHL : hζH.toLp _ = Wkp.iteratedGradient 1 w - TL := by
    rw [hTL_def, sub_sub_cancel]
  have hCl : 0 ≤ (C : ℝ) / lam := by positivity
  rw [← toReal_eLpNorm, ← Lp.norm_toLp _ hζH, hHL]
  calc ‖Wkp.iteratedGradient 1 w - TL‖
      ≤ ‖Wkp.iteratedGradient 1 w‖ + ‖TL‖ := norm_sub_le _ _
    _ ≤ C / lam * (lpNorm (fun x => zeta x * f x) p (volume.restrict Omega)
          + n ^ 2 * Λ * ‖TL‖) + ‖TL‖ := by
        gcongr
        exact hkey.trans (by gcongr)
    _ = C / lam * lpNorm (fun x => zeta x * f x) p (volume.restrict Omega)
          + (C / lam * n ^ 2 * Λ + 1) * ‖TL‖ := by ring
    _ ≤ _ := by gcongr

end PDE

end TauCeti
