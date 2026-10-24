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

Let `0 < n`, `1 < p < ∞`, and let `Ω ⊆ ℝⁿ` be open. This file localizes the whole-space
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

section LeibnizRemainder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Leibniz remainder `∇ζ ⊗ v + v ⊗ ∇ζ + s D²ζ` vanishes off the support of `ζ`. -/
private theorem leibnizRemainder_eq_zero {zeta : E → ℝ} {x : E} (hx : x ∉ tsupport zeta)
    (v : E) (s : ℝ) :
    (innerSL ℝ (∇ zeta x)).smulRight v + (innerSL ℝ v).smulRight (∇ zeta x)
      + s • fderiv ℝ (∇ zeta) x = 0 := by
  have hs0 := tsupport_iteratedGradientChain_subset zeta 0
  have hs1 := tsupport_iteratedGradientChain_subset zeta 1
  rw [iteratedGradientChain_zero] at hs0
  rw [iteratedGradientChain_succ, iteratedGradientChain_zero] at hs1
  have h1 : ∇ zeta x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs0 h)
  have h2 : fderiv ℝ (∇ zeta) x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs1 h)
  simp [h1, h2]

end LeibnizRemainder

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Extending `w ∈ W^{2,p}_0(Ω)` by zero to all of `ℝⁿ` preserves the vanishing of `w` off a set
`K`, and turns an equation `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼw = g` on `Ω` into the same equation on `ℝⁿ` with right
side `g` extended by zero. -/
private theorem ae_extendByZeroₗᵢ_of_ae {Omega : Opens (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))} {a : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    {w : Wkp0 (volume : Measure (EuclideanSpace ℝ (Fin n))) Omega p 2}
    {g : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Omega)}
    (hK : ∀ᵐ x ∂volume.restrict Omega, x ∉ K →
      Wkp.value 2 (w : Wkp volume Omega p 2) x = 0)
    (hg : ∀ᵐ x ∂volume.restrict Omega,
      Matrix.contraction (a x) (Wkp.iteratedGradient 1 (w : Wkp volume Omega p 2) x) = g x) :
    (∀ᵐ x, x ∉ K → Wkp.value 2 (Wkp0.extendByZeroₗᵢ le_top 2 w : Wkp volume ⊤ p 2) x = 0) ∧
      ∀ᵐ x, Matrix.contraction (a x)
          (Wkp.iteratedGradient 1 (Wkp0.extendByZeroₗᵢ le_top 2 w : Wkp volume ⊤ p 2) x) =
        extendByZeroLpₗᵢ ℝ volume Omega.isOpen.measurableSet
          (SetLike.coe_subset_coe.mpr le_top) g x := by
  have hΩ : MeasurableSet (Omega : Set (EuclideanSpace ℝ (Fin n))) := Omega.isOpen.measurableSet
  have htop : ae ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)))) = ae volume := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have hsub : (Omega : Set (EuclideanSpace ℝ (Fin n))) ⊆
      ((⊤ : Opens (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))) :=
    SetLike.coe_subset_coe.mpr le_top
  rw [Wkp0.value_extendByZeroₗᵢ, Wkp0.iteratedGradient_extendByZeroₗᵢ]
  constructor
  · have h1 := ae_extendByZeroLpₗᵢ_eq_of_mem ℝ hΩ hsub (Wkp.value 2 (w : Wkp volume Omega p 2))
    have h2 := ae_extendByZeroLpₗᵢ_eq_zero_of_notMem ℝ hΩ hsub
      (Wkp.value 2 (w : Wkp volume Omega p 2))
    rw [htop] at h1 h2
    filter_upwards [h1, h2, (ae_restrict_iff' hΩ).1 hK] with x h1 h2 hK hxK
    by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ (Fin n)))
    · rw [h1 hxΩ, hK hxΩ hxK]
    · exact h2 hxΩ
  · have h1 := ae_extendByZeroLpₗᵢ_eq_of_mem ℝ hΩ hsub
      (Wkp.iteratedGradient 1 (w : Wkp volume Omega p 2))
    have h2 := ae_extendByZeroLpₗᵢ_eq_zero_of_notMem ℝ hΩ hsub
      (Wkp.iteratedGradient 1 (w : Wkp volume Omega p 2))
    have h3 := ae_extendByZeroLpₗᵢ_eq_of_mem ℝ hΩ hsub g
    have h4 := ae_extendByZeroLpₗᵢ_eq_zero_of_notMem ℝ hΩ hsub g
    rw [htop] at h1 h2 h3 h4
    filter_upwards [h1, h2, h3, h4, (ae_restrict_iff' hΩ).1 hg] with x h1 h2 h3 h4 hg
    by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ (Fin n)))
    · rw [h1 hxΩ, h3 hxΩ, hg hxΩ]
    · rw [h2 hxΩ, h4 hxΩ, map_zero]

/-- **The localized Calderón–Zygmund estimate for coefficients of small oscillation.**
Let `0 < n` and `1 < p < ∞`. There are constants `C` and `δ > 0`, depending only on `n` and `p`,
with the following property. Let `A` be a matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `0 < λ`, let `Ω` be
open, and let `ζ` be smooth with compact support in `Ω`, `‖∇ζ‖ ≤ M₁` and `‖D²ζ‖ ≤ M₂`. Let `a` be
a measurable matrix-valued coefficient on `Ω` with `|aᵢⱼ(x) - Aᵢⱼ| ≤ ε` and `|aᵢⱼ(x)| ≤ Λ` for
almost every `x` in the support of `ζ`, where `ε ≤ δ λ` and `0 ≤ Λ`. Then every
`u ∈ W^{2,p}(Ω)` with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on `Ω`, with `f ∈ Lᵖ(Ω)`, satisfies

`‖ζ D²u‖_{Lᵖ(Ω)} ≤ (C / λ) ‖ζ f‖_{Lᵖ(Ω)} + (C n² Λ / λ + 1) (2 M₁ ‖∇u‖_{Lᵖ(Ω)} + M₂ ‖u‖_{Lᵖ(Ω)})`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u` and `∇u` is the weak gradient
`TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)`. No boundary condition on `u` and
no regularity of `Ω` is assumed. -/
theorem exists_lpNorm_smul_iteratedGradient_le_of_sum_mul_inner_eq_of_abs_sub_le (hn : 0 < n)
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
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  -- The Leibniz remainder `T = ∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ`, which vanishes off the support of `ζ`.
  set T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun x => (innerSL ℝ (∇ zeta x)).smulRight (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x)
      + (innerSL ℝ (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x)).smulRight (∇ zeta x)
      + Wkp.value 2 u x • fderiv ℝ (∇ zeta) x with hT
  -- The cutoff `w = ζ u ∈ W^{2,p}_0(Ω)` and its weak Hessian `ζ D²u + T`.
  obtain ⟨w, hw0, hwv⟩ := Wkp.exists_mem_wkp0Submodule_value_ae_eq_mul hp_top hζ hcpt hts 2 u
  have hD := Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul hζ hwv
  have hζ_top := hζ.continuous.memLp_top_of_hasCompactSupport hcpt (volume.restrict Omega)
  have hζH : MemLp (fun x => zeta x • Wkp.iteratedGradient 1 u x) p (volume.restrict Omega) :=
    hζ_top.smul (Lp.memLp _)
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
    refine (norm_leibnizRemainder_le zeta _ _ x).trans ?_
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
    · simp [hT, leibnizRemainder_eq_zero hx]
  have hE : MemLp (fun x => Matrix.contraction (a x) (T x)) p (volume.restrict Omega) :=
    (Lp.memLp TL).of_le_mul hEmeas hEle
  have hζf : MemLp (fun x => zeta x * f x) p (volume.restrict Omega) := hζ_top.smul (Lp.memLp f)
  set FL := hζf.toLp _ + hE.toLp _ with hFL_def
  have hFLnorm : ‖FL‖ ≤ lpNorm (fun x => zeta x * f x) p (volume.restrict Omega)
      + n ^ 2 * Λ * ‖TL‖ := by
    refine (norm_add_le _ _).trans (add_le_add (Lp.norm_toLp _ _).le ?_)
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [hE.coeFn_toLp, hEle] with x h1 h2
    rwa [h1]
  -- The equation `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ(ζ u) = ζ f + ∑ᵢⱼ aᵢⱼ Tᵢⱼ` on `Ω`, extended by zero to `ℝⁿ`.
  have hweq : ∀ᵐ x ∂volume.restrict Omega,
      Matrix.contraction (a x) (Wkp.iteratedGradient 1 w x) = FL x := by
    filter_upwards [hf, hD, Lp.coeFn_add (hζf.toLp _) (hE.toLp _), hζf.coeFn_toLp,
      hE.coeFn_toLp] with x hxf hxD h h' h''
    -- `hxf` applies the Hessian through the instances of `IteratedGradient`, which unfold to those
    -- of `ContinuousLinearMap` used by `Matrix.contraction_apply`.
    replace hxf : Matrix.contraction (a x) (Wkp.iteratedGradient 1 u x) = f x := by
      rw [Matrix.contraction_apply]
      exact hxf
    rw [h, Pi.add_apply, h', h'', hxD, ← hxf]
    simp only [hT, add_assoc, map_add, map_smul, smul_eq_mul]
  have hwK : ∀ᵐ x ∂volume.restrict Omega, x ∉ tsupport zeta → Wkp.value 2 w x = 0 := by
    filter_upwards [hwv] with x hx hxs
    rw [hx, image_eq_zero_of_notMem_tsupport hxs, zero_mul]
  obtain ⟨hWzero, hWeq⟩ := ae_extendByZeroₗᵢ_of_ae (w := ⟨w, hw0⟩) hwK hweq
  -- The whole-space estimate, and `ζ D²u = D²(ζ u) - T`.
  have hkey := hCZ hlam hA (isClosed_tsupport zeta) hε ha _ _ hWzero
    (by
      -- As for `hxf`, the two sides differ only by unfolding the instances of `IteratedGradient`.
      filter_upwards [hWeq] with x hx
      rw [← Matrix.contraction_apply]
      exact hx)
  rw [Wkp0.iteratedGradient_extendByZeroₗᵢ, LinearIsometry.norm_map, LinearIsometry.norm_map]
    at hkey
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
