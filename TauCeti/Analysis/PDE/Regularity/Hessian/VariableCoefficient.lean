/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.PDE.Regularity.Hessian.ConstantCoefficient
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Calculus.Morse.Linearization
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.Density

/-!
# The Calderón–Zygmund estimate in `W^{2,p}(ℝⁿ)` for coefficients of small oscillation

Let `n ≥ 3` and `1 < p < ∞`. For `u ∈ W^{2,p}(ℝⁿ)` write `D²u` for its weak Hessian
`TauCeti.Wkp.iteratedGradient 1 u`, an `Lᵖ` field of endomorphisms of `ℝⁿ`, so that
`⟪D²u(x) eᵢ, eⱼ⟫` is the weak second derivative `∂ᵢ∂ⱼu`. This file proves two strong-solution
estimates for the non-divergence-form operator `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu`.

* **Constant coefficients**
  (`TauCeti.PDE.exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq`). There is a
  constant `C`, depending only on `n` and `p`, such that for every matrix `A` with
  `λ ‖ξ‖² ≤ ξᵀ A ξ` and `0 < λ`, every `u ∈ W^{2,p}(ℝⁿ)` with `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f` almost
  everywhere satisfies `‖D²u‖_{Lᵖ} ≤ (C / λ) ‖f‖_{Lᵖ}`.
* **Coefficients of small oscillation**
  (`TauCeti.PDE.exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq_of_abs_sub_le`).
  There are `C` and `δ > 0`, depending only on `n` and `p`, with the following property. Let `A`
  be as above, let `s` be closed, and let `a` be a matrix-valued coefficient with
  `|aᵢⱼ(x) - Aᵢⱼ| ≤ ε ≤ δ λ` for almost every `x ∈ s`. Then every `u ∈ W^{2,p}(ℝⁿ)` vanishing
  outside `s` with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere satisfies
  `‖D²u‖_{Lᵖ} ≤ (C / λ) ‖f‖_{Lᵖ}`. No regularity of `a` is assumed.

## The argument

The constant-coefficient estimate holds for Schwartz functions
(`TauCeti.PDE.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_sum_smul_fderiv_fderiv_real`), hence
for test functions. Both sides of the estimate are continuous on `W^{2,p}(ℝⁿ)`: `D²u` is a
continuous projection, and `D²u ↦ ∑ᵢⱼ Aᵢⱼ ⟪D²u eᵢ, eⱼ⟫` is a continuous linear map applied
pointwise. Test functions are dense in `W^{2,p}(ℝⁿ)` for `p < ∞`
(`TauCeti.Wkp.denseRange_ofTestFunctionₗ_top`), so the estimate holds on all of `W^{2,p}(ℝⁿ)`.

For variable coefficients, freeze them at `A`:
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f + ∑ᵢⱼ (Aᵢⱼ - aᵢⱼ) ∂ᵢ∂ⱼu`. Outside `s` the weak Hessian vanishes
(`TauCeti.Wkp.iteratedGradient_ae_eq_zero_of_value_ae_eq_zero`), and on `s` the error term is at
most `n² ε ‖D²u‖` pointwise. The constant-coefficient estimate gives
`‖D²u‖ ≤ (C₀ / λ) (‖f‖ + n² ε ‖D²u‖)`, and the choice of `δ` makes the coefficient of `‖D²u‖`
on the right at most `1 / 2`, so it is absorbed on the left. This is the step of the `W^{2,p}`
theory for continuous coefficients that is applied, after a partition of unity, on each ball small
enough that the oscillation of the coefficients is below `δ λ`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.11 and its proof (freezing the coefficients and absorbing the error).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The contraction `H ↦ ∑ᵢⱼ Aᵢⱼ ⟪H eᵢ, eⱼ⟫` of an endomorphism of `ℝⁿ` with a matrix, as a
continuous linear functional. -/
private def matrixContraction (A : Matrix (Fin n) (Fin n) ℝ) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
  ∑ i, ∑ j, A i j • (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace.single i 1))

private theorem matrixContraction_apply (A : Matrix (Fin n) (Fin n) ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    matrixContraction A H = ∑ i, ∑ j, A i j *
      ⟪H (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ := by
  simp [matrixContraction, real_inner_comm]

/-- If every entry of `M` is at most `ε` in absolute value, then
`|∑ᵢⱼ Mᵢⱼ ⟪H eᵢ, eⱼ⟫| ≤ n² ε ‖H‖`. -/
private theorem abs_matrixContraction_le {M : Matrix (Fin n) (Fin n) ℝ} {ε : ℝ}
    (hM : ∀ i j, |M i j| ≤ ε) (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    |matrixContraction M H| ≤ n ^ 2 * ε * ‖H‖ := by
  have h1 : ∀ k : Fin n, ‖EuclideanSpace.single k (1 : ℝ)‖ = 1 := fun k => by simp
  rw [matrixContraction_apply]
  calc |∑ i, ∑ j, M i j * ⟪H (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ|
      ≤ ∑ _i : Fin n, ∑ _j : Fin n, ε * ‖H‖ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        refine mul_le_mul (hM i j) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hM i j))
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [h1, mul_one]
        exact (H.le_opNorm_of_le (h1 i).le).trans_eq (mul_one _)
    _ = n ^ 2 * ε * ‖H‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The Calderón–Zygmund estimate for constant coefficients in `W^{2,p}(ℝⁿ)`.** Let `n ≥ 3`
and `1 < p < ∞`. There is a constant `C`, depending only on `n` and `p`, such that for every
matrix `A` with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `0 < λ`, every `u ∈ W^{2,p}(ℝⁿ)` solving
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere, with `f ∈ Lᵖ(ℝⁿ)`, satisfies

`‖D²u‖_{Lᵖ} ≤ (C / λ) ‖f‖_{Lᵖ}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `ℝⁿ`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq (hn : 3 ≤ n)
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ {A : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ}, 0 < lam →
      (∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) ⊤ p 2)
        (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin n))))),
        (∀ᵐ x, ∑ i, ∑ j, A i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ = f x) →
        ‖Wkp.iteratedGradient 1 u‖ ≤ C / lam * ‖f‖ := by
  obtain ⟨C, hC⟩ :=
    exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_sum_smul_fderiv_fderiv_real hn hp hp_top
  refine ⟨C, fun {A lam} hlam hA u f hf => ?_⟩
  set T := matrixContraction A
  have hvol : ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
      ((⊤ : Opens (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)))) = volume := by
    rw [Opens.coe_top, Measure.restrict_univ]
  -- The equation says that `f` is the contraction of the weak Hessian with `A`.
  have hTf : T.compLpL p _ (Wkp.iteratedGradient 1 u) = f := by
    refine Lp.ext ?_
    filter_upwards [T.coeFn_compLpL (Wkp.iteratedGradient 1 u), ae_restrict_of_ae hf]
      with x hx hfx
    rw [hx, matrixContraction_apply, hfx]
  rw [← hTf]
  -- Both sides are continuous on `W^{2,p}(ℝⁿ)`, so it suffices to treat test functions.
  refine (Wkp.denseRange_ofTestFunctionₗ_top hp_top 2).induction_on u
    (isClosed_le ?_ ?_) fun φ => ?_
  · simp only [← Wkp.iteratedGradientL_apply]
    exact (Wkp.iteratedGradientL 1).continuous.norm
  · simp only [← Wkp.iteratedGradientL_apply]
    exact continuous_const.mul ((T.compLpL p _).continuous.comp
      (Wkp.iteratedGradientL 1).continuous).norm
  -- For a test function, both sides are the norms of its classical Hessian and of
  -- `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼφ`, and the estimate is the one for Schwartz functions.
  have hφ : ContDiff ℝ 2 (φ : EuclideanSpace ℝ (Fin n) → ℝ) := φ.contDiff.of_le (by simp)
  obtain ⟨L, hL⟩ : ∃ L : EuclideanSpace ℝ (Fin n) → ℝ, L = fun x => ∑ i, ∑ j, A i j •
    fderiv ℝ (fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ)) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := ⟨_, rfl⟩
  have hH : Wkp.iteratedGradient 1 (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ) =
      iteratedGradientTestFunctionLp p 1 φ :=
    Wkp.iteratedGradient_ofTestFunctionₗ 1 φ
  have hae : (T.compLpL p _ (Wkp.iteratedGradient 1
      (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ)) : EuclideanSpace ℝ (Fin n) → ℝ)
        =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          ((⊤ : Opens (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)))] L := by
    filter_upwards [T.coeFn_compLpL (Wkp.iteratedGradient 1
        (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ)),
      iteratedGradientTestFunctionLp_apply_ae (mu := volume) p 1 φ] with x hx hHx
    rw [hx, matrixContraction_apply, hH, hHx, iteratedGradientTestFunction_def, hL]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, iteratedGradientChain_succ, iteratedGradientChain_zero, fderiv_gradient,
      inner_hessianOperator_left]
  have hLfin : eLpNorm L p volume ≠ ∞ := by
    rw [← hvol, ← eLpNorm_congr_ae hae]
    exact Lp.eLpNorm_ne_top _
  have hTH : ‖T.compLpL p _ (Wkp.iteratedGradient 1
      (Wkp.ofTestFunctionₗ (mu := volume) (p := p) 2 φ))‖ = lpNorm L p volume := by
    rw [Lp.norm_def, eLpNorm_congr_ae hae, hvol, lpNorm]
  have h : eLpNorm (iteratedFDeriv ℝ 2 (φ : EuclideanSpace ℝ (Fin n) → ℝ)) p volume ≤
      ENNReal.ofReal (C / lam) * eLpNorm L p volume := by
    have hcoe : ⇑(φ.hasCompactSupport.toSchwartzMap φ.contDiff) = φ :=
      funext (HasCompactSupport.toSchwartzMap_toFun _ _)
    have := hC hlam hA (φ.hasCompactSupport.toSchwartzMap φ.contDiff)
    rwa [hcoe, ← hL] at this
  rw [hTH, Wkp.norm_iteratedGradient_eq_lpNorm_of_contDiffOn 1 _ hφ.contDiffOn
    (by rw [Wkp.value_ofTestFunctionₗ]; exact testFunctionLp_apply_ae p φ), hvol]
  calc lpNorm (iteratedFDeriv ℝ (1 + 1) (φ : EuclideanSpace ℝ (Fin n) → ℝ)) p volume
      ≤ (ENNReal.ofReal (C / lam) * eLpNorm L p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLfin) h
    _ = C / lam * lpNorm L p volume := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), lpNorm]

/-- **The Calderón–Zygmund estimate in `W^{2,p}(ℝⁿ)` for coefficients of small oscillation.**
Let `n ≥ 3` and `1 < p < ∞`. There are constants `C` and `δ > 0`, depending only on `n` and `p`,
with the following property. Let `A` be a matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `0 < λ`, let `s` be a
closed set, and let `a` be a matrix-valued coefficient with `|aᵢⱼ(x) - Aᵢⱼ| ≤ ε` for almost every
`x ∈ s`, where `ε ≤ δ λ`. Then every `u ∈ W^{2,p}(ℝⁿ)` vanishing almost everywhere outside `s`
and solving `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere, with `f ∈ Lᵖ(ℝⁿ)`, satisfies

`‖D²u‖_{Lᵖ} ≤ (C / λ) ‖f‖_{Lᵖ}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`. No measurability or continuity
of `a` is assumed. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq_of_abs_sub_le (hn : 3 ≤ n)
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ {A : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ}, 0 < lam →
      (∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      ∀ {a : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
        {s : Set (EuclideanSpace ℝ (Fin n))} {ε : ℝ}, IsClosed s → ε ≤ δ * lam →
        (∀ᵐ x, x ∈ s → ∀ i j, |a x i j - A i j| ≤ ε) →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) ⊤ p 2)
        (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin n))))),
        (∀ᵐ x, x ∉ s → Wkp.value 2 u x = 0) →
        (∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ = f x) →
        ‖Wkp.iteratedGradient 1 u‖ ≤ C / lam * ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq hn hp hp_top
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine ⟨2 * C, 1 / (2 * (C + 1) * n ^ 2), by positivity,
    fun {A lam} hlam hA {a s ε} hs hε ha u f hu hf => ?_⟩
  set H := Wkp.iteratedGradient 1 u
  set T := matrixContraction A with hT
  set g := T.compLpL p _ H
  have htop :
      MeasurableSet ((⊤ : Opens (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))) :=
    (⊤ : Opens (EuclideanSpace ℝ (Fin n))).isOpen.measurableSet
  have hg : ∀ᵐ x, g x = T (H x) := by
    filter_upwards [(ae_restrict_iff' htop).1 (T.coeFn_compLpL H)] with x hx using hx (by simp)
  -- The weak Hessian vanishes outside `s`, where `u` does.
  have hH0 : ∀ᵐ x, x ∉ s → H x = 0 := by
    let V : Opens (EuclideanSpace ℝ (Fin n)) := ⟨sᶜ, hs.isOpen_compl⟩
    have hval : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
        (V : Set (EuclideanSpace ℝ (Fin n))), Wkp.value 2 u x = 0 := by
      rw [ae_restrict_iff' V.isOpen.measurableSet]
      filter_upwards [hu] with x hx hxV using hx hxV
    exact (ae_restrict_iff' V.isOpen.measurableSet).1
      (Wkp.iteratedGradient_ae_eq_zero_of_value_ae_eq_zero 1 u le_top hval)
  -- The constant-coefficient estimate, applied to the frozen operator.
  have hHg : ‖H‖ ≤ C / lam * ‖g‖ :=
    hC hlam hA u g (by filter_upwards [hg] with x hx; rw [hx, matrixContraction_apply])
  -- The error of freezing is at most `n² ε |D²u|` pointwise.
  have hgf : ‖g - f‖ ≤ n ^ 2 * ε * ‖H‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [Lp.coeFn_sub g f, ae_restrict_of_ae hg, ae_restrict_of_ae hf,
      ae_restrict_of_ae ha, ae_restrict_of_ae hH0] with x hsub hgx hfx hax hHx
    by_cases hxs : x ∈ s
    · -- On `s`, the difference is the contraction of the weak Hessian with `A - a(x)`.
      have hdiff : g x - f x = matrixContraction (A - a x) (H x) := by
        simp only [hgx, ← hfx, hT, matrixContraction_apply, Matrix.sub_apply, sub_mul,
          Finset.sum_sub_distrib]
      rw [hsub, Pi.sub_apply, hdiff, Real.norm_eq_abs]
      exact abs_matrixContraction_le (fun i j => by
        rw [Matrix.sub_apply, abs_sub_comm]
        exact hax hxs i j) (H x)
    · rw [hsub, Pi.sub_apply, hgx, ← hfx, hHx hxs]
      simp
  have hK : (C : ℝ) / lam * (n ^ 2 * ε) ≤ 1 / 2 := by
    calc (C : ℝ) / lam * (n ^ 2 * ε)
        ≤ (C : ℝ) / lam * (n ^ 2 * (1 / (2 * ((C : ℝ) + 1) * n ^ 2) * lam)) := by gcongr
      _ = (C : ℝ) / (2 * ((C : ℝ) + 1)) := by field_simp
      _ ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) two_pos]
          linarith [C.coe_nonneg]
  have hfg := norm_sub_norm_le g f
  have hCl : 0 ≤ (C : ℝ) / lam := by positivity
  have habs : ‖H‖ ≤ C / lam * ‖f‖ + 1 / 2 * ‖H‖ := by
    calc ‖H‖ ≤ C / lam * ‖g‖ := hHg
      _ ≤ C / lam * (‖f‖ + n ^ 2 * ε * ‖H‖) := by gcongr; linarith
      _ = C / lam * ‖f‖ + C / lam * (n ^ 2 * ε) * ‖H‖ := by ring
      _ ≤ C / lam * ‖f‖ + 1 / 2 * ‖H‖ := by gcongr
  have h2 : ((2 * C : ℝ≥0) : ℝ) / lam * ‖f‖ = 2 * (C / lam * ‖f‖) := by push_cast; ring
  linarith

end PDE

end TauCeti
