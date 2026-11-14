/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Calculus.Morse.Linearization
import TauCeti.Analysis.Matrix.Contraction
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Basic
import TauCeti.Analysis.Sobolev.Wkp.Local.Approximation

/-!
# Approximation of strong supersolutions by classical ones

Equations in non-divergence form with measurable coefficients have, in general, only strong
solutions: functions `u ∈ W^{2,p}`, with a continuous representative `ū`, satisfying
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere with the weak Hessian `D²u`. This file approximates them by
classical supersolutions, so that estimates proved for `C²` functions pass to strong solutions.

Mollifying `u` gives smooth functions `v` close to `ū` uniformly on a compact set `K` and with
Hessians close to `D²u` in `Lᵖ(K)`
(`TauCeti.Wkp.exists_contDiff_abs_sub_le_and_eLpNorm_fderiv_gradient_sub_le`). With the same
coefficients, `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv ≤ f + N ‖D²v - D²u‖` almost everywhere, where `N` depends only on the
dimension and a bound for the entries of the coefficients. So `v` is a classical supersolution
with a right-hand side whose positive part is at most `‖f⁺‖_{Lᵖ} + η` in `Lᵖ`. No regularity or
measurability of the coefficients is needed.

Shifting `v` up by `ζ` and dividing by `1 + 3 ζ` absorbs the error `η` in the right-hand side: the
result `w` lies between `ū / (1 + 3 ζ)` and `(ū + 2 ζ) / (1 + 3 ζ)` on `K`, and its right-hand side
obeys the same `Lᵖ` bound as `f⁺`. So `w ≥ 0` where `ū ≥ 0`, and `w ≤ 1` where `ū ≤ 1`, which is
the form in which the Krylov–Safonov estimates consume supersolutions.

## Main declarations

* `TauCeti.PDE.exists_contDiff_abs_sub_le_and_sum_mul_fderiv_fderiv_le_of_wkp`: a strong
  supersolution is uniformly approximated by smooth classical supersolutions whose right-hand
  sides have nearly the same `Lᵖ` norm of the positive part.
* `TauCeti.PDE.exists_contDiff_div_le_and_sum_mul_fderiv_fderiv_le_of_wkp`: the rescaled
  approximations, classical supersolutions whose right-hand sides obey a given `Lᵖ` bound for
  `f⁺`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.7 (the Krylov–Safonov estimates for `W^{2,n}` solutions).
* L. C. Evans, *Partial Differential Equations*, §5.3.1 (interior mollification).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Approximation of a strong supersolution by classical ones.** Let `u ∈ W^{2,p}(Ω)`, `p < ∞`,
have a representative `ū` continuous on `Ω`, let `K ⊆ Ω` be compact and `S ⊆ K`, and suppose that
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere on `S` for the weak Hessian, with coefficient entries
bounded by `Λ` almost everywhere on `S`. For every `η > 0` there are a smooth function `v` with
`|v - ū| ≤ η` on `K` and a function `g` with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv ≤ g` at every point of `S` and
`‖g⁺‖_{Lᵖ(S)} ≤ ‖f⁺‖_{Lᵖ(S)} + η`. The coefficients need not be measurable. -/
theorem exists_contDiff_abs_sub_le_and_sum_mul_fderiv_fderiv_le_of_wkp {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ ι)} (u : Wkp volume Ω p 2)
    {ū : EuclideanSpace ℝ ι → ℝ} (hcont : ContinuousOn ū Ω)
    (hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū)
    {K S : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hSK : S ⊆ K)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {Λ : ℝ}
    (ha : ∀ᵐ x ∂volume.restrict S, ∀ i j, |a x i j| ≤ Λ)
    {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ∀ᵐ x ∂volume.restrict S,
      ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x)
    {η : ℝ} (hη : 0 < η) :
    ∃ v g : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧ (∀ y ∈ K, |v y - ū y| ≤ η) ∧
      (∀ x ∈ S, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ g x) ∧
      eLpNorm (fun x ↦ (g x)⁺) p (volume.restrict S) ≤
        eLpNorm (fun x ↦ (f x)⁺) p (volume.restrict S) + ENNReal.ofReal η := by
  -- `N` bounds the contraction with `a` of an endomorphism of norm one.
  set N : ℝ := (Fintype.card ι : ℝ) ^ 2 * max Λ 0 + 1
  have hN : 0 < N := by positivity
  have hN1 : 1 ≤ N := le_add_of_nonneg_left (by positivity)
  obtain ⟨v, hv, hvK, hvH⟩ := Wkp.exists_contDiff_abs_sub_le_and_eLpNorm_fderiv_gradient_sub_le hp
    u hcont hū hK hKΩ (div_pos hη hN)
  set D : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    fun x ↦ fderiv ℝ (∇ v) x - Wkp.iteratedGradient 1 u x
  set L : EuclideanSpace ℝ ι → ℝ := fun x ↦ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ v) x
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  -- Off a null set of `S`, the principal part of `v` exceeds that of `u` by at most `N ‖D‖`.
  have hL : ∀ᵐ x ∂volume.restrict S, L x ≤ (f x)⁺ + N * ‖D x‖ := by
    filter_upwards [hf, ha] with x hfx hax
    -- `L x` is the contraction of `fderiv (∇ v) x = D²u(x) + D x` with `a x`.
    have hLx : L x =
        ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i +
          ∑ i, ∑ j, a x i j * D x (EuclideanSpace.single j 1) i := by
      simp only [L, D, ← Finset.sum_add_distrib, ← mul_add]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← hessianOperator_single_apply ((contDiff_infty.1 hv 2).contDiffAt), ← fderiv_gradient]
      simp
    have hD : ∑ i, ∑ j, a x i j * D x (EuclideanSpace.single j 1) i ≤ N * ‖D x‖ := by
      refine (le_abs_self _).trans ((Matrix.abs_sum_sum_mul_apply_single_le _ _).trans ?_)
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc ∑ i, ∑ j, |a x i j| ≤ ∑ _i : ι, ∑ _j : ι, max Λ 0 :=
            Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ (hax i j).trans
              (le_max_left _ _)
        _ ≤ N := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            nlinarith [le_max_right Λ 0]
    rw [hLx]
    exact add_le_add (hfx.trans (le_max_left _ _)) hD
  refine ⟨v, fun x ↦ max (L x) ((f x)⁺ + N * ‖D x‖), hv,
    fun y hy ↦ (hvK y hy).trans (div_le_self hη.le hN1), fun x _ ↦ le_max_left _ _, ?_⟩
  -- Almost everywhere on `S` the maximum is its nonnegative second argument.
  have hae : (fun x ↦ (max (L x) ((f x)⁺ + N * ‖D x‖))⁺) =ᵐ[volume.restrict S]
      (fun x ↦ (f x)⁺) + N • fun x ↦ ‖D x‖ := by
    filter_upwards [hL] with x hx
    rw [max_eq_right hx, posPart_eq_self.2 (by positivity)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hD : AEStronglyMeasurable D (volume.restrict S) :=
    (measurable_fderiv ℝ (∇ v)).aestronglyMeasurable.sub ((Lp.aestronglyMeasurable _).mono_measure
      (Measure.restrict_mono (hSK.trans hKΩ) le_rfl))
  have hDK : eLpNorm (fun x ↦ ‖D x‖) p (volume.restrict S) ≤ ENNReal.ofReal (η / N) := by
    rw [eLpNorm_norm _ hD]
    exact (eLpNorm_mono_measure _ (Measure.restrict_mono hSK le_rfl)).trans hvH
  calc _ = eLpNorm ((fun x ↦ (f x)⁺) + N • fun x ↦ ‖D x‖) p (volume.restrict S) :=
        eLpNorm_congr_ae hae
    _ ≤ eLpNorm (fun x ↦ (f x)⁺) p (volume.restrict S) +
          ‖N‖ₑ * eLpNorm (fun x ↦ ‖D x‖) p (volume.restrict S) := by
        rw [← eLpNorm_const_smul]
        exact eLpNorm_add_le Fact.out
    _ ≤ eLpNorm (fun x ↦ (f x)⁺) p (volume.restrict S) +
          ENNReal.ofReal N * ENNReal.ofReal (η / N) := by
        rw [Real.eNorm_eq_ofReal hN.le]
        gcongr
    _ = eLpNorm (fun x ↦ (f x)⁺) p (volume.restrict S) + ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_mul hN.le, mul_div_cancel₀ _ hN.ne']


/-- **Rescaled approximation of a strong supersolution.** Let `u ∈ W^{2,p}(Ω)`, `p < ∞`, have a
representative `ū` continuous on `Ω`, let `K ⊆ Ω` be compact and `S ⊆ K`, and suppose that
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere on `S` for the weak Hessian, with coefficient entries
bounded by `Λ` almost everywhere on `S` and `‖f⁺‖_{Lᵖ(S)} ≤ M` for some `M > 0`. For every `ζ > 0`
there are a smooth function `w` with `ū / (1 + 3 ζ) ≤ w ≤ (ū + 2 ζ) / (1 + 3 ζ)` on `K` and a
function `g` with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼw ≤ g` at every point of `S` and `‖g⁺‖_{Lᵖ(S)} ≤ M`. The
coefficients need not be measurable. -/
theorem exists_contDiff_div_le_and_sum_mul_fderiv_fderiv_le_of_wkp {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ ι)} (u : Wkp volume Ω p 2)
    {ū : EuclideanSpace ℝ ι → ℝ} (hcont : ContinuousOn ū Ω)
    (hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict Ω] ū)
    {K S : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hSK : S ⊆ K)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {Λ : ℝ}
    (ha : ∀ᵐ x ∂volume.restrict S, ∀ i j, |a x i j| ≤ Λ)
    {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ∀ᵐ x ∂volume.restrict S,
      ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x)
    {M : ℝ} (hM : 0 < M)
    (hfM : eLpNorm (fun x ↦ (f x)⁺) p (volume.restrict S) ≤ ENNReal.ofReal M)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ w g : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) w ∧
      (∀ y ∈ K, ū y / (1 + 3 * ζ) ≤ w y ∧ w y ≤ (ū y + 2 * ζ) / (1 + 3 * ζ)) ∧
      (∀ x ∈ S, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ w) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ g x) ∧
      eLpNorm (fun x ↦ (g x)⁺) p (volume.restrict S) ≤ ENNReal.ofReal M := by
  -- `w = (v + ζ) / σ` for an approximation `v` within `η` of `ū`, where `η ≤ ζ M` absorbs the
  -- error in the right-hand side.
  set η := min ζ (ζ * M)
  have hη : 0 < η := lt_min hζ (by positivity)
  obtain ⟨v, g, hv, hvū, hvg, hg⟩ :=
    exists_contDiff_abs_sub_le_and_sum_mul_fderiv_fderiv_le_of_wkp hp u hcont hū hK hKΩ hSK ha hf
      hη
  set σ := 1 + 3 * ζ
  have hσ : 0 < σ := by positivity
  have hvū' (y : EuclideanSpace ℝ ι) (hy : y ∈ K) : |v y - ū y| ≤ ζ :=
    (hvū y hy).trans (min_le_left _ _)
  refine ⟨fun y ↦ σ⁻¹ * (v y + ζ), fun x ↦ σ⁻¹ * g x, contDiff_const.mul (hv.add contDiff_const),
    fun y hy ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · rw [div_eq_inv_mul, div_eq_inv_mul]
    have h := abs_le.1 (hvū' y hy)
    exact ⟨mul_le_mul_of_nonneg_left (by linarith) (inv_pos.2 hσ).le,
      mul_le_mul_of_nonneg_left (by linarith) (inv_pos.2 hσ).le⟩
  · -- The principal part of `w` is that of `v` divided by `σ`.
    rw [sum_mul_fderiv_fderiv_const_mul]
    have h : fderiv ℝ (fun y ↦ v y + ζ) = fderiv ℝ v := funext fun y ↦ fderiv_add_const ζ
    rw [h]
    exact mul_le_mul_of_nonneg_left (hvg x hx) (inv_pos.2 hσ).le
  have hpos : (fun x ↦ (σ⁻¹ * g x)⁺) = σ⁻¹ • fun x ↦ (g x)⁺ := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, posPart_def, mul_max_of_nonneg _ _
      (inv_pos.2 hσ).le, mul_zero]
  calc eLpNorm (fun x ↦ (σ⁻¹ * g x)⁺) p (volume.restrict S)
      = ENNReal.ofReal σ⁻¹ * eLpNorm (fun x ↦ (g x)⁺) p (volume.restrict S) := by
        rw [hpos, eLpNorm_const_smul, Real.eNorm_eq_ofReal (inv_pos.2 hσ).le]
    _ ≤ ENNReal.ofReal σ⁻¹ * (ENNReal.ofReal M + ENNReal.ofReal η) := by
        gcongr
        exact hg.trans (add_le_add_left hfM _)
    _ = ENNReal.ofReal (σ⁻¹ * (M + η)) := by
        rw [← ENNReal.ofReal_add hM.le hη.le, ← ENNReal.ofReal_mul (inv_pos.2 hσ).le]
    _ ≤ ENNReal.ofReal M := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [inv_mul_le_iff₀ hσ]
        nlinarith [min_le_right ζ (ζ * M)]

end PDE

end TauCeti
