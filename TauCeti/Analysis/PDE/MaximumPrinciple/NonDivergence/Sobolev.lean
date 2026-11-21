/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Calculus.Morse.Linearization
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Matrix.Contraction
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence.Basic
import TauCeti.Analysis.Sobolev.Wkp.Local.Approximation

/-!
# Approximation of strong supersolutions and subsolutions by classical ones

Equations in non-divergence form with measurable coefficients have, in general, only strong
solutions: functions `u ∈ W^{2,p}`, with a continuous representative `ū`, satisfying
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere with the weak Hessian `D²u`. This file approximates them by
classical supersolutions, so that estimates proved for `C²` functions pass to strong solutions.

Mollifying `u` gives smooth functions `v` close to `ū` uniformly on a compact set `K` and with
Hessians close to `D²u` in `Lᵖ(K)`
(`TauCeti.Wkp.exists_contDiff_abs_sub_le_and_eLpNorm_fderiv_gradient_sub_le`). With the same
coefficients, the principal parts of `v` and `u` differ by at most `N ‖D²v - D²u‖` almost
everywhere, where `N` depends only on the dimension and a bound for the entries of the
coefficients. This two-sided comparison serves solutions of equations as well as inequalities.
In particular `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv ≤ f + N ‖D²v - D²u‖`, so `v` is a classical supersolution
with a right-hand side whose positive part is at most `‖f⁺‖_{Lᵖ} + η` in `Lᵖ`. No regularity or
measurability of the coefficients is needed.

Shifting `v` up by `η / 2` gives a smooth `w` with `ū ≤ w ≤ ū + η` on `K` (preserving nonnegativity
without rescaling, for the weak Harnack and Harnack inequalities); shifting `v` up by `ζ` and
dividing by `1 + 3 ζ` absorbs the error `η` in the right-hand side: the result `w` lies between
`ū / (1 + 3 ζ)` and `(ū + 2 ζ) / (1 + 3 ζ)` on `K`, and its right-hand side obeys the same `Lᵖ`
bound as `f⁺`. So `w ≥ 0` where `ū ≥ 0`, and `w ≤ 1` where `ū ≤ 1`.

Subsolutions, `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f`, are approximated in the same way, now from below: shifting `v`
down gives a smooth `w` with `ū - η ≤ w ≤ ū` on `K`, a classical subsolution whose right-hand
side has negative part at most `‖f⁻‖_{Lᵖ} + η` in `Lᵖ`. This is the form in which the local maximum
principle consumes subsolutions.

## Main declarations

* `TauCeti.PDE.exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_sub_le_of_wkp`: smooth
  functions uniformly close to `ū` whose principal parts are close to that of `u` in `Lᵖ`.
* `TauCeti.PDE.exists_contDiff_abs_sub_le_and_sum_mul_fderiv_fderiv_le_of_wkp`: a strong
  supersolution is uniformly approximated by smooth classical supersolutions whose right-hand
  sides have nearly the same `Lᵖ` norm of the positive part.
* `TauCeti.PDE.exists_contDiff_le_and_le_add_and_sum_mul_fderiv_fderiv_le_of_wkp`: an upward
  approximation `ū ≤ w ≤ ū + η` of a strong supersolution.
* `TauCeti.PDE.exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp`: the same for
  a two-sided bound `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`.
* `TauCeti.PDE.exists_contDiff_le_and_le_add_and_abs_sum_mul_fderiv_fderiv_le_of_wkp`: an upward
  approximation `ū ≤ w ≤ ū + η` for a two-sided bound `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`.
* `TauCeti.PDE.exists_contDiff_div_le_and_sum_mul_fderiv_fderiv_le_of_wkp`: the rescaled
  approximations, classical supersolutions whose right-hand sides obey a given `Lᵖ` bound for
  `f⁺`.
* `TauCeti.PDE.exists_contDiff_sub_le_and_le_sum_mul_fderiv_fderiv_of_wkp`: a strong subsolution
  is approximated from below by smooth classical subsolutions whose right-hand sides have nearly
  the same `Lᵖ` norm of the negative part.

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

/-- The principal parts of a `C²` function `v` and of a second-order field `T` differ by at most
`N ‖D²v - T‖`, where `N = n² max Λ 0 + 1` and `Λ` bounds the coefficient entries. -/
private theorem abs_sum_mul_fderiv_fderiv_sub_le {v : EuclideanSpace ℝ ι → ℝ}
    {x : EuclideanSpace ℝ ι} (hv : ContDiffAt ℝ 2 v x) {A : Matrix ι ι ℝ} {Λ : ℝ}
    (hA : ∀ i j, |A i j| ≤ Λ) (T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    |∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
      ∑ i, ∑ j, A i j * T (EuclideanSpace.single j 1) i| ≤
      ((Fintype.card ι : ℝ) ^ 2 * max Λ 0 + 1) * ‖fderiv ℝ (∇ v) x - T‖ := by
  -- The difference is the contraction of `D²v - T` with `A`.
  have h : ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
      ∑ i, ∑ j, A i j * T (EuclideanSpace.single j 1) i =
      ∑ i, ∑ j, A i j * (fderiv ℝ (∇ v) x - T) (EuclideanSpace.single j 1) i := by
    simp only [← Finset.sum_sub_distrib, ← mul_sub]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [fderiv_gradient, ← hessianOperator_single_apply hv]
    simp
  rw [h]
  refine (Matrix.abs_sum_sum_mul_apply_single_le _ _).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  calc ∑ i, ∑ j, |A i j| ≤ ∑ _i : ι, ∑ _j : ι, max Λ 0 :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ (hA i j).trans (le_max_left _ _)
    _ ≤ _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        nlinarith [le_max_right Λ 0]

section

variable {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]

/-- **Mollified principal parts of a `W^{2,p}` function.** Let `u ∈ W^{2,p}(Ω)`, `p < ∞`, have a
representative `ū` continuous on `Ω`, let `K ⊆ Ω` be compact and `S ⊆ K`, and let the
coefficient entries be bounded by `Λ` almost everywhere on `S`. For every `η > 0` there are a smooth
function `v` with `|v - ū| ≤ η` on `K` and a function `e` with `‖e‖_{Lᵖ(S)} ≤ η` such that the
principal part `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv` differs from `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu`, taken with the weak Hessian, by at
most `e` almost everywhere on `S`. The coefficients need not be measurable. -/
theorem exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_sub_le_of_wkp {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ ι)} (u : Wkp mu Ω p 2)
    {ū : EuclideanSpace ℝ ι → ℝ} (hcont : ContinuousOn ū Ω)
    (hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū)
    {K S : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hSK : S ⊆ K)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {Λ : ℝ}
    (ha : ∀ᵐ x ∂mu.restrict S, ∀ i j, |a x i j| ≤ Λ) {η : ℝ} (hη : 0 < η) :
    ∃ v e : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧ (∀ y ∈ K, |v y - ū y| ≤ η) ∧
      (∀ᵐ x ∂mu.restrict S,
        |∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ v) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
          ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ e x) ∧
      eLpNorm e p (mu.restrict S) ≤ ENNReal.ofReal η := by
  -- `N` bounds the contraction with `a` of an endomorphism of norm one.
  set N : ℝ := (Fintype.card ι : ℝ) ^ 2 * max Λ 0 + 1
  have hN : 0 < N := by positivity
  have hN1 : 1 ≤ N := le_add_of_nonneg_left (by positivity)
  obtain ⟨v, hv, hvK, hvH⟩ := Wkp.exists_contDiff_abs_sub_le_and_eLpNorm_fderiv_gradient_sub_le hp
    u hcont hū hK hKΩ (div_pos hη hN)
  set D : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    fun x ↦ fderiv ℝ (∇ v) x - Wkp.iteratedGradient 1 u x
  refine ⟨v, N • fun x ↦ ‖D x‖, hv, fun y hy ↦ (hvK y hy).trans (div_le_self hη.le hN1), ?_, ?_⟩
  · filter_upwards [ha] with x hax
    rw [Pi.smul_apply, smul_eq_mul]
    exact abs_sum_mul_fderiv_fderiv_sub_le (contDiff_infty.1 hv 2).contDiffAt hax _
  have hD : AEStronglyMeasurable D (mu.restrict S) :=
    (measurable_fderiv ℝ (∇ v)).aestronglyMeasurable.sub ((Lp.aestronglyMeasurable _).mono_measure
      (Measure.restrict_mono (hSK.trans hKΩ) le_rfl))
  calc eLpNorm (N • fun x ↦ ‖D x‖) p (mu.restrict S)
      = ENNReal.ofReal N * eLpNorm (fun x ↦ ‖D x‖) p (mu.restrict S) := by
        rw [eLpNorm_const_smul, Real.eNorm_eq_ofReal hN.le]
    _ ≤ ENNReal.ofReal N * ENNReal.ofReal (η / N) := by
        rw [eLpNorm_norm _ hD]
        gcongr
        exact (eLpNorm_mono_measure _ (Measure.restrict_mono hSK le_rfl)).trans hvH
    _ = ENNReal.ofReal η := by rw [← ENNReal.ofReal_mul hN.le, mul_div_cancel₀ _ hN.ne']

omit [DecidableEq ι] in
/-- On `S ⊆ K ⊆ Ω`, adding `N` times the Hessian error `‖D²v - D²u‖` to a function `F` costs at most
`N δ` in `Lᵖ(S)` when that error is at most `δ` in `Lᵖ(K)`. -/
private theorem eLpNorm_add_smul_norm_fderiv_gradient_sub_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens (EuclideanSpace ℝ ι)} (u : Wkp mu Ω p 2) {v : EuclideanSpace ℝ ι → ℝ}
    {K S : Set (EuclideanSpace ℝ ι)} (hKΩ : K ⊆ Ω) (hSK : S ⊆ K) {δ : ℝ}
    (hvH : eLpNorm (fun y ↦ fderiv ℝ (∇ v) y - Wkp.iteratedGradient 1 u y) p
      (mu.restrict K) ≤ ENNReal.ofReal δ)
    (F : EuclideanSpace ℝ ι → ℝ) {N : ℝ} (hN : 0 ≤ N) :
    eLpNorm (F + N • fun x ↦ ‖fderiv ℝ (∇ v) x - Wkp.iteratedGradient 1 u x‖) p
      (mu.restrict S) ≤ eLpNorm F p (mu.restrict S) + ENNReal.ofReal (N * δ) := by
  have hD : AEStronglyMeasurable (fun x ↦ fderiv ℝ (∇ v) x - Wkp.iteratedGradient 1 u x)
      (mu.restrict S) :=
    (measurable_fderiv ℝ (∇ v)).aestronglyMeasurable.sub ((Lp.aestronglyMeasurable _).mono_measure
      (Measure.restrict_mono (hSK.trans hKΩ) le_rfl))
  calc _ ≤ eLpNorm F p (mu.restrict S) + ‖N‖ₑ * eLpNorm
        (fun x ↦ ‖fderiv ℝ (∇ v) x - Wkp.iteratedGradient 1 u x‖) p (mu.restrict S) := by
        rw [← eLpNorm_const_smul]
        exact eLpNorm_add_le Fact.out
    _ ≤ eLpNorm F p (mu.restrict S) + ENNReal.ofReal N * ENNReal.ofReal δ := by
        rw [Real.eNorm_eq_ofReal hN, eLpNorm_norm _ hD]
        gcongr
        exact (eLpNorm_mono_measure _ (Measure.restrict_mono hSK le_rfl)).trans hvH
    _ = _ := by rw [← ENNReal.ofReal_mul hN]

/-- **Approximation of a strong supersolution by classical ones.** Let `u ∈ W^{2,p}(Ω)`, `p < ∞`,
have a representative `ū` continuous on `Ω`, let `K ⊆ Ω` be compact and `S ⊆ K`, and suppose that
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere on `S` for the weak Hessian, with coefficient entries
bounded by `Λ` almost everywhere on `S`. For every `η > 0` there are a smooth function `v` with
`|v - ū| ≤ η` on `K` and a function `g` with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv ≤ g` at every point of `S` and
`‖g⁺‖_{Lᵖ(S)} ≤ ‖f⁺‖_{Lᵖ(S)} + η`. The coefficients need not be measurable. -/
theorem exists_contDiff_abs_sub_le_and_sum_mul_fderiv_fderiv_le_of_wkp {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ ι)} (u : Wkp mu Ω p 2)
    {ū : EuclideanSpace ℝ ι → ℝ} (hcont : ContinuousOn ū Ω)
    (hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū)
    {K S : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hSK : S ⊆ K)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {Λ : ℝ}
    (ha : ∀ᵐ x ∂mu.restrict S, ∀ i j, |a x i j| ≤ Λ)
    {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ∀ᵐ x ∂mu.restrict S,
      ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x)
    {η : ℝ} (hη : 0 < η) :
    ∃ v g : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧ (∀ y ∈ K, |v y - ū y| ≤ η) ∧
      (∀ x ∈ S, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ g x) ∧
      eLpNorm (fun x ↦ (g x)⁺) p (mu.restrict S) ≤
        eLpNorm (fun x ↦ (f x)⁺) p (mu.restrict S) + ENNReal.ofReal η := by
  obtain ⟨v, e, hv, hvK, hve, he⟩ :=
    exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_sub_le_of_wkp hp u hcont hū hK hKΩ
      hSK ha hη
  set L : EuclideanSpace ℝ ι → ℝ := fun x ↦ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ v) x
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  -- Off a null set of `S`, the principal part of `v` exceeds that of `u` by at most `e`.
  have hL : ∀ᵐ x ∂mu.restrict S, L x ≤ (f x)⁺ + e x := by
    filter_upwards [hf, hve] with x hfx hx
    linarith [(abs_sub_le_iff.1 hx).1, le_posPart (f x)]
  refine ⟨v, fun x ↦ max (L x) ((f x)⁺ + e x), hv, hvK, fun x _ ↦ le_max_left _ _, ?_⟩
  -- Almost everywhere on `S` the maximum is its nonnegative second argument.
  have hae : (fun x ↦ (max (L x) ((f x)⁺ + e x))⁺) =ᵐ[mu.restrict S]
      (fun x ↦ (f x)⁺) + e := by
    filter_upwards [hL, hve] with x hx hex
    rw [max_eq_right hx,
      posPart_eq_self.2 (add_nonneg (posPart_nonneg _) ((abs_nonneg _).trans hex))]
    simp only [Pi.add_apply]
  calc _ = eLpNorm ((fun x ↦ (f x)⁺) + e) p (mu.restrict S) := eLpNorm_congr_ae hae
    _ ≤ eLpNorm (fun x ↦ (f x)⁺) p (mu.restrict S) + eLpNorm e p (mu.restrict S) :=
        eLpNorm_add_le Fact.out
    _ ≤ _ := by gcongr

/-- **Approximation of a strong subsolution by classical ones.** Let `u ∈ W^{2,p}(Ω)`, `p < ∞`,
have a representative `ū` continuous on `Ω`, let `K ⊆ Ω` be compact and `S ⊆ K`, and suppose that
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≥ f` almost everywhere on `S` for the weak Hessian, with coefficient entries
bounded by `Λ` almost everywhere on `S`. For every `η > 0` there are a smooth function `w` with
`ū - η ≤ w ≤ ū` on `K` and a function `g` with `g ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼw` at every point of `S` and
`‖g⁻‖_{Lᵖ(S)} ≤ ‖f⁻‖_{Lᵖ(S)} + η`. The coefficients need not be measurable. -/
theorem exists_contDiff_sub_le_and_le_sum_mul_fderiv_fderiv_of_wkp {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ ι)} (u : Wkp mu Ω p 2)
    {ū : EuclideanSpace ℝ ι → ℝ} (hcont : ContinuousOn ū Ω)
    (hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū)
    {K S : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hSK : S ⊆ K)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {Λ : ℝ}
    (ha : ∀ᵐ x ∂mu.restrict S, ∀ i j, |a x i j| ≤ Λ)
    {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ∀ᵐ x ∂mu.restrict S,
      f x ≤ ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i)
    {η : ℝ} (hη : 0 < η) :
    ∃ w g : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) w ∧
      (∀ y ∈ K, ū y - η ≤ w y ∧ w y ≤ ū y) ∧
      (∀ x ∈ S, g x ≤ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ w) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      eLpNorm (fun x ↦ (g x)⁻) p (mu.restrict S) ≤
        eLpNorm (fun x ↦ (f x)⁻) p (mu.restrict S) + ENNReal.ofReal η := by
  set N : ℝ := (Fintype.card ι : ℝ) ^ 2 * max Λ 0 + 1
  have hN : 0 < N := by positivity
  have hN1 : 1 ≤ N := le_add_of_nonneg_left (by positivity)
  -- `w = v - η / 2` for an approximation `v` within `δ = η / (2 N) ≤ η / 2` of `ū`.
  set δ := η / (2 * N)
  have hδ : 0 < δ := by positivity
  have hδη : δ ≤ η / 2 := div_le_div_of_nonneg_left hη.le two_pos (by linarith)
  obtain ⟨v, hv, hvK, hvH⟩ := Wkp.exists_contDiff_abs_sub_le_and_eLpNorm_fderiv_gradient_sub_le hp
    u hcont hū hK hKΩ hδ
  set w : EuclideanSpace ℝ ι → ℝ := fun y ↦ v y - η / 2
  have hww : ∀ x, fderiv ℝ (fderiv ℝ w) x = fderiv ℝ (fderiv ℝ v) x :=
    fderiv_fderiv_sub_const v (η / 2)
  set D : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    fun x ↦ fderiv ℝ (∇ v) x - Wkp.iteratedGradient 1 u x
  set L : EuclideanSpace ℝ ι → ℝ := fun x ↦ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ w) x
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  set h : EuclideanSpace ℝ ι → ℝ := fun x ↦ -(f x)⁻ - N * ‖D x‖
  -- Off a null set of `S`, the principal part of `w` is at least `-f⁻ - N ‖D‖`.
  have hL : ∀ᵐ x ∂mu.restrict S, h x ≤ L x := by
    filter_upwards [hf, ha] with x hfx hax
    have hd : ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i -
        L x ≤ N * ‖D x‖ := by
      simp only [L, hww]
      exact (abs_sub_le_iff.1 (abs_sum_mul_fderiv_fderiv_sub_le
        (contDiff_infty.1 hv 2).contDiffAt hax (Wkp.iteratedGradient 1 u x))).2
    linarith [posPart_sub_negPart (f x), posPart_nonneg (f x)]
  have hgh : (fun x ↦ min (L x) (h x)) =ᵐ[mu.restrict S] h := by
    filter_upwards [hL] with x hx
    exact min_eq_right hx
  refine ⟨w, fun x ↦ min (L x) (h x), hv.sub contDiff_const, fun y hy ↦ ?_,
    fun x _ ↦ min_le_left _ _, ?_⟩
  · have h1 := abs_le.1 ((hvK y hy).trans hδη)
    constructor <;> simp only [w] <;> linarith [h1.1, h1.2]
  -- Almost everywhere on `S`, the negative part of the right-hand side is `f⁻ + N ‖D‖`.
  have hae : (fun x ↦ (min (L x) (h x))⁻) =ᵐ[mu.restrict S]
      (fun x ↦ (f x)⁻) + N • fun x ↦ ‖D x‖ := by
    filter_upwards [hgh] with x hx
    have hx0 : h x ≤ 0 := by
      have := mul_nonneg hN.le (norm_nonneg (D x))
      simp only [h]
      linarith [negPart_nonneg (f x)]
    rw [hx, negPart_eq_neg.2 hx0]
    simp only [h, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  calc _ = eLpNorm ((fun x ↦ (f x)⁻) + N • fun x ↦ ‖D x‖) p (mu.restrict S) :=
        eLpNorm_congr_ae hae
    _ ≤ _ := eLpNorm_add_smul_norm_fderiv_gradient_sub_le u hKΩ hSK hvH _ hN.le
    _ ≤ _ := by
        gcongr
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

/-- **Approximation of a strong supersolution from above.** Under the hypotheses of
`TauCeti.PDE.exists_contDiff_abs_sub_le_and_sum_mul_fderiv_fderiv_le_of_wkp`, shifting the smooth
approximations upward by `η / 2` gives `w` with `ū ≤ w ≤ ū + η` on `K`, `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼw ≤ g` on
`S`, and `‖g⁺‖_{Lᵖ(S)} ≤ ‖f⁺‖_{Lᵖ(S)} + η`. -/
theorem exists_contDiff_le_and_le_add_and_sum_mul_fderiv_fderiv_le_of_wkp {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ ι)} (u : Wkp mu Ω p 2)
    {ū : EuclideanSpace ℝ ι → ℝ} (hcont : ContinuousOn ū Ω)
    (hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū)
    {K S : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hSK : S ⊆ K)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {Λ : ℝ}
    (ha : ∀ᵐ x ∂mu.restrict S, ∀ i j, |a x i j| ≤ Λ)
    {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ∀ᵐ x ∂mu.restrict S,
      ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x)
    {η : ℝ} (hη : 0 < η) :
    ∃ w g : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) w ∧
      (∀ y ∈ K, ū y ≤ w y ∧ w y ≤ ū y + η) ∧
      (∀ x ∈ S, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ w) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ g x) ∧
      eLpNorm (fun x ↦ (g x)⁺) p (mu.restrict S) ≤
        eLpNorm (fun x ↦ (f x)⁺) p (mu.restrict S) + ENNReal.ofReal η := by
  obtain ⟨v, g, hv, hvK, hvg, hg⟩ :=
    exists_contDiff_abs_sub_le_and_sum_mul_fderiv_fderiv_le_of_wkp hp u hcont hū hK hKΩ hSK ha hf
      (half_pos hη)
  refine ⟨fun y ↦ v y + η / 2, g, hv.add contDiff_const, fun y hy ↦ ?_, fun x hx ↦ ?_,
    hg.trans (by gcongr; exact half_le_self hη.le)⟩
  · have h := abs_le.1 (hvK y hy)
    constructor <;> linarith
  · simpa only [fderiv_fderiv_add_const] using hvg x hx

/-- **Approximation of a two-sided strong inequality by classical ones.** Let `u ∈ W^{2,p}(Ω)`,
`p < ∞`, have a representative `ū` continuous on `Ω`, let `K ⊆ Ω` be compact and `S ⊆ K`, and
suppose that `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` almost everywhere on `S` for the weak Hessian, with coefficient
entries bounded by `Λ` almost everywhere on `S`. For every `η > 0` there are a smooth function `v`
with `|v - ū| ≤ η` on `K` and a function `g` with `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼv| ≤ g` at every point of `S` and
`‖g‖_{Lᵖ(S)} ≤ ‖f‖_{Lᵖ(S)} + η`. The coefficients need not be measurable. -/
theorem exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ ι)} (u : Wkp mu Ω p 2)
    {ū : EuclideanSpace ℝ ι → ℝ} (hcont : ContinuousOn ū Ω)
    (hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū)
    {K S : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hSK : S ⊆ K)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {Λ : ℝ}
    (ha : ∀ᵐ x ∂mu.restrict S, ∀ i j, |a x i j| ≤ Λ)
    {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ∀ᵐ x ∂mu.restrict S,
      |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x)
    {η : ℝ} (hη : 0 < η) :
    ∃ v g : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧ (∀ y ∈ K, |v y - ū y| ≤ η) ∧
      (∀ x ∈ S, |∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ g x) ∧
      eLpNorm g p (mu.restrict S) ≤ eLpNorm f p (mu.restrict S) + ENNReal.ofReal η := by
  obtain ⟨v, e, hv, hvK, hve, he⟩ :=
    exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_sub_le_of_wkp hp u hcont hū hK hKΩ
      hSK ha hη
  set L : EuclideanSpace ℝ ι → ℝ := fun x ↦ ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ v) x
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  refine ⟨v, fun x ↦ max |L x| (f x + e x), hv, hvK, fun x _ ↦ le_max_left _ _, ?_⟩
  -- Off a null set of `S`, `|L| ≤ f + e`, so the maximum is its second argument.
  have hae : (fun x ↦ max |L x| (f x + e x)) =ᵐ[mu.restrict S] f + e := by
    filter_upwards [hf, hve] with x hfx hx
    have h := abs_sub_abs_le_abs_sub (L x)
      (∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i)
    exact max_eq_right (by linarith)
  calc _ = eLpNorm (f + e) p (mu.restrict S) := eLpNorm_congr_ae hae
    _ ≤ eLpNorm f p (mu.restrict S) + eLpNorm e p (mu.restrict S) :=
        eLpNorm_add_le Fact.out
    _ ≤ _ := by gcongr

/-- **Approximation of a two-sided strong inequality from above.** Under the hypotheses of
`TauCeti.PDE.exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp`, shifting the
smooth approximations upward by `η / 2` gives `w` with `ū ≤ w ≤ ū + η` on `K`,
`|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼw| ≤ g` on `S`, and `‖g‖_{Lᵖ(S)} ≤ ‖f‖_{Lᵖ(S)} + η`. -/
theorem exists_contDiff_le_and_le_add_and_abs_sum_mul_fderiv_fderiv_le_of_wkp {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ ι)} (u : Wkp mu Ω p 2)
    {ū : EuclideanSpace ℝ ι → ℝ} (hcont : ContinuousOn ū Ω)
    (hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū)
    {K S : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hSK : S ⊆ K)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {Λ : ℝ}
    (ha : ∀ᵐ x ∂mu.restrict S, ∀ i j, |a x i j| ≤ Λ)
    {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ∀ᵐ x ∂mu.restrict S,
      |∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i| ≤ f x)
    {η : ℝ} (hη : 0 < η) :
    ∃ w g : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) w ∧
      (∀ y ∈ K, ū y ≤ w y ∧ w y ≤ ū y + η) ∧
      (∀ x ∈ S, |∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ w) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ g x) ∧
      eLpNorm g p (mu.restrict S) ≤ eLpNorm f p (mu.restrict S) + ENNReal.ofReal η := by
  obtain ⟨v, g, hv, hvK, hvg, hg⟩ :=
    exists_contDiff_abs_sub_le_and_abs_sum_mul_fderiv_fderiv_le_of_wkp hp u hcont hū hK hKΩ hSK ha
      hf (half_pos hη)
  refine ⟨fun y ↦ v y + η / 2, g, hv.add contDiff_const, fun y hy ↦ ?_, fun x hx ↦ ?_,
    hg.trans (by gcongr; exact half_le_self hη.le)⟩
  · have h := abs_le.1 (hvK y hy)
    constructor <;> linarith
  · simpa only [fderiv_fderiv_add_const] using hvg x hx

/-- **Rescaled approximation of a strong supersolution.** Let `u ∈ W^{2,p}(Ω)`, `p < ∞`, have a
representative `ū` continuous on `Ω`, let `K ⊆ Ω` be compact and `S ⊆ K`, and suppose that
`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu ≤ f` almost everywhere on `S` for the weak Hessian, with coefficient entries
bounded by `Λ` almost everywhere on `S` and `‖f⁺‖_{Lᵖ(S)} ≤ M` for some `M > 0`. For every `ζ > 0`
there are a smooth function `w` with `ū / (1 + 3 ζ) ≤ w ≤ (ū + 2 ζ) / (1 + 3 ζ)` on `K` and a
function `g` with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼw ≤ g` at every point of `S` and `‖g⁺‖_{Lᵖ(S)} ≤ M`. The
coefficients need not be measurable. -/
theorem exists_contDiff_div_le_and_sum_mul_fderiv_fderiv_le_of_wkp {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {Ω : Opens (EuclideanSpace ℝ ι)} (u : Wkp mu Ω p 2)
    {ū : EuclideanSpace ℝ ι → ℝ} (hcont : ContinuousOn ū Ω)
    (hū : (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Ω] ū)
    {K S : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hSK : S ⊆ K)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {Λ : ℝ}
    (ha : ∀ᵐ x ∂mu.restrict S, ∀ i j, |a x i j| ≤ Λ)
    {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ∀ᵐ x ∂mu.restrict S,
      ∑ i, ∑ j, a x i j * Wkp.iteratedGradient 1 u x (EuclideanSpace.single j 1) i ≤ f x)
    {M : ℝ} (hM : 0 < M)
    (hfM : eLpNorm (fun x ↦ (f x)⁺) p (mu.restrict S) ≤ ENNReal.ofReal M)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ w g : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ (⊤ : ℕ∞) w ∧
      (∀ y ∈ K, ū y / (1 + 3 * ζ) ≤ w y ∧ w y ≤ (ū y + 2 * ζ) / (1 + 3 * ζ)) ∧
      (∀ x ∈ S, ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ w) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ≤ g x) ∧
      eLpNorm (fun x ↦ (g x)⁺) p (mu.restrict S) ≤ ENNReal.ofReal M := by
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
    simp_rw [fderiv_fderiv_add_const]
    exact mul_le_mul_of_nonneg_left (hvg x hx) (inv_pos.2 hσ).le
  have hpos : (fun x ↦ (σ⁻¹ * g x)⁺) = σ⁻¹ • fun x ↦ (g x)⁺ := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, posPart_def, mul_max_of_nonneg _ _
      (inv_pos.2 hσ).le, mul_zero]
  calc eLpNorm (fun x ↦ (σ⁻¹ * g x)⁺) p (mu.restrict S)
      = ENNReal.ofReal σ⁻¹ * eLpNorm (fun x ↦ (g x)⁺) p (mu.restrict S) := by
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

end

end PDE

end TauCeti
