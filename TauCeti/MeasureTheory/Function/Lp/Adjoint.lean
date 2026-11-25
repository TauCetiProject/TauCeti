/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# `Lᵖ` bounds for an operator on `L²` from bounds for its adjoint

Let `T : L²(μ; E) → L²(ν; F)` be a bounded operator between `L²` spaces of Hilbert space valued
functions, and let `T†` be its Hilbert space adjoint. If `T†` is bounded from `L^{q'}` to
`L^{p'}` on `L²`, that is `‖T† g‖_{p'} ≤ C ‖g‖_{q'}` for every `g ∈ L²`, then `T` is bounded from
`Lᵖ` to `L^q` on `L²` with the same constant, where `p, p'` and `q, q'` are pairs of Hölder
conjugate exponents and the target measure is σ-finite.

This is the duality argument that transfers a bound in one range of exponents to the dual
range: for instance the Calderón–Zygmund bound for `1 < p < 2` gives the bound for `2 < p < ∞`.
Neither `‖T f‖_q` nor `‖f‖_p` is assumed finite, so when `C < ∞` the theorem in particular shows
that `T` maps `L² ∩ Lᵖ` into `L^q`: the pairing of `T f` is only tested against bounded functions
of finite-measure support (`AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le`).

The same argument transfers weighted bounds. For real weights `u` on the source and `w` on the
target, a bound `‖u⁻¹ T† g‖_{p'} ≤ C ‖w⁻¹ g‖_{q'}` for the adjoint gives
`‖w T f‖_q ≤ C ‖u f‖_p` for the operator. The weights need not be bounded: the pairing of `w T f`
is computed through the bounded truncations `wₙ = w / (1 + |w| / (n + 1))`, which converge to
`w` with `|wₙ| ≤ |w|`. For exponential weights `u = w = exp (c ρ)` this turns an estimate showing
that `T†` preserves decay at rate `-c` into one showing that `T` preserves decay at rate `c`.

## Main declarations

* `ContinuousLinearMap.eLpNorm_smul_le_of_eLpNorm_smul_adjoint_le`: a weighted `L^{q'} → L^{p'}`
  bound for the adjoint gives the dual weighted `Lᵖ → L^q` bound for the operator.
* `ContinuousLinearMap.eLpNorm_le_of_eLpNorm_adjoint_le`: the unweighted case.

## References

* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter II, §2.4.
* L. Grafakos, *Classical Fourier Analysis*, Section 5.3.
-/

public section

open MeasureTheory TauCeti
open scoped ENNReal InnerProductSpace

namespace ContinuousLinearMap

variable {α β 𝕜 E F : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The weighted duality bound for a bounded weight `V` on the target with `|w⁻¹ V| ≤ 1`: the
pairing of `V T f` with a bounded function `g` of finite-measure support is the pairing of
`u f` with `u⁻¹ T† (V g)`, and `V g` is an element of `L²`. -/
private theorem eLpNorm_smul_le_of_eLpNorm_smul_adjoint_le_of_le [SigmaFinite ν]
    (T : Lp E 2 μ →L[𝕜] Lp F 2 ν) {p p' q q' : ℝ≥0∞} [p.HolderConjugate p'] [q.HolderConjugate q']
    {u : α → ℝ} {w V : β → ℝ} (hu : ∀ᵐ x ∂μ, u x ≠ 0) (hw : AEStronglyMeasurable w ν)
    (hV : AEStronglyMeasurable (fun y ↦ (V y : 𝕜)) ν) {M : ℝ} (hVM : ∀ y, ‖(V y : 𝕜)‖ ≤ M)
    (hVw : ∀ y, ‖(w y : 𝕜)⁻¹ * (V y : 𝕜)‖ ≤ 1) {C : ℝ≥0∞}
    (hT : ∀ g : Lp F 2 ν, eLpNorm (fun x ↦ (u x : 𝕜)⁻¹ • adjoint T g x) p' μ ≤
      C * eLpNorm (fun y ↦ (w y : 𝕜)⁻¹ • g y) q' ν) (f : Lp E 2 μ) :
    eLpNorm (fun y ↦ (V y : 𝕜) • T f y) q ν ≤ C * eLpNorm (fun x ↦ (u x : 𝕜) • f x) p μ := by
  refine (hV.smul (Lp.aestronglyMeasurable (T f))).eLpNorm_le_of_forall_enorm_integral_inner_le
    (𝕜 := 𝕜) (q' := q') fun g s hs hgs hg ↦ ?_
  have hVg_top : MemLp (fun y ↦ (V y : 𝕜) • g y) ∞ ν :=
    hg.of_le_mul (hV.smul hg.aestronglyMeasurable)
      (ae_of_all _ fun y ↦ by rw [norm_smul]; gcongr; exact hVM y)
  have hVg : MemLp (fun y ↦ (V y : 𝕜) • g y) 2 ν :=
    hVg_top.mono_exponent_of_measure_support_ne_top (fun y hy ↦ by simp [hgs y hy]) hs le_top
  set G := hVg.toLp _
  have hGg : (G : β → F) =ᵐ[ν] fun y ↦ (V y : 𝕜) • g y := hVg.coeFn_toLp
  have hpair : ∫ y, ⟪(V y : 𝕜) • T f y, g y⟫_𝕜 ∂ν =
      ∫ x, ⟪(u x : 𝕜) • f x, (u x : 𝕜)⁻¹ • adjoint T G x⟫_𝕜 ∂μ := by
    calc ∫ y, ⟪(V y : 𝕜) • T f y, g y⟫_𝕜 ∂ν = ∫ y, ⟪T f y, G y⟫_𝕜 ∂ν :=
          integral_congr_ae (hGg.mono fun y hy ↦ by
            simp only [hy, inner_smul_left, inner_smul_right, RCLike.conj_ofReal])
      _ = ∫ x, ⟪f x, adjoint T G x⟫_𝕜 ∂μ := by
          rw [← L2.inner_def, ← adjoint_inner_right, L2.inner_def]
      _ = _ := integral_congr_ae (hu.mono fun x hx ↦ by
          have hx' : (u x : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hx
          simp [inner_smul_left, inner_smul_right, hx'])
  calc ‖∫ y, ⟪(V y : 𝕜) • T f y, g y⟫_𝕜 ∂ν‖ₑ
      = ‖∫ x, ⟪(u x : 𝕜) • f x, (u x : 𝕜)⁻¹ • adjoint T G x⟫_𝕜 ∂μ‖ₑ := by rw [hpair]
    _ ≤ eLpNorm (fun x ↦ (u x : 𝕜) • f x) p μ *
        eLpNorm (fun x ↦ (u x : 𝕜)⁻¹ • adjoint T G x) p' μ := enorm_integral_inner_le
    _ ≤ eLpNorm (fun x ↦ (u x : 𝕜) • f x) p μ *
        (C * eLpNorm (fun y ↦ (w y : 𝕜)⁻¹ • G y) q' ν) := by gcongr; exact hT G
    _ ≤ eLpNorm (fun x ↦ (u x : 𝕜) • f x) p μ * (C * eLpNorm g q' ν) := by
        gcongr
        refine eLpNorm_mono_ae ((RCLike.continuous_ofReal.comp_aestronglyMeasurable hw).inv₀.smul
          (Lp.aestronglyMeasurable G)) (hGg.mono fun y hy ↦ ?_)
        rw [hy, smul_smul, norm_smul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hVw y)
    _ = C * eLpNorm (fun x ↦ (u x : 𝕜) • f x) p μ * eLpNorm g q' ν := by ring

/-- **Weighted duality for operators on `L²`.** Let `T : L²(μ; E) → L²(ν; F)` be a bounded operator
on a σ-finite target, let `p, p'` and `q, q'` be Hölder conjugate, and let `u` and `w`
be real weights on the source and the target, with `u` nonzero almost everywhere and `w` almost
everywhere strongly measurable. If the adjoint satisfies `‖u⁻¹ T† g‖_{p'} ≤ C ‖w⁻¹ g‖_{q'}` for
every `g ∈ L²`, then `‖w T f‖_q ≤ C ‖u f‖_p` for every `f ∈ L²`.

Neither side of the conclusion is assumed finite, and the weights need not be bounded. -/
theorem eLpNorm_smul_le_of_eLpNorm_smul_adjoint_le [SigmaFinite ν] (T : Lp E 2 μ →L[𝕜] Lp F 2 ν)
    {p p' q q' : ℝ≥0∞} [p.HolderConjugate p'] [q.HolderConjugate q']
    {u : α → ℝ} {w : β → ℝ} (hu : ∀ᵐ x ∂μ, u x ≠ 0) (hw : AEStronglyMeasurable w ν) {C : ℝ≥0∞}
    (hT : ∀ g : Lp F 2 ν, eLpNorm (fun x ↦ (u x : 𝕜)⁻¹ • adjoint T g x) p' μ ≤
      C * eLpNorm (fun y ↦ (w y : 𝕜)⁻¹ • g y) q' ν) (f : Lp E 2 μ) :
    eLpNorm (fun y ↦ (w y : 𝕜) • T f y) q ν ≤ C * eLpNorm (fun x ↦ (u x : 𝕜) • f x) p μ := by
  -- The truncated weights `wₙ = w / (1 + |w| / (n + 1))` are bounded by `n + 1`, satisfy
  -- `|w⁻¹ wₙ| ≤ 1`, and tend to `w`.
  set W : ℕ → β → ℝ := fun n y ↦ w y / (1 + |w y| * (1 / ((n : ℝ) + 1)))
  have hden (n : ℕ) (y : β) : 0 < 1 + |w y| * (1 / ((n : ℝ) + 1)) := by positivity
  have hWm (n : ℕ) : AEStronglyMeasurable (fun y ↦ (W n y : 𝕜)) ν :=
    RCLike.continuous_ofReal.comp_aestronglyMeasurable
      (hw.div₀ (aestronglyMeasurable_const.add (hw.norm.mul aestronglyMeasurable_const)))
  have hWb (n : ℕ) (y : β) : ‖(W n y : 𝕜)‖ ≤ (n : ℝ) + 1 := by
    rw [RCLike.norm_ofReal, abs_div, abs_of_pos (hden n y), div_le_iff₀ (hden n y)]
    field_simp
    nlinarith [abs_nonneg (w y)]
  have hWw (n : ℕ) (y : β) : ‖(w y : 𝕜)⁻¹ * (W n y : 𝕜)‖ ≤ 1 := by
    -- `|W n y| ≤ |w y|`, since the denominator is at least `1`.
    simp only [W, norm_mul, norm_inv, RCLike.norm_ofReal, abs_div, abs_of_pos (hden n y)]
    exact inv_mul_le_one_of_le₀
      (div_le_self (abs_nonneg _) (le_add_of_nonneg_right (by positivity))) (abs_nonneg _)
  have hlim (y : β) : Filter.Tendsto (fun n : ℕ ↦ W n y) Filter.atTop (nhds (w y)) := by
    have hden_lim : Filter.Tendsto (fun n : ℕ ↦ 1 + |w y| * (1 / ((n : ℝ) + 1))) Filter.atTop
        (nhds (1 + |w y| * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat)
    have h := (tendsto_const_nhds (x := w y)).div hden_lim (by simp)
    rwa [mul_zero, add_zero, div_one] at h
  exact Lp.eLpNorm_le_of_ae_tendsto (u := Filter.atTop) (Filter.Eventually.of_forall fun n ↦
      eLpNorm_smul_le_of_eLpNorm_smul_adjoint_le_of_le T hu hw (hWm n) (hWb n) (hWw n) hT f)
    (fun n ↦ (hWm n).smul (Lp.aestronglyMeasurable (T f)))
    ((RCLike.continuous_ofReal.comp_aestronglyMeasurable hw).smul (Lp.aestronglyMeasurable (T f)))
    (ae_of_all _ fun y ↦ ((RCLike.continuous_ofReal.tendsto _).comp (hlim y)).smul_const _)

/-- **Duality for operators on `L²`.** Let `T : L²(μ; E) → L²(ν; F)` be a bounded operator on a
σ-finite target, let `p, p'` and `q, q'` be Hölder conjugate, and suppose the
adjoint satisfies `‖T† g‖_{p'} ≤ C ‖g‖_{q'}` for every `g ∈ L²`. Then
`‖T f‖_q ≤ C ‖f‖_p` for every `f ∈ L²`. -/
theorem eLpNorm_le_of_eLpNorm_adjoint_le [SigmaFinite ν] (T : Lp E 2 μ →L[𝕜] Lp F 2 ν)
    {p p' q q' : ℝ≥0∞} [p.HolderConjugate p'] [q.HolderConjugate q'] {C : ℝ≥0∞}
    (hT : ∀ g : Lp F 2 ν, eLpNorm (adjoint T g) p' μ ≤ C * eLpNorm g q' ν) (f : Lp E 2 μ) :
    eLpNorm (T f) q ν ≤ C * eLpNorm f p μ := by
  simpa using eLpNorm_smul_le_of_eLpNorm_smul_adjoint_le T (u := 1) (w := 1)
    (ae_of_all _ fun _ ↦ one_ne_zero) aestronglyMeasurable_const (by simpa using hT) f

end ContinuousLinearMap
