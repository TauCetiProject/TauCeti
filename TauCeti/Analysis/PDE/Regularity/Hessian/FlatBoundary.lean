/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.HalfSpace
public import TauCeti.Analysis.Sobolev.Wkp.Leibniz
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.InnerProductSpace.Trace.OpNorm
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.Sobolev.Wkp.Extension

/-!
# The localized Calderón–Zygmund estimate near a flat boundary portion

Let `1 < p < ∞`, let `H = {x | a < x.fst}` be a half-space of `ℝ × E`, and let `Ω ⊆ H` be open.
This file carries the half-space `W^{2,p}` estimate for coefficients of small oscillation,
`exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace`,
over to strong solutions on `Ω` near a part of `∂Ω` lying on the hyperplane `∂H`.

First, the estimate `‖D²w‖_{Lᵖ(Ω)} ≤ (C / λ) ‖tr (A ∘ D²w)‖_{Lᵖ(Ω)}` holds for every
`w ∈ W^{2,p}(Ω)` with first-order part in `W^{1,p}_0(Ω)` which vanishes off a closed set `s` with
`H ∩ s ⊆ Ω`, provided `A` is within `δ λ` of an operator `A₀` with ellipticity constant `λ` on `s`
(`TauCeti.PDE.exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_comp_eq_of_le_normalHalfSpace`).
Near `s` the domain is the half-space, and the condition on `w` is its zero boundary value on the
flat part `∂H ∩ s` of `∂Ω`.

Then it is localized by a cutoff whose support may cross the hyperplane `∂H`
(`PDE.exists_lpNorm_smul_iteratedGradient_le_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace`
in namespace `TauCeti`). There are `C` and `δ > 0`, depending only on `E` and `p`, with the
following property. Let `A₀` be an operator with `λ ‖ξ‖² ≤ ⟪A₀ ξ, ξ⟫` and `0 < λ`, and let `ζ` be
smooth with compact support, `‖∇ζ‖ ≤ M₁` and `‖D²ζ‖ ≤ M₂`, such that `H ∩ supp ζ ⊆ Ω`. Let `A` be
a measurable field of endomorphisms with `‖A x - A₀‖ ≤ ε ≤ δ λ` and `‖A x‖ ≤ Λ` almost everywhere
on the support of `ζ`. Then every `u ∈ W^{2,p}(Ω)` with `tr (A ∘ D²u) = f ∈ Lᵖ(Ω)` almost
everywhere on `Ω`, and with `ζ u ∈ W^{1,p}_0(Ω)`, satisfies

`‖ζ D²u‖_{Lᵖ(Ω)} ≤ (C / λ) ‖ζ f‖_{Lᵖ(Ω)} + (C N Λ / λ + 1) (2 M₁ ‖∇u‖_{Lᵖ(Ω)} + M₂ ‖u‖_{Lᵖ(Ω)})`,

where `N` is the dimension of `ℝ × E`. The condition `ζ u ∈ W^{1,p}_0(Ω)` says that `u` vanishes
on the flat part `∂H ∩ supp ζ` of the boundary. This is the boundary counterpart of the interior
estimate `TauCeti.PDE.exists_lpNorm_smul_iteratedGradient_le_of_sum_mul_inner_eq_of_abs_sub_le`.
For instance `Ω` may be a half ball `H ∩ B(x₀, R)` about a point `x₀ ∈ ∂H`, with `ζ` supported in
`B(x₀, R)`. Flattening the boundary of a `C^{1,1}` domain brings the equation near a boundary
point to this form, which is how the global `W^{2,p}` estimate for continuous coefficients is
assembled.

## The argument

For the first estimate, `w` vanishes off the closed set `s`, which meets `H` only inside `Ω`, so
its extension by zero lies in `W^{2,p}(H)`, with weak Hessian the extension of that of `w`
(`TauCeti.Wkp.exists_value_eq_extendByZeroLpₗᵢ_of_isClosed`,
`TauCeti.Wkp.iteratedGradient_ae_eq_indicator_of_isClosed`). Its first-order part is the extension
of an element of `W^{1,p}_0(Ω)`, so it lies in `W^{1,p}_0(H)`, and the half-space estimate applies.

For the localized estimate, `ζ u` lies in `W^{2,p}(Ω)`
(`TauCeti.Wkp.exists_value_ae_eq_mul_of_hasCompactSupport`) and vanishes off `supp ζ`. By the
Leibniz rule for the weak Hessian (`TauCeti.Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul`),
`D²(ζ u) = ζ D²u + T` with `T = ∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ`, so

`tr (A ∘ D²(ζ u)) = ζ f + tr (A ∘ T)`.

The first estimate bounds `‖D²(ζ u)‖` by `(C / λ)` times the `Lᵖ` norm of the right side, the
coefficient bound gives `|tr (A ∘ T)| ≤ N Λ ‖T‖` (`ContinuousLinearMap.norm_traceCLM_le`), and
`‖T‖ ≤ 2 M₁ ‖∇u‖ + M₂ |u|` pointwise. Finally `ζ D²u = D²(ζ u) - T`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 9.12 and the proof of Theorem 9.13.
-/
public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Gradient ContDiff

namespace TauCeti

namespace PDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The Calderón–Zygmund estimate on a domain with a flat boundary portion.** Let `1 < p < ∞`.
There are constants `C` and `δ > 0`, depending only on `E` and `p`, with the following property.
Let `H = {x | a < x.fst}` be a half-space of `ℝ × E`, let `Ω ⊆ H` be open, and let `s` be a closed
set with `H ∩ s ⊆ Ω`. Let `A₀` be an operator on `ℝ × E` with `λ ‖ξ‖² ≤ ⟪A₀ ξ, ξ⟫` and `0 < λ`,
and let `A` be a field of endomorphisms of `ℝ × E` with `‖A x - A₀‖ ≤ ε` for almost every
`x ∈ s ∩ Ω`, where `ε ≤ δ λ`. Then every `w ∈ W^{2,p}(Ω)` whose first-order part lies in
`W^{1,p}_0(Ω)`, which vanishes almost everywhere on `Ω \ s`, and which solves
`tr (A ∘ D²w) = g` almost everywhere on `Ω`, with `g ∈ Lᵖ(Ω)`, satisfies

`‖D²w‖_{Lᵖ(Ω)} ≤ (C / λ) ‖g‖_{Lᵖ(Ω)}`,

where `D²w` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 w`. Near `s` the domain is the
half-space; `w` need not vanish near the flat part `∂H ∩ s` of `∂Ω`, only on it, in the sense of
`W^{1,p}_0(Ω)`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_comp_eq_of_le_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ {a : ℝ} {Omega : Opens (WithLp 2 (ℝ × E))}
      {s : Set (WithLp 2 (ℝ × E))}, Omega ≤ normalHalfSpace a → IsClosed s →
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ s ⊆ Omega →
      ∀ {A₀ : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
        {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)} {lam ε : ℝ},
        0 < lam → (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A₀ ξ, ξ⟫_ℝ) → ε ≤ δ * lam →
        (∀ᵐ x ∂(volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))), x ∈ s → ‖A x - A₀‖ ≤ ε) →
      ∀ (w : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
        (g : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
        Wkp.firstOrder 1 w ∈ w1p0Submodule volume Omega p →
        (∀ᵐ x ∂(volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))), x ∉ s → Wkp.value 2 w x = 0) →
        (∀ᵐ x ∂(volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 w x) = g x) →
        ‖Wkp.iteratedGradient 1 w‖ ≤ C / lam * ‖g‖ := by
  obtain ⟨C, δ, hδ, hCZ⟩ :=
    exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace
      (E := E) hp hp_top
  refine ⟨C, δ, hδ, fun {a Omega s} hΩH hs hHs {A₀ A lam ε} hlam hA₀ hε hA w g hw0 hws hweq => ?_⟩
  set N : ℝ := (Module.finrank ℝ (WithLp 2 (ℝ × E)) : ℝ)
  have hΩm : MeasurableSet (Omega : Set (WithLp 2 (ℝ × E))) := Omega.isOpen.measurableSet
  have hΩH' : (Omega : Set (WithLp 2 (ℝ × E))) ⊆ normalHalfSpace (E := E) a :=
    SetLike.coe_subset_coe.mpr hΩH
  -- The extension `z` of `w` by zero to the half-space, with zero boundary values.
  obtain ⟨z, hzv⟩ := Wkp.exists_value_eq_extendByZeroLpₗᵢ_of_isClosed hΩH hs hHs 2 w hws
  have hzD := Wkp.iteratedGradient_eq_extendByZeroLpₗᵢ_of_isClosed hΩH hs hHs 1 hws hzv
  have hz0 : Wkp.firstOrder 1 z ∈ w1p0Submodule volume (normalHalfSpace a) p := by
    have hz1 : W1p.value (Wkp.firstOrder 1 z) = Wkp.value 2 z := Wkp.value_firstOrder 1 z
    have hw1 : W1p.value (Wkp.firstOrder 1 w) = Wkp.value 2 w := Wkp.value_firstOrder 1 w
    have hfo : Wkp.firstOrder 1 z =
        (W1p0.extendByZeroL hΩH ⟨Wkp.firstOrder 1 w, hw0⟩ : W1p _ _ p) := by
      refine W1p.ext_value ?_
      rw [W1p0.value_extendByZeroL, hz1]
      exact hzv.trans (congrArg (extendByZeroLpₗᵢ ℝ volume hΩm hΩH') hw1.symm)
    exact (congrArg (· ∈ w1p0Submodule volume (normalHalfSpace (E := E) a) p) hfo).mpr
      (W1p0.extendByZeroL hΩH ⟨Wkp.firstOrder 1 w, hw0⟩).2
  have hzs : ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
      x ∉ s → Wkp.value 2 z x = 0 := by
    rw [hzv]
    filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ hΩm hΩH' (Wkp.value 2 w),
      ae_restrict_of_ae ((ae_restrict_iff' hΩm).1 hws)] with x he hx hxs
    rw [he]
    by_cases hxΩ : x ∈ (Omega : Set (WithLp 2 (ℝ × E)))
    · rw [indicator_of_mem hxΩ, hx hxΩ hxs]
    · rw [indicator_of_notMem hxΩ]
  -- The equation on the half-space, with right side `g` extended by zero.
  have hzeq : ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 z x) =
        extendByZeroLpₗᵢ ℝ volume hΩm hΩH' g x := by
    filter_upwards [Wkp.iteratedGradient_ae_eq_indicator_of_isClosed hΩH hs hHs 1 hws hzv,
      coeFn_extendByZeroLpₗᵢ ℝ hΩm hΩH' g,
      ae_restrict_of_ae ((ae_restrict_iff' hΩm).1 hweq)] with x h1 h2 h3
    by_cases hxΩ : x ∈ (Omega : Set (WithLp 2 (ℝ × E)))
    · simp only [h1, h2, indicator_of_mem hxΩ, h3 hxΩ]
    · -- Off `Ω`, the weak Hessian of the extension vanishes, and so does the right side.
      have hD0 := h1.trans (indicator_of_notMem hxΩ _)
      refine (norm_le_zero_iff.1 ?_).trans (h2.trans (indicator_of_notMem hxΩ _)).symm
      calc ‖traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 z x)‖
          ≤ N * ‖A x ∘L Wkp.iteratedGradient 1 z x‖ := ContinuousLinearMap.norm_traceCLM_le _
        _ ≤ N * (‖A x‖ * ‖Wkp.iteratedGradient 1 z x‖) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
        _ = 0 := by rw [hD0, norm_zero, mul_zero, mul_zero]
  -- The coefficients are controlled on `H ∩ s`, which lies in `Ω`.
  have hAH : ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
      x ∈ s → ‖A x - A₀‖ ≤ ε := by
    filter_upwards [ae_restrict_mem (normalHalfSpace (E := E) a).isOpen.measurableSet,
      ae_restrict_of_ae ((ae_restrict_iff' hΩm).1 hA)] with x hxH hx hxs
    exact hx (hHs ⟨hxH, hxs⟩) hxs
  have hkey := hCZ a hlam hA₀ hs hε hAH z _ hz0 hzs hzeq
  simpa only [hzD, LinearIsometry.norm_map] using hkey

/-- **The localized Calderón–Zygmund estimate near a flat boundary portion.** Let `1 < p < ∞`.
There are constants `C` and `δ > 0`, depending only on `E` and `p`, with the following property.
Let `H = {x | a < x.fst}` be a half-space of `ℝ × E`, let `Ω ⊆ H` be open, and let `ζ` be smooth
with compact support, `‖∇ζ‖ ≤ M₁` and `‖D²ζ‖ ≤ M₂`, such that `H ∩ supp ζ ⊆ Ω`. Let `A₀` be an
operator on `ℝ × E` with `λ ‖ξ‖² ≤ ⟪A₀ ξ, ξ⟫` and `0 < λ`, and let `A` be a measurable field of
endomorphisms of `ℝ × E` with `‖A x - A₀‖ ≤ ε` and `‖A x‖ ≤ Λ` for almost every `x` in the support
of `ζ`, where `ε ≤ δ λ` and `0 ≤ Λ`. Then every `u ∈ W^{2,p}(Ω)` with `ζ u ∈ W^{1,p}_0(Ω)` which
solves `tr (A ∘ D²u) = f` almost everywhere on `Ω`, with `f ∈ Lᵖ(Ω)`, satisfies

`‖ζ D²u‖_{Lᵖ(Ω)} ≤ (C / λ) ‖ζ f‖_{Lᵖ(Ω)} + (C N Λ / λ + 1) (2 M₁ ‖∇u‖_{Lᵖ(Ω)} + M₂ ‖u‖_{Lᵖ(Ω)})`,

where `N` is the dimension of `ℝ × E`, `D²u` is the weak Hessian
`TauCeti.Wkp.iteratedGradient 1 u` and `∇u` is the weak gradient
`TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)`. The condition on `ζ u` is the
boundary condition `u = 0` on the flat boundary portion `∂H ∩ supp ζ`; nothing is assumed about the
rest of `∂Ω`. -/
theorem
    exists_lpNorm_smul_iteratedGradient_le_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ {a : ℝ} {Omega : Opens (WithLp 2 (ℝ × E))}
      {zeta : WithLp 2 (ℝ × E) → ℝ} {M₁ M₂ : ℝ}, Omega ≤ normalHalfSpace a →
      ContDiff ℝ ∞ zeta → HasCompactSupport zeta →
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ tsupport zeta ⊆ Omega →
      (∀ x, ‖∇ zeta x‖ ≤ M₁) → (∀ x, ‖fderiv ℝ (∇ zeta) x‖ ≤ M₂) →
      ∀ {A₀ : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
        {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)} {lam ε Λ : ℝ},
        0 < lam → (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A₀ ξ, ξ⟫_ℝ) →
        AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) →
        ε ≤ δ * lam → (∀ᵐ x, x ∈ tsupport zeta → ‖A x - A₀‖ ≤ ε) → 0 ≤ Λ →
        (∀ᵐ x, x ∈ tsupport zeta → ‖A x‖ ≤ Λ) →
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
        (∃ v ∈ w1p0Submodule volume Omega p,
          W1p.value v =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
            fun x => zeta x * Wkp.value 2 u x) →
        (∀ᵐ x ∂(volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) = f x) →
        lpNorm (fun x => zeta x • Wkp.iteratedGradient 1 u x) p (volume.restrict Omega) ≤
          C / lam * lpNorm (fun x => zeta x * f x) p (volume.restrict Omega) +
            (C / lam * Module.finrank ℝ (WithLp 2 (ℝ × E)) * Λ + 1) *
              (2 * M₁ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ +
                M₂ * ‖Wkp.value 2 u‖) := by
  obtain ⟨C, δ, hδ, hCZ⟩ :=
    exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_comp_eq_of_le_normalHalfSpace
      (E := E) hp hp_top
  refine ⟨C, δ, hδ, fun {a Omega zeta M₁ M₂} hΩH hζ hcpt hHζ hM₁ hM₂ {A₀ A lam ε Λ} hlam hA₀
    hA_meas hε hA hΛ hAΛ u f hu0 hf => ?_⟩
  set N : ℝ := (Module.finrank ℝ (WithLp 2 (ℝ × E)) : ℝ)
  -- The Leibniz remainder `T = ∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ`, which vanishes off the support of `ζ`.
  obtain ⟨T, hT⟩ : ∃ T : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E),
      T = fun x => (innerSL ℝ (∇ zeta x)).smulRight (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x)
        + (innerSL ℝ (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x)).smulRight (∇ zeta x)
        + Wkp.value 2 u x • fderiv ℝ (∇ zeta) x := ⟨_, rfl⟩
  -- The product `w = ζ u ∈ W^{2,p}(Ω)` and its weak Hessian `ζ D²u + T`.
  obtain ⟨w, hwv⟩ := Wkp.exists_value_ae_eq_mul_of_hasCompactSupport 2 hζ hcpt u
  have hD := Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul hζ hwv
  have hζ_top := hζ.continuous.memLp_top_of_hasCompactSupport hcpt
    (volume.restrict (Omega : Set (WithLp 2 (ℝ × E))))
  have hζH : MemLp (fun x => zeta x • Wkp.iteratedGradient 1 u x) p (volume.restrict Omega) :=
    hζ_top.smul (Lp.memLp _)
  obtain ⟨TL, hTL_def⟩ : ∃ TL, TL = Wkp.iteratedGradient 1 w - hζH.toLp _ := ⟨_, rfl⟩
  have hTL : ∀ᵐ x ∂volume.restrict Omega, TL x = T x := by
    filter_upwards [Lp.coeFn_sub (Wkp.iteratedGradient 1 w) (hζH.toLp _), hD,
      hζH.coeFn_toLp] with x h1 h2 h3
    rw [hTL_def, h1, Pi.sub_apply, h2, h3, hT]
    simp only [add_assoc, add_sub_cancel_left]
  have hTnorm : ‖TL‖ ≤ 2 * M₁ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖
      + M₂ * ‖Wkp.value 2 u‖ :=
    hTL_def ▸ Wkp.norm_iteratedGradient_one_sub_toLp_le_of_value_ae_eq_mul hζ hM₁ hM₂ hζH hwv
  -- The forcing term `ζ f + tr (A ∘ T)` of the equation for `ζ u`.
  have hEmeas : AEStronglyMeasurable (fun x => traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L TL x))
      (volume.restrict Omega) := by
    have hTm : AEStronglyMeasurable T (volume.restrict Omega) :=
      (Lp.aestronglyMeasurable TL).congr hTL
    refine ((traceCLM ℝ (WithLp 2 (ℝ × E))).continuous.comp_aestronglyMeasurable
      ((continuous_fst.clm_comp continuous_snd).comp_aestronglyMeasurable
        (hA_meas.prodMk hTm))).congr ?_
    filter_upwards [hTL] with x hx
    rw [hx]
  have hEle : ∀ᵐ x ∂volume.restrict Omega,
      ‖traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L TL x)‖ ≤ N * Λ * ‖TL x‖ := by
    filter_upwards [hTL, ae_restrict_of_ae hAΛ] with x h1 h2
    by_cases hx : x ∈ tsupport zeta
    · calc ‖traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L TL x)‖
          ≤ N * ‖A x ∘L TL x‖ := ContinuousLinearMap.norm_traceCLM_le _
        _ ≤ N * (‖A x‖ * ‖TL x‖) := by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ N * (Λ * ‖TL x‖) := by gcongr; exact h2 hx
        _ = N * Λ * ‖TL x‖ := by ring
    · rw [h1]
      simp [hT, leibnizRemainder_eq_zero_of_notMem_tsupport hx]
  have hE : MemLp (fun x => traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L TL x)) p
      (volume.restrict Omega) :=
    (Lp.memLp TL).of_le_mul hEmeas hEle
  have hζf : MemLp (fun x => zeta x * f x) p (volume.restrict Omega) := hζ_top.smul (Lp.memLp f)
  obtain ⟨FL, hFL⟩ : ∃ FL : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega),
      FL = hζf.toLp _ + hE.toLp _ := ⟨_, rfl⟩
  have hFLnorm : ‖FL‖ ≤ lpNorm (fun x => zeta x * f x) p (volume.restrict Omega)
      + N * Λ * ‖TL‖ := by
    rw [hFL]
    refine (norm_add_le _ _).trans (add_le_add (Lp.norm_toLp _ _).le ?_)
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [hE.coeFn_toLp, hEle] with x h1 h2
    rwa [h1]
  -- The equation `tr (A ∘ D²(ζ u)) = ζ f + tr (A ∘ T)` on `Ω`, from `D²(ζ u) = ζ D²u + T`.
  have hwdec : Wkp.iteratedGradient 1 w = hζH.toLp _ + TL := by
    rw [hTL_def, add_sub_cancel]
  have hweq : ∀ᵐ x ∂volume.restrict Omega,
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 w x) = FL x := by
    -- `M ↦ tr (B ∘ M)` as a linear map on the values of weak Hessians, so that it is additive
    -- for their operations.
    have hL : ∀ (B : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))
        (M : IteratedGradient (WithLp 2 (ℝ × E)) 1),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (B ∘L M) =
          ((traceCLM ℝ (WithLp 2 (ℝ × E)) ∘L ContinuousLinearMap.compL ℝ (WithLp 2 (ℝ × E))
            (WithLp 2 (ℝ × E)) (WithLp 2 (ℝ × E)) B :
            (WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) →L[ℝ] ℝ) :
            IteratedGradient (WithLp 2 (ℝ × E)) 1 →L[ℝ] ℝ) M := fun _ _ => rfl
    filter_upwards [hf, hFL ▸ Lp.coeFn_add (hζf.toLp _) (hE.toLp _), hζf.coeFn_toLp,
      hE.coeFn_toLp, Lp.coeFn_add (hζH.toLp _) TL, hζH.coeFn_toLp]
      with x hxf h h' h'' hadd hζx
    rw [h, Pi.add_apply, h', h'', hwdec, hadd, Pi.add_apply, hζx, ← hxf, hL, hL, hL, map_add,
      map_smul, smul_eq_mul]
  have hwK : ∀ᵐ x ∂volume.restrict Omega, x ∉ tsupport zeta → Wkp.value 2 w x = 0 := by
    filter_upwards [hwv] with x hx hxs
    rw [hx, image_eq_zero_of_notMem_tsupport hxs, zero_mul]
  -- `ζ u` has zero boundary values, so the estimate on a domain with a flat boundary applies.
  obtain ⟨v, hv0, hvv⟩ := hu0
  have hw0 : Wkp.firstOrder 1 w ∈ w1p0Submodule volume Omega p := by
    have hw1 : W1p.value (Wkp.firstOrder 1 w) = Wkp.value 2 w := Wkp.value_firstOrder 1 w
    have hwv' : Wkp.firstOrder 1 w = v :=
      W1p.ext_value (hw1.trans (Lp.ext (hwv.trans hvv.symm)))
    exact (congrArg (· ∈ w1p0Submodule volume Omega p) hwv').mpr hv0
  have hkey := hCZ hΩH (isClosed_tsupport zeta) hHζ hlam hA₀ hε (ae_restrict_of_ae hA) w FL hw0
    hwK hweq
  have hHL : hζH.toLp _ = Wkp.iteratedGradient 1 w - TL := by
    rw [hTL_def, sub_sub_cancel]
  have hCl : 0 ≤ (C : ℝ) / lam := by positivity
  rw [← toReal_eLpNorm, ← Lp.norm_toLp _ hζH, hHL]
  calc ‖Wkp.iteratedGradient 1 w - TL‖
      ≤ ‖Wkp.iteratedGradient 1 w‖ + ‖TL‖ := norm_sub_le _ _
    _ ≤ C / lam * (lpNorm (fun x => zeta x * f x) p (volume.restrict Omega)
          + N * Λ * ‖TL‖) + ‖TL‖ := by
        gcongr
        exact hkey.trans (by gcongr)
    _ = C / lam * lpNorm (fun x => zeta x * f x) p (volume.restrict Omega)
          + (C / lam * N * Λ + 1) * ‖TL‖ := by ring
    _ ≤ _ := by gcongr

end PDE

end TauCeti
