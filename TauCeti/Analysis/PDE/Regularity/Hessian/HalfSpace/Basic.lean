/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Sobolev
public import TauCeti.Analysis.Sobolev.Trace.OddReflection
import TauCeti.Analysis.InnerProductSpace.Positive.Definite
import TauCeti.Analysis.InnerProductSpace.Trace.Free
import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables

import TauCeti.Analysis.InnerProductSpace.Trace.OpNorm
import TauCeti.Analysis.PDE.Regularity.Hessian.VariableCoefficient
import TauCeti.Analysis.Sobolev.Wkp.Laplacian
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The Calderón–Zygmund estimate on a half-space

Let `E` be a finite-dimensional real inner product space, let `1 < p < ∞`, and let
`H = {x | a < x.fst}` be a half-space of the Euclidean product `ℝ × E`. This file proves the
`W^{2,p}` estimate of the Hessian on `H` for strong solutions of Poisson's equation that vanish on
the boundary hyperplane: there is a constant `C`, depending only on `E` and `p`, such that every
`u ∈ W^{2,p}(H)` whose first-order part lies in `W^{1,p}_0(H)` and which solves `Δu = f` with
`f ∈ Lᵖ(H)` satisfies

`‖D²u‖_{Lᵖ(H)} ≤ C ‖f‖_{Lᵖ(H)}`.

Here `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`. The equation is taken either
strongly, the trace of `D²u` being `f`
(`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq_of_normalHalfSpace`), or
against test functions on `H`, in
`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_integral_laplacian_smul_eq_of_normalHalfSpace`.
The constant does not depend on the position `a` of the boundary.

The same estimate holds for constant-coefficient operators: if `A` is an operator on `ℝ × E`
with `λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` and `0 < λ`, every such `u` solving `tr (A D²u) = f` strongly
satisfies `‖D²u‖_{Lᵖ(H)} ≤ (C / λ) ‖f‖_{Lᵖ(H)}`, with the constant `C` of the Laplacian
(`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_comp_eq_of_normalHalfSpace`).
For an orthonormal basis `eᵢ`, `tr (A D²u) = ∑ᵢⱼ ⟪A eⱼ, eᵢ⟫ ∂ᵢ∂ⱼu`. The constant does not depend
on `A` beyond `λ`, which is what freezing variable coefficients near the boundary requires.

The estimate extends to strong solutions of the non-divergence-form equation `tr (A ∘ D²u) = f`
whose coefficient field `A` is uniformly close to a constant operator `A₀` with
`λ ‖ξ‖² ≤ ⟪A₀ ξ, ξ⟫`: if `‖A x - A₀‖ ≤ δ λ`, with `δ` depending only on `E` and `p`, then
`‖D²u‖ ≤ (C / λ) ‖f‖` (in namespace `TauCeti`,
`exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace`).
As in the whole-space estimate for coefficients of small oscillation, the coefficients need only be
controlled on a closed set `s` outside which `u` vanishes, which is the situation after cutting
`u` off near a boundary point, where `A₀` is the value of a continuous coefficient field at that
point.

This is the flat-boundary model of the global `W^{2,p}` estimates for the Dirichlet problem:
flattening the boundary of a `C^{1,1}` domain turns the equation near a boundary point into one on
a half-space. The zero boundary condition enters through the odd reflection of `u`, which lies in
`W^{2,p}` of the whole space only because `u` vanishes on the boundary hyperplane.

## The argument

The odd reflection `v` of `u` across the boundary hyperplane lies in `W^{2,p}(ℝ × E)`, with weak
Hessian `D²u` on `H` and `-R ∘ D²u(ρ x) ∘ R` on the other side, where `ρ` is the reflection in the
hyperplane and `R` its linear part
(`TauCeti.Wkp.exists_value_ae_eq_sub_comp_normalReflection`). Since `R` is an involution, the
trace of `R ∘ M ∘ R` is the trace of `M`, so `Δv` is the odd reflection of `f`, whose `Lᵖ` norm is
at most `2 ‖f‖_{Lᵖ(H)}` because `ρ` preserves volume. The whole-space estimate
(`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq`) bounds `D²v` by
`Δv`, and `D²v` restricts to `D²u` on `H`.

For constant coefficients, only the symmetric part `S = (A + A†) / 2` of `A` enters
(`ContinuousLinearMap.traceCLM_symmPart_comp`), because the weak Hessian is self-adjoint almost
everywhere (`TauCeti.Wkp.adjoint_iteratedGradient_one_ae_eq`). Write `S = e e†` for a linear
automorphism `e` whose adjoint maps the normal `(1, 0)` to a positive multiple `c (1, 0)`
(`ContinuousLinearMap.exists_continuousLinearEquiv_comp_adjoint_eq_of_isSymmetric`). Then `e`
maps the half-space `{a / c < x.fst}` onto `H`, and `v = u ∘ e` lies in `W^{2,p}` of that
half-space, with zero boundary values and weak Hessian `e† ∘ D²u(e ·) ∘ e`
(`TauCeti.Wkp.exists_value_ae_eq_comp_continuousLinearEquiv`). Its trace is
`tr (D²u(e ·) e e†) = tr (S D²u) ∘ e = f ∘ e`, so the estimate for the Laplacian applies to `v`.
Since `‖e⁻¹‖ ≤ λ^(-1/2)`, `‖D²u ∘ e‖ ≤ λ⁻¹ ‖D²v‖` pointwise, and changing variables multiplies
the `Lᵖ` norms of `D²u ∘ e` and of `f ∘ e` by the same Jacobian factor
(`TauCeti.Wkp.norm_iteratedGradient_le_of_ae_eq_adjoint_comp_comp`).

For variable coefficients, freeze them at `A₀`:
`tr (A₀ ∘ D²u) = f - tr ((A - A₀) ∘ D²u)`. The weak Hessian vanishes where `u` does
(`TauCeti.Wkp.iteratedGradient_ae_eq_zero_of_value_ae_eq_zero_of_isOpen`), and on `s` the error
term is at most `dim (ℝ × E) · δ λ ‖D²u‖` pointwise (`ContinuousLinearMap.norm_traceCLM_le`). The
constant-coefficient estimate then gives `‖D²u‖ ≤ (C₀ / λ) (‖f‖ + dim (ℝ × E) δ λ ‖D²u‖)`, and
the choice of `δ` makes the coefficient of `‖D²u‖` on the right at most `1 / 2`, so it is absorbed
(`TauCeti.PDE.le_two_mul_div_mul_of_le_div_mul_of_le_add`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.9 and §9.5, Lemma 9.12 (the estimate near a flat boundary portion, by reflection),
  and Section 6.1 (reduction of a constant-coefficient operator to the Laplacian by a linear change
  of variables).

  and the proof of Theorem 9.11 (freezing the coefficients and absorbing the error).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace InnerProductSpace
open scoped ENNReal NNReal Laplacian Distributions

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

section Reflection

variable {a : ℝ} {D W : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}

/-- If `W` is the odd reflection `D x - R ∘ D (ρ x) ∘ R` of a field `D` vanishing off the half-space
`H`, the `Lᵖ` norm of `tr W` is at most twice that of `tr D` on `H`. -/
private theorem eLpNorm_traceCLM_le_of_ae_eq_sub_comp_normalReflection
    (hD : AEStronglyMeasurable D
      ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)))
    (hW : W =ᵐ[volume] fun x =>
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator D x -
        (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator D
            (normalReflection E a x) ∘L
          (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))) :
    eLpNorm (fun x => traceCLM ℝ (WithLp 2 (ℝ × E)) (W x)) p volume ≤
      2 * eLpNorm (fun x => traceCLM ℝ (WithLp 2 (ℝ × E)) (D x)) p
        ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) := by
  have hS := (normalHalfSpace (E := E) a).isOpen.measurableSet
  -- `g` is the trace of `D`, extended by zero off `H`.
  obtain ⟨g, hg_def⟩ : ∃ g : WithLp 2 (ℝ × E) → ℝ,
      g = (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator
        fun x => traceCLM ℝ (WithLp 2 (ℝ × E)) (D x) := ⟨_, rfl⟩
  have hgD : ∀ x, traceCLM ℝ (WithLp 2 (ℝ × E))
      ((normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator D x) = g x := fun x => by
    rw [hg_def]
    by_cases hx : x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, map_zero]
  have hg_meas : AEStronglyMeasurable g volume := hg_def ▸
    (aestronglyMeasurable_indicator_iff hS).2
      ((traceCLM ℝ (WithLp 2 (ℝ × E))).continuous.comp_aestronglyMeasurable hD)
  -- The trace of `W` is the odd reflection `g - g ∘ ρ` of `g`, since `tr (R ∘ M ∘ R) = tr M`.
  have htr : (fun x => traceCLM ℝ (WithLp 2 (ℝ × E)) (W x)) =ᵐ[volume]
      g - g ∘ normalReflection E a := by
    filter_upwards [hW] with x hx
    have hR := (normalLinearReflection E).toContinuousLinearEquiv.traceCLM_comp_comp_symm
      ((normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator D (normalReflection E a x))
    rw [← LinearIsometryEquiv.toContinuousLinearEquiv_symm, normalLinearReflection_symm] at hR
    rw [hx, map_sub, hR, hgD, hgD, Pi.sub_apply, Function.comp_apply]
  rw [eLpNorm_congr_ae htr, ← eLpNorm_indicator_eq_eLpNorm_restrict hS.nullMeasurableSet, ← hg_def,
    two_mul]
  calc eLpNorm (g - g ∘ normalReflection E a) p volume
      ≤ eLpNorm g p volume + eLpNorm (g ∘ normalReflection E a) p volume :=
        eLpNorm_sub_le Fact.out
    _ = eLpNorm g p volume + eLpNorm g p volume := by
        rw [eLpNorm_comp_measurePreserving hg_meas (normalReflection E a).measurePreserving]

omit [Fact (1 ≤ p)] in
/-- If `W` is the odd reflection `D x - R ∘ D (ρ x) ∘ R` of a field `D` vanishing off the half-space
`H`, then `W = D` on `H`, so the `Lᵖ` norm of `D` on `H` is at most that of `W`. -/
private theorem eLpNorm_restrict_le_of_ae_eq_sub_comp_normalReflection
    (hW : W =ᵐ[volume] fun x =>
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator D x -
        (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator D
            (normalReflection E a x) ∘L
          (normalLinearReflection E : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))) :
    eLpNorm D p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) ≤
      eLpNorm W p volume := by
  have hS := (normalHalfSpace (E := E) a).isOpen.measurableSet
  have heq :
      D =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)] W := by
    filter_upwards [ae_restrict_of_ae hW, ae_restrict_mem hS] with x hx hxS
    -- `ρ` maps `H` off itself.
    have hρx : normalReflection E a x ∉ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) := by
      rw [SetLike.mem_coe, normalReflection_mem_normalHalfSpace_iff]
      exact ((mem_normalHalfSpace a x).1 hxS).not_gt
    rw [hx, indicator_of_mem hxS, indicator_of_notMem hρx]
    simp
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

end Reflection

/-- **The Calderón–Zygmund estimate on a half-space, for strong solutions.** Let `1 < p < ∞`.
There is a constant `C` such that for every half-space `H = {x | a < x.fst}` of `ℝ × E`, every
`u ∈ W^{2,p}(H)` whose first-order part lies in `W^{1,p}_0(H)` and which solves `Δu = f` with
`f ∈ Lᵖ(H)` strongly, in the sense that the trace of the weak Hessian of `u` is `f` in `Lᵖ(H)`,
satisfies

`‖D²u‖_{Lᵖ(H)} ≤ C ‖f‖_{Lᵖ(H)}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `ℝ × E`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (a : ℝ) (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))),
      Wkp.firstOrder 1 u ∈ w1p0Submodule volume (normalHalfSpace a) p →
      (traceCLM ℝ (WithLp 2 (ℝ × E))).compLpL p _ (Wkp.iteratedGradient 1 u) = f →
      ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ :=
    exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq (V := WithLp 2 (ℝ × E)) hp
      hp_top
  refine ⟨2 * C, fun a u f hu hf => ?_⟩
  have hvol : (volume : Measure (WithLp 2 (ℝ × E))).restrict
      ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E))) = volume := by
    rw [Opens.coe_top, Measure.restrict_univ]
  -- The odd reflection `w` of `u` lies in `W^{2,p}(ℝ × E)`.
  obtain ⟨w, -, hw⟩ := Wkp.exists_value_ae_eq_sub_comp_normalReflection u hu
  -- The right side of the whole-space estimate for `w` is at most `2 ‖f‖`.
  have hT : ‖(traceCLM ℝ (WithLp 2 (ℝ × E))).compLpL p _ (Wkp.iteratedGradient 1 w)‖ ≤
      2 * ‖f‖ := by
    have hle := eLpNorm_traceCLM_le_of_ae_eq_sub_comp_normalReflection (p := p)
      (Lp.aestronglyMeasurable (Wkp.iteratedGradient 1 u)) hw
    have h₁ : eLpNorm ((traceCLM ℝ (WithLp 2 (ℝ × E))).compLpL p _ (Wkp.iteratedGradient 1 w)) p
        ((volume : Measure (WithLp 2 (ℝ × E))).restrict
          ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E)))) =
        eLpNorm (fun x => traceCLM ℝ (WithLp 2 (ℝ × E)) (Wkp.iteratedGradient 1 w x)) p volume := by
      rw [eLpNorm_congr_ae ((traceCLM ℝ (WithLp 2 (ℝ × E))).coeFn_compLpL
        (Wkp.iteratedGradient 1 w))]
      exact congrArg (fun μ => eLpNorm
        (fun x => traceCLM ℝ (WithLp 2 (ℝ × E)) (Wkp.iteratedGradient 1 w x)) p μ) hvol
    have h₂ : eLpNorm (fun x => traceCLM ℝ (WithLp 2 (ℝ × E)) (Wkp.iteratedGradient 1 u x)) p
        ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) =
        eLpNorm f p
          ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) := by
      rw [← hf]
      exact (eLpNorm_congr_ae ((traceCLM ℝ (WithLp 2 (ℝ × E))).coeFn_compLpL
        (Wkp.iteratedGradient 1 u))).symm
    rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_ofNat, ← ENNReal.toReal_mul, h₁, ← h₂]
    exact ENNReal.toReal_mono (h₂ ▸ ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Lp.eLpNorm_ne_top f))
      hle
  -- On `H` the weak Hessian of `w` is `D²u`.
  have hD : ‖Wkp.iteratedGradient 1 u‖ ≤ ‖Wkp.iteratedGradient 1 w‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) ?_
    exact (eLpNorm_restrict_le_of_ae_eq_sub_comp_normalReflection hw).trans_eq
      (congrArg (fun μ => eLpNorm ⇑(Wkp.iteratedGradient 1 w) p μ) hvol).symm
  calc ‖Wkp.iteratedGradient 1 u‖ ≤ ‖Wkp.iteratedGradient 1 w‖ := hD
    _ ≤ C * ‖(traceCLM ℝ (WithLp 2 (ℝ × E))).compLpL p _ (Wkp.iteratedGradient 1 w)‖ :=
        hC w _ rfl
    _ ≤ C * (2 * ‖f‖) := by gcongr
    _ = (2 * C : ℝ≥0) * ‖f‖ := by push_cast; ring

/-- **The Calderón–Zygmund estimate on a half-space, against test functions.** Let `1 < p < ∞`.
There is a constant `C` such that for every half-space `H = {x | a < x.fst}` of `ℝ × E`, every
`u ∈ W^{2,p}(H)` whose first-order part lies in `W^{1,p}_0(H)` and which solves `Δu = f` with
`f ∈ Lᵖ(H)`, in the sense that `∫ Δφ • u = ∫ φ • f` for every test function `φ` on `H`, satisfies

`‖D²u‖_{Lᵖ(H)} ≤ C ‖f‖_{Lᵖ(H)}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `ℝ × E`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_integral_laplacian_smul_eq_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (a : ℝ) (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))),
      Wkp.firstOrder 1 u ∈ w1p0Submodule volume (normalHalfSpace a) p →
      (∀ φ : 𝓓(normalHalfSpace (E := E) a, ℝ),
        ∫ x, Δ (φ : WithLp 2 (ℝ × E) → ℝ) x • Wkp.value 2 u x = ∫ x, φ x • f x) →
      ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ :=
    exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq_of_normalHalfSpace (E := E)
      hp hp_top
  refine ⟨C, fun a u f hu hf => hC a u f hu ?_⟩
  -- A solution against test functions is a strong solution: the trace of its weak Hessian is `f`.
  have hloc : LocallyIntegrableOn (f : WithLp 2 (ℝ × E) → ℝ) (normalHalfSpace (E := E) a)
      volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp f).locallyIntegrable Fact.out)
  refine Lp.ext ?_
  filter_upwards [(traceCLM ℝ (WithLp 2 (ℝ × E))).coeFn_compLpL (Wkp.iteratedGradient 1 u),
    (Wkp.forall_integral_laplacian_smul_value_eq_iff u hloc).1 hf] with x hx htr
  rw [hx, traceCLM_apply, htr]

/-! ### Constant coefficients -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- For `A` on `ℝ × E` with `λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` and `0 < λ`, there is a linear automorphism `e`
with `e e† = (A + A†) / 2` and `‖e⁻¹ x‖ ≤ ‖x‖ / √λ` that maps each half-space `{a / c < x.fst}`
onto `{a < x.fst}`, for a fixed `c`. -/
private theorem exists_continuousLinearEquiv_preimage_normalHalfSpace
    {A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)} {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ) :
    ∃ (e : WithLp 2 (ℝ × E) ≃L[ℝ] WithLp 2 (ℝ × E)) (c : ℝ),
      (e : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
        (e : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)).adjoint = (2⁻¹ : ℝ) • (A + A.adjoint) ∧
      (∀ x, ‖e.symm x‖ ≤ (√lam)⁻¹ * ‖x‖) ∧ ∀ a : ℝ,
        ((normalHalfSpace (E := E) (a / c) : Opens (WithLp 2 (ℝ × E))) :
          Set (WithLp 2 (ℝ × E))) =
          e ⁻¹' (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) := by
  -- the symmetric part of `A` has the same quadratic form
  have hS : (((2⁻¹ : ℝ) • (A + A.adjoint) : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) :
      WithLp 2 (ℝ × E) →ₗ[ℝ] WithLp 2 (ℝ × E)).IsSymmetric := fun x y => by
    simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
    ring
  have hSA (ξ : WithLp 2 (ℝ × E)) :
      ⟪((2⁻¹ : ℝ) • (A + A.adjoint)) ξ, ξ⟫_ℝ = ⟪A ξ, ξ⟫_ℝ := by
    simp [inner_add_left, inner_smul_left, ContinuousLinearMap.adjoint_inner_left,
      real_inner_comm (A ξ) ξ]
    ring
  set ν : WithLp 2 (ℝ × E) := WithLp.toLp 2 (1, 0)
  have hν : ν ≠ 0 := fun h => one_ne_zero (congrArg (fun x => (WithLp.ofLp x).1) h)
  obtain ⟨e, hee, ⟨c, hc, hcν⟩, he⟩ :=
    ContinuousLinearMap.exists_continuousLinearEquiv_comp_adjoint_eq_of_isSymmetric _ hS hlam
      (fun ξ => (hSA ξ).symm ▸ hA ξ) hν
  have hinner (x : WithLp 2 (ℝ × E)) : ⟪x, ν⟫_ℝ = (WithLp.ofLp x).1 := by
    simp [ν, WithLp.prod_inner_apply]
  -- `(e y).fst = ⟪e y, ν⟫ = ⟪y, e† ν⟫ = c y.fst`
  have hfst (y : WithLp 2 (ℝ × E)) : (WithLp.ofLp (e y)).1 = c * (WithLp.ofLp y).1 := by
    rw [← hinner, ← ContinuousLinearEquiv.coe_coe, ← ContinuousLinearMap.adjoint_inner_right,
      hcν, inner_smul_right, hinner]
  refine ⟨e, c, hee, he, fun a => ?_⟩
  ext y
  simp only [mem_preimage, SetLike.mem_coe, mem_normalHalfSpace, hfst, div_lt_iff₀' hc]

/-- **The Calderón–Zygmund estimate on a half-space, for constant coefficients.** Let
`1 < p < ∞`. There is a constant `C` such that for every operator `A` on `ℝ × E` with
`λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` and `0 < λ`, every half-space `H = {x | a < x.fst}`, and every
`u ∈ W^{2,p}(H)` whose first-order part lies in `W^{1,p}_0(H)` and which solves `tr (A D²u) = f`
almost everywhere on `H`, with `f ∈ Lᵖ(H)`,

`‖D²u‖_{Lᵖ(H)} ≤ (C / λ) ‖f‖_{Lᵖ(H)}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `ℝ × E`. The constant depends only on `E` and `p`, not on `A` beyond `λ` and not
on `a`. Only the symmetric part of `A` enters, since `D²u` is self-adjoint almost everywhere. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_comp_eq_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ {A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)} {lam : ℝ}, 0 < lam →
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ) →
      ∀ (a : ℝ) (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict
          (normalHalfSpace (E := E) a))),
        Wkp.firstOrder 1 u ∈ w1p0Submodule volume (normalHalfSpace a) p →
        (∀ᵐ x ∂((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A ∘L Wkp.iteratedGradient 1 u x) = f x) →
        ‖Wkp.iteratedGradient 1 u‖ ≤ C / lam * ‖f‖ := by
  obtain ⟨C, hC⟩ :=
    exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq_of_normalHalfSpace (E := E)
      hp hp_top
  refine ⟨C, fun {A lam} hlam hA a u f hu hf => ?_⟩
  -- A linear change of variables `e` with `e e† = (A + A†) / 2` maps the half-space
  -- `{a / c < x.fst}` onto `{a < x.fst}` and turns the equation into Poisson's equation.
  obtain ⟨e, c, hee, he, hH⟩ := exists_continuousLinearEquiv_preimage_normalHalfSpace hlam hA
  obtain ⟨v, -, hD, h0⟩ := Wkp.exists_value_ae_eq_comp_continuousLinearEquiv hp_top e (hH a) u
  refine Wkp.norm_iteratedGradient_le_of_ae_eq_adjoint_comp_comp e hee hlam he (hH a) hD ?_
    fun g hg => hC (a / c) v g (h0 hu) hg
  filter_upwards [hf, Wkp.adjoint_iteratedGradient_one_ae_eq u] with x h1 h2
  rw [A.traceCLM_symmPart_comp _ h2, h1]

/-- **The Calderón–Zygmund estimate on a half-space for coefficients of small oscillation.** Let
`1 < p < ∞`. There are constants `C` and `δ > 0`, depending only on `E` and `p`, with the
following property. Let `H = {x | a < x.fst}` be a half-space of `ℝ × E`, let `s` be a closed set,
let `A₀` be an operator on `ℝ × E` with `λ ‖ξ‖² ≤ ⟪A₀ ξ, ξ⟫` and `0 < λ`, and let `A` be a field of
endomorphisms of `ℝ × E` with `‖A x - A₀‖ ≤ ε` for almost every `x ∈ s ∩ H`, where `ε ≤ δ λ`. Then
every `u ∈ W^{2,p}(H)` whose first-order part lies in `W^{1,p}_0(H)`, which vanishes almost
everywhere on `H \ s`, and which solves the non-divergence-form equation `tr (A ∘ D²u) = f` almost
everywhere on `H`, with `f ∈ Lᵖ(H)`, satisfies

`‖D²u‖_{Lᵖ(H)} ≤ (C / λ) ‖f‖_{Lᵖ(H)}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `ℝ × E`. Since the weak Hessian is symmetric, in an orthonormal basis
`tr (A ∘ D²u) = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu`, where `aᵢⱼ` are the matrix entries of `A`. Neither `A₀` nor `A`
need be symmetric, and no measurability or continuity of `A` is assumed. -/
theorem
    exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ (a : ℝ) {A₀ : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
      {lam : ℝ}, 0 < lam → (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A₀ ξ, ξ⟫_ℝ) →
      ∀ {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
        {s : Set (WithLp 2 (ℝ × E))} {ε : ℝ}, IsClosed s → ε ≤ δ * lam →
      (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
        x ∈ s → ‖A x - A₀‖ ≤ ε) →
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))),
        Wkp.firstOrder 1 u ∈ w1p0Submodule volume (normalHalfSpace a) p →
        (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
          x ∉ s → Wkp.value 2 u x = 0) →
        (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) = f x) →
        ‖Wkp.iteratedGradient 1 u‖ ≤ C / lam * ‖f‖ := by
  obtain ⟨C, hC⟩ :=
    exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_comp_eq_of_normalHalfSpace (E := E)
      hp hp_top
  set N : ℝ := (Module.finrank ℝ (WithLp 2 (ℝ × E)) : ℝ)
  have hN : 0 < N := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨2 * C, 1 / (2 * (C + 1) * N), by positivity,
    fun a {A₀ lam} hlam hA₀ {A s ε} hs hε hA u f hu hus hf => ?_⟩
  set D := Wkp.iteratedGradient 1 u
  -- The frozen operator `M ↦ tr (A₀ ∘ M)`, applied to the weak Hessian.
  set T : (WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) →L[ℝ] ℝ :=
    (traceCLM ℝ (WithLp 2 (ℝ × E))).comp
      (ContinuousLinearMap.compL ℝ (WithLp 2 (ℝ × E)) (WithLp 2 (ℝ × E)) (WithLp 2 (ℝ × E)) A₀)
  set g := T.compLpL p _ D
  -- The weak Hessian vanishes on `H \ s`, where `u` does.
  have hD0 : ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
      x ∉ s → D x = 0 :=
    Wkp.iteratedGradient_ae_eq_zero_of_value_ae_eq_zero_of_isOpen 1 u hs.isOpen_compl hus
  -- The constant-coefficient estimate, applied to `tr (A₀ ∘ D²u)`.
  have hDg : ‖D‖ ≤ C / lam * ‖g‖ := hC hlam hA₀ a u g hu (by
    filter_upwards [T.coeFn_compLpL D] with x hx
    rw [hx, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply])
  -- Freezing the coefficients at `A₀` costs at most `N ε |D²u|` pointwise.
  have hgf : ‖g - f‖ ≤ N * ε * ‖D‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [Lp.coeFn_sub g f, T.coeFn_compLpL D, hf, hA, hD0]
      with x hsub hgx hfx hAx hDx
    rw [hsub, Pi.sub_apply, hgx, ← hfx]
    by_cases hxs : x ∈ s
    · -- On `s`, the difference is minus the trace of `(A x - A₀) ∘ D²u`.
      have hdiff : T (D x) - traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L D x) =
          -traceCLM ℝ (WithLp 2 (ℝ × E)) ((A x - A₀) ∘L D x) := by
        simp [T, ContinuousLinearMap.sub_comp]
      rw [hdiff, norm_neg]
      calc ‖traceCLM ℝ (WithLp 2 (ℝ × E)) ((A x - A₀) ∘L D x)‖
          ≤ N * ‖(A x - A₀) ∘L D x‖ := ContinuousLinearMap.norm_traceCLM_le _
        _ ≤ N * (‖A x - A₀‖ * ‖D x‖) := by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ N * (ε * ‖D x‖) := by gcongr; exact hAx hxs
        _ = N * ε * ‖D x‖ := by ring
    · rw [hDx hxs]
      simp
  -- Hence `‖g‖ ≤ ‖f‖ + N ε ‖D²u‖`, and the error term is absorbed on the left.
  rw [NNReal.coe_mul, NNReal.coe_ofNat]
  exact PDE.le_two_mul_div_mul_of_le_div_mul_of_le_add hlam C.coe_nonneg hN hε (norm_nonneg _) hDg
    (by linarith [norm_sub_norm_le g f])

end TauCeti
