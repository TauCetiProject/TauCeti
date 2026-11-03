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
import TauCeti.Analysis.Sobolev.Wkp.Laplacian
import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.MeasureTheory.Function.Lp.Precomposition
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

For constant coefficients, only the symmetric part `S = (A + A†) / 2` of `A` enters, because the
weak Hessian is self-adjoint almost everywhere (`TauCeti.Wkp.adjoint_iteratedGradient_one_ae_eq`).
Write `S = e e†` for a linear automorphism `e` whose adjoint maps the normal `(1, 0)` to a
positive multiple `c (1, 0)`
(`TauCeti.exists_continuousLinearEquiv_comp_adjoint_eq_of_isSymmetric`). Then `e` maps the
half-space `{a / c < x.fst}` onto `H`, and `v = u ∘ e` lies in `W^{2,p}` of that half-space, with
zero boundary values and weak Hessian `e† ∘ D²u(e ·) ∘ e`
(`TauCeti.Wkp.exists_value_ae_eq_comp_continuousLinearEquiv`). Its trace is
`tr (D²u(e ·) e e†) = tr (S D²u) ∘ e = f ∘ e`, so the estimate for the Laplacian applies to `v`.
Since `‖e⁻¹‖ ≤ λ^(-1/2)`, `‖D²u ∘ e‖ ≤ λ⁻¹ ‖D²v‖` pointwise, and changing variables multiplies
the `Lᵖ` norms of `D²u ∘ e` and of `f ∘ e` by the same Jacobian factor.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.9 and §9.5, Lemma 9.12 (the estimate near a flat boundary portion, by reflection),
  and Section 6.1 (reduction of a constant-coefficient operator to the Laplacian by a linear change
  of variables).
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

/-- If `‖e⁻¹ x‖ ≤ ‖x‖ / √λ` for all `x`, then `‖M‖ ≤ λ⁻¹ ‖e† ∘ M ∘ e‖`. -/
private theorem norm_le_inv_mul_norm_adjoint_comp_comp {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] (e : V ≃L[ℝ] V) {lam : ℝ} (hlam : 0 < lam)
    (he : ∀ x, ‖e.symm x‖ ≤ (√lam)⁻¹ * ‖x‖) (M : V →L[ℝ] V) :
    ‖M‖ ≤ lam⁻¹ * ‖(e : V →L[ℝ] V).adjoint ∘L M ∘L (e : V →L[ℝ] V)‖ := by
  have hK : ‖(e.symm : V →L[ℝ] V)‖ ≤ (√lam)⁻¹ :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) he
  -- `M = (e⁻¹)† ∘ (e† ∘ M ∘ e) ∘ e⁻¹`
  have hM : M = (e.symm : V →L[ℝ] V).adjoint ∘L
      ((e : V →L[ℝ] V).adjoint ∘L M ∘L (e : V →L[ℝ] V)) ∘L (e.symm : V →L[ℝ] V) := by
    ext x
    refine ext_inner_right ℝ fun z => ?_
    simp [ContinuousLinearMap.adjoint_inner_left]
  set N := (e : V →L[ℝ] V).adjoint ∘L M ∘L (e : V →L[ℝ] V)
  calc ‖M‖ = ‖(e.symm : V →L[ℝ] V).adjoint ∘L N ∘L (e.symm : V →L[ℝ] V)‖ := by rw [← hM]
    _ ≤ ‖(e.symm : V →L[ℝ] V).adjoint‖ * (‖N‖ * ‖(e.symm : V →L[ℝ] V)‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (√lam)⁻¹ * (‖N‖ * (√lam)⁻¹) := by
        rw [LinearIsometryEquiv.norm_map]
        gcongr
    _ = lam⁻¹ * ‖N‖ := by
        rw [mul_comm ‖N‖, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hlam.le]

/-- **Transferring the estimate along a linear change of variables.** Let `e e† = A` with
`‖e⁻¹ x‖ ≤ ‖x‖ / √λ`, let `U = e⁻¹(W)`, and let `v ∈ W^{2,p}(U)` have weak Hessian
`e† ∘ D²u(e ·) ∘ e`. If `u` solves `tr (A D²u) = f` on `W` and the Hessian of `v` is bounded by
`C` times the norm of its trace, then `‖D²u‖ ≤ (C / λ) ‖f‖`. -/
private theorem norm_iteratedGradient_le_of_ae_eq_adjoint_comp_comp {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] {A : V →L[ℝ] V} (e : V ≃L[ℝ] V) (hee : (e : V →L[ℝ] V) ∘L
      (e : V →L[ℝ] V).adjoint = A) {lam : ℝ} (hlam : 0 < lam)
    (he : ∀ x, ‖e.symm x‖ ≤ (√lam)⁻¹ * ‖x‖) {U W : Opens V} (hUW : (U : Set V) = e ⁻¹' W)
    {u : Wkp (volume : Measure V) W p 2} {v : Wkp (volume : Measure V) U p 2}
    (hD : Wkp.iteratedGradient 1 v =ᵐ[volume.restrict U] fun x =>
      (e : V →L[ℝ] V).adjoint ∘L Wkp.iteratedGradient 1 u (e x) ∘L (e : V →L[ℝ] V))
    {f : Lp ℝ p ((volume : Measure V).restrict W)}
    (hf : ∀ᵐ x ∂((volume : Measure V).restrict W),
      traceCLM ℝ V (A ∘L Wkp.iteratedGradient 1 u x) = f x)
    {C : ℝ} (hv : ∀ g : Lp ℝ p ((volume : Measure V).restrict U),
      (traceCLM ℝ V).compLpL p _ (Wkp.iteratedGradient 1 v) = g →
        ‖Wkp.iteratedGradient 1 v‖ ≤ C * ‖g‖) :
    ‖Wkp.iteratedGradient 1 u‖ ≤ C / lam * ‖f‖ := by
  have habs : 0 < |(e : V →L[ℝ] V).det| :=
    abs_pos.2 (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hmap : ((volume : Measure V).restrict U).map e ≤
      (ENNReal.ofReal |(e : V →L[ℝ] V).det|)⁻¹ • (volume : Measure V).restrict W :=
    map_restrict_le_smul_restrict_of_differentiableOn volume U.isOpen
      e.differentiable.differentiableOn e.injective.injOn (hUW ▸ mapsTo_preimage _ _) habs
      fun x _ => by rw [e.fderiv]
  have hC' : (ENNReal.ofReal |(e : V →L[ℝ] V).det|)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 habs).ne'
  have hqmp := QuasiMeasurePreserving.of_map_le_smul e.continuous.measurable hmap
  -- `v` solves Poisson's equation with forcing term `f ∘ e`
  set f' := Lp.compOfMapLeSmul ℝ e.continuous.measurable hC' hmap f
  have hf'e := Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) e.continuous.measurable hC' hmap f
  have hv' := hv f' <| Lp.ext <| by
    filter_upwards [(traceCLM ℝ V).coeFn_compLpL (Wkp.iteratedGradient 1 v), hD, hf'e,
      hqmp.ae hf] with y h1 h2 h3 h4
    -- `tr (e† M e) = tr (M e e†) = tr (M A) = tr (A M)`
    rw [h1, h2, h3, Function.comp_apply, ← h4, traceCLM_comp_comm, ContinuousLinearMap.comp_assoc,
      hee, traceCLM_comp_comm]
  -- Both sides change by the same Jacobian factor `δ` under the change of variables.
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ENNReal.ofReal |(LinearMap.det (e : V →ₗ[ℝ] V))⁻¹| ^ (1 / p).toReal :=
    ⟨_, rfl⟩
  have hf' : eLpNorm f' p ((volume : Measure V).restrict U) =
      δ * eLpNorm f p ((volume : Measure V).restrict W) := by
    rw [eLpNorm_congr_ae hf'e, hUW, hδ]
    exact eLpNorm_comp_continuousLinearEquiv_restrict_preimage volume _ e p
  have hDu : δ * eLpNorm (Wkp.iteratedGradient 1 u) p ((volume : Measure V).restrict W) ≤
      ENNReal.ofReal lam⁻¹ * eLpNorm (Wkp.iteratedGradient 1 v) p
        ((volume : Measure V).restrict U) := by
    have hcomp := eLpNorm_comp_continuousLinearEquiv_restrict_preimage (volume : Measure V)
      (⇑(Wkp.iteratedGradient 1 u)) e p (s := (W : Set V))
    rw [← hδ, ← hUW] at hcomp
    rw [← hcomp]
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((Lp.aestronglyMeasurable _).comp_quasiMeasurePreserving hqmp) ?_ p
    filter_upwards [hD] with y hy
    rw [hy, Function.comp_apply]
    exact norm_le_inv_mul_norm_adjoint_comp_comp e hlam he (Wkp.iteratedGradient 1 u (e y))
  -- Back to real norms, cancelling `δ`.
  have hδr : 0 < δ.toReal := by
    rw [hδ, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (abs_nonneg _)]
    exact Real.rpow_pos_of_pos (abs_pos.2 (inv_ne_zero
      (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero)) _
  have h1 := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _)) hDu
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hlam.le),
    ← Lp.norm_def, ← Lp.norm_def] at h1
  have h2 : ‖f'‖ = δ.toReal * ‖f‖ := by
    rw [Lp.norm_def, Lp.norm_def, hf', ENNReal.toReal_mul]
  refine le_of_mul_le_mul_left ?_ hδr
  calc δ.toReal * ‖Wkp.iteratedGradient 1 u‖ ≤ lam⁻¹ * ‖Wkp.iteratedGradient 1 v‖ := h1
    _ ≤ lam⁻¹ * (C * (δ.toReal * ‖f‖)) := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_left hv' (inv_nonneg.2 hlam.le)
    _ = δ.toReal * (C / lam * ‖f‖) := by ring

/-- Only the symmetric part `(A + A†) / 2` of `A` enters `tr (A M)` for self-adjoint `M`. -/
private theorem traceCLM_symmPart_comp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (A M : V →L[ℝ] V) (hM : M.adjoint = M) :
    traceCLM ℝ V (((2⁻¹ : ℝ) • (A + A.adjoint)) ∘L M) = traceCLM ℝ V (A ∘L M) := by
  -- `tr (A† M) = tr ((M A)†) = tr (M A) = tr (A M)`
  have h : traceCLM ℝ V (A.adjoint ∘L M) = traceCLM ℝ V (A ∘L M) := by
    conv_lhs => rw [← hM, ← ContinuousLinearMap.adjoint_comp]
    rw [traceCLM_apply, ContinuousLinearMap.trace_adjoint, RCLike.conj_to_real, ← traceCLM_apply,
      traceCLM_comp_comm]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.add_comp, map_smul, map_add, h,
    smul_eq_mul]
  ring

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
    exists_continuousLinearEquiv_comp_adjoint_eq_of_isSymmetric _ hS hlam
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
  refine norm_iteratedGradient_le_of_ae_eq_adjoint_comp_comp e hee hlam he (hH a) hD ?_
    fun g hg => hC (a / c) v g (h0 hu) hg
  filter_upwards [hf, Wkp.adjoint_iteratedGradient_one_ae_eq u] with x h1 h2
  rw [traceCLM_symmPart_comp A _ h2, h1]

end TauCeti
