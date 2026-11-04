/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Sobolev
public import TauCeti.Analysis.Sobolev.Trace.OddReflection
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

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.9 and §9.5, Lemma 9.12 (the estimate near a flat boundary portion, by reflection).
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

end TauCeti
