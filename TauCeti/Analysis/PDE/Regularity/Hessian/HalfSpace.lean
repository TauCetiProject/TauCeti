/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Sobolev
public import TauCeti.Analysis.Sobolev.Trace.OddReflection
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

The estimate extends to strong solutions of the non-divergence-form equation `tr (A ∘ D²u) = f`
whose coefficient field `A` is uniformly close to a positive multiple of the identity,
`‖A x - μ • 1‖ ≤ δ μ` with `δ` depending only on `E` and `p`: then `‖D²u‖ ≤ (C / μ) ‖f‖`
(in namespace `TauCeti`,
`exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace`).
As in the whole-space estimate for coefficients of small oscillation, the coefficients need only be
controlled on a closed set `s` outside which `u` vanishes, which is the situation after cutting
`u` off near a boundary point. A general constant elliptic matrix is not covered: unlike on the
whole space, the linear change of variables turning it into the Laplacian must also preserve the
half-space.

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

For variable coefficients, freeze them at `μ • 1`:
`μ tr D²u = f - tr ((A - μ • 1) ∘ D²u)`. The weak Hessian vanishes where `u` does
(`TauCeti.Wkp.iteratedGradient_ae_eq_zero_of_value_ae_eq_zero_of_isOpen`), and on `s` the error
term is at most `dim (ℝ × E) · δ μ ‖D²u‖` pointwise (`ContinuousLinearMap.norm_traceCLM_le`). The
estimate for the Laplacian then gives `‖D²u‖ ≤ (C₀ / μ) (‖f‖ + dim (ℝ × E) δ μ ‖D²u‖)`, and the
choice of `δ` makes the coefficient of `‖D²u‖` on the right at most `1 / 2`, so it is absorbed
(`TauCeti.PDE.le_two_mul_div_mul_of_le_div_mul_of_le_add`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.9 and §9.5, Lemma 9.12 (the estimate near a flat boundary portion, by reflection),
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

/-- **The Calderón–Zygmund estimate on a half-space for coefficients of small oscillation.** Let
`1 < p < ∞`. There are constants `C` and `δ > 0`, depending only on `E` and `p`, with the
following property. Let `H = {x | a < x.fst}` be a half-space of `ℝ × E`, let `s` be a closed set,
let `μ > 0`, and let `A` be a field of endomorphisms of `ℝ × E` with `‖A x - μ • 1‖ ≤ ε` for almost
every `x ∈ s ∩ H`, where `ε ≤ δ μ`. Then every `u ∈ W^{2,p}(H)` whose first-order part lies in
`W^{1,p}_0(H)`, which vanishes almost everywhere on `H \ s`, and which solves the
non-divergence-form equation `tr (A ∘ D²u) = f` almost everywhere on `H`, with `f ∈ Lᵖ(H)`,
satisfies

`‖D²u‖_{Lᵖ(H)} ≤ (C / μ) ‖f‖_{Lᵖ(H)}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `ℝ × E`. Since the weak Hessian is symmetric, in an orthonormal basis
`tr (A ∘ D²u) = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu`, where `aᵢⱼ` are the matrix entries of `A`. No measurability or
continuity of `A` is assumed. -/
theorem
    exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ (a : ℝ)
      {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
      {s : Set (WithLp 2 (ℝ × E))} {μ ε : ℝ}, 0 < μ → IsClosed s → ε ≤ δ * μ →
      (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
        x ∈ s → ‖A x - μ • 1‖ ≤ ε) →
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))),
        Wkp.firstOrder 1 u ∈ w1p0Submodule volume (normalHalfSpace a) p →
        (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
          x ∉ s → Wkp.value 2 u x = 0) →
        (∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) = f x) →
        ‖Wkp.iteratedGradient 1 u‖ ≤ C / μ * ‖f‖ := by
  obtain ⟨C, hC⟩ :=
    exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq_of_normalHalfSpace (E := E)
      hp hp_top
  set N : ℝ := (Module.finrank ℝ (WithLp 2 (ℝ × E)) : ℝ)
  have hN : 0 < N := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨2 * C, 1 / (2 * (C + 1) * N), by positivity,
    fun a {A s μ ε} hμ hs hε hA u f hu hus hf => ?_⟩
  set D := Wkp.iteratedGradient 1 u
  set g := (traceCLM ℝ (WithLp 2 (ℝ × E))).compLpL p _ D
  -- The weak Hessian vanishes on `H \ s`, where `u` does.
  have hD0 : ∀ᵐ x ∂(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a),
      x ∉ s → D x = 0 :=
    Wkp.iteratedGradient_ae_eq_zero_of_value_ae_eq_zero_of_isOpen 1 u hs.isOpen_compl hus
  -- The half-space estimate for the Laplacian, applied to the trace of the weak Hessian.
  have hDg : ‖D‖ ≤ C * ‖g‖ := hC a u g hu rfl
  -- Freezing the coefficients at `μ • 1` costs at most `N ε |D²u|` pointwise.
  have hgf : ‖μ • g - f‖ ≤ N * ε * ‖D‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [Lp.coeFn_sub (μ • g) f, Lp.coeFn_smul μ g,
      (traceCLM ℝ (WithLp 2 (ℝ × E))).coeFn_compLpL D, hf, hA, hD0]
      with x hsub hsmul hgx hfx hAx hDx
    rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hgx, ← hfx]
    by_cases hxs : x ∈ s
    · -- On `s`, the difference is minus the trace of `(A x - μ • 1) ∘ D²u`.
      have hdiff : μ • traceCLM ℝ (WithLp 2 (ℝ × E)) (D x) -
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L D x) =
          -traceCLM ℝ (WithLp 2 (ℝ × E)) ((A x - μ • 1) ∘L D x) := by
        simp [ContinuousLinearMap.sub_comp, ContinuousLinearMap.one_def]
      rw [hdiff, norm_neg]
      calc ‖traceCLM ℝ (WithLp 2 (ℝ × E)) ((A x - μ • 1) ∘L D x)‖
          ≤ N * ‖(A x - μ • 1) ∘L D x‖ := ContinuousLinearMap.norm_traceCLM_le _
        _ ≤ N * (‖A x - μ • 1‖ * ‖D x‖) := by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ N * (ε * ‖D x‖) := by gcongr; exact hAx hxs
        _ = N * ε * ‖D x‖ := by ring
    · rw [hDx hxs]
      simp
  -- Hence `‖μ • g‖ ≤ ‖f‖ + N ε ‖D²u‖`, and the error term is absorbed on the left.
  have hDμg : ‖D‖ ≤ C / μ * ‖μ • g‖ := by
    rw [norm_smul, Real.norm_of_nonneg hμ.le, ← mul_assoc, div_mul_cancel₀ _ hμ.ne']
    exact hDg
  rw [NNReal.coe_mul, NNReal.coe_ofNat]
  exact PDE.le_two_mul_div_mul_of_le_div_mul_of_le_add hμ C.coe_nonneg hN hε (norm_nonneg _) hDμg
    (by linarith [norm_sub_norm_le (μ • g) f])

end TauCeti
