/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Sobolev
public import TauCeti.Analysis.Sobolev.Trace.OddReflection
import TauCeti.Analysis.Sobolev.Wkp.Laplacian
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The Calderón–Zygmund estimate on a half-space with zero boundary values

Let `H = {x | a < x.fst}` be a half-space of the Euclidean product `ℝ × E`, with `E` a
finite-dimensional real inner product space, and let `1 < p < ∞`. This file proves the boundary
`W^{2,p}` estimate for the Laplacian on `H`: there is a constant `C`, depending only on `p` and
`E` (that is, on `p` and the dimension) and not on `a`, such that every `u ∈ W^{2,p}(H)` whose
first-order part lies in `W^{1,p}_0(H)`, and which solves `Δu = f` with `f ∈ Lᵖ(H)`, satisfies

`‖D²u‖_{Lᵖ(H)} ≤ C ‖f‖_{Lᵖ(H)}`.

The equation is taken either strongly, the trace of the weak Hessian of `u` being `f` in `Lᵖ(H)`
(`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq_of_normalHalfSpace`),
or against test functions supported in `H`
(`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_integral_laplacian_smul_eq_of_normalHalfSpace`
).

In contrast to the interior estimates, the right side involves only `f`: no lower-order norm of
`u` and no shrinking of the domain. The zero boundary condition is what makes this possible.
Without it the estimate fails: for `E = ℝ` and `p > 2`, the real part of `1 / (z + 1)` on the
right half-plane lies in `W^{2,p}`, is harmonic, and has nonzero Hessian. This is the model case of
the global `W^{2,p}` estimate on a domain, where the boundary is flattened in local charts.

## The argument

The odd reflection `v` of `u` across the boundary hyperplane lies in `W^{2,p}(ℝ × E)`
(`TauCeti.Wkp.exists_value_ae_eq_sub_comp_normalReflection`), and its weak Hessian is `D²u` on `H`
and `R ∘ D²u(ρ x) ∘ R` up to sign on the other side, where `ρ` is the reflection in the boundary
hyperplane and `R` its linear part. Since `R` is an involution, the trace of `R ∘ M ∘ R` is the
trace of `M`, so `Δv` is the odd reflection of `f`, whose `Lᵖ` norm is at most `2 ‖f‖_{Lᵖ(H)}`.
The whole-space estimate
(`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq`) bounds `D²v`, and
`D²u` is the restriction of `D²v` to `H`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.13 and its proof (boundary `Lᵖ` estimates via a flat boundary portion).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Lemma 9.2 (extension by reflection across a hyperplane).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal Laplacian Distributions

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Conjugating by the reflection `R (s, z) = (-s, z)` preserves the trace of an endomorphism. -/
private theorem traceCLM_normalLinearReflection_comp_comp
    (M : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) :
    traceCLM ℝ (WithLp 2 (ℝ × E))
        (((normalLinearReflection E).toContinuousLinearEquiv :
            WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L M ∘L
          ((normalLinearReflection E).toContinuousLinearEquiv :
            WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))) =
      traceCLM ℝ (WithLp 2 (ℝ × E)) M := by
  set R : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E) :=
    ((normalLinearReflection E).toContinuousLinearEquiv :
      WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))
  have hRR : R ∘L R = ContinuousLinearMap.id ℝ _ := by
    ext x
    exact normalLinearReflection_normalLinearReflection x
  rw [traceCLM_apply, traceCLM_apply, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm', LinearMap.comp_assoc,
    ← ContinuousLinearMap.toLinearMap_comp, hRR, ContinuousLinearMap.coe_id, LinearMap.comp_id]

variable [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞}

/-- An endomorphism field `w` on `ℝ × E` that is the odd reflection of a field `d` on the
half-space `H = {x | a < x.fst}`, in the sense of
`TauCeti.Wkp.exists_value_ae_eq_sub_comp_normalReflection`, agrees with `d` on `H`. -/
private theorem ae_restrict_eq_of_ae_eq_sub_comp_normalReflection {a : ℝ}
    {d w : WithLp 2 (ℝ × E) → IteratedGradient (WithLp 2 (ℝ × E)) 1}
    (hw : w =ᵐ[volume] fun x =>
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator d x -
        ((normalLinearReflection E).toContinuousLinearEquiv :
            WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator d
            (normalReflection E a x) ∘L
          ((normalLinearReflection E).toContinuousLinearEquiv :
            WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))) :
    d =ᵐ[volume.restrict (normalHalfSpace (E := E) a)] w := by
  have hH := (normalHalfSpace (E := E) a).isOpen.measurableSet
  filter_upwards [ae_restrict_mem hH, ae_restrict_of_ae hw] with x hx hwx
  have hρx : normalReflection E a x ∉ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) :=
    fun h => lt_asymm ((mem_normalHalfSpace a x).1 hx)
      ((normalReflection_mem_normalHalfSpace_iff a x).1 h)
  rw [hwx, indicator_of_mem hx, indicator_of_notMem hρx, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero, sub_zero]

/-- The trace of the odd reflection `w` of an endomorphism field `d` on the half-space
`H = {x | a < x.fst}` is the odd reflection of the trace of `d`, so its `Lᵖ` norm on `ℝ × E` is at
most twice the `Lᵖ` norm of the trace of `d` on `H`. -/
private theorem eLpNorm_traceCLM_le_of_ae_eq_sub_comp_normalReflection [Fact (1 ≤ p)] {a : ℝ}
    {d w : WithLp 2 (ℝ × E) → IteratedGradient (WithLp 2 (ℝ × E)) 1}
    (hd : AEStronglyMeasurable d (volume.restrict (normalHalfSpace (E := E) a)))
    (hw : w =ᵐ[volume] fun x =>
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator d x -
        ((normalLinearReflection E).toContinuousLinearEquiv :
            WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) ∘L
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator d
            (normalReflection E a x) ∘L
          ((normalLinearReflection E).toContinuousLinearEquiv :
            WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))) :
    eLpNorm (fun x => traceCLM ℝ (WithLp 2 (ℝ × E)) (w x)) p volume ≤
      2 * eLpNorm (fun x => traceCLM ℝ (WithLp 2 (ℝ × E)) (d x)) p
        (volume.restrict (normalHalfSpace (E := E) a)) := by
  set H := (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
  have hH : MeasurableSet H := (normalHalfSpace (E := E) a).isOpen.measurableSet
  have hρ := measurePreserving_normalReflection (E := E) a
  set T := traceCLM ℝ (WithLp 2 (ℝ × E))
  -- The trace of `w` is the odd reflection of `φ`, the trace of `d` extended by zero off `H`.
  obtain ⟨φ, hφ⟩ : ∃ φ : WithLp 2 (ℝ × E) → ℝ, φ = H.indicator fun x => T (d x) := ⟨_, rfl⟩
  have hφm : AEStronglyMeasurable φ volume :=
    hφ ▸ (aestronglyMeasurable_indicator_iff hH).2 (T.continuous.comp_aestronglyMeasurable hd)
  have hTφ (y : WithLp 2 (ℝ × E)) : T (H.indicator d y) = φ y := by
    by_cases hy : y ∈ H <;> simp [hφ, hy]
  have hae : (fun x => T (w x)) =ᵐ[volume] φ - φ ∘ normalReflection E a := by
    filter_upwards [hw] with x hwx
    rw [hwx, map_sub, traceCLM_normalLinearReflection_comp_comp, hTφ, hTφ, Pi.sub_apply,
      Function.comp_apply]
  calc eLpNorm (fun x => T (w x)) p volume
      = eLpNorm (φ - φ ∘ normalReflection E a) p volume := eLpNorm_congr_ae hae
    _ ≤ eLpNorm φ p volume + eLpNorm (φ ∘ normalReflection E a) p volume :=
      eLpNorm_sub_le Fact.out
    _ = 2 * eLpNorm (fun x => T (d x)) p (volume.restrict H) := by
      rw [eLpNorm_comp_measurePreserving hφm hρ, ← two_mul, hφ,
        eLpNorm_indicator_eq_eLpNorm_restrict hH.nullMeasurableSet]

variable [Fact (1 ≤ p)]

/-- **The Calderón–Zygmund estimate on a half-space with zero boundary values.** Let `1 < p < ∞`.
There is a constant `C` such that, for every half-space `H = {x | a < x.fst}` of `ℝ × E`, every
`u ∈ W^{2,p}(H)` with first-order part in `W^{1,p}_0(H)` solving `Δu = f` with `f ∈ Lᵖ(H)`
strongly, in the sense that the trace of the weak Hessian of `u` is `f` in `Lᵖ(H)`, satisfies

`‖D²u‖_{Lᵖ(H)} ≤ C ‖f‖_{Lᵖ(H)}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `ℝ × E`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (a : ℝ)
      (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))),
      Wkp.firstOrder 1 u ∈ w1p0Submodule volume (normalHalfSpace a) p →
      (traceCLM ℝ (WithLp 2 (ℝ × E))).compLpL p _ (Wkp.iteratedGradient 1 u) = f →
      ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq
    (F := WithLp 2 (ℝ × E)) hp hp_top
  refine ⟨2 * C, fun a u f hu hf => ?_⟩
  set T := traceCLM ℝ (WithLp 2 (ℝ × E))
  subst hf
  -- The odd reflection `v` of `u` is a whole-space Sobolev function, so the whole-space estimate
  -- bounds its weak Hessian by the trace `g` of that Hessian.
  obtain ⟨v, -, hvD⟩ := Wkp.exists_value_ae_eq_sub_comp_normalReflection u hu
  obtain ⟨g, hg⟩ : ∃ g, T.compLpL p _ (Wkp.iteratedGradient 1 v) = g := ⟨_, rfl⟩
  have hv : ‖Wkp.iteratedGradient 1 v‖ ≤ C * ‖g‖ := hC v g hg
  -- The weak Hessian of `u` is the restriction of that of `v` to the half-space.
  have hDv : ‖Wkp.iteratedGradient 1 u‖ ≤ ‖Wkp.iteratedGradient 1 v‖ := by
    rw [Lp.norm_def, Lp.norm_def,
      eLpNorm_congr_ae (ae_restrict_eq_of_ae_eq_sub_comp_normalReflection hvD)]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
      (eLpNorm_mono_measure _ (Measure.restrict_mono (by simp) le_rfl))
  -- The trace `g` is the odd reflection of `f`.
  have hf' := eLpNorm_congr_ae (p := p) (T.coeFn_compLpL (Wkp.iteratedGradient 1 u))
  have hgf := eLpNorm_traceCLM_le_of_ae_eq_sub_comp_normalReflection (p := p)
    (Lp.aestronglyMeasurable (Wkp.iteratedGradient 1 u)) hvD
  have hΔv : ‖g‖ ≤ 2 * ‖T.compLpL p _ (Wkp.iteratedGradient 1 u)‖ := by
    rw [Lp.norm_def, Lp.norm_def, ← hg,
      eLpNorm_congr_ae (T.coeFn_compLpL (Wkp.iteratedGradient 1 v)), hf',
      ← ENNReal.toReal_ofNat 2, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ?_)
      ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans hgf)
    rw [← hf']
    exact Lp.eLpNorm_ne_top _
  calc ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖g‖ := hDv.trans hv
    _ ≤ C * (2 * _) := mul_le_mul_of_nonneg_left hΔv C.coe_nonneg
    _ = _ := by push_cast; ring

/-- **The Calderón–Zygmund estimate on a half-space with zero boundary values, against test
functions.** Let `1 < p < ∞`. There is a constant `C` such that, for every half-space
`H = {x | a < x.fst}` of `ℝ × E`, every `u ∈ W^{2,p}(H)` with first-order part in `W^{1,p}_0(H)`
solving `Δu = f` with `f ∈ Lᵖ(H)`, in the sense that `∫ Δφ • u = ∫ φ • f` for every test function
`φ` supported in `H`, satisfies

`‖D²u‖_{Lᵖ(H)} ≤ C ‖f‖_{Lᵖ(H)}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, with the operator norm on
endomorphisms of `ℝ × E`. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_integral_laplacian_smul_eq_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (a : ℝ)
      (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))),
      Wkp.firstOrder 1 u ∈ w1p0Submodule volume (normalHalfSpace a) p →
      (∀ φ : 𝓓(normalHalfSpace (E := E) a, ℝ),
        ∫ x, Δ (φ : WithLp 2 (ℝ × E) → ℝ) x • Wkp.value 2 u x = ∫ x, φ x • f x) →
      ‖Wkp.iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ :=
    exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_compLpL_eq_of_normalHalfSpace
      (E := E) hp hp_top
  refine ⟨C, fun a u f hu hf => hC a u f hu ?_⟩
  -- A solution against test functions is a strong solution: the trace of its weak Hessian is `f`.
  have hloc : LocallyIntegrableOn (f : WithLp 2 (ℝ × E) → ℝ) (normalHalfSpace (E := E) a) volume :=
    Lp.locallyIntegrableOn f Fact.out
  refine Lp.ext ?_
  filter_upwards [(traceCLM ℝ (WithLp 2 (ℝ × E))).coeFn_compLpL (Wkp.iteratedGradient 1 u),
    (Wkp.forall_integral_laplacian_smul_value_eq_iff u hloc).1 hf] with x hx htr
  rw [hx, traceCLM_apply, htr]

end TauCeti
