/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Resolvent
public import TauCeti.Analysis.Sobolev.Trace.OddReflection
public import TauCeti.Analysis.Sobolev.Wkp.Restriction
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import TauCeti.Analysis.PDE.Regularity.Hessian.HalfSpace.Basic
import TauCeti.Analysis.Sobolev.Trace.Kernel

/-!
# `W^{2,p}` solutions of `u - Δu = f` on a half-space with zero boundary values

Let `E` be a finite-dimensional real inner product space, `1 < p < ∞`, and let
`H = {x | a < x.fst}` be a half-space of the Euclidean product `ℝ × E`, with boundary hyperplane
`{a} × E`. This file solves the Dirichlet problem

`u - Δu = f` in `H`, `u = 0` on `∂H`,

in `W^{2,p}(H) ∩ W^{1,p}_0(H)` for every `f ∈ Lᵖ(H)`, where `Δu` is the trace of the weak Hessian
`D²u`. The solution operator is the bounded linear map

`TauCeti.Wkp.halfSpaceDirichletResolventL : Lᵖ(H) →L[ℝ] W^{2,p}(H)`.

Its values have zero boundary values
(`TauCeti.Wkp.firstOrder_halfSpaceDirichletResolventL_mem_w1p0Submodule`) and solve the equation
(`TauCeti.Wkp.value_sub_trace_halfSpaceDirichletResolventL_ae_eq`), and they are the only such
solutions (`TauCeti.Wkp.eq_halfSpaceDirichletResolventL`): for every `1 ≤ p ≤ ∞`, a function in
`W^{2,p}(H) ∩ W^{1,p}_0(H)` with `u - Δu = 0` vanishes
(`TauCeti.Wkp.eq_zero_of_value_sub_trace_ae_eq_zero_of_normalHalfSpace`).

The solution is given by an explicit formula
(`TauCeti.Wkp.value_halfSpaceDirichletResolventL_ae`): on `H` it is `G₁ ⋆ F`, where `G₁` is the
heat resolvent kernel `TauCeti.heatResolventKernel 1` and `F` is the odd extension of `f`,
`F x = f x` on `H` and `F x = -f (ρ x)` on the other side, `ρ` being the reflection in the
boundary hyperplane. The formula does not depend on `p`, so solutions for different exponents
agree whenever the data do. This is what a fixed-point argument needs in order to improve the
integrability of a strong solution up to a flat boundary portion, as for the whole-space operator
`TauCeti.Wkp.oneSubLaplacianEquiv`.

## The argument

* **Existence.** Let `w ∈ W^{2,p}(ℝ × E)` be the whole-space solution of `w - Δw = F`
  (`TauCeti.Wkp.oneSubLaplacianEquiv`), whose value is `G₁ ⋆ F`
  (`TauCeti.Wkp.value_oneSubLaplacianEquiv_symm_ae`). Since `G₁` is radial
  (`TauCeti.heatResolventKernel_eq_of_norm_eq`) and `ρ` is an affine isometry, `G₁ ⋆ F` is odd
  with respect to `ρ`, like `F`. An odd function in `W^{1,p}(ℝ × E)` restricts to a function in
  `W^{1,p}_0(H)` (`TauCeti.W1p.restrictL_mem_w1p0Submodule_normalHalfSpace_of_odd`), so the
  restriction of `w` to `H` is the solution.
* **Uniqueness.** The odd reflection `v` of a solution `u ∈ W^{2,p}(H) ∩ W^{1,p}_0(H)` of
  `u - Δu = 0` lies in `W^{2,p}(ℝ × E)`
  (`TauCeti.Wkp.exists_value_ae_eq_sub_comp_normalReflection`), and since the trace is invariant
  under conjugation by the linear part of `ρ`
  (`TauCeti.traceCLM_ae_eq_sub_comp_normalReflection`), `v - Δv` is the odd reflection of
  `u - Δu = 0`. As
  `1 - Δ` is injective on `W^{2,p}(ℝ × E)`
  (`TauCeti.Wkp.oneSubLaplacianL_injective`), `v = 0`, so `u = 0`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §9.5 and Lemma 9.16 (regularity up to a flat boundary portion, by reflection).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Lemma 9.2 (extension by reflection across a hyperplane).
-/

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Convolution ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Odd data -/

section OddExtension

omit [MeasurableSpace E] [BorelSpace E] in
/-- The indicator difference `x ↦ g x - g (ρ x)` is odd with respect to the reflection `ρ` in
the hyperplane `{a} × E`. -/
private theorem sub_comp_normalReflection_odd (a : ℝ) (g : WithLp 2 (ℝ × E) → ℝ)
    (x : WithLp 2 (ℝ × E)) :
    g (normalReflection E a x) - g (normalReflection E a (normalReflection E a x)) =
      -(g x - g (normalReflection E a x)) := by
  rw [normalReflection_normalReflection]
  ring

/-- **Convolution with the heat resolvent kernel preserves oddness across a hyperplane.** If `g`
is odd with respect to the reflection `ρ` in `{a} × E`, so is `G_λ ⋆ g`. -/
private theorem heatResolventKernel_convolution_normalReflection (lam a : ℝ)
    {g : WithLp 2 (ℝ × E) → ℝ} (hg : ∀ x, g (normalReflection E a x) = -g x)
    (x : WithLp 2 (ℝ × E)) :
    (heatResolventKernel lam ⋆ g) (normalReflection E a x) =
      -(heatResolventKernel lam ⋆ g) x := by
  set R := normalLinearReflection E
  -- `ρ x - t = ρ (x - R t)`, because `ρ = R + (2a, 0)` and `R` is an involution.
  have hρ (t : WithLp 2 (ℝ × E)) :
      normalReflection E a x - t = normalReflection E a (x - R t) := by
    simp only [normalReflection_eq_add, map_sub, R, normalLinearReflection_normalLinearReflection]
    abel
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  calc ∫ t, heatResolventKernel lam t * g (normalReflection E a x - t)
      = ∫ t, -(heatResolventKernel lam (R t) * g (x - R t)) := by
        refine integral_congr_ae (.of_forall fun t => ?_)
        dsimp only
        rw [hρ, hg, heatResolventKernel_eq_of_norm_eq lam (R.norm_map t).symm]
        ring
    _ = -∫ s, heatResolventKernel lam s * g (x - s) := by
        rw [integral_neg, R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding
          fun s => heatResolventKernel lam s * g (x - s)]

/-- The odd extension `f ↦ F` from `Lᵖ(H)` to `Lᵖ(ℝ × E)`, `F = f` on `H` and `F = -f ∘ ρ` on
the other side. -/
private def oddExtensionL (a : ℝ) :
    Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) →L[ℝ]
      Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (⊤ : Opens (WithLp 2 (ℝ × E)))) :=
  (ContinuousLinearMap.id ℝ _ - (Lp.compMeasurePreservingₗᵢ ℝ (normalReflection E a)
      (measurePreserving_normalReflection_top a)).toContinuousLinearMap).comp
    (extendByZeroLpₗᵢ ℝ volume (normalHalfSpace (E := E) a).isOpen.measurableSet.nullMeasurableSet
      (SetLike.coe_subset_coe.mpr le_top)).toContinuousLinearMap

private theorem oddExtensionL_ae (a : ℝ)
    (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))) :
    (oddExtensionL a f : WithLp 2 (ℝ × E) → ℝ) =ᵐ[volume] fun x =>
      (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator f x -
        (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator f
          (normalReflection E a x) := by
  set Z := extendByZeroLpₗᵢ ℝ volume
    (normalHalfSpace (E := E) a).isOpen.measurableSet.nullMeasurableSet
    (SetLike.coe_subset_coe.mpr le_top) f
  have hZ := coeFn_extendByZeroLpₗᵢ ℝ
    (normalHalfSpace (E := E) a).isOpen.measurableSet.nullMeasurableSet
    (SetLike.coe_subset_coe.mpr (le_top : normalHalfSpace (E := E) a ≤ ⊤)) f
  rw [Measure.ae_restrict_coe_opens_top] at hZ
  have hsub := Lp.coeFn_sub Z (Lp.compMeasurePreservingₗᵢ ℝ (normalReflection E a)
    (measurePreserving_normalReflection_top a) Z)
  have hcomp := Lp.coeFn_compMeasurePreserving Z (measurePreserving_normalReflection_top (E := E) a)
  rw [Measure.ae_restrict_coe_opens_top] at hsub hcomp
  filter_upwards [hsub, hcomp, hZ,
    (measurePreserving_normalReflection (E := E) a).quasiMeasurePreserving.ae_eq_comp hZ]
    with x h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₂ h₄
  simp only [oddExtensionL, ContinuousLinearMap.comp_apply, _root_.sub_apply,
    ContinuousLinearMap.id_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [h₁, Pi.sub_apply, Lp.compMeasurePreservingₗᵢ_apply, h₂, h₃, h₄]

end OddExtension

/-! ### The solution operator -/

namespace Wkp

/-- **The solution operator of the Dirichlet problem for `u - Δu = f` on a half-space.** For
`1 < p < ∞` and `f ∈ Lᵖ(H)` on `H = {x | a < x.fst}`, `halfSpaceDirichletResolventL hp hp_top a f`
is the unique `u ∈ W^{2,p}(H)` with zero boundary values solving `u - tr D²u = f` almost
everywhere on `H` (`TauCeti.Wkp.firstOrder_halfSpaceDirichletResolventL_mem_w1p0Submodule`,
`TauCeti.Wkp.value_sub_trace_halfSpaceDirichletResolventL_ae_eq` and
`TauCeti.Wkp.eq_halfSpaceDirichletResolventL`). Its value is the convolution of the heat resolvent
kernel with the odd extension of `f` (`TauCeti.Wkp.value_halfSpaceDirichletResolventL_ae`). -/
def halfSpaceDirichletResolventL (hp : 1 < p) (hp_top : p ≠ ⊤) (a : ℝ) :
    Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)) →L[ℝ]
      Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2 :=
  (restrictL (le_top : normalHalfSpace (E := E) a ≤ ⊤) 2).comp
    ((oneSubLaplacianEquiv (E := WithLp 2 (ℝ × E)) hp hp_top).symm.toContinuousLinearMap.comp
      (oddExtensionL a))

/-- The whole-space solution of `w - Δw = F` restricts to `halfSpaceDirichletResolventL`. -/
private theorem halfSpaceDirichletResolventL_apply (hp : 1 < p) (hp_top : p ≠ ⊤) (a : ℝ)
    (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))) :
    halfSpaceDirichletResolventL hp hp_top a f =
      restrictL le_top 2 ((oneSubLaplacianEquiv hp hp_top).symm (oddExtensionL a f)) :=
  (rfl)

/-- The value of the whole-space solution of `w - Δw = F` is `G₁ ⋆ F`. -/
private theorem value_oneSubLaplacianEquiv_symm_oddExtensionL_ae (hp : 1 < p) (hp_top : p ≠ ⊤)
    (a : ℝ)
    (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))) :
    (value 2 ((oneSubLaplacianEquiv hp hp_top).symm (oddExtensionL a f)) :
        WithLp 2 (ℝ × E) → ℝ) =ᵐ[volume]
      heatResolventKernel 1 ⋆ fun x =>
        (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator f x -
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator f
            (normalReflection E a x) := by
  rw [← convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (EventuallyEq.refl _ _)
    (oddExtensionL_ae a f)]
  exact value_oneSubLaplacianEquiv_symm_ae hp hp_top _

/-- **The value of the half-space solution.** On `H`, the value of
`halfSpaceDirichletResolventL hp hp_top a f` is `G₁ ⋆ F`, where `G₁` is the heat resolvent kernel
at `1` and `F` is the odd extension of `f` across the boundary hyperplane: `F = f` on `H` and
`F = -f ∘ ρ` on the other side, `ρ` being the reflection in `{a} × E`. -/
theorem value_halfSpaceDirichletResolventL_ae (hp : 1 < p) (hp_top : p ≠ ⊤) (a : ℝ)
    (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))) :
    (value 2 (halfSpaceDirichletResolventL hp hp_top a f) : WithLp 2 (ℝ × E) → ℝ)
      =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)]
      heatResolventKernel 1 ⋆ fun x =>
        (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator f x -
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator f
            (normalReflection E a x) := by
  rw [halfSpaceDirichletResolventL_apply]
  exact (value_restrictL_ae le_top 2 _).trans
    (ae_restrict_of_ae (value_oneSubLaplacianEquiv_symm_oddExtensionL_ae hp hp_top a f))

/-- **The half-space solution has zero boundary values**: the first-order part of
`halfSpaceDirichletResolventL hp hp_top a f` lies in `W^{1,p}_0(H)`. -/
theorem firstOrder_halfSpaceDirichletResolventL_mem_w1p0Submodule (hp : 1 < p) (hp_top : p ≠ ⊤)
    (a : ℝ)
    (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))) :
    firstOrder 1 (halfSpaceDirichletResolventL hp hp_top a f) ∈
      w1p0Submodule volume (normalHalfSpace (E := E) a) p := by
  set w := (oneSubLaplacianEquiv hp hp_top).symm (oddExtensionL a f)
  -- The value of `w` is `G₁ ⋆ F`, which is odd with respect to `ρ` because `F` is.
  have hconv := value_oneSubLaplacianEquiv_symm_oddExtensionL_ae hp hp_top a f
  have hodd : ∀ᵐ x ∂volume, W1p.value (lowerOrder 1 w) (normalReflection E a x) =
      -W1p.value (lowerOrder 1 w) x := by
    rw [value_lowerOrder_one]
    filter_upwards [hconv,
      (measurePreserving_normalReflection (E := E) a).quasiMeasurePreserving.ae_eq_comp hconv]
      with x h₁ h₂
    simp only [Function.comp_apply] at h₂
    rw [h₁, h₂]
    exact heatResolventKernel_convolution_normalReflection 1 a
      (sub_comp_normalReflection_odd a _) x
  rw [halfSpaceDirichletResolventL_apply, firstOrder_one, lowerOrder_restrictL, restrictL_one]
  exact W1p.restrictL_mem_w1p0Submodule_normalHalfSpace_of_odd hp_top a _ hodd

/-- **The half-space solution solves `u - Δu = f`**: for
`u = halfSpaceDirichletResolventL hp hp_top a f`, `u - tr D²u = f` almost everywhere on `H`. -/
theorem value_sub_trace_halfSpaceDirichletResolventL_ae_eq (hp : 1 < p) (hp_top : p ≠ ⊤)
    (a : ℝ)
    (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))) :
    (fun x => value 2 (halfSpaceDirichletResolventL hp hp_top a f) x -
        LinearMap.trace ℝ (WithLp 2 (ℝ × E))
          (iteratedGradient 1 (halfSpaceDirichletResolventL hp hp_top a f) x))
      =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)] f := by
  set w := (oneSubLaplacianEquiv hp hp_top).symm (oddExtensionL a f)
  have hH : MeasurableSet (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) :=
    (normalHalfSpace (E := E) a).isOpen.measurableSet
  -- On the whole space, `w - Δw = F`, and `F = f` on `H`.
  have hw := oneSubLaplacianL_ae w
  rw [oneSubLaplacianL_oneSubLaplacianEquiv_symm] at hw
  rw [halfSpaceDirichletResolventL_apply]
  filter_upwards [value_restrictL_ae le_top 2 w, iteratedGradient_restrictL_ae le_top 1 w,
    ae_restrict_of_ae hw, ae_restrict_of_ae (oddExtensionL_ae a f), ae_restrict_mem hH]
    with x h₁ h₂ h₃ h₄ hx
  rw [h₁, h₂, ← h₃, h₄, indicator_of_mem hx,
    indicator_of_notMem (normalReflection_notMem_normalHalfSpace hx), sub_zero]

/-! ### Uniqueness -/

/-- **Uniqueness for the Dirichlet problem for `u - Δu` on a half-space.** For every
`1 ≤ p ≤ ∞`, a function `u ∈ W^{2,p}(H)` on `H = {x | a < x.fst}` whose first-order part lies in
`W^{1,p}_0(H)` and which solves `u - tr D²u = 0` almost everywhere on `H` vanishes. -/
theorem eq_zero_of_value_sub_trace_ae_eq_zero_of_normalHalfSpace {a : ℝ}
    {u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2}
    (hu : firstOrder 1 u ∈ w1p0Submodule volume (normalHalfSpace (E := E) a) p)
    (heq : (fun x => value 2 u x - LinearMap.trace ℝ (WithLp 2 (ℝ × E)) (iteratedGradient 1 u x))
      =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)] 0) :
    u = 0 := by
  set H := (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
  have hH : MeasurableSet H := (normalHalfSpace (E := E) a).isOpen.measurableSet
  obtain ⟨v, hv, hvD⟩ := exists_value_ae_eq_sub_comp_normalReflection u hu
  -- `k` is `u - Δu`, extended by zero off `H`; it vanishes almost everywhere.
  set k : WithLp 2 (ℝ × E) → ℝ := H.indicator fun x =>
    value 2 u x - LinearMap.trace ℝ (WithLp 2 (ℝ × E)) (iteratedGradient 1 u x)
  have hk : k =ᵐ[volume] 0 := by
    have h := (ae_eq_restrict_iff_indicator_ae_eq hH).1 heq
    rwa [indicator_zero'] at h
  have hkI (y : WithLp 2 (ℝ × E)) : H.indicator (value 2 u) y -
      H.indicator (fun x => traceCLM ℝ (WithLp 2 (ℝ × E)) (iteratedGradient 1 u x)) y = k y := by
    by_cases hy : y ∈ H
    · simp only [k, indicator_of_mem hy, traceCLM_apply]
    · simp only [k, indicator_of_notMem hy, sub_zero]
  -- `v - Δv` is the odd reflection `k - k ∘ ρ` of `u - Δu`, since `tr (R ∘ M ∘ R) = tr M`.
  have hv0 : oneSubLaplacianL v = 0 := by
    refine Lp.ext ?_
    rw [Filter.EventuallyEq, Measure.ae_restrict_coe_opens_top]
    filter_upwards [oneSubLaplacianL_ae v, hv, traceCLM_ae_eq_sub_comp_normalReflection hvD, hk,
      (measurePreserving_normalReflection (E := E) a).quasiMeasurePreserving.ae_eq_comp hk,
      (Lp.coeFn_zero ℝ p _).filter_mono Measure.ae_le_ae_restrict_coe_opens_top]
      with x h₁ h₂ h₃ h₄ h₅ h₆
    simp only [Function.comp_apply, Pi.sub_apply, Pi.zero_apply] at h₃ h₄ h₅
    rw [h₁, h₂, h₆, Pi.zero_apply, ← traceCLM_apply, h₃]
    linear_combination hkI x - hkI (normalReflection E a x) + h₄ - h₅
  have hv' : v = 0 := oneSubLaplacianL_injective (by rw [hv0, map_zero])
  subst hv'
  -- On `H`, the value of `v = 0` is that of `u`.
  refine ext 2 (Lp.ext ?_)
  have h0 := (value_zero_ae (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (Omega := ⊤) (p := p)
    2).filter_mono Measure.ae_le_ae_restrict_coe_opens_top
  filter_upwards [ae_restrict_of_ae hv, ae_restrict_of_ae h0, ae_restrict_mem hH,
    value_zero_ae (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (Omega := normalHalfSpace a)
      (p := p) 2] with x h₁ h₂ hx h₃
  rw [Pi.zero_apply] at h₂ h₃
  rw [h₂, indicator_of_mem hx, indicator_of_notMem (normalReflection_notMem_normalHalfSpace hx),
    sub_zero] at h₁
  rw [h₃, ← h₁]

/-- **The half-space solution is the only one.** For `1 < p < ∞`, every `u ∈ W^{2,p}(H)` on
`H = {x | a < x.fst}` whose first-order part lies in `W^{1,p}_0(H)` and which solves
`u - tr D²u = f` almost everywhere on `H` is `halfSpaceDirichletResolventL hp hp_top a f`. -/
theorem eq_halfSpaceDirichletResolventL (hp : 1 < p) (hp_top : p ≠ ⊤) {a : ℝ}
    {u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p 2}
    {f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a))}
    (hu : firstOrder 1 u ∈ w1p0Submodule volume (normalHalfSpace (E := E) a) p)
    (heq : (fun x => value 2 u x - LinearMap.trace ℝ (WithLp 2 (ℝ × E)) (iteratedGradient 1 u x))
      =ᵐ[(volume : Measure (WithLp 2 (ℝ × E))).restrict (normalHalfSpace (E := E) a)] f) :
    u = halfSpaceDirichletResolventL hp hp_top a f := by
  set w := halfSpaceDirichletResolventL hp hp_top a f
  refine sub_eq_zero.1 (eq_zero_of_value_sub_trace_ae_eq_zero_of_normalHalfSpace ?_ ?_)
  · rw [← firstOrderL_apply, map_sub, firstOrderL_apply, firstOrderL_apply,
      ← ClosedSubmodule.mem_toSubmodule_iff]
    exact Submodule.sub_mem _ hu
      (firstOrder_halfSpaceDirichletResolventL_mem_w1p0Submodule hp hp_top a f)
  · have hD : iteratedGradient 1 (u - w) = iteratedGradient 1 u - iteratedGradient 1 w := by
      rw [← iteratedGradientL_apply, map_sub, iteratedGradientL_apply, iteratedGradientL_apply]
    filter_upwards [Lp.coeFn_sub (value 2 u) (value 2 w), hD ▸ Lp.coeFn_sub
      (iteratedGradient 1 u) (iteratedGradient 1 w), heq,
      value_sub_trace_halfSpaceDirichletResolventL_ae_eq hp hp_top a f] with x h₁ h₂ h₃ h₄
    rw [value_sub, h₁, h₂, Pi.sub_apply, Pi.sub_apply, ContinuousLinearMap.toLinearMap_sub, map_sub,
      Pi.zero_apply]
    linear_combination h₃ - h₄

end Wkp

end TauCeti
