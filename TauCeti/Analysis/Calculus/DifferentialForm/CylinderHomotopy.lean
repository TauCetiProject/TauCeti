/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.Fin
import TauCeti.MeasureTheory.Constructions.UnitInterval

/-!
# The homotopy operator on a cylinder over a subset of a normed space

Let `ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F` be a differential `(n + 1)`-form on the product
of a real normed space `E` with the time line. The *cylinder homotopy operator*
(`TauCeti.cylinderHomotopy`) contracts `ω` with the unit time vector `∂ₜ = (0, 1)` and integrates
the result over the time interval `[0, 1]`:

`(h ω)(x)(v₁, …, vₙ) = ∫₀¹ ω(x, t)(∂ₜ, v₁, …, vₙ) dt`,

where each `vᵢ ∈ E` is viewed in `E × ℝ` through `ContinuousLinearMap.inl`. Writing
`ιₜ^* ω = x ↦ (ω (x, t)).compContinuousLinearMap (.inl ℝ E ℝ)` for the pullback of `ω` along the
slice `x ↦ (x, t)`, the operator satisfies the cochain-homotopy identity

`d (h ω) + h (d ω) = ι₁^* ω - ι₀^* ω`.

Everything is relative to a cylinder `s ×ˢ Icc 0 1`: the form only needs to be `C¹` on it, and the
exterior derivatives are taken within it (and within `s` for `h ω`). The base `s` is a convex set
with unique derivatives that need not be open, such as a closed half-ball, the local shape of the
image of a boundary chart of a manifold with boundary; the time direction always has boundary.
Convexity is what Mathlib's mean value inequality needs to differentiate under the integral
within `s`. In degree zero the identity reduces to the fundamental theorem of calculus
`h (d f) = ι₁^* f - ι₀^* f` (`TauCeti.cylinderHomotopy_extDerivWithin_eq_sub`), which needs no
convexity.

The proof differentiates under the integral sign and uses the fundamental theorem of calculus in
the time variable. Pointwise, the derivative terms combine through the constant-coefficient Cartan
formula `ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft_comp_add_curryLeft` for the
vector `∂ₜ`, pulled back along `inl` by
`ContinuousAlternatingMap.alternatizeUncurryFin_compContinuousLinearMap`, into the time derivative
of `ιₜ^* ω`.

This is the chart-level form of the homotopy operator on forms on `M × [0, 1]` for a manifold `M`
with or without boundary, the analytic input for homotopy invariance of de Rham cohomology. It is
proved directly, without Stokes' theorem on the manifold with corners `M × [0, 1]`.

## Main declarations

* `TauCeti.cylinderHomotopy`: the cylinder homotopy operator.
* `Convex.contDiffOn_cylinderHomotopy`, `TauCeti.contDiff_cylinderHomotopy`: it preserves `C^r`
  regularity.
* `Convex.extDerivWithin_cylinderHomotopy_add_cylinderHomotopy_extDerivWithin`: the
  cochain-homotopy identity `d (h ω) + h (d ω) = ι₁^* ω - ι₀^* ω`.
* `Convex.extDerivWithin_cylinderHomotopy`: for a closed form, `ι₁^* ω - ι₀^* ω = d (h ω)`.
* `TauCeti.cylinderHomotopy_extDerivWithin_eq_sub`: the degree-zero case
  `h (d f) = ι₁^* f - ι₀^* f`.
* `TauCeti.extDeriv_cylinderHomotopy_add_cylinderHomotopy_extDeriv`,
  `TauCeti.cylinderHomotopy_extDeriv_eq_sub`: the same identities for forms `C¹` on all of
  `E × ℝ`, with exterior derivatives on the whole spaces.
* `TauCeti.support_cylinderHomotopy_subset`, `TauCeti.tsupport_cylinderHomotopy_subset`,
  `TauCeti.norm_cylinderHomotopy_le`, `TauCeti.norm_iteratedFDeriv_cylinderHomotopy_le`: support
  and sup-norm bounds for `h ω` and its derivatives, which make `h` continuous on compactly
  supported smooth forms.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, section Homotopy
  Invariance, whose homotopy operator on `M × [0, 1]` is the manifold version of this one.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4 (the homotopy
  operator `K` of the Poincaré lemma, integration along the fibre of `M × ℝ → M`).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped unitInterval Interval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

namespace TauCeti

/-- The **cylinder homotopy operator**: the `n`-form `x ↦ ∫₀¹ ω(x, t)((0, 1), ·) dt` on `E` built
from a differential `(n + 1)`-form `ω` on `E × ℝ`, with the arguments in `E` included into `E × ℝ`
by `ContinuousLinearMap.inl`. For a `C¹` form with values in a Banach space it satisfies
`d (h ω) + h (d ω) = ι₁^* ω - ι₀^* ω`, where `ιₜ` is the slice `x ↦ (x, t)`. -/
def cylinderHomotopy (ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F) (x : E) :
    E [⋀^Fin n]→L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, ((ω (x, t)).curryLeft (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ)

theorem cylinderHomotopy_apply (ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F) (x : E) :
    cylinderHomotopy ω x =
      ∫ t in (0 : ℝ)..1, ((ω (x, t)).curryLeft (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ) :=
  (rfl)

/-- The contraction with `(0, 1)` followed by the pullback along `inl`, as a continuous linear
map; the cylinder homotopy operator integrates it over time. -/
private def contractInl : ((E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F) →L[ℝ] E [⋀^Fin n]→L[ℝ] F :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM (.inl ℝ E ℝ) ∘L
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E × ℝ) (F := F)
      (n := n)).toContinuousLinearMap.flip (0, 1)

private theorem contractInl_def :
    contractInl (E := E) (F := F) (n := n) =
      ContinuousAlternatingMap.compContinuousLinearMapCLM (.inl ℝ E ℝ) ∘L
        (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := E × ℝ) (F := F)
          (n := n)).toContinuousLinearMap.flip (0, 1) :=
  (rfl)

private theorem contractInl_apply (α : (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F) :
    contractInl α = (α.curryLeft (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ) :=
  (rfl)

private theorem cylinderHomotopy_eq_integral_unitInterval
    (ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F) :
    cylinderHomotopy ω = fun x ↦ ∫ t : I, (1 : ℝ) • contractInl (ω (x, (t : ℝ))) := by
  funext x
  simp only [cylinderHomotopy_apply, intervalIntegral_eq_integral_unitInterval, one_smul,
    contractInl_apply]

/-- The cylinder homotopy operator at `x` only depends on the form along the segment
`{x} × [0, 1]`. -/
theorem cylinderHomotopy_congr {x : E} {ω₁ ω₂ : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ω₁ (x, t) = ω₂ (x, t)) :
    cylinderHomotopy ω₁ x = cylinderHomotopy ω₂ x := by
  rw [cylinderHomotopy_apply, cylinderHomotopy_apply]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  simp only [h t (by rwa [uIcc_of_le zero_le_one] at ht)]

/-- Evaluated on vectors `v₁, …, vₙ` of `E`, the cylinder homotopy operator is the time integral
`∫₀¹ ω(x, t)(∂ₜ, (v₁, 0), …, (vₙ, 0)) dt`, for a form integrable along the segment
`{x} × [0, 1]`. -/
theorem cylinderHomotopy_apply_apply [CompleteSpace F]
    {ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F} {x : E}
    (hω : IntervalIntegrable (fun t ↦ ω (x, t)) volume 0 1) (v : Fin n → E) :
    cylinderHomotopy ω x v = ∫ t in (0 : ℝ)..1, ω (x, t) (Fin.cons (0, 1) fun i ↦ (v i, 0)) := by
  have h : cylinderHomotopy ω x = contractInl (∫ t in (0 : ℝ)..1, ω (x, t)) := by
    rw [cylinderHomotopy_apply]
    exact contractInl.intervalIntegral_comp_comm hω
  rw [h, contractInl_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply]
  exact ((ContinuousAlternatingMap.apply ℝ (E × ℝ) F _).intervalIntegral_comp_comm hω).symm

/-- The cylinder homotopy operator of the zero form is zero. -/
@[simp]
theorem cylinderHomotopy_zero :
    cylinderHomotopy (0 : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F) = 0 := by
  funext x
  simp only [cylinderHomotopy_apply, Pi.zero_apply, ← contractInl_apply, map_zero,
    intervalIntegral.integral_zero]

/-- The cylinder homotopy operator commutes with real scalar multiplication of forms. -/
theorem cylinderHomotopy_smul (c : ℝ) (ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F) :
    cylinderHomotopy (c • ω) = c • cylinderHomotopy ω := by
  funext x
  simp only [cylinderHomotopy_apply, Pi.smul_apply, ← contractInl_apply, map_smul,
    intervalIntegral.integral_smul]

/-- The cylinder homotopy operator is additive on forms that are continuous along the segment
`{x} × [0, 1]`. -/
theorem cylinderHomotopy_add_apply {x : E} {ω₁ ω₂ : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F}
    (h₁ : ContinuousOn ω₁ ({x} ×ˢ Icc 0 1)) (h₂ : ContinuousOn ω₂ ({x} ×ˢ Icc 0 1)) :
    cylinderHomotopy (ω₁ + ω₂) x = cylinderHomotopy ω₁ x + cylinderHomotopy ω₂ x := by
  have hint {ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F} (hω : ContinuousOn ω ({x} ×ˢ Icc 0 1)) :
      IntervalIntegrable (fun t : ℝ ↦ contractInl (ω (x, t))) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact contractInl.continuous.comp_continuousOn
      (hω.comp (continuous_const.prodMk continuous_id).continuousOn fun t ht ↦ ⟨rfl, ht⟩)
  simp only [cylinderHomotopy_apply, Pi.add_apply, ← contractInl_apply, map_add]
  exact intervalIntegral.integral_add (hint h₁) (hint h₂)

/-- The cylinder homotopy operator is supported over the part of the support of the form that lies
in `E × [0, 1]`. -/
theorem support_cylinderHomotopy_subset (ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F) :
    Function.support (cylinderHomotopy ω) ⊆
      Prod.fst '' (Function.support ω ∩ univ ×ˢ Icc 0 1) := by
  intro x hx
  by_contra h
  refine hx ?_
  rw [cylinderHomotopy_congr (ω₂ := 0) fun t ht ↦ ?_, cylinderHomotopy_zero, Pi.zero_apply]
  exact Function.notMem_support.1 fun hs ↦ h ⟨(x, t), ⟨hs, mem_univ _, ht⟩, rfl⟩

/-- The cylinder homotopy operator of a compactly supported form is topologically supported over
the part of the topological support of the form that lies in `E × [0, 1]`. -/
theorem tsupport_cylinderHomotopy_subset {ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F}
    (hω : HasCompactSupport ω) :
    tsupport (cylinderHomotopy ω) ⊆ Prod.fst '' (tsupport ω ∩ univ ×ˢ Icc 0 1) :=
  closure_minimal ((support_cylinderHomotopy_subset _).trans
      (image_mono (inter_subset_inter_left _ (subset_tsupport _))))
    ((hω.inter_right (isClosed_univ.prod isClosed_Icc)).image continuous_fst).isClosed

/-- The contraction with `(0, 1)` followed by the pullback along `inl` does not increase norms,
for the sup norm on `E × ℝ`. -/
private theorem norm_contractInl_le_one : ‖contractInl (E := E) (F := F) (n := n)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α ↦ ?_
  rw [contractInl_apply, one_mul]
  calc ‖(α.curryLeft (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ)‖
      ≤ ‖α.curryLeft (0, 1)‖ * ‖ContinuousLinearMap.inl ℝ E ℝ‖ ^ n :=
        (ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _).trans_eq (by simp)
    _ ≤ ‖α.curryLeft (0, 1)‖ * 1 := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inl_le_one ℝ E ℝ)
    _ ≤ ‖α.curryLeft‖ * ‖((0 : E), (1 : ℝ))‖ := by
        rw [mul_one]
        exact α.curryLeft.le_opNorm _
    _ = ‖α‖ := by simp [ContinuousAlternatingMap.norm_curryLeft]

/-- The cylinder homotopy operator at `x` is bounded by any bound for the form along the segment
`{x} × [0, 1]`, for the sup norm on `E × ℝ`. -/
theorem norm_cylinderHomotopy_le {ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F} {x : E} {B : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ‖ω (x, t)‖ ≤ B) : ‖cylinderHomotopy ω x‖ ≤ B := by
  have hle : ∀ t ∈ Ι (0 : ℝ) 1, ‖contractInl (ω (x, t))‖ ≤ B := fun t ht ↦ by
    rw [uIoc_of_le zero_le_one] at ht
    exact ((contractInl (E := E) (F := F) (n := n)).le_of_opNorm_le norm_contractInl_le_one _).trans
      ((one_mul _).trans_le (h t (Ioc_subset_Icc_self ht)))
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hle
  rw [sub_zero, abs_one, mul_one] at hI
  rw [cylinderHomotopy_apply]
  simp only [← contractInl_apply]
  exact hI

/-- The `i`-th derivative of a time slice of `x ↦ contractInl (ω (x, t))`, explicitly. -/
private theorem iteratedFDeriv_contractInl_comp {r : WithTop ℕ∞}
    {ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F} (hω : ContDiff ℝ r ω) {i : ℕ} (hi : i ≤ r)
    (t : ℝ) (x : E) :
    iteratedFDeriv ℝ i (fun y ↦ contractInl (ω (y, t))) x =
      contractInl.compContinuousMultilinearMap
        ((iteratedFDeriv ℝ i ω (x, t)).compContinuousLinearMap fun _ ↦ .inl ℝ E ℝ) := by
  have hshift : ContDiff ℝ r fun p : E × ℝ ↦ ω (p + (0, t)) :=
    hω.comp (contDiff_id.add contDiff_const)
  have hcomp : (fun y ↦ contractInl (ω (y, t))) =
      contractInl ∘ ((fun p : E × ℝ ↦ ω (p + (0, t))) ∘ ContinuousLinearMap.inl ℝ E ℝ) := by
    funext y
    simp
  rw [hcomp, contractInl.iteratedFDeriv_comp_left
      (hshift.comp (ContinuousLinearMap.inl ℝ E ℝ).contDiff).contDiffAt hi,
    (ContinuousLinearMap.inl ℝ E ℝ).iteratedFDeriv_comp_right hshift x hi,
    iteratedFDeriv_comp_add_right]
  simp

/-- The derivatives of the cylinder homotopy operator of a compactly supported `C^r` form are
bounded by those of the form: if `‖Dⁱ ω (x, t)‖ ≤ B` for `t ∈ [0, 1]` and `i ≤ r`, then
`‖Dⁱ (h ω) x‖ ≤ B`, for the sup norm on `E × ℝ`. -/
theorem norm_iteratedFDeriv_cylinderHomotopy_le [CompleteSpace F] {r : WithTop ℕ∞}
    {ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F} (hω : ContDiff ℝ r ω)
    (hc : HasCompactSupport ω) {i : ℕ} (hi : i ≤ r) {x : E} {B : ℝ}
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ i ω (x, t)‖ ≤ B) :
    ‖iteratedFDeriv ℝ i (cylinderHomotopy ω) x‖ ≤ B := by
  have hki {k : ℕ} (hk : k ≤ i) : (k : WithTop ℕ∞) ≤ r := le_trans (by exact_mod_cast hk) hi
  have hnorm {k : ℕ} (hk : k ≤ i) (t : ℝ) (y : E) :
      ‖iteratedFDeriv ℝ k (fun y ↦ contractInl (ω (y, t))) y‖ ≤
        ‖iteratedFDeriv ℝ k ω (y, t)‖ := by
    rw [iteratedFDeriv_contractInl_comp hω (hki hk)]
    refine ((contractInl (E := E) (F := F) (n := n)).norm_compContinuousMultilinearMap_le
      _).trans ?_
    refine (mul_le_of_le_one_left (norm_nonneg _) norm_contractInl_le_one).trans ?_
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    exact mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
      fun _ _ ↦ ContinuousLinearMap.norm_inl_le_one ℝ E ℝ)
  -- uniform bounds for the derivatives of `ω` of order at most `i`
  have hbd : ∀ k ≤ i, ∃ C, ∀ p, ‖iteratedFDeriv ℝ k ω p‖ ≤ C := fun k hk ↦
    (hω.continuous_iteratedFDeriv (hki hk)).norm.bddAbove_range_of_hasCompactSupport
      (hc.iteratedFDeriv k).norm |>.imp fun _ h p ↦ h ⟨p, rfl⟩
  choose! C hC using hbd
  -- the derivatives in `x` of the integrand are continuous in time
  have hcont {k : ℕ} (hk : k ≤ i) (y : E) :
      Continuous fun t : ℝ ↦ iteratedFDeriv ℝ k (fun y ↦ contractInl (ω (y, t))) y := by
    simp_rw [iteratedFDeriv_contractInl_comp hω (hki hk)]
    exact ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ _ _ _ contractInl).comp
      (ContinuousMultilinearMap.compContinuousLinearMapL fun _ ↦ .inl ℝ E ℝ)).continuous.comp
        ((hω.continuous_iteratedFDeriv (hki hk)).comp (continuous_const.prodMk continuous_id))
  have hderiv := iteratedFDeriv_intervalIntegral (μ := volume) (a := 0) (b := 1)
    (u := fun t y ↦ contractInl (ω (y, t))) (N := i)
    (Filter.Eventually.of_forall fun t ↦ (contractInl (E := E) (F := F) (n := n)).contDiff.comp
      ((hω.comp (contDiff_id.prodMk (contDiff_const (c := t)))).of_le hi))
    (fun k hk y ↦ (hcont hk y).aestronglyMeasurable)
    (bound := fun k _ ↦ C k) (fun _ _ ↦ intervalIntegrable_const)
    (fun k hk ↦ Filter.Eventually.of_forall fun t y ↦ (hnorm hk t y).trans (hC k hk _)) le_rfl
  have heq : cylinderHomotopy ω = fun y ↦ ∫ t in (0 : ℝ)..1, contractInl (ω (y, t)) := by
    funext y
    simp only [cylinderHomotopy_apply, ← contractInl_apply]
  have hle : ∀ t ∈ Ι (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ i (fun y ↦ contractInl (ω (y, t))) x‖ ≤ B := fun t ht ↦ by
    rw [uIoc_of_le zero_le_one] at ht
    exact (hnorm le_rfl t x).trans (hB t (Ioc_subset_Icc_self ht))
  rw [heq, hderiv]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hle

/-- The fundamental theorem of calculus along the segment `{x} × [0, 1]`: integrating the time
derivative of the slice pullbacks `ιₜ^* ω` recovers `ι₁^* ω - ι₀^* ω`. -/
private theorem integral_fderivWithin_apply_eq_sub {m : ℕ} [CompleteSpace F] {s : Set E}
    (hsu : UniqueDiffOn ℝ s) {ω : E × ℝ → (E × ℝ) [⋀^Fin m]→L[ℝ] F}
    (hω : ContDiffOn ℝ 1 ω (s ×ˢ Icc 0 1)) {x : E} (hx : x ∈ s) :
    ∫ t in (0 : ℝ)..1, (fderivWithin ℝ ω (s ×ˢ Icc 0 1) (x, t) (0, 1)).compContinuousLinearMap
        (.inl ℝ E ℝ) =
      (ω (x, 1)).compContinuousLinearMap (.inl ℝ E ℝ) -
        (ω (x, 0)).compContinuousLinearMap (.inl ℝ E ℝ) := by
  set C := ContinuousAlternatingMap.compContinuousLinearMapCLM (F := F) (ι := Fin m)
    (.inl ℝ E ℝ)
  have hmaps : MapsTo (fun t : ℝ ↦ (x, t)) (Icc 0 1) (s ×ˢ Icc 0 1) := fun _ ht ↦ ⟨hx, ht⟩
  have hcurve : Continuous fun t : ℝ ↦ (x, t) := continuous_const.prodMk continuous_id
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ ↦ C (ω (x, t))) (C (fderivWithin ℝ ω (s ×ˢ Icc 0 1) (x, t) (0, 1)))
        t := by
    have hω' : HasDerivWithinAt (fun t : ℝ ↦ ω (x, t))
        (fderivWithin ℝ ω (s ×ˢ Icc 0 1) (x, t) (0, 1)) (Icc 0 1) t :=
      (hω.differentiableOn one_ne_zero _ (hmaps (Ioo_subset_Icc_self ht))).hasFDerivWithinAt
        |>.comp_hasDerivWithinAt t
          ((hasDerivAt_const t x).prodMk (hasDerivAt_id t)).hasDerivWithinAt hmaps
    exact C.hasFDerivAt.comp_hasDerivAt t (hω'.hasDerivAt (Icc_mem_nhds ht.1 ht.2))
  have hcont : ContinuousOn (fun t : ℝ ↦ C (ω (x, t))) (Icc 0 1) :=
    C.continuous.comp_continuousOn (hω.continuousOn.comp hcurve.continuousOn hmaps)
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ C (fderivWithin ℝ ω (s ×ˢ Icc 0 1) (x, t) (0, 1))) volume 0 1 :=
    ((C.comp (ContinuousLinearMap.apply ℝ _ (0, 1))).continuous.comp_continuousOn
      ((hω.continuousOn_fderivWithin (hsu.prod uniqueDiffOn_Icc_zero_one) le_rfl).comp
        hcurve.continuousOn hmaps)).intervalIntegrable_of_Icc zero_le_one
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint

/-- **The cylinder homotopy identity in degree zero**, the fundamental theorem of calculus
`h (d f) = ι₁^* f - ι₀^* f` for a `C¹` function `f` on the cylinder `s ×ˢ Icc 0 1`, viewed as a
`0`-form. -/
theorem cylinderHomotopy_extDerivWithin_eq_sub [CompleteSpace F] {s : Set E}
    (hsu : UniqueDiffOn ℝ s) {ω : E × ℝ → (E × ℝ) [⋀^Fin 0]→L[ℝ] F}
    (hω : ContDiffOn ℝ 1 ω (s ×ˢ Icc 0 1)) {x : E} (hx : x ∈ s) :
    cylinderHomotopy (extDerivWithin ω (s ×ˢ Icc 0 1)) x =
      (ω (x, 1)).compContinuousLinearMap (.inl ℝ E ℝ) -
        (ω (x, 0)).compContinuousLinearMap (.inl ℝ E ℝ) := by
  rw [← integral_fderivWithin_apply_eq_sub hsu hω hx, cylinderHomotopy_apply]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  ext v
  simp [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply]

end TauCeti

open TauCeti

namespace Convex

variable {s : Set E} {ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F}

/-- The cylinder homotopy operator of a form that is `C^r` on the cylinder `s ×ˢ Icc 0 1` over a
convex set `s` with unique derivatives is `C^r` on `s`. -/
theorem contDiffOn_cylinderHomotopy (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s) {r : ℕ∞}
    (hω : ContDiffOn ℝ r ω (s ×ˢ Icc 0 1)) : ContDiffOn ℝ r (cylinderHomotopy ω) s := by
  rw [cylinderHomotopy_eq_integral_unitInterval]
  exact hs.contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure I))
    (integrable_const (1 : ℝ)) continuous_subtype_val hsu (hsu.prod uniqueDiffOn_Icc_zero_one)
    (contractInl.contDiff.comp_contDiffOn hω) fun x hx t ↦ ⟨hx, t.2⟩

variable [CompleteSpace F]

/-- The exterior derivative within a convex set `s` of the cylinder homotopy operator, as an
integral over `[0, 1]`. -/
private theorem extDerivWithin_cylinderHomotopy_eq (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s)
    (hω : ContDiffOn ℝ 1 ω (s ×ˢ Icc 0 1)) {x : E} (hx : x ∈ s) :
    extDerivWithin (cylinderHomotopy ω) s x =
      ∫ t in (0 : ℝ)..1, ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F
        (contractInl ∘L fderivWithin ℝ ω (s ×ˢ Icc 0 1) (x, t) ∘L .inl ℝ E ℝ) := by
  have hW : UniqueDiffOn ℝ (s ×ˢ Icc (0 : ℝ) 1) := hsu.prod uniqueDiffOn_Icc_zero_one
  -- the partial derivative in `x` of the integrand, explicitly
  set D : ℝ → E →L[ℝ] E [⋀^Fin n]→L[ℝ] F := fun t ↦
    contractInl ∘L fderivWithin ℝ ω (s ×ˢ Icc 0 1) (x, t) ∘L .inl ℝ E ℝ
  have hpart (t : I) : HasFDerivWithinAt (fun x' ↦ contractInl (ω (x', (t : ℝ)))) (D t) s x :=
    (contractInl (E := E) (F := F) (n := n)).hasFDerivAt.comp_hasFDerivWithinAt x
      ((hω.differentiableOn one_ne_zero _ ⟨hx, t.2⟩).hasFDerivWithinAt.comp x
        (hasFDerivAt_prodMk_left x (t : ℝ)).hasFDerivWithinAt fun x' hx' ↦ ⟨hx', t.2⟩)
  have h := hs.hasFDerivWithinAt_integral_smul_of_contDiffOn (μ := (volume : Measure I))
    (integrable_const (1 : ℝ)) continuous_subtype_val hW
    (contractInl.contDiff.comp_contDiffOn hω) (fun x hx t ↦ ⟨hx, t.2⟩) hx (hsu x hx)
  simp only [Function.comp_apply] at h
  have hDc : ContinuousOn D (Icc 0 1) :=
    continuousOn_const.clm_comp (((hω.continuousOn_fderivWithin hW le_rfl).comp
      (continuous_const.prodMk continuous_id).continuousOn fun _ ht ↦ ⟨hx, ht⟩).clm_comp
        continuousOn_const)
  have hint := integrable_smul_of_continuousOn (μ := (volume : Measure I)) (x := x)
    (integrable_const (1 : ℝ)) continuous_subtype_val (F := fun p : E × ℝ ↦ D p.2)
    (W := {p | p.2 ∈ Icc 0 1}) (hDc.comp continuous_snd.continuousOn fun _ hp ↦ hp) fun t ↦ t.2
  simp only [one_smul] at hint
  calc extDerivWithin (cylinderHomotopy ω) s x
      = ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F (∫ t : I, D t) := by
        rw [extDerivWithin, cylinderHomotopy_eq_integral_unitInterval,
          h.fderivWithin (hsu x hx), ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
        simp only [one_smul]
        exact (hpart t).fderivWithin (hsu x hx)
    _ = ∫ t : I, ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F (D t) :=
        (ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
          (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F (n := n)) hint).symm
    _ = _ := by rw [intervalIntegral_eq_integral_unitInterval]

/-- **The cylinder homotopy identity** `d (h ω) + h (d ω) = ι₁^* ω - ι₀^* ω`, with exterior
derivatives within `s` and within the cylinder `s ×ˢ Icc 0 1`, for a form `C¹` on the cylinder
over a convex set `s` with unique derivatives. Here `ιₜ^* ω` is the pullback of `ω` along the
slice `x ↦ (x, t)`. -/
theorem extDerivWithin_cylinderHomotopy_add_cylinderHomotopy_extDerivWithin (hs : Convex ℝ s)
    (hsu : UniqueDiffOn ℝ s) (hω : ContDiffOn ℝ 1 ω (s ×ˢ Icc 0 1)) {x : E} (hx : x ∈ s) :
    extDerivWithin (cylinderHomotopy ω) s x +
        cylinderHomotopy (extDerivWithin ω (s ×ˢ Icc 0 1)) x =
      (ω (x, 1)).compContinuousLinearMap (.inl ℝ E ℝ) -
        (ω (x, 0)).compContinuousLinearMap (.inl ℝ E ℝ) := by
  have hW : UniqueDiffOn ℝ (s ×ˢ Icc (0 : ℝ) 1) := hsu.prod uniqueDiffOn_Icc_zero_one
  set A : ℝ → (E × ℝ) →L[ℝ] (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F := fun t ↦
    fderivWithin ℝ ω (s ×ˢ Icc 0 1) (x, t)
  have hAc : ContinuousOn A (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (hω.continuousOn_fderivWithin hW le_rfl).comp
      (continuous_const.prodMk continuous_id).continuousOn fun _ ht ↦ ⟨hx, ht⟩
  have hint₁ : IntervalIntegrable (fun t ↦ ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F
      (contractInl ∘L A t ∘L .inl ℝ E ℝ)) volume 0 1 :=
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F).continuous.comp_continuousOn
      (continuousOn_const.clm_comp (hAc.clm_comp continuousOn_const))).intervalIntegrable
  have hint₂ : IntervalIntegrable (fun t ↦ contractInl
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (E × ℝ) F (A t))) volume 0 1 :=
    (contractInl.continuous.comp_continuousOn
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (E × ℝ) F).continuous.comp_continuousOn
        hAc)).intervalIntegrable
  have hh : cylinderHomotopy (extDerivWithin ω (s ×ˢ Icc 0 1)) x = ∫ t in (0 : ℝ)..1,
      contractInl (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (E × ℝ) F (A t)) := by
    simp only [cylinderHomotopy_apply, ← contractInl_apply, extDerivWithin, A,
      ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
  rw [extDerivWithin_cylinderHomotopy_eq hs hsu hω hx, hh,
    ← intervalIntegral.integral_add hint₁ hint₂, ← integral_fderivWithin_apply_eq_sub hsu hω hx]
  -- pointwise, this is the constant-coefficient Cartan formula for `(0, 1)`, pulled back by `inl`
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have key := congrArg (ContinuousAlternatingMap.compContinuousLinearMapCLM (.inl ℝ E ℝ))
    (ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft_comp_add_curryLeft (A t) (0, 1))
  rw [map_add, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_compContinuousLinearMap] at key
  rw [ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
    ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, contractInl_apply, contractInl_def]
  exact key

/-- **Closed forms on a cylinder.** For a form `C¹` on the cylinder `s ×ˢ Icc 0 1` over a convex
set `s` with unique derivatives and closed within the cylinder, the difference of its slice
pullbacks `ι₁^* ω - ι₀^* ω` is the exterior derivative within `s` of its cylinder homotopy
operator. -/
theorem extDerivWithin_cylinderHomotopy (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s)
    (hω : ContDiffOn ℝ 1 ω (s ×ˢ Icc 0 1))
    (hclosed : ∀ p ∈ s ×ˢ Icc (0 : ℝ) 1, extDerivWithin ω (s ×ˢ Icc 0 1) p = 0) {x : E}
    (hx : x ∈ s) :
    extDerivWithin (cylinderHomotopy ω) s x =
      (ω (x, 1)).compContinuousLinearMap (.inl ℝ E ℝ) -
        (ω (x, 0)).compContinuousLinearMap (.inl ℝ E ℝ) := by
  have h0 : cylinderHomotopy (extDerivWithin ω (s ×ˢ Icc 0 1)) x = 0 := by
    rw [cylinderHomotopy_congr (ω₂ := 0) fun t ht ↦ hclosed (x, t) ⟨hx, ht⟩,
      cylinderHomotopy_zero, Pi.zero_apply]
  simpa [h0] using
    hs.extDerivWithin_cylinderHomotopy_add_cylinderHomotopy_extDerivWithin hsu hω hx

end Convex

namespace TauCeti

/-- The cylinder homotopy operator of a form that is `C^r` on all of `E × ℝ` is `C^r`. -/
theorem contDiff_cylinderHomotopy {r : ℕ∞} {ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F}
    (hω : ContDiff ℝ r ω) : ContDiff ℝ r (cylinderHomotopy ω) :=
  contDiffOn_univ.1 (convex_univ.contDiffOn_cylinderHomotopy uniqueDiffOn_univ hω.contDiffOn)

variable [CompleteSpace F]

/-- **The cylinder homotopy identity** `d (h ω) + h (d ω) = ι₁^* ω - ι₀^* ω` for a form that is
`C¹` on all of `E × ℝ`, with exterior derivatives on the whole spaces. Here `ιₜ^* ω` is the
pullback of `ω` along the slice `x ↦ (x, t)`. -/
theorem extDeriv_cylinderHomotopy_add_cylinderHomotopy_extDeriv
    {ω : E × ℝ → (E × ℝ) [⋀^Fin (n + 1)]→L[ℝ] F} (hω : ContDiff ℝ 1 ω) (x : E) :
    extDeriv (cylinderHomotopy ω) x + cylinderHomotopy (extDeriv ω) x =
      (ω (x, 1)).compContinuousLinearMap (.inl ℝ E ℝ) -
        (ω (x, 0)).compContinuousLinearMap (.inl ℝ E ℝ) := by
  have h := convex_univ.extDerivWithin_cylinderHomotopy_add_cylinderHomotopy_extDerivWithin
    uniqueDiffOn_univ hω.contDiffOn (mem_univ x)
  rwa [extDerivWithin_univ, cylinderHomotopy_congr (ω₂ := extDeriv ω)
    fun t ht ↦ (hω.differentiable one_ne_zero _).extDerivWithin
      ((uniqueDiffOn_univ.prod uniqueDiffOn_Icc_zero_one) _ ⟨mem_univ x, ht⟩)] at h

/-- **The cylinder homotopy identity in degree zero**, `h (d f) = ι₁^* f - ι₀^* f` for a function
`f` that is `C¹` on all of `E × ℝ`, viewed as a `0`-form. -/
theorem cylinderHomotopy_extDeriv_eq_sub {ω : E × ℝ → (E × ℝ) [⋀^Fin 0]→L[ℝ] F}
    (hω : ContDiff ℝ 1 ω) (x : E) :
    cylinderHomotopy (extDeriv ω) x =
      (ω (x, 1)).compContinuousLinearMap (.inl ℝ E ℝ) -
        (ω (x, 0)).compContinuousLinearMap (.inl ℝ E ℝ) := by
  rw [← cylinderHomotopy_extDerivWithin_eq_sub uniqueDiffOn_univ hω.contDiffOn (mem_univ x)]
  exact cylinderHomotopy_congr fun t ht ↦ ((hω.differentiable one_ne_zero _).extDerivWithin
    ((uniqueDiffOn_univ.prod uniqueDiffOn_Icc_zero_one) _ ⟨mem_univ x, ht⟩)).symm

end TauCeti
