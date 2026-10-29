/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.CylinderHomotopy
public import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Relative Poincaré primitives by fiber scaling

On a product `E × N`, scale only the normal coordinate: `H((q, p), t) = (q, t • p)`.
Integrating the time contraction of `H*ω` gives `fiberwisePoincareHomotopy ω`.
This form vanishes as a full ambient tensor at every `(q, 0)`, even if `ω` does not.
For a closed form on an open convex set stable under this scaling, its exterior derivative is
`ω - r*ω`, where `r(q, p) = (q, 0)`. Thus vanishing of the restriction of `ω` to the zero
section suffices to obtain a primitive vanishing there. This is the local product construction
used to compare symplectic forms relative to a submanifold.

All positive degrees and Banach coefficient spaces are allowed. The base and normal spaces
need not be finite-dimensional or complete. Regularity and closedness are required only on
the specified set, which may be an adapted coordinate box.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Springer, 2001, §6
  (the relative Poincaré lemma).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4
  (integration along a homotopy).
-/

public section

noncomputable section

open Set MeasureTheory

namespace TauCeti

variable {E N F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

private def fiberScaling (z : (E × N) × ℝ) : E × N := (z.1.1, z.2 • z.1.2)

private theorem contDiff_fiberScaling {r : WithTop ℕ∞} :
    ContDiff ℝ r (fiberScaling (E := E) (N := N)) :=
  contDiff_fst.fst.prodMk (contDiff_snd.smul contDiff_fst.snd)

private theorem fderiv_fiberScaling_apply (z v : (E × N) × ℝ) :
    fderiv ℝ fiberScaling z v = (v.1.1, z.2 • v.1.2 + v.2 • z.1.2) := by
  unfold fiberScaling
  have h0 := hasFDerivAt_id (𝕜 := ℝ) z
  have h := h0.fst.fst.prodMk (h0.snd.smul h0.fst.snd)
  simpa [Pi.smul_apply] using DFunLike.congr_fun h.fderiv v

private def fiberScalingPullback
    (ω : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F) :
    (E × N) × ℝ → ((E × N) × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F :=
  fun z ↦ (ω (fiberScaling z)).compContinuousLinearMap (fderiv ℝ fiberScaling z)

/-- Integrate the time contraction of the pullback by `(q, p, t) ↦ (q, t • p)`.
This relative Poincaré operator fixes the base and contracts the normal coordinate. -/
def fiberwisePoincareHomotopy
    (ω : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F) :
    E × N → (E × N) [⋀^Fin k]→L[ℝ] F :=
  cylinderHomotopy (fiberScalingPullback ω)

/-- The relative primitive evaluated as an integral of ambient alternating tensors.
The remaining arguments are transformed by `(v, w) ↦ (v, t • w)`. -/
theorem fiberwisePoincareHomotopy_apply
    (ω : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F) (x : E × N) :
    fiberwisePoincareHomotopy ω x =
      ∫ t in (0 : ℝ)..1, ((ω (x.1, t • x.2)).curryLeft (0, x.2)).compContinuousLinearMap
        ((ContinuousLinearMap.id ℝ E).prodMap (t • ContinuousLinearMap.id ℝ N)) := by
  rw [fiberwisePoincareHomotopy, cylinderHomotopy_apply]
  congr 1
  funext t
  ext v
  simp only [fiberScalingPullback, fiberScaling,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp [fderiv_fiberScaling_apply]
  | succ j =>
    simp [fderiv_fiberScaling_apply]
    rfl

/-- The relative Poincaré operator vanishes on the zero section as a full ambient tensor. -/
@[simp]
theorem fiberwisePoincareHomotopy_zeroSection
    (ω : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F) (q : E) :
    fiberwisePoincareHomotopy ω (q, 0) = 0 := by
  rw [fiberwisePoincareHomotopy_apply]
  have hz (t : ℝ) : ((ω (q, t • (0 : N))).curryLeft (0, (0 : N))).compContinuousLinearMap
      ((ContinuousLinearMap.id ℝ E).prodMap (t • ContinuousLinearMap.id ℝ N)) = 0 := by
    ext v
    simp [Prod.mk_zero_zero]
  simp only [hz, intervalIntegral.integral_zero]

private theorem mapsTo_fiberScaling_segment (x : E × N) :
    MapsTo fiberScaling ({x} ×ˢ Icc (0 : ℝ) 1) (segment ℝ (x.1, 0) x) := by
  rintro ⟨y, t⟩ ⟨rfl : y = x, ht⟩
  rw [segment_eq_image']
  exact ⟨t, ht, by ext <;> simp [fiberScaling]⟩

private theorem continuousOn_fiberScalingPullback {s : Set (E × N)} {t : Set ((E × N) × ℝ)}
    {ω : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F}
    (hω : ContinuousOn ω s) (hst : MapsTo fiberScaling t s) :
    ContinuousOn (fiberScalingPullback ω) t :=
  (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp
    ((contDiff_fiberScaling (r := 1)).continuous_fderiv one_ne_zero)).continuousOn.clm_apply
      (hω.comp (contDiff_fiberScaling (r := 0)).continuous.continuousOn hst)

/-- The relative Poincaré operator at `x` only depends on the form along the segment from
`(x.1, 0)` to `x`. -/
theorem fiberwisePoincareHomotopy_congr {x : E × N}
    {ω₁ ω₂ : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F}
    (h : EqOn ω₁ ω₂ (segment ℝ (x.1, 0) x)) :
    fiberwisePoincareHomotopy ω₁ x = fiberwisePoincareHomotopy ω₂ x :=
  cylinderHomotopy_congr fun t ht ↦ by
    rw [fiberScalingPullback, fiberScalingPullback,
      h (mapsTo_fiberScaling_segment x (mem_prod.2 ⟨mem_singleton x, ht⟩))]

/-- The relative Poincaré operator of the zero form is zero. -/
@[simp]
theorem fiberwisePoincareHomotopy_zero :
    fiberwisePoincareHomotopy (0 : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F) = 0 := by
  have h : fiberScalingPullback (0 : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F) = 0 := by
    funext z
    ext v
    simp [fiberScalingPullback]
  rw [fiberwisePoincareHomotopy, h, cylinderHomotopy_zero]

/-- The relative Poincaré operator commutes with real scalar multiplication of forms. -/
theorem fiberwisePoincareHomotopy_smul (c : ℝ)
    (ω : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F) :
    fiberwisePoincareHomotopy (c • ω) = c • fiberwisePoincareHomotopy ω := by
  have h : fiberScalingPullback (c • ω) = c • fiberScalingPullback ω := by
    funext z
    ext v
    simp [fiberScalingPullback]
  rw [fiberwisePoincareHomotopy, h, cylinderHomotopy_smul, fiberwisePoincareHomotopy]

/-- The relative Poincaré operator is additive on forms that are continuous along the segment
from `(x.1, 0)` to `x`. -/
theorem fiberwisePoincareHomotopy_add_apply {x : E × N}
    {ω₁ ω₂ : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F}
    (h₁ : ContinuousOn ω₁ (segment ℝ (x.1, 0) x)) (h₂ : ContinuousOn ω₂ (segment ℝ (x.1, 0) x)) :
    fiberwisePoincareHomotopy (ω₁ + ω₂) x =
      fiberwisePoincareHomotopy ω₁ x + fiberwisePoincareHomotopy ω₂ x := by
  have h : fiberScalingPullback (ω₁ + ω₂) = fiberScalingPullback ω₁ + fiberScalingPullback ω₂ := by
    funext z
    ext v
    simp [fiberScalingPullback]
  rw [fiberwisePoincareHomotopy, h, cylinderHomotopy_add_apply
    (continuousOn_fiberScalingPullback h₁ (mapsTo_fiberScaling_segment x))
    (continuousOn_fiberScalingPullback h₂ (mapsTo_fiberScaling_segment x))]
  rfl

private theorem contDiffOn_fiberScalingPullback {s : Set (E × N)} {r : ℕ∞}
    {ω : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F}
    (hω : ContDiffOn ℝ r ω s)
    (hscale : ∀ x ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, (x.1, t • x.2) ∈ s) :
    ContDiffOn ℝ r (fiberScalingPullback ω) (s ×ˢ Icc 0 1) := by
  have hD : ContDiff ℝ r (fderiv ℝ (fiberScaling (E := E) (N := N))) :=
    (contDiff_fiberScaling (r := (r : WithTop ℕ∞) + 1)).fderiv_right le_rfl
  exact ((ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := ℝ) (E := (E × N) × ℝ) (F := E × N) (G := F) (ι := Fin (k + 1)) r).comp
    hD).contDiffOn.clm_apply
      (hω.comp contDiff_fiberScaling.contDiffOn fun z hz ↦ hscale z.1 hz.1 z.2 hz.2)

/-- Fiberwise Poincaré integration preserves regularity on a convex set stable under scaling
the normal coordinate. -/
theorem _root_.Convex.contDiffOn_fiberwisePoincareHomotopy {s : Set (E × N)} (hs : Convex ℝ s)
    (hsu : UniqueDiffOn ℝ s) {r : ℕ∞}
    {ω : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F}
    (hω : ContDiffOn ℝ r ω s)
    (hscale : ∀ x ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, (x.1, t • x.2) ∈ s) :
    ContDiffOn ℝ r (fiberwisePoincareHomotopy ω) s :=
  hs.contDiffOn_cylinderHomotopy hsu (contDiffOn_fiberScalingPullback hω hscale)

variable [CompleteSpace F]

/-- The relative Poincaré identity for a closed form: `dKω = ω - r*ω`, where
`r(q, p) = (q, 0)`. Only the tangential restriction of `ω` occurs in the correction term. -/
theorem _root_.Convex.extDeriv_fiberwisePoincareHomotopy {s : Set (E × N)} (hs : Convex ℝ s)
    (hso : IsOpen s) {ω : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F}
    (hω : ContDiffOn ℝ 1 ω s)
    (hscale : ∀ x ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, (x.1, t • x.2) ∈ s)
    (hclosed : ∀ x ∈ s, extDeriv ω x = 0) {x : E × N} (hx : x ∈ s) :
    extDeriv (fiberwisePoincareHomotopy ω) x = ω x -
      (ω (x.1, 0)).compContinuousLinearMap
        ((ContinuousLinearMap.id ℝ E).prodMap (0 : N →L[ℝ] N)) := by
  have hsu : UniqueDiffOn ℝ s := hso.uniqueDiffOn
  have hW := hsu.prod uniqueDiffOn_Icc_zero_one
  have hψ := contDiffOn_fiberScalingPullback hω hscale
  have hcl (z : (E × N) × ℝ) (hz : z ∈ s ×ˢ Icc (0 : ℝ) 1) :
      extDerivWithin (fiberScalingPullback ω) (s ×ˢ Icc 0 1) z = 0 := by
    have hderiv (w : (E × N) × ℝ) (hw : w ∈ s ×ˢ Icc (0 : ℝ) 1) :
        fderivWithin ℝ fiberScaling (s ×ˢ Icc 0 1) w = fderiv ℝ fiberScaling w :=
      ((contDiff_fiberScaling (r := 1)).differentiable one_ne_zero w).fderivWithin (hW w hw)
    have hxc : z ∈ closure (interior (s ×ˢ Icc (0 : ℝ) 1)) := by
      have hzcl : z ∈ closure s ×ˢ Icc (0 : ℝ) 1 := ⟨subset_closure hz.1, hz.2⟩
      simpa [interior_prod_eq, hso.interior_eq, closure_prod_eq,
        closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)] using hzcl
    have hωz := ((hω _ (hscale z.1 hz.1 z.2 hz.2)).contDiffAt
      (hso.mem_nhds (hscale z.1 hz.1 z.2 hz.2))).differentiableAt one_ne_zero
    have hnat := extDerivWithin_pullback (r := 2) (f := fiberScaling) (x := z)
      (t := univ) hωz.differentiableWithinAt
      (contDiff_fiberScaling (r := 2)).contDiffWithinAt (by norm_num) hW hxc hz
      (mapsTo_univ _ _)
    have heq : (fun w ↦ (ω (fiberScaling w)).compContinuousLinearMap
        (fderivWithin ℝ fiberScaling (s ×ˢ Icc 0 1) w))
        =ᶠ[nhdsWithin z (s ×ˢ Icc 0 1)] fiberScalingPullback ω := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      rw [hderiv w hw]
      rfl
    rw [← heq.extDerivWithin_eq_of_mem hz, hnat, extDerivWithin_univ]
    simp only [fiberScaling, hclosed _ (hscale z.1 hz.1 z.2 hz.2)]
    ext v
    rfl
  have h := hs.extDerivWithin_cylinderHomotopy hsu hψ hcl hx
  have hK := ((hs.contDiffOn_cylinderHomotopy hsu hψ _ hx).contDiffAt
    (hso.mem_nhds hx)).differentiableAt one_ne_zero
  rw [extDerivWithin, hK.fderivWithin (hsu _ hx), ← extDeriv] at h
  refine h.trans ?_
  congr 1 <;> ext v <;>
    simp only [fiberScalingPullback, fiberScaling, one_smul, zero_smul,
      ContinuousAlternatingMap.compContinuousLinearMap_apply] <;>
    congr 1 <;> funext i <;>
    simp only [Function.comp_def, fderiv_fiberScaling_apply,
      ContinuousLinearMap.inl_apply, one_smul, zero_smul, add_zero]
  all_goals rfl

/-- If the tangential restriction to the zero section vanishes, fiber scaling gives a
primitive whose exterior derivative is the original closed form. No ambient vanishing
of the original form on the zero section is required. -/
theorem _root_.Convex.extDeriv_fiberwisePoincareHomotopy_eq {s : Set (E × N)}
    (hs : Convex ℝ s) (hso : IsOpen s)
    {ω : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F}
    (hω : ContDiffOn ℝ 1 ω s)
    (hscale : ∀ x ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, (x.1, t • x.2) ∈ s)
    (hclosed : ∀ x ∈ s, extDeriv ω x = 0)
    (hzero : ∀ q : E, (q, (0 : N)) ∈ s →
      (ω (q, 0)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ E N) = 0)
    {x : E × N} (hx : x ∈ s) :
    extDeriv (fiberwisePoincareHomotopy ω) x = ω x := by
  rw [hs.extDeriv_fiberwisePoincareHomotopy hso hω hscale hclosed hx]
  have hx0 : (x.1, (0 : N)) ∈ s := by simpa using hscale x hx 0 (by simp)
  have hc : (ω (x.1, 0)).compContinuousLinearMap
      ((ContinuousLinearMap.id ℝ E).prodMap (0 : N →L[ℝ] N)) = 0 := by
    ext v
    have h := congrArg (fun α : E [⋀^Fin (k + 1)]→L[ℝ] F ↦ α (fun i ↦ (v i).1))
      (hzero x.1 hx0)
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h ⊢
    exact h
  rw [hc, sub_zero]

/-- **The relative Poincaré lemma on an adapted convex neighborhood.** A closed form of
positive degree whose restriction to the zero section vanishes has a primitive of the same
regularity, vanishing there as a full ambient tensor. The neighborhood must be stable under
scaling the normal coordinate towards zero. -/
theorem _root_.Convex.exists_contDiffOn_relative_primitive {s : Set (E × N)}
    (hs : Convex ℝ s) (hso : IsOpen s) {r : ℕ∞} (hr : 1 ≤ r)
    {ω : E × N → (E × N) [⋀^Fin (k + 1)]→L[ℝ] F}
    (hω : ContDiffOn ℝ r ω s)
    (hscale : ∀ x ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, (x.1, t • x.2) ∈ s)
    (hclosed : ∀ x ∈ s, extDeriv ω x = 0)
    (hzero : ∀ q : E, (q, (0 : N)) ∈ s →
      (ω (q, 0)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ E N) = 0) :
    ∃ β : E × N → (E × N) [⋀^Fin k]→L[ℝ] F,
      ContDiffOn ℝ r β s ∧ (∀ q : E, β (q, 0) = 0) ∧ ∀ x ∈ s, extDeriv β x = ω x := by
  refine ⟨fiberwisePoincareHomotopy ω, hs.contDiffOn_fiberwisePoincareHomotopy
    hso.uniqueDiffOn hω hscale, fiberwisePoincareHomotopy_zeroSection ω, fun x hx ↦ ?_⟩
  exact hs.extDeriv_fiberwisePoincareHomotopy_eq hso
    (hω.of_le (by exact_mod_cast hr)) hscale hclosed hzero hx

end TauCeti
