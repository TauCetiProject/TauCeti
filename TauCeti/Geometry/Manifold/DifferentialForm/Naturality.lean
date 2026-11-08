/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart

/-!
# Naturality of the manifold exterior derivative

Pullback by a twice continuously differentiable map commutes with the exterior derivative of a
continuously differentiable fixed-coefficient form. The pointwise and on-set forms expose the
local hypotheses needed by later constructions, while the global theorem is the cochain-map law
used by de Rham cohomology; in particular pullback preserves closed forms
(`TauCeti.IsSmoothForm.mextDeriv_mpullback_eq_zero`).

For a map from a subset `s` of a normed space, such as a cylinder `s ×ˢ Icc 0 1` or a simplex,
the within-set pullback commutes with the flat exterior derivative within `s`
(`TauCeti.extDerivWithin_mpullbackWithin`). This is how flat constructions on non-open parameter
domains are compared with the manifold exterior derivative.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 14.26.
* Mathlib's `extDerivWithin_pullback`.
-/

public section

noncomputable section

open Set Filter Bundle
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- At a point where `f` and `g` are differentiable, pullback by `f` of the exterior derivative
of `g` is the exterior derivative of the composite. -/
theorem mpullback_mextDeriv_ofFunction_apply {f : M → M'} {x : M} (hf : MDifferentiableAt I I' f x)
    {g : M' → F} (hg : MDifferentiableAt I' 𝓘(ℝ, F) g (f x)) :
    mpullback I I' f (mextDeriv (RoughForm.ofFunction I' g)) x =
      mextDeriv (RoughForm.ofFunction I (g ∘ f)) x := by
  ext v
  simp only [mpullback_apply, mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, mvfderiv_apply_eq_mfderiv_apply]
  rw [mfderiv_comp x hg hf]
  -- `NormedSpace.fromTangentSpace` is the identity of `F`
  rfl

/-- Pullback by a differentiable map of the exterior derivative of a differentiable function is
the exterior derivative of the composite. -/
theorem mpullback_mextDeriv_ofFunction {f : M → M'} (hf : MDifferentiable I I' f) {g : M' → F}
    (hg : MDifferentiable I' 𝓘(ℝ, F) g) :
    mpullback I I' f (mextDeriv (RoughForm.ofFunction I' g)) =
      mextDeriv (RoughForm.ofFunction I (g ∘ f)) := by
  ext x : 1
  exact mpullback_mextDeriv_ofFunction_apply (hf x) (hg _)

/-- The pullback of the coordinate one-form `dz` of the real line along a real function `h` is
the differential `dh`. -/
theorem SmoothForm.mpullback_realLineCoordForm (h : M → ℝ) :
    TauCeti.mpullback I 𝓘(ℝ) h realLineCoordForm.1 = mextDeriv (RoughForm.ofFunction I h) := by
  ext x v
  rw [TauCeti.mpullback_apply, realLineCoordForm_apply, mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, mvfderiv_apply_eq_mfderiv_apply]

variable [IsManifold I 2 M] [IsManifold I' 2 M']

private theorem inChartAt_mpullback_eventuallyEq {f : M → M'} (x : M)
    (hf : ContMDiffAt I I' 2 f x) (φ : RoughForm I' M' F k) :
    (mpullback I I' f φ).inChartAt x =ᶠ[𝓝[range I] extChartAt I x x]
      fun z ↦ (φ.inChartAt (f x) (writtenInExtChartAt I I' x f z)).compContinuousLinearMap
        (fderivWithin ℝ (writtenInExtChartAt I I' x f) (range I) z) := by
  have hsrc : ∀ᶠ y in 𝓝 x, f y ∈ (extChartAt I' (f x)).source :=
    hf.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I') (f x))
  have h := hsrc.and ((contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hf)
  rw [← map_extChartAt_symm_nhdsWithin_range (I := I) x] at h
  filter_upwards [extChartAt_target_mem_nhdsWithin x, h] with z hz hz'
  exact RoughForm.inChartAt_mpullback_eq_compContinuousLinearMap φ x (f x) hz
    (hz'.2.mdifferentiableAt (by norm_num)) hz'.1

/-- At a point, pullback commutes with the exterior derivative. -/
theorem mpullback_mextDeriv_at {f : M → M'} (hf : ContMDiffAt I I' 2 f x)
    {φ : RoughForm I' M' F k}
    (hφ : ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) 1
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (φ y)) (f x)) :
    mpullback I I' f (mextDeriv φ) x = mextDeriv (mpullback I I' f φ) x := by
  let e := extChartAt I x
  let e' := extChartAt I' (f x)
  let z := e x
  let g := writtenInExtChartAt I I' x f
  have hex : e.symm z = x := by
    simpa only [e, z] using extChartAt_to_inv (I := I) x
  have hz : z ∈ e.target := by
    simpa only [e, z] using mem_extChartAt_target (I := I) x
  have hzrange : z ∈ range I := extChartAt_target_subset_range x hz
  have hgz : g z = e' (f x) := by
    simp only [g, z, e, e', writtenInExtChartAt, Function.comp_apply,
      extChartAt_to_inv]
  have hφcoord : DifferentiableWithinAt ℝ (φ.inChartAt (f x)) (range I') (e' (f x)) := by
    have h := φ.contDiffWithinAt_inChartAt (s := univ) hφ.contMDiffWithinAt
    simpa only [preimage_univ, univ_inter, e'] using
      h.differentiableWithinAt (by norm_num)
  have hg : ContDiffWithinAt ℝ 2 g (range I) z := by
    simpa only [g, z, e, writtenInExtChartAt] using (contMDiffAt_iff.mp hf).2
  have htarget : (f ∘ e.symm) ⁻¹' e'.source ∈ 𝓝[range I] z := by
    have hfc : ContinuousAt f (e.symm z) := by
      simpa only [hex] using hf.continuousAt
    apply (hfc.comp_continuousWithinAt
      (mdifferentiableWithinAt_extChartAt_symm hz).continuousWithinAt).preimage_mem_nhdsWithin
    simpa only [Function.comp_apply, hex] using
      extChartAt_source_mem_nhds (I := I') (f x)
  have hmaps : g ⁻¹' range I' ∈ 𝓝[range I] z := by
    apply mem_of_superset htarget
    intro w hw
    exact extChartAt_target_subset_range (I := I') (f x) (e'.map_source hw)
  have hflat := extDerivWithin_pullback_of_preimage_mem_nhdsWithin
    (f := g) (s := range I) (t := range I') (x := z)
    (hgz.symm ▸ hφcoord) hg (by norm_num) I.uniqueDiffOn
    (I.range_subset_closure_interior hzrange) hzrange hmaps
  rw [hgz] at hflat
  have hpull := inChartAt_mpullback_eventuallyEq x hf φ
  have hpullderiv := hpull.extDerivWithin_eq (hpull.self_of_nhdsWithin hzrange)
  apply ContinuousAlternatingMap.ext
  intro v
  rw [mpullback_apply, mextDeriv_def, mextDeriv_def]
  rw [(hf.mdifferentiableAt (by norm_num)).mfderiv_abuse]
  rw [hpullderiv, hflat]
  rfl

/-- On a set, pullback commutes pointwise with the exterior derivative. -/
theorem mpullback_mextDeriv_on {f : M → M'} {s : Set M}
    (hf : ∀ x ∈ s, ContMDiffAt I I' 2 f x) {φ : RoughForm I' M' F k}
    (hφ : ∀ x ∈ s, ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) 1
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (φ y)) (f x)) :
    ∀ x ∈ s, mpullback I I' f (mextDeriv φ) x =
      mextDeriv (mpullback I I' f φ) x := by
  intro x hx
  exact mpullback_mextDeriv_at (hf x hx) (hφ x hx)

/-- Pullback by a `C²` map commutes with the exterior derivative of a `C¹` form. -/
theorem mpullback_mextDeriv {f : M → M'} (hf : ContMDiff I I' 2 f)
    {φ : RoughForm I' M' F k}
    (hφ : IsSmoothBundleForm (I := I') (F := F) (V := Trivial M' F) 1 φ) :
    mpullback I I' f (mextDeriv φ) = mextDeriv (mpullback I I' f φ) := by
  funext x
  exact mpullback_mextDeriv_at hf.contMDiffAt
    ((isSmoothBundleForm_def 1 φ).mp hφ).contMDiffAt

/-- The pullback of a closed `C¹` form along a `C²` map is closed. -/
theorem IsSmoothForm.mextDeriv_mpullback_eq_zero {θ : RoughForm I' M' F k}
    (hθ : IsSmoothForm I' 1 θ) (hclosed : mextDeriv θ = 0) {f : M → M'} (hf : ContMDiff I I' 2 f) :
    mextDeriv (TauCeti.mpullback I I' f θ) = 0 := by
  rw [← mpullback_mextDeriv hf ((isSmoothBundleForm_def 1 θ).mpr hθ.contMDiff), hclosed,
    mpullback_zero]

section ModelSource

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']

/-- Pullback within a subset `s` of a normed space, along a map that is `C²` within `s`, commutes
with exterior differentiation: the flat exterior derivative within `s` of the pulled-back form is
the pullback of the manifold exterior derivative. The set `s` has unique derivatives and the point
lies in the closure of its interior, as for `extDerivWithin_pullback`; it need not be open. -/
theorem extDerivWithin_mpullbackWithin {f : E'' → M} {s : Set E''} {z : E''}
    (hf : ContMDiffWithinAt 𝓘(ℝ, E'') I 2 f s z) (hs : UniqueDiffOn ℝ s)
    (hzc : z ∈ closure (interior s)) (hz : z ∈ s) {φ : RoughForm I M F k}
    (hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) (f z)) :
    extDerivWithin (mpullbackWithin 𝓘(ℝ, E'') I f s φ) s z =
      mpullbackWithin 𝓘(ℝ, E'') I f s (mextDeriv φ) z := by
  set e := extChartAt I (f z)
  have hfz : f z ∈ e.source := mem_extChartAt_source (f z)
  have hpre : f ⁻¹' e.source ∈ 𝓝[s] z :=
    hf.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds' hfz)
  have hfs : ∀ᶠ w in 𝓝[s] z, ContMDiffWithinAt 𝓘(ℝ, E'') I 2 f s w :=
    nhdsWithin_mono _ (subset_insert z s)
      ((contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin (by simp)).1 hf)
  -- Near `z`, the pullback is the flat pullback of the chart expression of `φ` at `f z`.
  have hloc : mpullbackWithin 𝓘(ℝ, E'') I f s φ =ᶠ[𝓝[s] z] fun w ↦
      (φ.inChartAt (f z) ((e ∘ f) w)).compContinuousLinearMap (fderivWithin ℝ (e ∘ f) s w) := by
    filter_upwards [hpre, hfs, self_mem_nhdsWithin] with w hw hfw hws
    exact RoughForm.mpullbackWithin_eq_compContinuousLinearMap φ (f z) hw
      (hfw.mdifferentiableWithinAt (by norm_num)) (hs w hws)
  have hg : ContDiffWithinAt ℝ 2 (e ∘ f) s z :=
    ((contMDiffAt_extChartAt (I := I) (n := 2) (x := f z)).comp_contMDiffWithinAt z hf)
      |>.contDiffWithinAt
  have hrange : (e ∘ f) ⁻¹' range I ∈ 𝓝[s] z := by
    filter_upwards [hpre] with a ha
    exact extChartAt_target_subset_range (f z) (e.map_source ha)
  have hφc : DifferentiableWithinAt ℝ (φ.inChartAt (f z)) (range I) ((e ∘ f) z) := by
    simpa only [preimage_univ, univ_inter, Function.comp_apply, e] using
      φ.differentiableWithinAt_inChartAt (s := univ) hφ.mdifferentiableWithinAt
  rw [hloc.extDerivWithin_eq (hloc.self_of_nhdsWithin hz),
    extDerivWithin_pullback_of_preimage_mem_nhdsWithin hφc hg (by simp) hs hzc hz hrange,
    RoughForm.mpullbackWithin_eq_compContinuousLinearMap (mextDeriv φ) (f z) hfz
      (hf.mdifferentiableWithinAt (by norm_num)) (hs z hz)]
  simp only [Function.comp_apply, e, RoughForm.inChartAt_extChartAt_self, mextDeriv_def]

end ModelSource

namespace SmoothForm

/-- The bundled exterior derivative commutes with smooth pullback. -/
theorem mextDerivₗ_mpullback (f : M → M') (hf : ContMDiff I I' ∞ f) (k : ℕ)
    (φ : SmoothForm I' M' F k) :
    mextDerivₗ I k (mpullback f hf φ) =
      mpullback f hf (mextDerivₗ I' k φ) := by
  apply Subtype.ext
  rw [coe_mpullback, mextDerivₗ_apply, mextDerivₗ_apply]
  rw [coe_mpullback]
  have hφ : IsSmoothBundleForm (I := I') (F := F) (V := Trivial M' F) 1 φ.1 :=
    (isSmoothBundleForm_def 1 φ.1).mpr (φ.contMDiff.of_le (by simp))
  exact (TauCeti.mpullback_mextDeriv (hf.of_le (by simp)) hφ).symm

end SmoothForm

end TauCeti

end
