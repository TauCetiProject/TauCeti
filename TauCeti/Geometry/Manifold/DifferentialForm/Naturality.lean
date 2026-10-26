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
used by de Rham cohomology.

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
  [IsManifold I 2 M] [IsManifold I' 2 M']

private theorem inChartAt_mpullback_eventuallyEq {f : M → M'} (x : M)
    (hf : ContMDiffAt I I' 2 f x) (φ : RoughForm I' M' F k) :
    (mpullback I I' f φ).inChartAt x =ᶠ[𝓝[range I] extChartAt I x x]
      fun z ↦ (φ.inChartAt (f x) (writtenInExtChartAt I I' x f z)).compContinuousLinearMap
        (fderivWithin ℝ (writtenInExtChartAt I I' x f) (range I) z) := by
  let e := extChartAt I x
  let e' := extChartAt I' (f x)
  let g := writtenInExtChartAt I I' x f
  have hex : e.symm (e x) = x := by
    simpa only [e] using extChartAt_to_inv (I := I) x
  -- Near `e x` in the model range, the chart inverse stays where `f` is `C²` and lands, after
  -- `f`, in the source of the target chart.
  have hflocal : ∀ᶠ y in 𝓝[range I] e x, ContMDiffAt I I' 2 f (e.symm y) := by
    have he : ContinuousWithinAt e.symm (range I) (e x) :=
      (mdifferentiableWithinAt_extChartAt_symm
        (mem_extChartAt_target (I := I) x)).continuousWithinAt
    have hf' := (contMDiffAt_iff_contMDiffAt_nhds (n := (2 : WithTop ℕ∞)) (by norm_num)).mp hf
    have hlim := he.tendsto
    rw [hex] at hlim
    exact hlim.eventually hf'
  have hsource : e.target ∈ 𝓝[range I] e x := extChartAt_target_mem_nhdsWithin x
  have htarget : (f ∘ e.symm) ⁻¹' e'.source ∈ 𝓝[range I] e x := by
    have hfc : ContinuousAt f (e.symm (e x)) := by
      simpa only [hex] using hf.continuousAt
    apply (hfc.comp_continuousWithinAt
      (mdifferentiableWithinAt_extChartAt_symm
        (mem_extChartAt_target (I := I) x)).continuousWithinAt).preimage_mem_nhdsWithin
    convert extChartAt_source_mem_nhds (I := I') (f x) using 1
    simp only [Function.comp_apply, hex]
  filter_upwards [hsource, htarget, hflocal] with z hz hzf hfx
  -- At such a point `z`, the coordinate expression `g` is `C²`, stays in the target model range,
  -- and agrees with `f ∘ e.symm` after composing with `e'.symm`.
  have hzf' : f (e.symm z) ∈ e'.source := hzf
  have hsmooth : ContMDiffWithinAt 𝓘(ℝ, E) I 2 e.symm (range I) z :=
    contMDiffWithinAt_extChartAt_symm_range x hz
  have hcoord : ContDiffWithinAt ℝ 2 g (range I) z := by
    have hchart : ContMDiffAt I' 𝓘(ℝ, E') 2 e' (f (e.symm z)) :=
      contMDiffAt_extChartAt' (by simpa only [e', extChartAt_source] using hzf')
    have hfsx : ContMDiffWithinAt 𝓘(ℝ, E) I' 2 (f ∘ e.symm) (range I) z :=
      hfx.contMDiffWithinAt.comp z hsmooth (mapsTo_univ _ _)
    simpa only [g, writtenInExtChartAt, Function.comp_assoc] using
      (hchart.contMDiffWithinAt.comp z hfsx (mapsTo_univ _ _)).contDiffWithinAt
  have hpre : (f ∘ e.symm) ⁻¹' e'.source ∈ 𝓝[range I] z := by
    apply (hfx.continuousAt.comp_continuousWithinAt
      hsmooth.continuousWithinAt).preimage_mem_nhdsWithin
    exact extChartAt_source_mem_nhds' hzf
  have hmaps : g ⁻¹' range I' ∈ 𝓝[range I] z := by
    apply mem_of_superset hpre
    intro w hw
    exact extChartAt_target_subset_range (I := I') (f x) (e'.map_source hw)
  have hcomp : (e'.symm ∘ g) =ᶠ[𝓝[range I] z] (f ∘ e.symm) := by
    filter_upwards [hpre] with w hw
    exact e'.left_inv hw
  -- Pull `φ` back along both factorizations `f ∘ e.symm` and `e'.symm ∘ g` and compare.
  have hleft := mpullbackWithin_comp_of_preimage_mem_nhdsWithin
    (I := 𝓘(ℝ, E)) (I' := I) (I'' := I') (f := e.symm) (g := f)
    (s := range I) (t := univ) (x := z)
    (hsmooth.mdifferentiableWithinAt (by norm_num))
    (hfx.mdifferentiableAt (by norm_num)).mdifferentiableWithinAt
    (by simp) ((I.uniqueDiffOn z (extChartAt_target_subset_range x hz)).uniqueMDiffWithinAt) φ
  have hright := mpullbackWithin_comp_of_preimage_mem_nhdsWithin
    (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E')) (I'' := I') (f := g) (g := e'.symm)
    (s := range I) (t := range I') (x := z)
    (hcoord.differentiableWithinAt (by norm_num)).mdifferentiableWithinAt
    (mdifferentiableWithinAt_extChartAt_symm (e'.map_source hzf)) hmaps
    ((I.uniqueDiffOn z (extChartAt_target_subset_range x hz)).uniqueMDiffWithinAt) φ
  have hcomposite :
      mpullbackWithin 𝓘(ℝ, E) I' (e'.symm ∘ g) (range I) φ z =
        mpullbackWithin 𝓘(ℝ, E) I' (f ∘ e.symm) (range I) φ z := by
    ext v
    simp only [mpullbackWithin_apply]
    have hzrange : z ∈ range I := extChartAt_target_subset_range x hz
    rw [hcomp.mfderivWithin_eq (hcomp.self_of_nhdsWithin hzrange)]
    rw [hcomp.self_of_nhdsWithin hzrange]
    simp [tangentSpaceCast]
  simp only [mpullbackWithin_univ] at hleft
  have hchain := hleft.symm.trans (hcomposite.symm.trans hright)
  -- Both chart expressions of forms are pullbacks along inverse extended charts.
  have hsourceForm :
      (mpullback I I' f φ).inChartAt x z =
        mpullbackWithin 𝓘(ℝ, E) I e.symm (range I) (mpullback I I' f φ) z := by
    apply ContinuousAlternatingMap.ext
    intro v
    let w : Fin k → TangentSpace 𝓘(ℝ, E) z := v
    have h₁ := RoughForm.inChartAt_apply (mpullback I I' f φ) x z v
    have h₂ := mpullbackWithin_apply e.symm (range I) (mpullback I I' f φ) z w
    convert h₁.trans h₂.symm using 1
  have htargetForm :
      φ.inChartAt (f x) (g z) =
        mpullbackWithin 𝓘(ℝ, E') I' e'.symm (range I') φ (g z) := by
    apply ContinuousAlternatingMap.ext
    intro v
    let w : Fin k → TangentSpace 𝓘(ℝ, E') (g z) := v
    have h₁ := RoughForm.inChartAt_apply φ (f x) (g z) v
    have h₂ := mpullbackWithin_apply e'.symm (range I') φ (g z) w
    convert h₁.trans h₂.symm using 1
  -- Pullback along the model-space map `g` is the flat pullback by its Fréchet derivative.
  rw [← hsourceForm, mpullbackWithin_eq_flat] at hchain
  beta_reduce at hchain
  rw [← htargetForm] at hchain
  apply ContinuousAlternatingMap.ext
  intro v
  let w : Fin k → TangentSpace 𝓘(ℝ, E) z := v
  have hv := congrArg (fun a ↦ a w) hchain
  dsimp only [Trivial] at hv
  convert hv using 1
  -- Model-space tangent spaces are definitionally the model spaces.
  rfl

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
