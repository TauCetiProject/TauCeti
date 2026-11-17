/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Connection
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# First jets of differential forms

This file studies the first jet of a differential form (`TauCeti.RoughForm`), especially at a
point where the form vanishes as a full ambient tensor.

## Pullback at a zero

At a point `x` where a form `η` vanishes at `f x`, the pullback `f^* η` read in preferred charts is
the flat pullback `z ↦ (η.inChartAt α (g z)).compContinuousLinearMap (Dg(z))` along the chart
expression `g` of `f`. Because `η.inChartAt α` vanishes at `g z₀`, differentiating the product
needs no derivative of `z ↦ compContinuousLinearMapCLM (Dg(z))`, only its continuity; hence `f`
only needs to be `C¹` at `x` (not `C²`), and the derivative transforms tensorially by the pullback
and chain rule (`TauCeti.RoughForm.hasFDerivWithinAt_inChartAt_mpullback_of_eq_zero`). In
particular, pulling back along a `C¹` map preserves zero first jets at a zero
(`TauCeti.RoughForm.hasFDerivWithinAt_inChartAt_mpullback_zero`,
`TauCeti.RoughForm.hasFDerivAt_inChartAt_mpullback_zero`), and having zero chart derivative at a
zero is chart-independent (`TauCeti.RoughForm.hasFDerivWithinAt_inChartAt_congr_chart_of_eq_zero`).

## Identification with `FirstJetBundle` and covariant derivatives

Near the chart centre `x`, the coordinate expression `η.inChartAt x` agrees with the local
representative `TauCeti.FirstJetBundle.localRep` of `η` as a section of the alternating-map bundle
`x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] F` (`TauCeti.RoughForm.localRep_eventuallyEq_inChartAt`).
Thus for a `C²` manifold, `η` has zero first jet `FirstJetBundle.jet` at `x` precisely when
`η x = 0` and the chart derivative of `η.inChartAt x` vanishes at `extChartAt I x x`
(`TauCeti.RoughForm.jet_eq_zero_iff`, `TauCeti.RoughForm.jet_eq_zero_iff_hasFDerivWithinAt`,
`TauCeti.RoughForm.jet_eq_zero_iff_hasFDerivAt`). For finite-dimensional model and coefficient
spaces, and any auxiliary covariant derivative `∇` on the bundle of `k`-forms over a set containing
`x`, a form differentiable at `x` has zero first jet at `x` if and only if both `η x = 0` and
`∇ η x = 0` (`TauCeti.RoughForm.jet_eq_zero_iff_covariantDerivative`,
`TauCeti.RoughForm.covariantDerivative_eq_zero_iff_hasFDerivWithinAt_inChartAt`,
`TauCeti.RoughForm.covariantDerivative_eq_zero_iff_hasFDerivAt_inChartAt`).

## Degree-one forms

Under `ContinuousAlternatingMap.ofSubsingleton`, the local representative of a bundle-valued
degree-one form is linearly isometric to the local representative of the corresponding section of
the bundle of linear maps `TangentSpace I x →L[ℝ] V x`
(`TauCeti.hasFDerivWithinAt_localRep_ofSubsingleton_iff`,
`TauCeti.SmoothForm.hasFDerivWithinAt_localRep_degreeOneEquiv_iff`). For `F = ℝ`, this identifies
zero first jets of one-forms with zero first jets of sections of the cotangent bundle.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, §7 (relative Moser theorem and primitives with vanishing first jet).
* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.16–12.17, §17.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology

namespace TauCeti

/-! ### Pullback of chart derivatives at a zero of a differential form -/

namespace RoughForm

section PullbackAtZero

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- **Pullback derivative at a zero of a differential form.** Let `f : M → M'` be `C¹` at `x`,
and let `η` be a `k`-form vanishing at `f x` whose coordinate expression in the preferred chart at
`α` has derivative `η'` within `range I'` at `extChartAt I' α (f x)`. Then in any preferred chart
at `β` containing `x`, the coordinate expression of `f^* η` is differentiable within `range I` at
`extChartAt I β x`, with derivative given by composing `η' ∘ Dg` with flat pullback along `Dg`,
where `g = extChartAt I' α ∘ f ∘ (extChartAt I β).symm`. Only `C¹` regularity of `f` is needed,
because the factor `η` vanishes at `f x`. -/
theorem hasFDerivWithinAt_inChartAt_mpullback_of_eq_zero
    {η : RoughForm I' M' F k} {f : M → M'} {β x : M} {α : M'}
    (hx : x ∈ (extChartAt I β).source) (hfx : f x ∈ (extChartAt I' α).source)
    (hf : ContMDiffAt I I' 1 f x) (hη0 : η (f x) = 0)
    {η' : E' →L[ℝ] E' [⋀^Fin k]→L[ℝ] F}
    (hη : HasFDerivWithinAt (η.inChartAt α) η' (range I') (extChartAt I' α (f x))) :
    HasFDerivWithinAt ((mpullback I I' f η).inChartAt β)
      ((ContinuousAlternatingMap.compContinuousLinearMapCLM
          (fderivWithin ℝ (extChartAt I' α ∘ f ∘ (extChartAt I β).symm) (range I)
            (extChartAt I β x))).comp
        (η'.comp (fderivWithin ℝ (extChartAt I' α ∘ f ∘ (extChartAt I β).symm) (range I)
          (extChartAt I β x))))
      (range I) (extChartAt I β x) := by
  set z₀ := extChartAt I β x
  set g : E → E' := extChartAt I' α ∘ f ∘ (extChartAt I β).symm
  have hz₀ : z₀ ∈ (extChartAt I β).target := (extChartAt I β).map_source hx
  have hz₀_range : z₀ ∈ range I := extChartAt_target_subset_range β hz₀
  have hgz₀ : g z₀ = extChartAt I' α (f x) := by
    simp only [g, Function.comp_apply, z₀, (extChartAt I β).left_inv hx]
  -- `g` is `C¹` within `range I` at `z₀`, so `fderivWithin ℝ g (range I)` is continuous there.
  have hg_contMDiff : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E') 1 g (range I) z₀ := by
    have h₁ : ContMDiffAt I 𝓘(ℝ, E') 1 (extChartAt I' α ∘ f) x :=
      (contMDiffAt_extChartAt' (by rwa [extChartAt_source] at hfx)).comp x hf
    have h₂ : ContMDiffWithinAt 𝓘(ℝ, E) I 1 (extChartAt I β).symm (range I) z₀ :=
      contMDiffWithinAt_extChartAt_symm_range β hz₀
    rw [← (extChartAt I β).left_inv hx] at h₁
    exact h₁.comp_contMDiffWithinAt z₀ h₂
  have hg : ContDiffWithinAt ℝ 1 g (range I) z₀ :=
    contMDiffWithinAt_iff_contDiffWithinAt.1 hg_contMDiff
  have hDg_cont : ContinuousWithinAt (fderivWithin ℝ g (range I)) (range I) z₀ :=
    (hg.fderivWithin_right (m := 0) I.uniqueDiffOn (by simp) hz₀_range).continuousWithinAt
  have hc : ContinuousWithinAt
      (fun z ↦ (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderivWithin ℝ g (range I) z) :
        (E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] E [⋀^Fin k]→L[ℝ] F)) (range I) z₀ :=
    (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.continuousWithinAt).comp
      hDg_cont (mapsTo_univ _ _)
  -- The composition `η.inChartAt α ∘ g` vanishes at `z₀` and has derivative `η' ∘ Dg(z₀)`.
  have hη_at : HasFDerivWithinAt (η.inChartAt α) η' (range I') (g z₀) := hgz₀ ▸ hη
  have hmaps : MapsTo g (range I) (range I') := fun z _ ↦ by
    simp only [g, Function.comp_apply, extChartAt_coe]
    exact mem_range_self _
  have hu : HasFDerivWithinAt (fun z ↦ η.inChartAt α (g z))
      (η'.comp (fderivWithin ℝ g (range I) z₀)) (range I) z₀ :=
    hη_at.comp z₀ (hg.differentiableWithinAt one_ne_zero).hasFDerivWithinAt hmaps
  have hη0_chart : η.inChartAt α (extChartAt I' α (f x)) = 0 := by
    ext v
    rw [inChartAt_apply, (extChartAt I' α).left_inv hfx, hη0]
    simp
  have hu0 : η.inChartAt α (g z₀) = 0 := hgz₀ ▸ hη0_chart
  have hd := HasFDerivWithinAt.clm_apply_of_eq_zero hc hu hu0
  -- Compare with `(mpullback I I' f η).inChartAt β` on a neighbourhood of `z₀` within `range I`.
  have hf_ev : ∀ᶠ y in 𝓝 x, ContMDiffAt I I' 1 f y :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hf
  have hsrc_ev : ∀ᶠ y in 𝓝 x, f y ∈ (extChartAt I' α).source :=
    hf.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source α).mem_nhds hfx)
  have hsymm_tend : Tendsto (extChartAt I β).symm (𝓝[range I] z₀) (𝓝 x) := by
    have h := (continuousOn_extChartAt_symm β z₀ hz₀).mono_of_mem_nhdsWithin
      (extChartAt_target_mem_nhdsWithin_of_mem hz₀)
    simpa only [ContinuousWithinAt, z₀, (extChartAt I β).left_inv hx] using h
  refine hd.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hz₀,
      hsymm_tend.eventually hf_ev, hsymm_tend.eventually hsrc_ev] with z hz hfz hfzα
    exact inChartAt_mpullback_eq_compContinuousLinearMap η β α hz
      (hfz.mdifferentiableAt one_ne_zero) hfzα
  · exact inChartAt_mpullback_eq_compContinuousLinearMap η β α hz₀
      ((extChartAt I β).left_inv hx ▸ hf.mdifferentiableAt one_ne_zero)
      ((extChartAt I β).left_inv hx ▸ hfx)

/-- Pulling back a form with zero first jet at `f x` along a map `f` that is `C¹` at `x` yields a
form with zero chart derivative in any chart `β` containing `x`. -/
theorem hasFDerivWithinAt_inChartAt_mpullback_zero_of_mem
    {η : RoughForm I' M' F k} {f : M → M'} {β x : M} {α : M'}
    (hx : x ∈ (extChartAt I β).source) (hfx : f x ∈ (extChartAt I' α).source)
    (hf : ContMDiffAt I I' 1 f x) (hη0 : η (f x) = 0)
    (hη : HasFDerivWithinAt (η.inChartAt α) (0 : E' →L[ℝ] E' [⋀^Fin k]→L[ℝ] F)
      (range I') (extChartAt I' α (f x))) :
    HasFDerivWithinAt ((mpullback I I' f η).inChartAt β)
      (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) (range I) (extChartAt I β x) := by
  simpa only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero] using
    hasFDerivWithinAt_inChartAt_mpullback_of_eq_zero hx hfx hf hη0 hη

/-- Pulling back a form with zero first jet at `f x` along a map `f` that is `C¹` at `x` yields a
form with zero first jet at `x`, in preferred charts. -/
theorem hasFDerivWithinAt_inChartAt_mpullback_zero
    {η : RoughForm I' M' F k} {f : M → M'} {x : M}
    (hf : ContMDiffAt I I' 1 f x) (hη0 : η (f x) = 0)
    (hη : HasFDerivWithinAt (η.inChartAt (f x)) (0 : E' →L[ℝ] E' [⋀^Fin k]→L[ℝ] F)
      (range I') (extChartAt I' (f x) (f x))) :
    HasFDerivWithinAt ((mpullback I I' f η).inChartAt x)
      (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) (range I) (extChartAt I x x) :=
  hasFDerivWithinAt_inChartAt_mpullback_zero_of_mem
    (mem_extChartAt_source x) (mem_extChartAt_source (f x)) hf hη0 hη

/-- On boundaryless manifolds, pulling back a form with zero first jet at `f x` along a map `f`
that is `C¹` at `x` yields a form with zero Fréchet derivative in the preferred chart at `x`. -/
theorem hasFDerivAt_inChartAt_mpullback_zero [I.Boundaryless] [I'.Boundaryless]
    {η : RoughForm I' M' F k} {f : M → M'} {x : M}
    (hf : ContMDiffAt I I' 1 f x) (hη0 : η (f x) = 0)
    (hη : HasFDerivAt (η.inChartAt (f x)) (0 : E' →L[ℝ] E' [⋀^Fin k]→L[ℝ] F)
      (extChartAt I' (f x) (f x))) :
    HasFDerivAt ((mpullback I I' f η).inChartAt x)
      (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) (extChartAt I x x) := by
  rw [← hasFDerivWithinAt_univ, ← I.range_eq_univ]
  rw [← hasFDerivWithinAt_univ, ← I'.range_eq_univ] at hη
  exact hasFDerivWithinAt_inChartAt_mpullback_zero hf hη0 hη

/-- **Chart independence of vanishing first jet for a differential form.** At a zero `x` of a
differential form `η` on a `C¹` manifold, having zero chart derivative within `range I` is
independent of the preferred chart containing `x`. -/
theorem hasFDerivWithinAt_inChartAt_congr_chart_of_eq_zero
    {η : RoughForm I M F k} {α β x : M}
    (hα : x ∈ (extChartAt I α).source) (hβ : x ∈ (extChartAt I β).source)
    (hη0 : η x = 0) :
    HasFDerivWithinAt (η.inChartAt α) (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
      (range I) (extChartAt I α x) ↔
    HasFDerivWithinAt (η.inChartAt β) (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
      (range I) (extChartAt I β x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa only [mpullback_id] using hasFDerivWithinAt_inChartAt_mpullback_zero_of_mem
      (f := id) hβ hα contMDiffAt_id hη0 h
  · simpa only [mpullback_id] using hasFDerivWithinAt_inChartAt_mpullback_zero_of_mem
      (f := id) hα hβ contMDiffAt_id hη0 h

end PullbackAtZero

/-! ### Identification with `FirstJetBundle` and covariant derivatives -/

section FirstJet

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

section OnceDifferentiable

variable [IsManifold I 1 M]

/-- Near the image of `α` within `range I`, the local representative of a form `η` as a section of
the alternating-map bundle agrees with its chart expression `η.inChartAt α`. -/
theorem localRep_eventuallyEq_inChartAt (η : RoughForm I M F k) (α : M) :
    FirstJetBundle.localRep I (E [⋀^Fin k]→L[ℝ] F) η α =ᶠ[𝓝[range I] (extChartAt I α α)]
      η.inChartAt α := by
  filter_upwards [η.trivializationAt_snd_eventuallyEq_inChartAt α] with z hz
  exact (FirstJetBundle.localRep_apply ..).trans hz

/-- At the chart centre `α`, `FirstJetBundle.localRep` and `η.inChartAt α` have the same value. -/
theorem localRep_extChartAt_self_eq_inChartAt (η : RoughForm I M F k) (α : M) :
    FirstJetBundle.localRep I (E [⋀^Fin k]→L[ℝ] F) η α (extChartAt I α α) =
      η.inChartAt α (extChartAt I α α) :=
  (FirstJetBundle.localRep_apply ..).trans
    (η.inChartAt_eq_trivializationAt α (mem_extChartAt_target α)).symm

/-- At the chart centre `α`, `FirstJetBundle.localRep` and `η.inChartAt α` have the same
`HasFDerivWithinAt` within `range I`. -/
theorem hasFDerivWithinAt_localRep_iff_inChartAt (η : RoughForm I M F k) (α : M)
    {L : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F} :
    HasFDerivWithinAt (FirstJetBundle.localRep I (E [⋀^Fin k]→L[ℝ] F) η α) L
        (range I) (extChartAt I α α) ↔
      HasFDerivWithinAt (η.inChartAt α) L (range I) (extChartAt I α α) :=
  ⟨fun h ↦ h.congr_of_eventuallyEq (η.localRep_eventuallyEq_inChartAt α).symm
      (η.localRep_extChartAt_self_eq_inChartAt α).symm,
    fun h ↦ h.congr_of_eventuallyEq (η.localRep_eventuallyEq_inChartAt α)
      (η.localRep_extChartAt_self_eq_inChartAt α)⟩

/-- On a boundaryless manifold, `FirstJetBundle.localRep` and `η.inChartAt α` have the same Fréchet
derivative at the chart centre `α`. -/
theorem hasFDerivAt_localRep_iff_inChartAt [I.Boundaryless] (η : RoughForm I M F k) (α : M)
    {L : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F} :
    HasFDerivAt (FirstJetBundle.localRep I (E [⋀^Fin k]→L[ℝ] F) η α) L (extChartAt I α α) ↔
      HasFDerivAt (η.inChartAt α) L (extChartAt I α α) := by
  simp only [← hasFDerivWithinAt_univ, ← I.range_eq_univ]
  exact η.hasFDerivWithinAt_localRep_iff_inChartAt α

/-- At the chart centre `α`, the `fderivWithin` of `FirstJetBundle.localRep` agrees with the
`fderivWithin` of `η.inChartAt α`. -/
theorem fderivWithin_localRep_eq_inChartAt (η : RoughForm I M F k) (α : M) :
    fderivWithin ℝ (FirstJetBundle.localRep I (E [⋀^Fin k]→L[ℝ] F) η α)
        (range I) (extChartAt I α α) =
      fderivWithin ℝ (η.inChartAt α) (range I) (extChartAt I α α) :=
  (η.localRep_eventuallyEq_inChartAt α).fderivWithin_eq
    (η.localRep_extChartAt_self_eq_inChartAt α)

end OnceDifferentiable

section TwiceDifferentiable

variable [IsManifold I 2 M]

/-- The first jet of a `k`-form `η` at `x` vanishes exactly when `η x = 0` and the chart derivative
of `η.inChartAt x` within `range I` vanishes at `extChartAt I x x`. -/
theorem jet_eq_zero_iff (η : RoughForm I M F k) (x : M) :
    FirstJetBundle.jet I (E [⋀^Fin k]→L[ℝ] F) η x = 0 ↔
      η x = 0 ∧ fderivWithin ℝ (η.inChartAt x) (range I) (extChartAt I x x) = 0 := by
  have : IsManifold I 1 M := .of_le one_le_two
  rw [FirstJetBundle.jet_eq_zero_iff, fderivWithin_localRep_eq_inChartAt]

/-- A `k`-form vanishing at `x` whose coordinate expression `η.inChartAt x` has derivative `0`
within `range I` at `extChartAt I x x` has zero first jet at `x`. -/
theorem jet_eq_zero_of_hasFDerivWithinAt_zero {η : RoughForm I M F k} {x : M} (hη0 : η x = 0)
    (hd : HasFDerivWithinAt (η.inChartAt x) (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
      (range I) (extChartAt I x x)) :
    FirstJetBundle.jet I (E [⋀^Fin k]→L[ℝ] F) η x = 0 := by
  have : IsManifold I 1 M := .of_le one_le_two
  exact FirstJetBundle.jet_eq_zero_of_hasFDerivWithinAt_zero hη0
    ((η.hasFDerivWithinAt_localRep_iff_inChartAt x).2 hd)

/-- For a `k`-form differentiable at `x`, its first jet vanishes at `x` exactly when `η x = 0` and
`η.inChartAt x` has derivative `0` within `range I` at `extChartAt I x x`. -/
theorem jet_eq_zero_iff_hasFDerivWithinAt {η : RoughForm I M F k} {x : M}
    (hη : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (η y)) x) :
    FirstJetBundle.jet I (E [⋀^Fin k]→L[ℝ] F) η x = 0 ↔
      η x = 0 ∧ HasFDerivWithinAt (η.inChartAt x) (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
        (range I) (extChartAt I x x) := by
  have : IsManifold I 1 M := .of_le one_le_two
  rw [FirstJetBundle.jet_eq_zero_iff_hasFDerivWithinAt hη,
    η.hasFDerivWithinAt_localRep_iff_inChartAt x]

/-- On a boundaryless `C²` manifold, a `k`-form differentiable at `x` has zero first jet at `x`
exactly when `η x = 0` and `η.inChartAt x` has Fréchet derivative `0` at `extChartAt I x x`. -/
theorem jet_eq_zero_iff_hasFDerivAt [I.Boundaryless] {η : RoughForm I M F k} {x : M}
    (hη : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (η y)) x) :
    FirstJetBundle.jet I (E [⋀^Fin k]→L[ℝ] F) η x = 0 ↔
      η x = 0 ∧ HasFDerivAt (η.inChartAt x) (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
        (extChartAt I x x) := by
  have : IsManifold I 1 M := .of_le one_le_two
  rw [jet_eq_zero_iff_hasFDerivWithinAt hη, ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ]

/-- **Zero first jet of a differential form via any auxiliary connection.** On a finite-dimensional
`C²` manifold, for any covariant derivative `cov` on the bundle of `F`-valued `k`-forms over a set
`U` containing `x`, a `k`-form `η` differentiable at `x` has zero first jet at `x` if and only if
both `η x = 0` and `cov η x = 0`. -/
theorem jet_eq_zero_iff_covariantDerivative [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {cov : (Π y : M, TangentSpace I y [⋀^Fin k]→L[ℝ] F) →
      (Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y [⋀^Fin k]→L[ℝ] F)}
    {U : Set M} {x : M} (hcov : IsCovariantDerivativeOn (E [⋀^Fin k]→L[ℝ] F) cov U)
    (hx : x ∈ U) {η : RoughForm I M F k}
    (hη : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (η y)) x) :
    FirstJetBundle.jet I (E [⋀^Fin k]→L[ℝ] F) η x = 0 ↔ η x = 0 ∧ cov η x = 0 := by
  have : IsManifold I 1 M := .of_le one_le_two
  exact FirstJetBundle.jet_eq_zero_iff_covariantDerivative hcov hx hη

/-- **Covariant derivative vanishing versus zero chart derivative at a zero.** On a
finite-dimensional `C²` manifold, for any auxiliary covariant derivative `cov` on `k`-forms over
`U ∋ x`, at a zero `η x = 0` of a form `η` differentiable at `x`, `cov η x = 0` holds if and only
if `η.inChartAt x` has derivative `0` within `range I` at `extChartAt I x x`. -/
theorem covariantDerivative_eq_zero_iff_hasFDerivWithinAt_inChartAt
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {cov : (Π y : M, TangentSpace I y [⋀^Fin k]→L[ℝ] F) →
      (Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y [⋀^Fin k]→L[ℝ] F)}
    {U : Set M} {x : M} (hcov : IsCovariantDerivativeOn (E [⋀^Fin k]→L[ℝ] F) cov U)
    (hx : x ∈ U) {η : RoughForm I M F k}
    (hη : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (η y)) x)
    (hη0 : η x = 0) :
    cov η x = 0 ↔
      HasFDerivWithinAt (η.inChartAt x) (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
        (range I) (extChartAt I x x) := by
  have : IsManifold I 1 M := .of_le one_le_two
  rw [FirstJetBundle.covariantDerivative_eq_zero_iff_hasFDerivWithinAt_localRep hcov hx hη hη0,
    η.hasFDerivWithinAt_localRep_iff_inChartAt x]

/-- Boundaryless version of
`TauCeti.RoughForm.covariantDerivative_eq_zero_iff_hasFDerivWithinAt_inChartAt`: at a zero of a
differentiable form, `cov η x = 0` holds if and only if `η.inChartAt x` has Fréchet derivative `0`
at `extChartAt I x x`. -/
theorem covariantDerivative_eq_zero_iff_hasFDerivAt_inChartAt
    [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {cov : (Π y : M, TangentSpace I y [⋀^Fin k]→L[ℝ] F) →
      (Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y [⋀^Fin k]→L[ℝ] F)}
    {U : Set M} {x : M} (hcov : IsCovariantDerivativeOn (E [⋀^Fin k]→L[ℝ] F) cov U)
    (hx : x ∈ U) {η : RoughForm I M F k}
    (hη : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (η y)) x)
    (hη0 : η x = 0) :
    cov η x = 0 ↔
      HasFDerivAt (η.inChartAt x) (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) (extChartAt I x x) := by
  rw [covariantDerivative_eq_zero_iff_hasFDerivWithinAt_inChartAt hcov hx hη hη0,
    ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ]

end TwiceDifferentiable

end FirstJet

end RoughForm

/-! ### Degree-one forms and sections of `Hom(TM, V)` -/

section DegreeOne

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

/-- In any chart `i`, the local representative of a bundle-valued degree-one form
`ofSubsingleton 0 ∘ α` is obtained from the local representative of `α` by applying the constant
linear isometry equivalence `ContinuousAlternatingMap.ofSubsingletonLIE`. -/
theorem localRep_ofSubsingleton (α : (x : M) → TangentSpace I x →L[ℝ] V x) (i : M) (z : E) :
    FirstJetBundle.localRep I (E [⋀^Fin 1]→L[ℝ] F)
      (fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) (V x) (0 : Fin 1)
        (α x)) i z =
      ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (ι := Fin 1) 0
        (FirstJetBundle.localRep I (E →L[ℝ] F) α i z) := by
  simp only [FirstJetBundle.localRep_apply,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply,
    ContinuousLinearMap.inCoordinates,
    ContinuousAlternatingMap.inCoordinates_ofSubsingleton]
  rfl

/-- For any set `s` and point `z`, a family of fibrewise linear maps
`α : (x : M) → TangentSpace I x →L[ℝ] V x` has local-representative derivative `L` within `s` at
`z` if and only if the corresponding degree-one form `ofSubsingleton 0 ∘ α` has derivative
`ofSubsingletonLIE 0 ∘ L`. -/
theorem hasFDerivWithinAt_localRep_ofSubsingleton_iff
    {α : (x : M) → TangentSpace I x →L[ℝ] V x} {i : M} {s : Set E} {z : E}
    {L : E →L[ℝ] E →L[ℝ] F} :
    HasFDerivWithinAt
        (FirstJetBundle.localRep I (E [⋀^Fin 1]→L[ℝ] F)
          (fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) (V x) (0 : Fin 1)
            (α x)) i)
        ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (ι := Fin 1)
          0).toContinuousLinearEquiv.toContinuousLinearMap.comp L) s z ↔
      HasFDerivWithinAt (FirstJetBundle.localRep I (E →L[ℝ] F) α i) L s z := by
  let e := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (ι := Fin 1)
    0).toContinuousLinearEquiv
  have heq : FirstJetBundle.localRep I (E [⋀^Fin 1]→L[ℝ] F)
      (fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) (V x) (0 : Fin 1)
        (α x)) i = e ∘ FirstJetBundle.localRep I (E →L[ℝ] F) α i :=
    funext fun w ↦ localRep_ofSubsingleton α i w
  rw [heq]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := e.symm.hasFDerivAt.comp_hasFDerivWithinAt z h
    have hL : e.symm.toContinuousLinearMap.comp (e.toContinuousLinearMap.comp L) = L := by
      ext v
      simp [e]
    have hfun : (⇑e.symm ∘ ⇑e ∘ FirstJetBundle.localRep I (E →L[ℝ] F) α i) =
        FirstJetBundle.localRep I (E →L[ℝ] F) α i := funext fun w ↦ e.symm_apply_apply _
    rw [← hfun, ← hL]
    exact h'
  · exact e.hasFDerivAt.comp_hasFDerivWithinAt z h

/-- A family of fibrewise linear maps `α : (x : M) → TangentSpace I x →L[ℝ] V x` has zero
local-representative derivative within `s` at `z` if and only if the corresponding degree-one form
`ofSubsingleton 0 ∘ α` does. -/
theorem hasFDerivWithinAt_localRep_ofSubsingleton_zero_iff
    {α : (x : M) → TangentSpace I x →L[ℝ] V x} {i : M} {s : Set E} {z : E} :
    HasFDerivWithinAt
        (FirstJetBundle.localRep I (E [⋀^Fin 1]→L[ℝ] F)
          (fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) (V x) (0 : Fin 1)
            (α x)) i)
        (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] F) s z ↔
      HasFDerivWithinAt (FirstJetBundle.localRep I (E →L[ℝ] F) α i)
        (0 : E →L[ℝ] E →L[ℝ] F) s z := by
  simpa only [ContinuousLinearMap.comp_zero] using
    hasFDerivWithinAt_localRep_ofSubsingleton_iff (α := α) (i := i) (s := s) (z := z) (L := 0)

/-- For a smooth one-form `β`, its section `SmoothForm.degreeOneEquiv β` of `Hom(TM, F)` has
local-representative derivative `L` within `range I` at `extChartAt I x x` if and only if
`RoughForm.inChartAt β.1 x` has derivative `ofSubsingletonLIE 0 ∘ L`. -/
theorem SmoothForm.hasFDerivWithinAt_localRep_degreeOneEquiv_iff
    (β : SmoothForm I M F 1) (x : M) {L : E →L[ℝ] E →L[ℝ] F} :
    HasFDerivWithinAt (FirstJetBundle.localRep I (E →L[ℝ] F) (SmoothForm.degreeOneEquiv β) x)
        L (range I) (extChartAt I x x) ↔
      HasFDerivWithinAt (RoughForm.inChartAt β.1 x)
        ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (ι := Fin 1)
          0).toContinuousLinearEquiv.toContinuousLinearMap.comp L)
        (range I) (extChartAt I x x) := by
  rw [← hasFDerivWithinAt_localRep_ofSubsingleton_iff (V := Trivial M F),
    ← RoughForm.hasFDerivWithinAt_localRep_iff_inChartAt (β.1 : RoughForm I M F 1) x]
  refine Iff.of_eq (congrArg (fun η ↦ HasFDerivWithinAt
    (FirstJetBundle.localRep I (E [⋀^Fin 1]→L[ℝ] F) η x)
    ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := F) (ι := Fin 1)
      0).toContinuousLinearEquiv.toContinuousLinearMap.comp L)
    (range I) (extChartAt I x x)) ?_)
  funext y
  ext v
  have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
  conv_rhs => rw [hv]
  simp [SmoothForm.degreeOneEquiv_apply_apply_vec]

/-- For a smooth one-form `β`, its section `SmoothForm.degreeOneEquiv β` of `Hom(TM, F)` has zero
local-representative derivative within `range I` at `extChartAt I x x` if and only if
`RoughForm.inChartAt β.1 x` does. -/
theorem SmoothForm.hasFDerivWithinAt_localRep_degreeOneEquiv_zero_iff
    (β : SmoothForm I M F 1) (x : M) :
    HasFDerivWithinAt (FirstJetBundle.localRep I (E →L[ℝ] F) (SmoothForm.degreeOneEquiv β) x)
        (0 : E →L[ℝ] E →L[ℝ] F) (range I) (extChartAt I x x) ↔
      HasFDerivWithinAt (RoughForm.inChartAt β.1 x) (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] F)
        (range I) (extChartAt I x x) := by
  simpa only [ContinuousLinearMap.comp_zero] using
    SmoothForm.hasFDerivWithinAt_localRep_degreeOneEquiv_iff β x (L := 0)

/-- Boundaryless version of `TauCeti.SmoothForm.hasFDerivWithinAt_localRep_degreeOneEquiv_zero_iff`.
-/
theorem SmoothForm.hasFDerivAt_localRep_degreeOneEquiv_zero_iff [I.Boundaryless]
    (β : SmoothForm I M F 1) (x : M) :
    HasFDerivAt (FirstJetBundle.localRep I (E →L[ℝ] F) (SmoothForm.degreeOneEquiv β) x)
        (0 : E →L[ℝ] E →L[ℝ] F) (extChartAt I x x) ↔
      HasFDerivAt (RoughForm.inChartAt β.1 x) (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] F)
        (extChartAt I x x) := by
  simp only [← hasFDerivWithinAt_univ, ← I.range_eq_univ]
  exact SmoothForm.hasFDerivWithinAt_localRep_degreeOneEquiv_zero_iff β x

end DegreeOne

end TauCeti
