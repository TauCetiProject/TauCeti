/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Pullback of differential forms along smooth families of maps

Let `f : N → M → M'` be a family of maps depending jointly `C^n` on the parameter `p ∈ N` and the
point `y ∈ M`, and let `g : N → M` be `C^m`, with `m + 1 ≤ n`. For a `C^m` form `φ` on `M'`, the
pullbacks `(f p)^* φ` evaluated at `g p` form a section of the bundle of alternating maps on `TM`
along `g`, and this section is `C^m` (`ContMDiffAt.mpullback_form_family`). For the constant
family `f p = f₀` and `g = id` this is `ContMDiffAt.mpullback_form`.

The main instance is the family of **slices** of a form `α` on a product `N × M`: the forms
`α_t = ι_t^* α` on `M` pulled back along the inclusions `ι_t : y ↦ (t, y)`. They depend smoothly on
`(t, y)` (`TauCeti.contMDiff_mpullback_prodMk_form`). So do their exterior derivatives, which are
the slices of the exterior derivative (`TauCeti.SmoothForm.contMDiff_mextDeriv_mpullback_prodMk`).
A smooth form on `ℝ × M` is how a smooth time-dependent family of forms on `M` is represented,
and this joint smoothness is what makes pointwise constructions from the slices, such as Reeb and
Moser vector fields, into smooth time-dependent vector fields.

## Main results

* `ContMDiffAt.mpullback_form_family`: pullbacks along a jointly smooth family of maps, evaluated
  along a smooth map, depend smoothly on the parameter.
* `TauCeti.contMDiff_mpullback_prodMk_form`: the slices `ι_t^* α` of a smooth form on `N × M` are
  jointly smooth in `(t, y)`.
* `TauCeti.SmoothForm.contMDiff_mpullback_prodMk`: the same for smooth pullback of smooth forms.
* `TauCeti.SmoothForm.contMDiff_mextDeriv_mpullback_prodMk`: the exterior derivatives of the slices
  of a smooth form on `N × M` are jointly smooth in `(t, y)`.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M E' H' M' EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  [TopologicalSpace N] [ChartedSpace HN N] {J : ModelWithCorners ℝ EN HN}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [IsManifold I 1 M] [IsManifold I' 1 M']
  {k : ℕ} {m n : WithTop ℕ∞}

omit [TopologicalSpace N] in
/-- In fibre coordinates centred at `g p₀` and `f p₀ (g p₀)`, the pullback of `φ` along `f p` at
`g p` precomposes the coordinates of `φ` with the coordinates of the derivative of `f p`. The
target tangent trivialization must be valid at `f p (g p)`. -/
theorem inCoordinates_mpullback_family (φ : RoughForm I' M' F k) (f : N → M → M') (g : N → M)
    (p₀ p : N)
    (hp : f p (g p) ∈ (trivializationAt E' (TangentSpace I') (f p₀ (g p₀))).baseSet) :
    ContinuousAlternatingMap.inCoordinates E F (g p₀) (g p) (g p₀) (g p)
        (mpullback I I' (f p) φ (g p)) =
      (ContinuousAlternatingMap.inCoordinates E' F (f p₀ (g p₀)) (f p (g p)) (f p₀ (g p₀))
        (f p (g p)) (φ (f p (g p)))).compContinuousLinearMap
          (inTangentCoordinates I I' g (fun p ↦ f p (g p)) (fun p ↦ mfderiv I I' (f p) (g p))
            p₀ p) := by
  have h := ContinuousAlternatingMap.inCoordinates_compContinuousLinearMap
    (F₁ := E) (F₂ := E') (F₃ := F) (V₁ := TangentSpace I) (V₂ := TangentSpace I')
    (V₃ := Trivial M' F) (x₀ := g p₀) (y₀ := f p₀ (g p₀)) (z₀ := f p₀ (g p₀))
    (φ (f p (g p))) (mfderiv I I' (f p) (g p)) hp
  ext v
  simpa only [ContinuousAlternatingMap.inCoordinates,
    Bundle.Trivial.eq_trivialization M F (trivializationAt F (Trivial M F) (g p₀)),
    Bundle.Trivial.eq_trivialization M' F (trivializationAt F (Trivial M' F) (f p₀ (g p₀))),
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_def,
    ContinuousLinearMap.id_apply, inTangentCoordinates, id_eq, mpullback_apply]
    using congrArg (fun a ↦ a v) h

/-- **Pullback along a smooth family of maps.** Let `f : N → M → M'` be jointly `C^n` at
`(p₀, g p₀)` and `g : N → M` be `C^m` at `p₀`, with `m + 1 ≤ n`. If the form `φ` is `C^m` at
`f p₀ (g p₀)`, then the pullbacks `(f p)^* φ` at `g p` form a `C^m` section along `g` at `p₀`. -/
theorem _root_.ContMDiffAt.mpullback_form_family [IsManifold J 1 N] {φ : RoughForm I' M' F k}
    {f : N → M → M'} {g : N → M} {p₀ : N}
    (hφ : ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (φ y)) (f p₀ (g p₀)))
    (hf : ContMDiffAt (J.prod I) I' n (Function.uncurry f) (p₀, g p₀))
    (hg : ContMDiffAt J I m g p₀) (hmn : m + 1 ≤ n) :
    ContMDiffAt J (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun p ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) (g p)
        (mpullback I I' (f p) φ (g p))) p₀ := by
  have hfg : ContMDiffAt J I' m (fun p ↦ f p (g p)) p₀ :=
    (hf.of_le ((le_add_of_nonneg_right zero_le_one).trans hmn)).comp p₀
      (contMDiffAt_id.prodMk hg)
  have hcoeff := ((contMDiffAt_continuousAlternatingMap_bundle _).mp hφ).2
  have hc := hcoeff.comp p₀ hfg
  have hd := hf.mfderiv f g hg hmn
  have hpre := ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := ℝ) (E := E) (F := E') (G := F) (ι := Fin k) m
  have hp := (hpre.comp_contMDiffAt hd).clm_apply hc
  apply (contMDiffAt_continuousAlternatingMap_bundle _).mpr
  refine ⟨hg, hp.congr_of_eventuallyEq ?_⟩
  have hmem : (fun p ↦ f p (g p)) ⁻¹'
      (trivializationAt E' (TangentSpace I') (f p₀ (g p₀))).baseSet ∈ 𝓝 p₀ :=
    hfg.continuousAt.preimage_mem_nhds
      ((trivializationAt E' (TangentSpace I') (f p₀ (g p₀))).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (f p₀ (g p₀))))
  filter_upwards [hmem] with p hp
  simpa only [Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
    using inCoordinates_mpullback_family (I := I) φ f g p₀ p hp

/-- **Slices of a form on a product are jointly smooth.** For a `C^m` form `α` on `N × M`, the
slices `ι_t^* α`, pulled back along the inclusions `ι_t : y ↦ (t, y)`, form a `C^m` section along
the projection `(t, y) ↦ y`. -/
theorem contMDiff_mpullback_prodMk_form [IsManifold J 1 N]
    {α : RoughForm (J.prod I) (N × M) F k}
    (hα : ContMDiff (J.prod I) ((J.prod I).prod 𝓘(ℝ, (EN × E) [⋀^Fin k]→L[ℝ] F)) m
      (fun p ↦ TotalSpace.mk' ((EN × E) [⋀^Fin k]→L[ℝ] F) p (α p))) :
    ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2
        (mpullback I (J.prod I) (Prod.mk p.1) α p.2)) := by
  intro p
  exact ContMDiffAt.mpullback_form_family (hα (p.1, p.2))
    (f := fun q : N × M ↦ Prod.mk q.1) (g := Prod.snd) (n := ω)
    ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffAt contMDiffAt_snd le_top

/-- The slices `ι_t^* α` of a smooth form `α` on `N × M` form a smooth section along the projection
`(t, y) ↦ y`. This is `TauCeti.contMDiff_mpullback_prodMk_form` for smooth pullback. -/
theorem SmoothForm.contMDiff_mpullback_prodMk [IsManifold J ∞ N]
    (α : SmoothForm (J.prod I) (N × M) F k) :
    ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2
        ((mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).1 p.2)) := by
  simpa only [coe_mpullback] using contMDiff_mpullback_prodMk_form α.contMDiff

/-- **Exterior derivatives of slices are jointly smooth.** For a smooth form `α` on `N × M`, the
exterior derivatives `d(ι_t^* α)` of its slices form a smooth section along the projection
`(t, y) ↦ y`. -/
theorem SmoothForm.contMDiff_mextDeriv_mpullback_prodMk [IsManifold I 2 M] [IsManifold J 2 N]
    (α : SmoothForm (J.prod I) (N × M) F k) :
    ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F)) ∞
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin (k + 1)]→L[ℝ] Trivial M F y) p.2
        (mextDeriv (mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).1 p.2)) := by
  -- The exterior derivative of a slice is the slice of the exterior derivative.
  convert contMDiff_mpullback_prodMk_form (contMDiff_mextDeriv α) using 3 with p
  rw [← mextDerivₗ_apply, mextDerivₗ_mpullback, coe_mpullback, mextDerivₗ_apply]

end TauCeti
