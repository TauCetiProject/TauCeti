/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.CylinderHomotopy
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The homotopy operator on forms on a cylinder `M × [0, 1]`

Let `M` be a manifold over a model with corners `I`, possibly with boundary or corners, and let
`φ` be a differential `(k + 1)`-form on the cylinder `M × [0, 1]`, whose model is
`I.prod (𝓡∂ 1)`. The *homotopy operator* (`TauCeti.homotopyOperator`) contracts `φ` with the unit
time vector `∂ₜ = (0, 1)` and integrates over the time interval:

`(h φ)(x)(v₁, …, vₖ) = ∫₀¹ φ(x, t)(∂ₜ, (v₁, 0), …, (vₖ, 0)) dt`.

Here `1 : TangentSpace (𝓡∂ 1) t` is Mathlib's unit tangent vector of the interval, the image of
`1` under the projection `ℝ → [0, 1]`; its coordinate in the preferred chart at the endpoint `1`,
which reverses orientation, is `-1`. Thus `h φ = ∫₀¹ ιₜ^*(∂ₜ ⌟ φ) dt`, where `ιₜ x = (x, t)`.

For a `C¹` form `φ` with values in a Banach space, `h φ` is `C¹`, and more generally `h` preserves
`C^r` regularity (`TauCeti.IsSmoothForm.homotopyOperator`). On a `C²` manifold it satisfies the
cochain-homotopy identity
(`TauCeti.mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv`)

`d (h φ) + h (d φ) = ι₁^* φ - ι₀^* φ`.

In particular, for a closed form `ι₁^* φ - ι₀^* φ = d (h φ)` is exact
(`TauCeti.mextDeriv_homotopyOperator`); this is the analytic input for homotopy invariance of de
Rham cohomology.

The identity is proved in the preferred chart at each point `x₀`, directly and without Stokes'
theorem on the manifold with corners `M × [0, 1]`, so `M` may have boundary. On the intersection
`s` of a small ball with `range I`, which is convex with unique derivatives but need not be open,
the form `φ` is pulled back along `(y, t) ↦ ((extChartAt I x₀).symm y, projIcc 0 1 t)` to a flat
form on the cylinder `s ×ˢ Icc 0 1`. The chart expression of `h φ` is the flat cylinder homotopy
operator `TauCeti.cylinderHomotopy` of this pullback, the pullback commutes with exterior
differentiation (`TauCeti.extDerivWithin_mpullbackWithin`), and the flat identity
`Convex.extDerivWithin_cylinderHomotopy_add_cylinderHomotopy_extDerivWithin` concludes. The
projection `projIcc` hides the two charts of `[0, 1]`: its derivative within `[0, 1]` sends `1` to
the unit tangent vector at every time.

## Main declarations

* `TauCeti.homotopyOperator`: the homotopy operator `h`.
* `TauCeti.IsSmoothForm.homotopyOperator`: `h` preserves `C^r` regularity.
* `TauCeti.mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv`: the cochain-homotopy
  identity `d (h φ) + h (d φ) = ι₁^* φ - ι₀^* φ`.
* `TauCeti.mextDeriv_homotopyOperator`: for a closed form, `d (h φ) = ι₁^* φ - ι₀^* φ`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, section Homotopy
  Invariance, whose homotopy operator on `M × I` this is.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public section

noncomputable section

open Set Filter Bundle MeasureTheory Metric
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The **homotopy operator** on forms on the cylinder `M × [0, 1]`: the `k`-form
`x ↦ ∫₀¹ φ(x, t)(∂ₜ, (·, 0)) dt` on `M` built from a `(k + 1)`-form `φ` on `M × [0, 1]`, where
`∂ₜ = (0, 1)` is the unit time vector and tangent vectors of `M` enter through
`ContinuousLinearMap.inl`. Equivalently `h φ = ∫₀¹ ιₜ^*(∂ₜ ⌟ φ) dt` for the slices
`ιₜ x = (x, t)`. For a `C¹` form with values in a Banach space,
`d (h φ) + h (d φ) = ι₁^* φ - ι₀^* φ`. -/
def homotopyOperator
    (φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) : RoughForm I M F k :=
  fun x ↦ intervalIntegral (E := E [⋀^Fin k]→L[ℝ] F) (fun t ↦
    (ContinuousAlternatingMap.curryLeft (E := E × EuclideanSpace ℝ (Fin 1))
      (φ (x, projIcc 0 1 zero_le_one t))
      ((0 : E), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one t)))).compContinuousLinearMap
        (.inl ℝ E (EuclideanSpace ℝ (Fin 1)))) 0 1 volume

/-- The value of the homotopy operator at a point, as an integral over the time interval. -/
theorem homotopyOperator_apply (φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1))
    (x : M) :
    homotopyOperator φ x = intervalIntegral (E := E [⋀^Fin k]→L[ℝ] F) (fun t ↦
      (ContinuousAlternatingMap.curryLeft (E := E × EuclideanSpace ℝ (Fin 1))
        (φ (x, projIcc 0 1 zero_le_one t))
        ((0 : E), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one t)))).compContinuousLinearMap
          (.inl ℝ E (EuclideanSpace ℝ (Fin 1)))) 0 1 volume :=
  (rfl)

/-- The homotopy operator of the zero form is zero. -/
@[simp]
theorem homotopyOperator_zero :
    homotopyOperator (0 : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) = 0 := by
  funext x
  -- The integrand of the zero form is the zero function.
  exact intervalIntegral.integral_zero (E := E [⋀^Fin k]→L[ℝ] F) (a := 0) (b := 1)

/-- The homotopy operator commutes with real scalar multiplication of forms. -/
theorem homotopyOperator_smul (c : ℝ)
    (φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) :
    homotopyOperator (c • φ) = c • homotopyOperator φ := by
  funext x
  -- The integrand of `c • φ` is `c` times the integrand of `φ`.
  exact intervalIntegral.integral_smul (E := E [⋀^Fin k]→L[ℝ] F) (μ := volume) (a := 0) (b := 1) c
    fun t ↦ (ContinuousAlternatingMap.curryLeft (E := E × EuclideanSpace ℝ (Fin 1))
      (φ (x, projIcc 0 1 zero_le_one t))
      ((0 : E), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one t)))).compContinuousLinearMap
        (.inl ℝ E (EuclideanSpace ℝ (Fin 1)))

/-! ### The chart expression of the homotopy operator -/

/-- The derivative of the map `(y, t) ↦ ((extChartAt I x₀).symm y, projIcc 0 1 t)` from a flat
cylinder into `M × [0, 1]`. -/
private theorem mfderivWithin_cylinderChart_apply [IsManifold I 1 M] (x₀ : M) {s : Set E}
    (hs : s ⊆ (extChartAt I x₀).target)
    (hsu : UniqueDiffOn ℝ s) {p : E × ℝ} (hp : p ∈ s ×ˢ Icc (0 : ℝ) 1) (w : E) (c : ℝ) :
    mfderivWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1))
      (fun p : E × ℝ ↦ ((extChartAt I x₀).symm p.1, projIcc 0 1 zero_le_one p.2)) (s ×ˢ Icc 0 1) p
        (w, c) =
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm s p.1 w,
        c • (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one p.2))) := by
  have hS : UniqueDiffOn ℝ (s ×ˢ Icc (0 : ℝ) 1) := hsu.prod uniqueDiffOn_Icc_zero_one
  have h1 : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I x₀).symm s p.1 :=
    ((contMDiffOn_extChartAt_symm (n := 1) x₀).mono hs p.1 hp.1).mdifferentiableWithinAt one_ne_zero
  have h2 : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (𝓡∂ 1) (projIcc (0 : ℝ) 1 zero_le_one) (Icc 0 1) p.2 :=
    (contMDiffOn_projIcc (n := 1) p.2 hp.2).mdifferentiableWithinAt one_ne_zero
  have hfst : MDifferentiableWithinAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) Prod.fst (s ×ˢ Icc 0 1) p :=
    contDiff_fst.contMDiff.mdifferentiableAt one_ne_zero |>.mdifferentiableWithinAt
  have hsnd : MDifferentiableWithinAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ℝ) Prod.snd (s ×ˢ Icc 0 1) p :=
    contDiff_snd.contMDiff.mdifferentiableAt one_ne_zero |>.mdifferentiableWithinAt
  have hu := (hS p hp).uniqueMDiffWithinAt
  have hc1 : mfderivWithin 𝓘(ℝ, E × ℝ) I (fun q : E × ℝ ↦ (extChartAt I x₀).symm q.1)
      (s ×ˢ Icc 0 1) p = (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm s p.1).comp
        (mfderivWithin 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) Prod.fst (s ×ˢ Icc 0 1) p) :=
    mfderivWithin_comp p h1 hfst (fun q hq ↦ hq.1) hu
  have hc2 : mfderivWithin 𝓘(ℝ, E × ℝ) (𝓡∂ 1) (fun q : E × ℝ ↦ projIcc 0 1 zero_le_one q.2)
      (s ×ˢ Icc 0 1) p = (mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ 1) (projIcc 0 1 zero_le_one) (Icc 0 1) p.2).comp
        (mfderivWithin 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ℝ) Prod.snd (s ×ˢ Icc 0 1) p) :=
    mfderivWithin_comp p h2 hsnd (fun q hq ↦ hq.2) hu
  rw [mfderivWithin_prodMk (f := fun q : E × ℝ ↦ (extChartAt I x₀).symm q.1)
    (g := fun q : E × ℝ ↦ projIcc 0 1 zero_le_one q.2) (h1.comp p hfst fun q hq ↦ hq.1)
    (h2.comp p hsnd fun q hq ↦ hq.2) hu, hc1, hc2]
  have hf : mfderivWithin 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) Prod.fst (s ×ˢ Icc 0 1) p (w, c) = w := by
    rw [mfderivWithin_eq_fderivWithin, fderivWithin_fst (hS p hp)]
    rfl
  have hg : mfderivWithin 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ℝ) Prod.snd (s ×ˢ Icc 0 1) p (w, c) = c := by
    rw [mfderivWithin_eq_fderivWithin, fderivWithin_snd (hS p hp)]
    rfl
  have h₁ : mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm s p.1
      (mfderivWithin 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) Prod.fst (s ×ˢ Icc 0 1) p (w, c)) =
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm s p.1 w := congrArg _ hf
  have h₂ : mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ 1) (projIcc 0 1 zero_le_one) (Icc 0 1) p.2
      (mfderivWithin 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ℝ) Prod.snd (s ×ˢ Icc 0 1) p (w, c)) =
        c • (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one p.2)) := by
    rw [hg, ← mfderivWithin_projIcc_one hp.2, ← map_smul]
    congr 1
    exact (mul_one c).symm
  exact Prod.ext_iff.2 ⟨h₁, h₂⟩

/-- Contracting the flat pullback of a form on the cylinder with the time vector `(0, 1)` gives
the integrand of the homotopy operator, read in the chart. -/
private theorem curryLeft_mpullbackWithin_cylinder [IsManifold I 1 M] (x₀ : M) {s : Set E}
    (hs : s ⊆ (extChartAt I x₀).target) (hsu : UniqueDiffOn ℝ s)
    (ψ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) {p : E × ℝ}
    (hp : p ∈ s ×ˢ Icc (0 : ℝ) 1) :
    (ContinuousAlternatingMap.curryLeft (E := E × ℝ) (mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1))
      (fun p : E × ℝ ↦ ((extChartAt I x₀).symm p.1, projIcc 0 1 zero_le_one p.2))
        (s ×ˢ Icc 0 1) ψ p) (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ) =
      ((ContinuousAlternatingMap.curryLeft (E := E × EuclideanSpace ℝ (Fin 1))
        (ψ ((extChartAt I x₀).symm p.1, projIcc 0 1 zero_le_one p.2))
        ((0 : E), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one p.2)))).compContinuousLinearMap
          (.inl ℝ E (EuclideanSpace ℝ (Fin 1)))).compContinuousLinearMap
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm s p.1) := by
  ext v
  -- Both sides evaluate the forms on explicit tuples; only Mathlib's currying is unfolded.
  calc _ = mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1))
        (fun p : E × ℝ ↦ ((extChartAt I x₀).symm p.1, projIcc 0 1 zero_le_one p.2))
          (s ×ˢ Icc 0 1) ψ p (Matrix.vecCons ((0 : E), (1 : ℝ)) fun i ↦ ((v i : E), (0 : ℝ))) :=
        rfl
    _ = ψ ((extChartAt I x₀).symm p.1, projIcc 0 1 zero_le_one p.2)
          (Matrix.vecCons ((0 : E), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one p.2)))
            fun i ↦ ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm s p.1 (v i) : E),
              (0 : EuclideanSpace ℝ (Fin 1)))) := by
        refine (mpullbackWithin_apply _ _ ψ p _).trans (congrArg _ (funext fun i ↦ ?_))
        cases i using Fin.cases with
        | zero =>
          refine (mfderivWithin_cylinderChart_apply x₀ hs hsu hp 0 1).trans ?_
          exact Prod.ext_iff.2 ⟨(mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm s p.1).map_zero,
            one_smul ℝ _⟩
        | succ j =>
          refine (mfderivWithin_cylinderChart_apply x₀ hs hsu hp (v j) 0).trans ?_
          exact Prod.ext_iff.2 ⟨rfl, zero_smul ℝ _⟩
    _ = _ := rfl

/-- In the chart at `x₀`, the homotopy operator is the flat cylinder homotopy operator of the
pullback of the form to the flat cylinder over `s`. -/
private theorem inChartAt_homotopyOperator [IsManifold I 1 M] (x₀ : M) {s : Set E}
    (hs : s ⊆ (extChartAt I x₀).target) (hsu : UniqueDiffOn ℝ s)
    (ψ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) {y : E} (hy : y ∈ s) :
    (homotopyOperator ψ).inChartAt x₀ y = cylinderHomotopy (mpullbackWithin 𝓘(ℝ, E × ℝ)
      (I.prod (𝓡∂ 1)) (fun p : E × ℝ ↦ ((extChartAt I x₀).symm p.1, projIcc 0 1 zero_le_one p.2))
        (s ×ˢ Icc 0 1) ψ) y := by
  obtain ⟨D, hD⟩ := isInvertible_mfderivWithin_extChartAt_symm (hs hy)
  -- The chart derivative, with the model-space tangent identifications made explicit.
  let Dm : E →L[ℝ] E := mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) y
  let D' : E ≃L[ℝ] E := D
  have hD' : (D' : E →L[ℝ] E) = Dm := hD
  have hDs : mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm s y = Dm :=
    (mdifferentiableWithinAt_extChartAt_symm (hs hy)).mfderivWithin_mono_of_mem_nhdsWithin
      (hsu y hy).uniqueMDiffWithinAt
      (mem_of_superset self_mem_nhdsWithin fun z hz ↦ extChartAt_target_subset_range x₀ (hs hz))
  have hL (g : E [⋀^Fin k]→L[ℝ] F) :
      D'.symm.continuousAlternatingMapCongrLeft g = g.compContinuousLinearMap Dm := by
    rw [ContinuousLinearEquiv.continuousAlternatingMapCongrLeft_apply,
      ContinuousLinearEquiv.symm_symm, hD']
  -- The integrand of the homotopy operator at the point `(extChartAt I x₀).symm y`.
  let A : ℝ → E [⋀^Fin k]→L[ℝ] F := fun t ↦
    (ContinuousAlternatingMap.curryLeft (E := E × EuclideanSpace ℝ (Fin 1))
      (ψ ((extChartAt I x₀).symm y, projIcc 0 1 zero_le_one t))
      ((0 : E), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one t)))).compContinuousLinearMap
        (.inl ℝ E (EuclideanSpace ℝ (Fin 1)))
  calc (homotopyOperator ψ).inChartAt x₀ y
      = D'.symm.continuousAlternatingMapCongrLeft (∫ t in (0 : ℝ)..1, A t) := by
        rw [hL]
        ext v
        exact RoughForm.inChartAt_apply _ x₀ y v
    _ = ∫ t in (0 : ℝ)..1, D'.symm.continuousAlternatingMapCongrLeft (A t) :=
        (ContinuousLinearEquiv.intervalIntegral_comp_comm _ _).symm
    _ = _ := by
        refine Eq.trans ?_ (cylinderHomotopy_apply _ y).symm
        refine intervalIntegral.integral_congr fun t ht ↦ ?_
        rw [uIcc_of_le zero_le_one] at ht
        simp only [A]
        rw [hL, curryLeft_mpullbackWithin_cylinder x₀ hs hsu ψ ⟨hy, ht⟩, hDs]
        rfl

/-- The map from the flat cylinder over a subset of the chart target into `M × [0, 1]` is as
smooth as the manifold. -/
private theorem contMDiffOn_cylinderChart {n : WithTop ℕ∞} [IsManifold I n M] (x₀ : M) {s : Set E}
    (hs : s ⊆ (extChartAt I x₀).target) :
    ContMDiffOn 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1)) n
      (fun p : E × ℝ ↦ ((extChartAt I x₀).symm p.1, projIcc 0 1 zero_le_one p.2))
        (s ×ˢ Icc 0 1) :=
  ((contMDiffOn_extChartAt_symm x₀).comp (s := s ×ˢ Icc (0 : ℝ) 1)
    contDiff_fst.contMDiff.contMDiffOn fun _ hp ↦ hs hp.1).prodMk
    ((contMDiffOn_projIcc).comp (s := s ×ˢ Icc (0 : ℝ) 1)
      contDiff_snd.contMDiff.contMDiffOn fun _ hp ↦ hp.2)

/-- The pullback of a `C^r` form on `M × [0, 1]` to the flat cylinder over a subset of a chart
target is `C^r`. -/
private theorem contDiffOn_mpullbackWithin_cylinder {r : ℕ∞} [IsManifold I 1 M]
    [IsManifold I (r + 1) M] (x₀ : M) {s : Set E}
    (hs : s ⊆ (extChartAt I x₀).target) (hsu : UniqueDiffOn ℝ s)
    {φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)}
    (hφ : IsSmoothForm (I.prod (𝓡∂ 1)) r φ) :
    ContDiffOn (F := (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F) ℝ r (mpullbackWithin 𝓘(ℝ, E × ℝ)
      (I.prod (𝓡∂ 1)) (fun p : E × ℝ ↦ ((extChartAt I x₀).symm p.1, projIcc 0 1 zero_le_one p.2))
        (s ×ˢ Icc 0 1) φ) (s ×ˢ Icc 0 1) := by
  have h := ContMDiffOn.mpullbackWithin_form (hφ.contMDiff.contMDiffOn (s := univ))
    (contMDiffOn_cylinderChart (n := r + 1) x₀ hs) le_rfl
    (mapsTo_univ _ _) (hsu.prod uniqueDiffOn_Icc_zero_one).uniqueMDiffOn
  intro p hp
  simpa [RoughForm.inChartAt_modelSpace, extChartAt_model_space_eq_id] using
    RoughForm.contDiffWithinAt_inChartAt _ (h p hp)

/-- A neighbourhood of the chart point in the model range on which the flat cylinder homotopy
identity applies: it lies in the chart target, is convex with unique derivatives, and its
interior accumulates at the chart point. -/
private theorem exists_chart_nhds (x₀ : M) :
    ∃ s : Set E, s ⊆ (extChartAt I x₀).target ∧ UniqueDiffOn ℝ s ∧ Convex ℝ s ∧
      s ∈ 𝓝[range I] extChartAt I x₀ x₀ ∧ extChartAt I x₀ x₀ ∈ s ∧
      extChartAt I x₀ x₀ ∈ closure (interior s) := by
  obtain ⟨ε, hε, hsub⟩ : ∃ ε > 0, ball (extChartAt I x₀ x₀) ε ∩ range I ⊆
      (extChartAt I x₀).target :=
    Metric.mem_nhdsWithin_iff.mp (extChartAt_target_mem_nhdsWithin x₀)
  have hx : extChartAt I x₀ x₀ ∈ range I :=
    extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)
  refine ⟨ball (extChartAt I x₀ x₀) ε ∩ range I, hsub, ?_, (convex_ball _ _).inter I.convex_range,
    ?_, ⟨mem_ball_self hε, hx⟩, ?_⟩
  · rw [inter_comm]
    exact I.uniqueDiffOn.inter isOpen_ball
  · rw [inter_comm]
    exact inter_mem_nhdsWithin _ (isOpen_ball.mem_nhds (mem_ball_self hε))
  · rw [interior_inter, isOpen_ball.interior_eq]
    exact isOpen_ball.inter_closure ⟨mem_ball_self hε, I.range_subset_closure_interior hx⟩

/-- At the chart point, the slice at time `t` of the flat pullback of `φ` is the pullback of `φ`
along the slice inclusion `x ↦ (x, t)`. -/
private theorem compContinuousLinearMap_inl_mpullbackWithin_cylinder [IsManifold I 1 M]
    (x₀ : M) {s : Set E} (hs : s ⊆ (extChartAt I x₀).target) (hsu : UniqueDiffOn ℝ s)
    (hx : extChartAt I x₀ x₀ ∈ s)
    (φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) (t : Icc (0 : ℝ) 1) :
    (mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1))
      (fun p : E × ℝ ↦ ((extChartAt I x₀).symm p.1, projIcc 0 1 zero_le_one p.2))
        (s ×ˢ Icc 0 1) φ (extChartAt I x₀ x₀, t)).compContinuousLinearMap (.inl ℝ E ℝ) =
      mpullback I (I.prod (𝓡∂ 1)) (fun x ↦ (x, t)) φ x₀ := by
  have hD : mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm s (extChartAt I x₀ x₀) =
      ContinuousLinearMap.id ℝ E := by
    refine Eq.trans ?_ (mfderivWithin_range_extChartAt_symm (I := I) (x := x₀))
    exact (mdifferentiableWithinAt_extChartAt_symm
      (mem_extChartAt_target x₀)).mfderivWithin_mono_of_mem_nhdsWithin
      (hsu _ hx).uniqueMDiffWithinAt (mem_of_superset self_mem_nhdsWithin
        fun z hz ↦ extChartAt_target_subset_range x₀ (hs hz))
  have hpt : ((extChartAt I x₀).symm (extChartAt I x₀ x₀), projIcc 0 1 zero_le_one (t : ℝ)) =
      (x₀, t) := by
    rw [extChartAt_to_inv, projIcc_val]
  have hl (w : E) : mfderivWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1))
      (fun p : E × ℝ ↦ ((extChartAt I x₀).symm p.1, projIcc 0 1 zero_le_one p.2))
      (s ×ˢ Icc 0 1) (extChartAt I x₀ x₀, (t : ℝ)) (ContinuousLinearMap.inl ℝ E ℝ w) =
        (w, (0 : EuclideanSpace ℝ (Fin 1))) := by
    refine (mfderivWithin_cylinderChart_apply x₀ hs hsu (p := (extChartAt I x₀ x₀, (t : ℝ)))
      ⟨hx, t.2⟩ w 0).trans ?_
    rw [hD, zero_smul]
    rfl
  have hr (w : E) : mfderiv I (I.prod (𝓡∂ 1)) (fun x ↦ (x, t)) x₀ w =
      (w, (0 : EuclideanSpace ℝ (Fin 1))) := by
    rw [mfderiv_prod_left]
    rfl
  ext v
  refine (ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _).trans
    ((mpullbackWithin_apply _ _ φ _ _).trans (Eq.trans ?_ (mpullback_apply _ φ x₀ v).symm))
  simp only [Function.comp_apply, hr]
  rw [hpt]
  exact congrArg _ (funext fun i ↦ hl (v i))

/-! ### Regularity and the cochain-homotopy identity -/

/-- The homotopy operator preserves `C^r` regularity of forms, for every `r`, on a `C^(r + 1)`
manifold, possibly with boundary or corners. -/
theorem IsSmoothForm.homotopyOperator {r : ℕ∞} [IsManifold I 1 M] [IsManifold I (r + 1) M]
    {φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)}
    (hφ : IsSmoothForm (I.prod (𝓡∂ 1)) r φ) : IsSmoothForm I r (homotopyOperator φ) := by
  refine IsSmoothForm.of_contDiffWithinAt_inChartAt_self fun x₀ ↦ ?_
  obtain ⟨s, hsub, hsu, hconv, hsn, hxs, -⟩ := exists_chart_nhds (I := I) x₀
  have heq : (TauCeti.homotopyOperator φ).inChartAt x₀ =ᶠ[𝓝[range I] extChartAt I x₀ x₀]
      cylinderHomotopy (mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1))
        (fun p : E × ℝ ↦ ((extChartAt I x₀).symm p.1, projIcc 0 1 zero_le_one p.2))
        (s ×ˢ Icc 0 1) φ) := by
    filter_upwards [hsn] with y hy
    exact inChartAt_homotopyOperator x₀ hsub hsu φ hy
  exact ((hconv.contDiffOn_cylinderHomotopy hsu (contDiffOn_mpullbackWithin_cylinder x₀ hsub hsu
    hφ) _ hxs).mono_of_mem_nhdsWithin hsn).congr_of_eventuallyEq heq
      (heq.self_of_nhdsWithin (extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)))

/-- **The cochain-homotopy identity** for the homotopy operator on the cylinder `M × [0, 1]`:
for a `C¹` form `φ` with values in a Banach space on a `C²` manifold, possibly with boundary or
corners, `d (h φ) + h (d φ) = ι₁^* φ - ι₀^* φ`, where `ιₜ x = (x, t)`. -/
theorem mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv [IsManifold I 2 M]
    [CompleteSpace F] {φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)}
    (hφ : IsSmoothForm (I.prod (𝓡∂ 1)) 1 φ) (x₀ : M) :
    mextDeriv (homotopyOperator φ) x₀ + homotopyOperator (mextDeriv φ) x₀ =
      mpullback I (I.prod (𝓡∂ 1)) (fun x ↦ (x, 1)) φ x₀ -
        mpullback I (I.prod (𝓡∂ 1)) (fun x ↦ (x, 0)) φ x₀ := by
  have : IsManifold I ((1 : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := 2) (by norm_num)
  obtain ⟨s, hsub, hsu, hconv, hsn, hxs, hxc⟩ := exists_chart_nhds (I := I) x₀
  -- The flat pullback of `φ` to the cylinder over `s`, and its cylinder homotopy identity.
  set η := mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1))
    (fun p : E × ℝ ↦ ((extChartAt I x₀).symm p.1, projIcc 0 1 zero_le_one p.2))
    (s ×ˢ Icc 0 1) φ
  have key := hconv.extDerivWithin_cylinderHomotopy_add_cylinderHomotopy_extDerivWithin
    («ω» := η) hsu (contDiffOn_mpullbackWithin_cylinder (r := 1) x₀ hsub hsu hφ) hxs
  -- `d (h φ)` at `x₀` is the flat exterior derivative of the chart expression of `h φ`.
  have h₁ : mextDeriv (homotopyOperator φ) x₀ =
      extDerivWithin (cylinderHomotopy η) s (extChartAt I x₀ x₀) := by
    have heq : (homotopyOperator φ).inChartAt x₀ =ᶠ[𝓝[s] extChartAt I x₀ x₀]
        cylinderHomotopy η :=
      eventually_of_mem self_mem_nhdsWithin fun y hy ↦ inChartAt_homotopyOperator x₀ hsub hsu φ hy
    have hset : s =ᶠ[𝓝 (extChartAt I x₀ x₀)] range I := by
      filter_upwards [mem_nhdsWithin_iff_eventually.1 hsn] with y hy
      exact propext ⟨fun h ↦ extChartAt_target_subset_range x₀ (hsub h), hy⟩
    rw [mextDeriv_def, ← extDerivWithin_congr_set hset]
    exact heq.extDerivWithin_eq (heq.self_of_nhdsWithin hxs)
  -- `h (d φ)` at `x₀` is the cylinder homotopy operator of the flat exterior derivative of `η`.
  have h₂ : homotopyOperator (mextDeriv φ) x₀ =
      cylinderHomotopy (extDerivWithin η (s ×ˢ Icc 0 1)) (extChartAt I x₀ x₀) := by
    refine (RoughForm.inChartAt_extChartAt_self _ x₀).symm.trans ?_
    refine (inChartAt_homotopyOperator x₀ hsub hsu (mextDeriv φ) hxs).trans ?_
    refine cylinderHomotopy_congr fun t ht ↦ ?_
    have hcl : (extChartAt I x₀ x₀, t) ∈ closure (interior (s ×ˢ Icc (0 : ℝ) 1)) := by
      rw [interior_prod_eq, closure_prod_eq, interior_Icc, closure_Ioo zero_ne_one]
      exact ⟨hxc, ht⟩
    exact (extDerivWithin_mpullbackWithin (contMDiffOn_cylinderChart (n := 2) x₀ hsub _ ⟨hxs, ht⟩)
      (hsu.prod uniqueDiffOn_Icc_zero_one) hcl ⟨hxs, ht⟩
      ((hφ.contMDiff _).mdifferentiableAt one_ne_zero)).symm
  rw [h₁, h₂]
  refine key.trans ?_
  congr 1
  · exact compContinuousLinearMap_inl_mpullbackWithin_cylinder x₀ hsub hsu hxs φ 1
  · exact compContinuousLinearMap_inl_mpullbackWithin_cylinder x₀ hsub hsu hxs φ 0

/-- **Closed forms on a cylinder.** For a closed `C¹` form `φ` on `M × [0, 1]` with values in a
Banach space, on a `C²` manifold possibly with boundary or corners, the difference
`ι₁^* φ - ι₀^* φ` of its slices is the exterior derivative of `h φ`. -/
theorem mextDeriv_homotopyOperator [IsManifold I 2 M] [CompleteSpace F]
    {φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)}
    (hφ : IsSmoothForm (I.prod (𝓡∂ 1)) 1 φ) (hclosed : mextDeriv φ = 0) (x : M) :
    mextDeriv (homotopyOperator φ) x =
      mpullback I (I.prod (𝓡∂ 1)) (fun y ↦ (y, 1)) φ x -
        mpullback I (I.prod (𝓡∂ 1)) (fun y ↦ (y, 0)) φ x := by
  rw [← mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv hφ x, hclosed,
    homotopyOperator_zero, Pi.zero_apply, add_zero]

end TauCeti
