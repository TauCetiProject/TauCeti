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
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
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

On a `C^(r + 1)` manifold, `h` sends `C^r` forms to `C^r` forms
(`TauCeti.IsSmoothForm.homotopyOperator`), and on a `C¹` manifold it is additive on continuous
forms (`TauCeti.homotopyOperator_add`). For a `C¹` form with values in a Banach space on a `C²`
manifold, it satisfies the cochain-homotopy identity
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
* `TauCeti.homotopyOperator_add`, `TauCeti.homotopyOperator_sub`: `h` is additive on continuous
  forms.
* `TauCeti.homotopyOperator_mpullback_fst`: `h` kills forms pulled back from `M`.
* `TauCeti.homotopyOperator_mpullback_prodMap_id`: `h` commutes with pullback along `g × id` for
  a map `g` with invertible derivatives.
* `TauCeti.homotopyOperator_mpullback_prodMap_id_of_isSmoothForm`: the same for a continuous form
  and an arbitrary differentiable map `g`.
* `TauCeti.mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv`: the cochain-homotopy
  identity `d (h φ) + h (d φ) = ι₁^* φ - ι₀^* φ`.
* `TauCeti.mextDeriv_homotopyOperator`: for a closed form, `d (h φ) = ι₁^* φ - ι₀^* φ`.
* `TauCeti.homotopyOperator_mextDeriv_of_mpullback_eq_zero`: for a form whose end slices vanish,
  `h (d φ) = -d (h φ)`.
* `TauCeti.homotopyOperator_mpullback_one_sub_mpullback_zero`: for a closed form `η` on the double
  cylinder `(M × [0, 1]) × [0, 1]` vanishing on the second time vector over both ends of the inner
  cylinder, `h (j₁^* η - j₀^* η) = -d (h (h η))`; this is the homotopy-rel-ends invariance of the
  homotopy operator.

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

/-- The integrand of the homotopy operator at `x` and time `t`: the contraction of `φ(x, t)` with
the unit time vector `∂ₜ = (0, 1)`, evaluated on tangent vectors of `M` included by
`ContinuousLinearMap.inl`. -/
private def homotopyIntegrand (φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1))
    (x : M) (t : ℝ) : E [⋀^Fin k]→L[ℝ] F :=
  (ContinuousAlternatingMap.curryLeft (E := E × EuclideanSpace ℝ (Fin 1))
    (φ (x, projIcc 0 1 zero_le_one t))
    ((0 : E), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one t)))).compContinuousLinearMap
      (.inl ℝ E (EuclideanSpace ℝ (Fin 1)))

/-- The **homotopy operator** on forms on the cylinder `M × [0, 1]`: the `k`-form
`x ↦ ∫₀¹ φ(x, t)(∂ₜ, (·, 0)) dt` on `M` built from a `(k + 1)`-form `φ` on `M × [0, 1]`, where
`∂ₜ = (0, 1)` is the unit time vector and tangent vectors of `M` enter through
`ContinuousLinearMap.inl`. Equivalently `h φ = ∫₀¹ ιₜ^*(∂ₜ ⌟ φ) dt` for the slices
`ιₜ x = (x, t)`. For a `C¹` form with values in a Banach space on a `C²` manifold,
`d (h φ) + h (d φ) = ι₁^* φ - ι₀^* φ`
(`TauCeti.mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv`). -/
def homotopyOperator
    (φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) : RoughForm I M F k :=
  fun x ↦ intervalIntegral (E := E [⋀^Fin k]→L[ℝ] F) (homotopyIntegrand φ x) 0 1 volume

/-- The value of the homotopy operator at a point, as an integral over the time interval. -/
theorem homotopyOperator_apply (φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1))
    (x : M) :
    homotopyOperator φ x = intervalIntegral (E := E [⋀^Fin k]→L[ℝ] F) (fun t ↦
      (ContinuousAlternatingMap.curryLeft (E := E × EuclideanSpace ℝ (Fin 1))
        (φ (x, projIcc 0 1 zero_le_one t))
        ((0 : E), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one t)))).compContinuousLinearMap
          (.inl ℝ E (EuclideanSpace ℝ (Fin 1)))) 0 1 volume :=
  (rfl)

/-- The homotopy operator vanishes at `x` when, at every time `t`, the form `φ (x, t)` vanishes on
every family whose first vector is the unit time vector `∂ₜ = (0, 1)`. -/
theorem homotopyOperator_apply_eq_zero
    {φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)} {x : M}
    (h : ∀ (t : Icc (0 : ℝ) 1) (v : Fin k → E × EuclideanSpace ℝ (Fin 1)),
      φ (x, t) (Matrix.vecCons ((0 : E), (1 : TangentSpace (𝓡∂ 1) t)) v) = 0) :
    homotopyOperator φ x = 0 := by
  rw [homotopyOperator_apply]
  -- The integrand vanishes: its first argument is `∂ₜ`.
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : E [⋀^Fin k]→L[ℝ] F))
    fun t _ ↦ ?_).trans (intervalIntegral.integral_zero (E := E [⋀^Fin k]→L[ℝ] F))
  refine ContinuousAlternatingMap.ext fun w ↦ ?_
  -- `curryLeft_apply_apply` does not fire: the tangent spaces of the cylinder are the model
  -- spaces only by definition. So state the evaluation of the curried form on `∂ₜ` followed by
  -- the included vectors explicitly.
  change φ (x, projIcc 0 1 zero_le_one t)
    (Matrix.vecCons ((0 : E), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one t)))
      fun i ↦ ((w i : E), (0 : EuclideanSpace ℝ (Fin 1)))) = 0
  exact h _ _

/-- The homotopy operator of the zero form is zero. -/
@[simp]
theorem homotopyOperator_zero :
    homotopyOperator (0 : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) = 0 := by
  funext _
  -- The integrand of the zero form is the zero function.
  exact intervalIntegral.integral_zero (E := E [⋀^Fin k]→L[ℝ] F) (a := 0) (b := 1)

/-- The homotopy operator commutes with real scalar multiplication of forms. -/
@[simp]
theorem homotopyOperator_smul (c : ℝ)
    (φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) :
    homotopyOperator (c • φ) = c • homotopyOperator φ := by
  funext x
  -- The integrand of `c • φ` is `c` times the integrand of `φ`.
  exact intervalIntegral.integral_smul (μ := volume) (a := 0) (b := 1) c (homotopyIntegrand φ x)

/-- The homotopy operator kills every form pulled back from `M` along the projection
`M × [0, 1] → M`: such a form vanishes on the unit time vector `∂ₜ`. -/
@[simp]
theorem homotopyOperator_mpullback_fst (φ : RoughForm I M F (k + 1)) :
    homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I Prod.fst φ) = 0 := by
  funext x
  refine homotopyOperator_apply_eq_zero fun t v ↦ ?_
  rw [mpullback_apply, mfderiv_fst]
  -- The projection sends the first vector `∂ₜ = (0, 1)` to `0`.
  exact (φ x).map_coord_zero 0 rfl

/-- The integrand of the homotopy operator of a pullback along `g × id` is the integrand at the
image point, evaluated on the images of the vectors under the derivative of `g`. -/
private theorem homotopyIntegrand_mpullback_prodMap_id_apply {E' H' M' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] {g : M' → M}
    (hg : MDifferentiable I' I g) (φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1))
    (y : M') (t : ℝ) (v : Fin k → E') :
    homotopyIntegrand (mpullback (I'.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) (Prod.map g id) φ) y t v =
      homotopyIntegrand φ (g y) t fun i ↦ mfderiv I' I g y (v i) := by
  -- Both sides evaluate `φ` at `(g y, t)` on `∂ₜ` and the vectors `(dg (v i), 0)`; the
  -- derivative of `g × id` acts componentwise.
  refine (mpullback_apply _ φ _ (Fin.cons _ fun i ↦ ((v i : E'),
    (0 : EuclideanSpace ℝ (Fin 1))))).trans (congrArg _ (funext fun i ↦ ?_))
  rw [mfderiv_prodMap (hg y) mdifferentiableAt_id, mfderiv_id]
  cases i using Fin.cases with
  | zero => exact Prod.ext (map_zero (mfderiv I' I g y)) rfl
  | succ j => rfl

/-- **Naturality of the homotopy operator.** Pulling a form on the cylinder back along `g × id`
commutes with the homotopy operator, for a differentiable map `g` whose derivatives are
invertible, for instance a diffeomorphism. For continuous forms the derivatives of `g` may be
arbitrary (`TauCeti.homotopyOperator_mpullback_prodMap_id_of_isSmoothForm`). -/
theorem homotopyOperator_mpullback_prodMap_id {E' H' M' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] {g : M' → M} (hg : MDifferentiable I' I g)
    (hdg : ∀ y, (mfderiv I' I g y).IsInvertible)
    (φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) :
    homotopyOperator (mpullback (I'.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) (Prod.map g id) φ) =
      mpullback I' I g (homotopyOperator φ) := by
  funext y
  obtain ⟨D, hD⟩ := hdg y
  -- The derivative of `g` at `y`, with the model-space tangent identifications made explicit.
  let Dm : E' →L[ℝ] E := mfderiv I' I g y
  let D' : E' ≃L[ℝ] E := D
  have hD' : (D' : E' →L[ℝ] E) = Dm := hD
  have hL (a : E [⋀^Fin k]→L[ℝ] F) :
      D'.symm.continuousAlternatingMapCongrLeft a = a.compContinuousLinearMap Dm := by
    rw [ContinuousLinearEquiv.continuousAlternatingMapCongrLeft_apply,
      ContinuousLinearEquiv.symm_symm, hD']
  -- The values of both forms at `y` are alternating maps on the model space `E'`.
  change @Eq (E' [⋀^Fin k]→L[ℝ] F) _ _
  calc _ = ∫ t in (0 : ℝ)..1, D'.symm.continuousAlternatingMapCongrLeft
          (homotopyIntegrand φ (g y) t) :=
        intervalIntegral.integral_congr fun t _ ↦ by
          rw [hL]
          ext v
          exact homotopyIntegrand_mpullback_prodMap_id_apply hg φ y t v
    _ = D'.symm.continuousAlternatingMapCongrLeft
          (∫ t in (0 : ℝ)..1, homotopyIntegrand φ (g y) t) :=
        ContinuousLinearEquiv.intervalIntegral_comp_comm _ _
    _ = _ := by
        rw [hL]
        ext v
        exact (mpullback_apply (I := I') (I' := I) g (homotopyOperator φ) y v).symm

/-! ### The chart expression of the homotopy operator -/

/-- The map `(y, t) ↦ ((extChartAt I x₀).symm y, projIcc 0 1 t)` from a flat cylinder into
`M × [0, 1]`, along which forms on `M × [0, 1]` are read in the chart at `x₀`. -/
private def cylinderChart (I : ModelWithCorners ℝ E H) (x₀ : M) : E × ℝ → M × Icc (0 : ℝ) 1 :=
  Prod.map (extChartAt I x₀).symm (projIcc 0 1 zero_le_one)

private theorem cylinderChart_apply (x₀ : M) (p : E × ℝ) :
    cylinderChart I x₀ p = ((extChartAt I x₀).symm p.1, projIcc 0 1 zero_le_one p.2) :=
  (rfl)

/-- The derivative of the cylinder chart `(y, t) ↦ ((extChartAt I x₀).symm y, projIcc 0 1 t)`. -/
private theorem mfderivWithin_cylinderChart_apply [IsManifold I 1 M] (x₀ : M) {s : Set E}
    (hs : s ⊆ (extChartAt I x₀).target)
    (hsu : UniqueDiffOn ℝ s) {p : E × ℝ} (hp : p ∈ s ×ˢ Icc (0 : ℝ) 1) (w : E) (c : ℝ) :
    mfderivWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1)) (cylinderChart I x₀) (s ×ˢ Icc 0 1) p (w, c) =
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm s p.1 w,
        c • (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one p.2))) := by
  have h1 : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I x₀).symm s p.1 :=
    ((contMDiffOn_extChartAt_symm (n := 1) x₀).mono hs p.1 hp.1).mdifferentiableWithinAt one_ne_zero
  have h2 : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (𝓡∂ 1) (projIcc (0 : ℝ) 1 zero_le_one) (Icc 0 1) p.2 :=
    (contMDiffOn_projIcc (n := 1) p.2 hp.2).mdifferentiableWithinAt one_ne_zero
  rw [cylinderChart, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
    mfderivWithin_prodMap h1 h2 (hsu _ hp.1).uniqueMDiffWithinAt
      (uniqueDiffOn_Icc_zero_one _ hp.2).uniqueMDiffWithinAt]
  rw [← mfderivWithin_projIcc_one hp.2, ← map_smul]
  -- `ContinuousLinearMap.prodMap` acts componentwise, and `c • 1` in `TangentSpace 𝓘(ℝ, ℝ) _`
  -- is the product `c * 1` in `ℝ`, both by definition.
  exact Prod.ext_iff.2 ⟨rfl, congrArg
    (mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ 1) (projIcc 0 1 zero_le_one) (Icc 0 1) p.2) (mul_one c).symm⟩

/-- Contracting the flat pullback of a form on the cylinder with the time vector `(0, 1)` gives
the integrand of the homotopy operator, read in the chart. -/
private theorem curryLeft_mpullbackWithin_cylinder [IsManifold I 1 M] (x₀ : M) {s : Set E}
    (hs : s ⊆ (extChartAt I x₀).target) (hsu : UniqueDiffOn ℝ s)
    (ψ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) {y : E} {t : ℝ} (hy : y ∈ s)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (ContinuousAlternatingMap.curryLeft (E := E × ℝ) (mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1))
      (cylinderChart I x₀) (s ×ˢ Icc 0 1) ψ (y, t)) (0, 1)).compContinuousLinearMap
        (.inl ℝ E ℝ) =
      (homotopyIntegrand ψ ((extChartAt I x₀).symm y) t).compContinuousLinearMap
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm s y) := by
  ext v
  -- Both sides evaluate the forms on explicit tuples; only Mathlib's currying and
  -- `homotopyIntegrand` are unfolded.
  calc _ = mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1)) (cylinderChart I x₀) (s ×ˢ Icc 0 1) ψ
          (y, t) (Matrix.vecCons ((0 : E), (1 : ℝ)) fun i ↦ ((v i : E), (0 : ℝ))) :=
        rfl
    _ = ψ ((extChartAt I x₀).symm y, projIcc 0 1 zero_le_one t)
          (Matrix.vecCons ((0 : E), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one t)))
            fun i ↦ ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm s y (v i) : E),
              (0 : EuclideanSpace ℝ (Fin 1)))) := by
        refine (mpullbackWithin_apply _ _ ψ (y, t) _).trans (congrArg _ (funext fun i ↦ ?_))
        cases i using Fin.cases with
        | zero =>
          refine (mfderivWithin_cylinderChart_apply x₀ hs hsu ⟨hy, ht⟩ 0 1).trans ?_
          exact Prod.ext_iff.2 ⟨(mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm s y).map_zero,
            one_smul ℝ _⟩
        | succ j =>
          refine (mfderivWithin_cylinderChart_apply x₀ hs hsu ⟨hy, ht⟩ (v j) 0).trans ?_
          exact Prod.ext_iff.2 ⟨rfl, zero_smul ℝ _⟩
    _ = _ := rfl

/-- Read in the chart at `x₀`, through the chart derivative `D`, the integrand of the homotopy
operator is the integrand of the flat cylinder homotopy operator of the pullback of the form to the
flat cylinder over `s`. -/
private theorem continuousAlternatingMapCongrLeft_homotopyIntegrand [IsManifold I 1 M] (x₀ : M)
    {s : Set E} (hs : s ⊆ (extChartAt I x₀).target) (hsu : UniqueDiffOn ℝ s)
    (ψ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) {y : E} (hy : y ∈ s) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {D : E ≃L[ℝ] E}
    (hD : (D : E →L[ℝ] E) = mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) y) :
    D.symm.continuousAlternatingMapCongrLeft (homotopyIntegrand ψ ((extChartAt I x₀).symm y) t) =
      (ContinuousAlternatingMap.curryLeft (E := E × ℝ) (mpullbackWithin 𝓘(ℝ, E × ℝ)
        (I.prod (𝓡∂ 1)) (cylinderChart I x₀) (s ×ˢ Icc 0 1) ψ (y, t))
          (0, 1)).compContinuousLinearMap (.inl ℝ E ℝ) := by
  rw [ContinuousLinearEquiv.continuousAlternatingMapCongrLeft_apply,
    ContinuousLinearEquiv.symm_symm, hD, curryLeft_mpullbackWithin_cylinder x₀ hs hsu ψ hy ht]
  exact congrArg _ (mfderivWithin_extChartAt_symm_of_subset x₀ hs hsu hy).symm

/-- In the chart at `x₀`, the homotopy operator is the flat cylinder homotopy operator of the
pullback of the form to the flat cylinder over `s`. -/
private theorem inChartAt_homotopyOperator [IsManifold I 1 M] (x₀ : M) {s : Set E}
    (hs : s ⊆ (extChartAt I x₀).target) (hsu : UniqueDiffOn ℝ s)
    (ψ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) {y : E} (hy : y ∈ s) :
    (homotopyOperator ψ).inChartAt x₀ y =
      cylinderHomotopy (mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1)) (cylinderChart I x₀)
        (s ×ˢ Icc 0 1) ψ) y := by
  obtain ⟨D, hD⟩ := isInvertible_mfderivWithin_extChartAt_symm (hs hy)
  -- The chart derivative, with the model-space tangent identifications made explicit.
  let Dm : E →L[ℝ] E := mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) y
  let D' : E ≃L[ℝ] E := D
  have hD' : (D' : E →L[ℝ] E) = Dm := hD
  have hL (g : E [⋀^Fin k]→L[ℝ] F) :
      D'.symm.continuousAlternatingMapCongrLeft g = g.compContinuousLinearMap Dm := by
    rw [ContinuousLinearEquiv.continuousAlternatingMapCongrLeft_apply,
      ContinuousLinearEquiv.symm_symm, hD']
  calc (homotopyOperator ψ).inChartAt x₀ y
      = D'.symm.continuousAlternatingMapCongrLeft
          (∫ t in (0 : ℝ)..1, homotopyIntegrand ψ ((extChartAt I x₀).symm y) t) := by
        rw [hL]
        ext v
        exact RoughForm.inChartAt_apply _ x₀ y v
    _ = ∫ t in (0 : ℝ)..1, D'.symm.continuousAlternatingMapCongrLeft
          (homotopyIntegrand ψ ((extChartAt I x₀).symm y) t) :=
        (ContinuousLinearEquiv.intervalIntegral_comp_comm _ _).symm
    _ = _ := by
        refine Eq.trans ?_ (cylinderHomotopy_apply _ y).symm
        refine intervalIntegral.integral_congr fun t ht ↦ ?_
        rw [uIcc_of_le zero_le_one] at ht
        exact continuousAlternatingMapCongrLeft_homotopyIntegrand x₀ hs hsu ψ hy ht hD'

/-- The cylinder chart over a subset of the chart target is as smooth as the manifold. -/
private theorem contMDiffOn_cylinderChart {n : WithTop ℕ∞} [IsManifold I n M] (x₀ : M) {s : Set E}
    (hs : s ⊆ (extChartAt I x₀).target) :
    ContMDiffOn 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1)) n (cylinderChart I x₀) (s ×ˢ Icc 0 1) := by
  rw [cylinderChart, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact ((contMDiffOn_extChartAt_symm x₀).mono hs).prodMap contMDiffOn_projIcc

/-- The pullback of a `C^r` form on `M × [0, 1]` to the flat cylinder over a subset of a chart
target is `C^r`. -/
private theorem contDiffOn_mpullbackWithin_cylinder {r : ℕ∞} [IsManifold I 1 M]
    [IsManifold I (r + 1) M] (x₀ : M) {s : Set E} (hs : s ⊆ (extChartAt I x₀).target)
    (hsu : UniqueDiffOn ℝ s)
    {φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)}
    (hφ : IsSmoothForm (I.prod (𝓡∂ 1)) r φ) :
    ContDiffOn (F := (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F) ℝ r
      (mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1)) (cylinderChart I x₀) (s ×ˢ Icc 0 1) φ)
      (s ×ˢ Icc 0 1) := by
  have h := ContMDiffOn.mpullbackWithin_form (hφ.contMDiff.contMDiffOn (s := univ))
    (contMDiffOn_cylinderChart (n := r + 1) x₀ hs) le_rfl
    (mapsTo_univ _ _) (hsu.prod uniqueDiffOn_Icc_zero_one).uniqueMDiffOn
  intro p hp
  exact RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace (h p hp)

/-- At the chart point, the slice at time `t` of the flat pullback of `φ` is the pullback of `φ`
along the slice inclusion `x ↦ (x, t)`. -/
private theorem compContinuousLinearMap_inl_mpullbackWithin_cylinder [IsManifold I 1 M]
    (x₀ : M) {s : Set E} (hs : s ⊆ (extChartAt I x₀).target) (hsu : UniqueDiffOn ℝ s)
    (hx : extChartAt I x₀ x₀ ∈ s)
    (φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) (t : Icc (0 : ℝ) 1) :
    (mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1)) (cylinderChart I x₀) (s ×ˢ Icc 0 1) φ
      (extChartAt I x₀ x₀, t)).compContinuousLinearMap (.inl ℝ E ℝ) =
      mpullback I (I.prod (𝓡∂ 1)) (fun x ↦ (x, t)) φ x₀ := by
  have hD : mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm s (extChartAt I x₀ x₀) =
      ContinuousLinearMap.id ℝ E :=
    (mfderivWithin_extChartAt_symm_of_subset x₀ hs hsu hx).trans
      (mfderivWithin_range_extChartAt_symm (I := I) (x := x₀))
  have hpt : cylinderChart I x₀ (extChartAt I x₀ x₀, (t : ℝ)) = (x₀, t) := by
    rw [cylinderChart_apply, extChartAt_to_inv, projIcc_val]
  have hl (w : E) : mfderivWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1)) (cylinderChart I x₀)
      (s ×ˢ Icc 0 1) (extChartAt I x₀ x₀, (t : ℝ)) (ContinuousLinearMap.inl ℝ E ℝ w) =
        (w, (0 : EuclideanSpace ℝ (Fin 1))) := by
    rw [ContinuousLinearMap.inl_apply, mfderivWithin_cylinderChart_apply x₀ hs hsu ⟨hx, t.2⟩,
      hD, zero_smul]
    -- `ContinuousLinearMap.id ℝ E w` is `w`, and `0 : TangentSpace (𝓡∂ 1) t` is
    -- `0 : EuclideanSpace ℝ (Fin 1)`, both by definition.
    rfl
  have hr (w : E) : mfderiv I (I.prod (𝓡∂ 1)) (fun x ↦ (x, t)) x₀ w =
      (w, (0 : EuclideanSpace ℝ (Fin 1))) := by
    rw [mfderiv_prod_left]
    -- `ContinuousLinearMap.inl` sends `w` to `(w, 0)`, and `0 : TangentSpace (𝓡∂ 1) t` is
    -- `0 : EuclideanSpace ℝ (Fin 1)`, both by definition.
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
  obtain ⟨s, hsub, hsu, hconv, hsn, hxs, -⟩ :=
    exists_convex_uniqueDiffOn_mem_nhdsWithin_extChartAt (I := I) x₀
  have heq : (TauCeti.homotopyOperator φ).inChartAt x₀ =ᶠ[𝓝[range I] extChartAt I x₀ x₀]
      cylinderHomotopy (mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1)) (cylinderChart I x₀)
        (s ×ˢ Icc 0 1) φ) := by
    filter_upwards [hsn] with y hy
    exact inChartAt_homotopyOperator x₀ hsub hsu φ hy
  exact ((hconv.contDiffOn_cylinderHomotopy hsu (contDiffOn_mpullbackWithin_cylinder x₀ hsub hsu
    hφ) _ hxs).mono_of_mem_nhdsWithin hsn).congr_of_eventuallyEq heq
      (heq.self_of_nhdsWithin (extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)))

/-- The homotopy operator is additive on continuous forms, on a `C¹` manifold possibly with
boundary or corners. -/
theorem homotopyOperator_add [IsManifold I 1 M]
    {φ ψ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)}
    (hφ : IsSmoothForm (I.prod (𝓡∂ 1)) 0 φ) (hψ : IsSmoothForm (I.prod (𝓡∂ 1)) 0 ψ) :
    homotopyOperator (φ + ψ) = homotopyOperator φ + homotopyOperator ψ := by
  have : IsManifold I ((0 : ℕ∞) + 1 : WithTop ℕ∞) M := by simpa only [zero_add]
  funext x₀
  obtain ⟨s, hsub, hsu, -, -, hxs, -⟩ :=
    exists_convex_uniqueDiffOn_mem_nhdsWithin_extChartAt (I := I) x₀
  -- At `x₀`, the homotopy operator is the flat cylinder homotopy operator in the chart at `x₀`.
  have key (χ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)) :
      homotopyOperator χ x₀ = cylinderHomotopy (mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1))
        (cylinderChart I x₀) (s ×ˢ Icc 0 1) χ) (extChartAt I x₀ x₀) :=
    (RoughForm.inChartAt_extChartAt_self _ x₀).symm.trans
      (inChartAt_homotopyOperator x₀ hsub hsu χ hxs)
  have hc {χ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)}
      (hχ : IsSmoothForm (I.prod (𝓡∂ 1)) 0 χ) :
      ContinuousOn (Y := (E × ℝ) [⋀^Fin (k + 1)]→L[ℝ] F)
        (mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1)) (cylinderChart I x₀) (s ×ˢ Icc 0 1) χ)
        ({extChartAt I x₀ x₀} ×ˢ Icc (0 : ℝ) 1) :=
    (contDiffOn_mpullbackWithin_cylinder (r := 0) x₀ hsub hsu hχ).continuousOn.mono
      (prod_mono (singleton_subset_iff.2 hxs) subset_rfl)
  rw [Pi.add_apply, key, key, key, mpullbackWithin_add]
  exact cylinderHomotopy_add_apply (hc hφ) (hc hψ)

/-- The homotopy operator commutes with subtraction of continuous forms, on a `C¹` manifold
possibly with boundary or corners. -/
theorem homotopyOperator_sub [IsManifold I 1 M]
    {φ ψ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)}
    (hφ : IsSmoothForm (I.prod (𝓡∂ 1)) 0 φ) (hψ : IsSmoothForm (I.prod (𝓡∂ 1)) 0 ψ) :
    homotopyOperator (φ - ψ) = homotopyOperator φ - homotopyOperator ψ := by
  rw [sub_eq_add_neg, homotopyOperator_add hφ hψ.neg, ← neg_one_smul ℝ ψ, homotopyOperator_smul,
    neg_one_smul, sub_eq_add_neg]

/-- For a continuous form on the cylinder, the integrand of the homotopy operator at a point is
interval integrable: in the chart at that point it is the integrand of the flat cylinder homotopy
operator, which is continuous in time, composed with an invertible chart derivative. -/
private theorem intervalIntegrable_homotopyIntegrand [IsManifold I 1 M]
    {φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)}
    (hφ : IsSmoothForm (I.prod (𝓡∂ 1)) 0 φ) (x₀ : M) :
    IntervalIntegrable (homotopyIntegrand φ x₀) volume 0 1 := by
  have : IsManifold I ((0 : ℕ∞) + 1 : WithTop ℕ∞) M := by simpa only [zero_add]
  obtain ⟨s, hsub, hsu, -, -, hxs, -⟩ :=
    exists_convex_uniqueDiffOn_mem_nhdsWithin_extChartAt (I := I) x₀
  obtain ⟨D, hD⟩ := isInvertible_mfderivWithin_extChartAt_symm (hsub hxs)
  let D' : E ≃L[ℝ] E := D
  let L : (E [⋀^Fin k]→L[ℝ] F) ≃L[ℝ] E [⋀^Fin k]→L[ℝ] F :=
    D'.symm.continuousAlternatingMapCongrLeft
  -- The integrand of the flat cylinder homotopy operator in the chart is interval integrable.
  have h := intervalIntegrable_curryLeft_inl_of_continuousOn
    ((contDiffOn_mpullbackWithin_cylinder (r := 0) x₀ hsub hsu hφ).continuousOn.mono
      (prod_mono (singleton_subset_iff.2 hxs) subset_rfl))
  have hL : IntervalIntegrable (fun t ↦ L.symm ((ContinuousAlternatingMap.curryLeft
      (E := E × ℝ) (mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1)) (cylinderChart I x₀)
        (s ×ˢ Icc 0 1) φ (extChartAt I x₀ x₀, t)) (0, 1)).compContinuousLinearMap
          (.inl ℝ E ℝ))) volume 0 1 :=
    ⟨L.symm.integrable_comp_iff.2 h.1, L.symm.integrable_comp_iff.2 h.2⟩
  refine (intervalIntegrable_congr fun t ht ↦ ?_).mp hL
  rw [uIoc_of_le zero_le_one] at ht
  rw [← continuousAlternatingMapCongrLeft_homotopyIntegrand x₀ hsub hsu φ hxs
    (Ioc_subset_Icc_self ht) (D := D') hD, extChartAt_to_inv]
  exact L.symm_apply_apply _

/-- **Naturality of the homotopy operator** for continuous forms. Pulling a continuous form on
the cylinder, with values in a Banach space, back along `g × id` commutes with the homotopy
operator, for every differentiable map `g`. Unlike `TauCeti.homotopyOperator_mpullback_prodMap_id`,
the derivatives of `g` need not be invertible: `g` may be the inclusion `x ↦ (x, c)` of a slice of
a product, for instance. -/
theorem homotopyOperator_mpullback_prodMap_id_of_isSmoothForm {E' H' M' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I 1 M]
    [CompleteSpace F] {g : M' → M} (hg : MDifferentiable I' I g)
    {φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)}
    (hφ : IsSmoothForm (I.prod (𝓡∂ 1)) 0 φ) :
    homotopyOperator (mpullback (I'.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) (Prod.map g id) φ) =
      mpullback I' I g (homotopyOperator φ) := by
  funext y
  -- Composition with the derivative of `g` at `y`, as a continuous linear map.
  let Dm : E' →L[ℝ] E := mfderiv I' I g y
  let L := ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin k) (F := F) Dm
  -- The values of both forms at `y` are alternating maps on the model space `E'`.
  change @Eq (E' [⋀^Fin k]→L[ℝ] F) _ _
  calc _ = ∫ t in (0 : ℝ)..1, L (homotopyIntegrand φ (g y) t) :=
        intervalIntegral.integral_congr fun t _ ↦ by
          ext v
          exact homotopyIntegrand_mpullback_prodMap_id_apply hg φ y t v
    _ = L (∫ t in (0 : ℝ)..1, homotopyIntegrand φ (g y) t) :=
        L.intervalIntegral_comp_comm (intervalIntegrable_homotopyIntegrand hφ (g y))
    _ = _ := by
        ext v
        exact (mpullback_apply (I := I') (I' := I) g (homotopyOperator φ) y v).symm

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
  obtain ⟨s, hsub, hsu, hconv, hsn, hxs, hxc⟩ :=
    exists_convex_uniqueDiffOn_mem_nhdsWithin_extChartAt (I := I) x₀
  -- The flat pullback of `φ` to the cylinder over `s`, and its cylinder homotopy identity.
  set η := mpullbackWithin 𝓘(ℝ, E × ℝ) (I.prod (𝓡∂ 1)) (cylinderChart I x₀) (s ×ˢ Icc 0 1) φ
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
      exact ⟨fun h ↦ extChartAt_target_subset_range x₀ (hsub h), hy⟩
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

/-! ### Forms vanishing at the ends of the cylinder, and the double cylinder -/

/-- For a `C¹` form `φ` on `M × [0, 1]` with values in a Banach space, on a `C²` manifold possibly
with boundary or corners, whose slices at both ends vanish, the homotopy operator anticommutes with
the exterior derivative: `h (d φ) = -d (h φ)`. -/
theorem homotopyOperator_mextDeriv_of_mpullback_eq_zero [IsManifold I 2 M] [CompleteSpace F]
    {φ : RoughForm (I.prod (𝓡∂ 1)) (M × Icc (0 : ℝ) 1) F (k + 1)}
    (hφ : IsSmoothForm (I.prod (𝓡∂ 1)) 1 φ)
    (h₀ : mpullback I (I.prod (𝓡∂ 1)) (fun x ↦ (x, 0)) φ = 0)
    (h₁ : mpullback I (I.prod (𝓡∂ 1)) (fun x ↦ (x, 1)) φ = 0) :
    homotopyOperator (mextDeriv φ) = -mextDeriv (homotopyOperator φ) := by
  funext x
  have key := mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv hφ x
  rw [h₀, h₁, Pi.zero_apply, sub_zero] at key
  rw [Pi.neg_apply, eq_neg_iff_add_eq_zero]
  exact (add_comm _ _).trans key

/-- **Closed forms on the double cylinder.** Let `η` be a closed `C¹` form, with values in a Banach
space, on the double cylinder `(M × [0, 1]) × [0, 1]` over a `C²` manifold `M` possibly with
boundary or corners, and write `jₛ p = (p, s)` for its slices. If `η` vanishes on every family
starting with the second time vector `∂ₛ` over both ends `M × {0}` and `M × {1}` of the inner
cylinder, then the homotopy operators of the two slices of `η` differ by an exact form:
`h (j₁^* η - j₀^* η) = -d (h (h η))`. -/
theorem homotopyOperator_mpullback_one_sub_mpullback_zero [IsManifold I 2 M] [CompleteSpace F]
    {η : RoughForm ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) ((M × Icc (0 : ℝ) 1) × Icc (0 : ℝ) 1) F
      (k + 2)}
    (hη : IsSmoothForm ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) 1 η) (hclosed : mextDeriv η = 0)
    (h₀ : ∀ (x : M) (s : Icc (0 : ℝ) 1) (v : Fin (k + 1) → (E × EuclideanSpace ℝ (Fin 1)) ×
        EuclideanSpace ℝ (Fin 1)),
      η ((x, 0), s) (Matrix.vecCons ((0 : E × EuclideanSpace ℝ (Fin 1)),
        (1 : TangentSpace (𝓡∂ 1) s)) v) = 0)
    (h₁ : ∀ (x : M) (s : Icc (0 : ℝ) 1) (v : Fin (k + 1) → (E × EuclideanSpace ℝ (Fin 1)) ×
        EuclideanSpace ℝ (Fin 1)),
      η ((x, 1), s) (Matrix.vecCons ((0 : E × EuclideanSpace ℝ (Fin 1)),
        (1 : TangentSpace (𝓡∂ 1) s)) v) = 0) :
    homotopyOperator
        (mpullback (I.prod (𝓡∂ 1)) ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (fun p ↦ (p, 1)) η -
          mpullback (I.prod (𝓡∂ 1)) ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (fun p ↦ (p, 0)) η) =
      -mextDeriv (homotopyOperator (homotopyOperator η)) := by
  have : IsManifold (I.prod (𝓡∂ 1)) ((1 : ℕ∞) + 1 : WithTop ℕ∞) (M × Icc (0 : ℝ) 1) :=
    IsManifold.of_le (n := 2) (by norm_num)
  have : IsManifold (I.prod (𝓡∂ 1)) 1 (M × Icc (0 : ℝ) 1) := IsManifold.of_le (n := 2) (by norm_num)
  -- The inner homotopy operator `β = h η` is a `C¹` form on `M × [0, 1]` with
  -- `d β = j₁^* η - j₀^* η`.
  have hβ : IsSmoothForm (I.prod (𝓡∂ 1)) 1 (homotopyOperator η) :=
    IsSmoothForm.homotopyOperator (r := 1) hη
  have hdβ : mextDeriv (homotopyOperator η) =
      mpullback (I.prod (𝓡∂ 1)) ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (fun p ↦ (p, 1)) η -
        mpullback (I.prod (𝓡∂ 1)) ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (fun p ↦ (p, 0)) η :=
    funext fun p ↦ mextDeriv_homotopyOperator hη hclosed p
  -- Over both ends of the inner cylinder `β` vanishes, since `η` vanishes on `∂ₛ` there; so
  -- `h (d β) = -d (h β)`.
  rw [← hdβ]
  refine homotopyOperator_mextDeriv_of_mpullback_eq_zero hβ ?_ ?_
  · exact funext fun x ↦ mpullback_apply_eq_zero (homotopyOperator_apply_eq_zero (h₀ x))
  · exact funext fun x ↦ mpullback_apply_eq_zero (homotopyOperator_apply_eq_zero (h₁ x))

end TauCeti
