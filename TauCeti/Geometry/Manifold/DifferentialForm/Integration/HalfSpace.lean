/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.HalfSpace
public import TauCeti.Geometry.Manifold.Boundary.Model
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Stokes' theorem on the standard manifold half-space

The volume normalization is the standard Euclidean volume in both dimensions. The negative
boundary coefficient is precisely the outward-first orientation determined by `-e₀`, as
identified by `TauCeti.orientationAt_boundaryOrientation_model` in `Boundary.InducedOrientation`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti

/-- Stokes on the standard half-space, including integrability of the actual exterior derivative
and the boundary restriction. Only regularity on the closed half-space is required. -/
theorem _root_.ContDiffOn.integral_extDerivWithin_euclideanHalfSpace {n : ℕ}
    {ω : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin n]→L[ℝ] ℝ}
    (hω : ContDiffOn ℝ 1 ω (range (𝓡∂ (n + 1)))) (hc : HasCompactSupport ω) :
    IntegrableOn (fun x ↦ extDerivWithin ω (range (𝓡∂ (n + 1))) x
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)) (range (𝓡∂ (n + 1))) ∧
    Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦
      ω (euclideanHalfSpaceBoundaryParam n y)
        (fun i ↦ euclideanHalfSpaceBoundaryParam n (EuclideanSpace.basisFun (Fin n) ℝ i))) ∧
    (∫ x in range (𝓡∂ (n + 1)), extDerivWithin ω (range (𝓡∂ (n + 1))) x
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)) =
    -(∫ y : EuclideanSpace ℝ (Fin n), ω (euclideanHalfSpaceBoundaryParam n y)
      (fun i ↦ euclideanHalfSpaceBoundaryParam n (EuclideanSpace.basisFun (Fin n) ℝ i))) := by
  let L := (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
  let B := (EuclideanSpace.equiv (Fin n) ℝ).symm
  let C := ContinuousAlternatingMap.compContinuousLinearMapCLM (F := ℝ) (ι := Fin n)
    L.toContinuousLinearMap
  let η := C ∘ ω ∘ L
  let H : Set (Fin (n + 1) → ℝ) := {x | 0 ≤ x 0}
  let T := range (𝓡∂ (n + 1))
  have hmap : MapsTo L H T := by
    intro x hx
    simpa [T, H, L, range_modelWithCornersEuclideanHalfSpace] using hx
  have hη : ContDiffOn ℝ 1 η H := C.contDiff.comp_contDiffOn
    (hω.comp L.contDiff.contDiffOn hmap)
  have hcη : HasCompactSupport η := (hc.comp_homeomorph L.toHomeomorph).comp_left C.map_zero
  have hr := ContDiffOn.integral_extDerivWithin_coordinate_halfSpace hη hcη
  have hd (x) (hx : x ∈ H) :
      extDerivWithin η H x (Pi.basisFun ℝ (Fin (n + 1))) =
      extDerivWithin ω T (L x) (EuclideanSpace.basisFun (Fin (n + 1)) ℝ) := by
    exact congrArg (fun a ↦ a (Pi.basisFun ℝ (Fin (n + 1))))
      (L.toContinuousLinearMap.extDerivWithin_pullback
        (uniqueDiffOn_pi_halfSpace 0 0 x hx)
        ((hω.differentiableOn one_ne_zero) (L x) (hmap hx)) hmap)
  have hparam (y : Fin n → ℝ) : L (Fin.cons 0 y) = euclideanHalfSpaceBoundaryParam n (B y) := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [L, B]
  have hb (y : Fin n → ℝ) : η (Fin.cons 0 y) (fun i ↦ Pi.single i.succ 1) =
      ω (euclideanHalfSpaceBoundaryParam n (B y))
        (fun i ↦ euclideanHalfSpaceBoundaryParam n (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
    -- Expose the boundary tuple after converting from alternating-map pullback to evaluation.
    change ω (L (Fin.cons 0 y)) (fun i ↦ L (Pi.single i.succ 1)) = _
    rw [hparam]
    congr 1
    funext i
    ext j
    refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp [L, EuclideanSpace.basisFun_apply]
  have hTm : MeasurableSet T := by
    dsimp only [T]
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact isClosed_le continuous_const (EuclideanSpace.proj 0).continuous |>.measurableSet
  have hHm : MeasurableSet H :=
    isClosed_le continuous_const (continuous_apply 0) |>.measurableSet
  have hp := (PiLp.volume_preserving_toLp (Fin (n + 1))).restrict_preimage hTm
  have hpre : WithLp.toLp 2 ⁻¹' T = H := by
    ext x
    simp [T, H, range_modelWithCornersEuclideanHalfSpace]
  rw [hpre] at hp
  have hpb := PiLp.volume_preserving_toLp (Fin n)
  have he := L.toHomeomorph.measurableEmbedding
  have heb := B.toHomeomorph.measurableEmbedding
  let d (x : EuclideanSpace ℝ (Fin (n + 1))) :=
    extDerivWithin ω T x (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)
  let b (y : EuclideanSpace ℝ (Fin n)) := ω (euclideanHalfSpaceBoundaryParam n y)
    (fun i ↦ euclideanHalfSpaceBoundaryParam n (EuclideanSpace.basisFun (Fin n) ℝ i))
  have hint := (hp.integrable_comp_emb he (g := d)).mp (hr.1.congr_fun hd hHm)
  have hintb := (hpb.integrable_comp_emb heb (g := b)).mp (hr.2.1.congr (by
    filter_upwards [] with y using hb y))
  refine ⟨hint, hintb, ?_⟩
  -- Expand the local scalar coefficients while keeping the half-space set T fixed.
  change (∫ x in T, d x) = -(∫ y, b y)
  rw [← hp.integral_comp he d, ← hpb.integral_comp heb b]
  calc
    _ = ∫ x in H, extDerivWithin η H x (Pi.basisFun ℝ (Fin (n + 1))) :=
      setIntegral_congr_fun hHm (fun x hx ↦ (hd x hx).symm)
    _ = _ := hr.2.2
    _ = _ := by simp_rw [hb]; rfl

end TauCeti
