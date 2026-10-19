/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# Orientations normalized by an invertible derivative

A C¹ map into a normed space whose actual manifold derivative is invertible everywhere
pulls back any orientation of that space. The construction includes boundary and corner points.
-/

public section
noncomputable section

open Bundle Filter Set
open scoped Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {E H M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [FiniteDimensional ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type*} [Fintype ι]

/-- Pull back an orientation by a C¹ map with an everywhere invertible actual derivative.
The model orientation chooses a representative; the tangent orientation is fixed by `o`. -/
def ofMFDerivEquiv {f : M → X} (hf : ContMDiff I 𝓘(ℝ, X) 1 f)
    (F : ∀ x, TangentSpace I x ≃L[ℝ] X)
    (hF : ∀ x, (F x).toContinuousLinearMap =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, X) f x))
    (model : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = Module.finrank ℝ E)
    (o : _root_.Orientation ℝ X ι) : Manifold.Orientation I M ι :=
  ofVectorBundleOrientation model hι
    ⟨fun x ↦ _root_.Orientation.map ι (F x).symm.toLinearEquiv o, fun a ↦ by
      -- Read `F x` as an equivalence onto the tangent space of `X` at `f x`. The trivializations
      -- of that tangent bundle are the identity, so `o` gives a constant family there.
      let T (y : X) := NormedSpace.fromTangentSpace (𝕜 := ℝ) y
      have hconst (y : X)
          (hy : y ∈ (trivializationAt X (TangentSpace 𝓘(ℝ, X)) (f a)).baseSet) :
          (trivializationAt X (TangentSpace 𝓘(ℝ, X)) (f a)).mapOrientation ι hy
            (_root_.Orientation.map ι (T y).symm.toLinearEquiv o) = o := by
        rw [Trivialization.mapOrientation_apply, ← _root_.Orientation.map_trans]
        have hid : (T y).symm.toLinearEquiv.trans
            ((trivializationAt X (TangentSpace 𝓘(ℝ, X)) (f a)).linearEquivAt ℝ y hy) =
              LinearEquiv.refl ℝ X :=
          LinearEquiv.ext fun v ↦ by
            simp only [LinearEquiv.trans_apply, Trivialization.linearEquivAt_apply,
              trivializationAt_model_space_apply, LinearEquiv.refl_apply]
            -- `NormedSpace.fromTangentSpace` is the identity by definition.
            rfl
        rw [hid, _root_.Orientation.map_refl, Equiv.refl_apply]
      have hred (x : M) : _root_.Orientation.map ι ((F x).trans (T (f x)).symm).symm.toLinearEquiv
          (_root_.Orientation.map ι (T (f x)).symm.toLinearEquiv o) =
            _root_.Orientation.map ι (F x).symm.toLinearEquiv o := by
        rw [← _root_.Orientation.map_trans]
        exact congrArg (fun L ↦ _root_.Orientation.map ι L o)
          (LinearEquiv.ext fun v ↦ by simp)
      have h := eventually_mapOrientation_map_symm_eq hf (fun x ↦ (F x).trans (T (f x)).symm)
        (fun x ↦ by
          ext v
          have hv := congrArg (fun L : TangentSpace I x →L[ℝ] X ↦ L v) (hF x)
          simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.coe_comp,
            Function.comp_apply] at hv
          simp [T, hv])
        hι (fun x ↦ _root_.Orientation.map ι (T (f x)).symm.toLinearEquiv o) a
        (Eventually.of_forall fun x hx ↦ by rw [hconst, hconst])
      simpa only [hred] using h⟩

/-- The derivative sends the induced tangent orientation to the chosen target orientation,
including at boundary and corner points. -/
@[simp]
theorem map_orientationAt_ofMFDerivEquiv {f : M → X} (hf : ContMDiff I 𝓘(ℝ, X) 1 f)
    (F : ∀ x, TangentSpace I x ≃L[ℝ] X)
    (hF : ∀ x, (F x).toContinuousLinearMap =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, X) f x))
    (model : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = Module.finrank ℝ E)
    (o : _root_.Orientation ℝ X ι) (x : M) :
    _root_.Orientation.map ι (F x).toLinearEquiv
      ((ofMFDerivEquiv hf F hF model hι o).orientationAt x) = o := by
  simp only [ofMFDerivEquiv, orientationAt_ofVectorBundleOrientation,
    VectorBundleOrientation.coe_mk]
  rw [← _root_.Orientation.map_trans]
  simp

end TauCeti.Manifold.Orientation
