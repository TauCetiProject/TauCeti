/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import TauCeti.Analysis.Complex.HasPrimitives.Basic

/-!
# Holomorphic primitives on the upper half-plane

Every holomorphic function on the upper half-plane has a global primitive.  This file gives an
explicit one: `Complex.wedgeIntegral b z f`, the integral along the horizontal-then-vertical
polygonal path from a chosen base point `b` to `z`, deduced by specializing the product-domain
primitive theorems of `TauCeti.Analysis.Complex.HasPrimitives.Basic` to
`upperHalfPlaneSet = univ ×ℂ Ioi 0`.

## Main results

* `Complex.IsConservativeOn.wedgeIntegral_sub_wedgeIntegral_eq_of_mem_upperHalfPlane` -- wedge
  integrals based at an upper-half-plane point are additive.
* `DifferentiableOn.hasDerivAt_wedgeIntegral_upperHalfPlane` -- the explicit wedge integral
  has derivative equal to its integrand.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {f : ℂ → E}

private theorem reProdIm_univ_Ioi_zero : (univ : Set ℝ) ×ℂ Ioi (0 : ℝ) = upperHalfPlaneSet := by
  ext; simp [upperHalfPlaneSet, mem_reProdIm]

omit [CompleteSpace E] in
/-- Wedge integrals based at a point of the upper half-plane are additive along any intermediate
point there.  Equivalently, the integral around the rectangle left between the three wedge paths
vanishes. -/
theorem Complex.IsConservativeOn.wedgeIntegral_sub_wedgeIntegral_eq_of_mem_upperHalfPlane
    (hf : IsConservativeOn f upperHalfPlaneSet) (hcont : ContinuousOn f upperHalfPlaneSet)
    {b z w : ℂ} (hb : b ∈ upperHalfPlaneSet) (hz : z ∈ upperHalfPlaneSet)
    (hw : w ∈ upperHalfPlaneSet) :
    wedgeIntegral b w f - wedgeIntegral b z f = wedgeIntegral z w f :=
  (reProdIm_univ_Ioi_zero.symm ▸ hf).wedgeIntegral_sub_wedgeIntegral_eq_of_mem_reProdIm
    ordConnected_univ ordConnected_Ioi (reProdIm_univ_Ioi_zero.symm ▸ hcont)
    (reProdIm_univ_Ioi_zero ▸ hb) (reProdIm_univ_Ioi_zero ▸ hz) (reProdIm_univ_Ioi_zero ▸ hw)

/-- The wedge integral of a holomorphic function from an upper-half-plane base point has derivative
equal to the function at every point of the upper half-plane. -/
theorem DifferentiableOn.hasDerivAt_wedgeIntegral_upperHalfPlane
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) (b : UpperHalfPlane) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    HasDerivAt (fun w ↦ wedgeIntegral (b : ℂ) w f) (f z) z :=
  (reProdIm_univ_Ioi_zero.symm ▸
      hf.isConservativeOn).hasDerivAt_wedgeIntegral_of_mem_reProdIm
    ordConnected_univ ordConnected_Ioi (reProdIm_univ_Ioi_zero.symm ▸ hf.continuousOn)
    (reProdIm_univ_Ioi_zero ▸ b.coe_im_pos)
    (reProdIm_univ_Ioi_zero ▸ isOpen_upperHalfPlaneSet.mem_nhds hz)
