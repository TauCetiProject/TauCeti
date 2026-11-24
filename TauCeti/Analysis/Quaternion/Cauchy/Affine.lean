/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.AffineFace
public import TauCeti.Analysis.Quaternion.Fueter
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Quaternionic Cauchy theorems on affine parallelepipeds

For `A u = p + L u`, the signed cofactor pullback transports a flux field on the
parallelepiped to the parameter cube. This file proves that its boundary flux vanishes
for the ordered field `g * eᵢ * f` when `g` is right Fueter regular and `f` is left
Fueter regular in the interior (`cauchy_affine_cofactor`), and then transfers this via
`ContinuousLinearEquiv.rawAffineBoundary_eq_affineFluxBoundary` to the geometrically parametrized
surface integral `ContinuousLinearMap.rawAffineBoundary` of `g * Dq * f` (`cauchy_affine`).
Taking either function to be `1` gives the left and right Cauchy theorems in both cofactor
and `rawAffineBoundary` forms.

The assumptions are continuity on the closed parallelepiped and pointwise regularity
in its interior, not continuity of the derivative. All integrals are Bochner integrals
on the real coordinate space; no measure on quaternions is introduced. Both the cofactor
pullback and `rawAffineBoundary` carry the parameter orientation of `A`, so these vanishing
statements hold for either orientation of the invertible affine chart.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Proposition 4 and Corollary 8.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979),
  199–225, for the quaternionic Cauchy theorem.

The pointwise version uses Mathlib's divergence theorem through
`ContinuousLinearEquiv.affineFluxBoundary_eq_zero_of_hasFDerivAt`.
-/

public section

open MeasureTheory Set Quaternion

namespace TauCeti

variable (L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)) (p : Fin 4 → ℝ)
  {f g : ℍ → ℍ}

/-- The two-sided Cauchy flux theorem in affine cofactor coordinates. A right regular
coefficient `g` and a left regular coefficient `f` give vanishing signed boundary flux
for `g * eᵢ * f`. Regularity is required only at interior points of the parallelepiped. -/
theorem cauchy_affine_cofactor
    (hg : ContinuousOn g (Quaternion.dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : ContinuousOn f (Quaternion.dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hgr : RightFueterOn g (Quaternion.dq '' ((fun u ↦ p + L u) '' pi univ (fun _ ↦ Ioo 0 1))))
    (hfl : LeftFueterOn f (Quaternion.dq '' ((fun u ↦ p + L u) '' pi univ (fun _ ↦ Ioo 0 1)))) :
    L.affineFluxBoundary p (fun i y ↦
      g (Quaternion.dq y) * Quaternion.dq (Pi.single i 1) * f (Quaternion.dq y)) = 0 := by
  have hgr' u (hu : u ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
      RightFueterAt g (Quaternion.dq (p + L u)) :=
    rightFueterOn_iff.mp hgr _ (mem_image_of_mem _ (mem_image_of_mem _ hu))
  have hfl' u (hu : u ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
      LeftFueterAt f (Quaternion.dq (p + L u)) :=
    leftFueterOn_iff.mp hfl _ (mem_image_of_mem _ (mem_image_of_mem _ hu))
  let G (i : Fin 4) (q : ℍ) :=
    g q * QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i * f q
  have hd u (hu : u ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) i :
      DifferentiableAt ℝ (G i) (Quaternion.dq (p + L u)) :=
    (((hgr' u hu).differentiableAt.mul_const _).mul (hfl' u hu).differentiableAt)
  simp only [Quaternion.dq_single, one_smul]
  refine L.affineFluxBoundary_eq_zero_of_hasFDerivAt p _
    (F' := fun i y ↦ (fderiv ℝ (G i) (Quaternion.dq y)).comp Quaternion.dq) ?_ ?_ ?_
  · intro i
    exact ((hg.comp Quaternion.dq.continuous.continuousOn (mapsTo_image _ _)).mul
      continuousOn_const).mul
      (hf.comp Quaternion.dq.continuous.continuousOn (mapsTo_image _ _))
  · intro u hu i
    exact (hd u hu i).hasFDerivAt.comp (p + L u) Quaternion.dq.hasFDerivAt
  · intro u hu
    refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
      ((hgr' u hu).sum_fderiv_mul_leftFueterAt (hfl' u hu))
    rw [ContinuousLinearMap.comp_apply, Quaternion.dq_single, one_smul]

/-- The left Cauchy theorem on an affine parallelepiped, stated as vanishing cofactor
boundary flux with the ordered coefficients `eᵢ * f`. -/
theorem left_cauchy_affine_cofactor
    (hf : ContinuousOn f (Quaternion.dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hfl : LeftFueterOn f (Quaternion.dq '' ((fun u ↦ p + L u) '' pi univ (fun _ ↦ Ioo 0 1)))) :
    L.affineFluxBoundary p (fun i y ↦
      Quaternion.dq (Pi.single i 1) * f (Quaternion.dq y)) = 0 := by
  simpa only [one_mul] using cauchy_affine_cofactor L p
    (g := fun _ ↦ 1) continuousOn_const hf
    (rightFueterOn_iff.mpr fun _ _ ↦ rightFueterAt_const _ _) hfl

/-- The right Cauchy theorem on an affine parallelepiped, stated as vanishing cofactor
boundary flux with the ordered coefficients `f * eᵢ`. -/
theorem right_cauchy_affine_cofactor
    (hf : ContinuousOn f (Quaternion.dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hfr : RightFueterOn f (Quaternion.dq '' ((fun u ↦ p + L u) '' pi univ (fun _ ↦ Ioo 0 1)))) :
    L.affineFluxBoundary p (fun i y ↦
      f (Quaternion.dq y) * Quaternion.dq (Pi.single i 1)) = 0 := by
  simpa only [mul_one] using cauchy_affine_cofactor L p hf
    (f := fun _ ↦ 1) continuousOn_const hfr
    (leftFueterOn_iff.mpr fun _ _ ↦ leftFueterAt_const _ _)

/-- The two-sided Cauchy theorem on an affine parallelepiped, stated as vanishing of the
geometrically parametrized surface integral `rawAffineBoundary` of `g * Dq * f` for a right
Fueter regular `g` and a left Fueter regular `f`. Both orientations of `L` are allowed. -/
theorem cauchy_affine
    (hg : ContinuousOn g (Quaternion.dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : ContinuousOn f (Quaternion.dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hgr : RightFueterOn g (Quaternion.dq '' ((fun u ↦ p + L u) '' pi univ (fun _ ↦ Ioo 0 1))))
    (hfl : LeftFueterOn f (Quaternion.dq '' ((fun u ↦ p + L u) '' pi univ (fun _ ↦ Ioo 0 1)))) :
    ContinuousLinearMap.rawAffineBoundary L.toContinuousLinearMap p
      (fun x ↦ ContinuousLinearMap.mulLeftRight ℝ ℍ
        (g (Quaternion.dq x)) (f (Quaternion.dq x))) = 0 := by
  rw [L.rawAffineBoundary_eq_affineFluxBoundary]
  simpa only [ContinuousLinearMap.mulLeftRight_apply] using
    cauchy_affine_cofactor L p hg hf hgr hfl

/-- The left Cauchy theorem on an affine parallelepiped, stated as vanishing of the
geometrically parametrized surface integral `rawAffineBoundary` of `Dq * f` for a left
Fueter regular `f`. Both orientations of `L` are allowed. -/
theorem left_cauchy_affine
    (hf : ContinuousOn f (Quaternion.dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hfl : LeftFueterOn f (Quaternion.dq '' ((fun u ↦ p + L u) '' pi univ (fun _ ↦ Ioo 0 1)))) :
    ContinuousLinearMap.rawAffineBoundary L.toContinuousLinearMap p
      (fun x ↦ (ContinuousLinearMap.mul ℝ ℍ).flip (f (Quaternion.dq x))) = 0 := by
  simp_rw [← ContinuousLinearMap.mulLeftRight_one]
  exact cauchy_affine L p (g := fun _ ↦ 1) continuousOn_const hf
    (rightFueterOn_iff.mpr fun _ _ ↦ rightFueterAt_const _ _) hfl

/-- The right Cauchy theorem on an affine parallelepiped, stated as vanishing of the
geometrically parametrized surface integral `rawAffineBoundary` of `f * Dq` for a right
Fueter regular `f`. Both orientations of `L` are allowed. -/
theorem right_cauchy_affine
    (hf : ContinuousOn f (Quaternion.dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hfr : RightFueterOn f (Quaternion.dq '' ((fun u ↦ p + L u) '' pi univ (fun _ ↦ Ioo 0 1)))) :
    ContinuousLinearMap.rawAffineBoundary L.toContinuousLinearMap p
      (fun x ↦ ContinuousLinearMap.mul ℝ ℍ (f (Quaternion.dq x))) = 0 := by
  simp_rw [← ContinuousLinearMap.mulLeftRight_one_right]
  exact cauchy_affine L p hf (f := fun _ ↦ 1) continuousOn_const hfr
    (leftFueterOn_iff.mpr fun _ _ ↦ leftFueterAt_const _ _)

end TauCeti
