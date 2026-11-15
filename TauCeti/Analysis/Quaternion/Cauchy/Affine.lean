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
`ContinuousLinearEquiv.rawAffineBoundary_eq_cofactor` to the geometrically parametrized
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
`ContinuousLinearEquiv.integral_divergence_affineFluxPullback`.
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
    (hg : ContinuousOn (fun x ↦ g (Quaternion.dq x))
      ((fun u ↦ p + L u) '' Icc 0 1))
    (hf : ContinuousOn (fun x ↦ f (Quaternion.dq x))
      ((fun u ↦ p + L u) '' Icc 0 1))
    (hgr : ∀ u ∈ univ.pi (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1),
      RightFueterAt g (Quaternion.dq (p + L u)))
    (hfl : ∀ u ∈ univ.pi (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1),
      LeftFueterAt f (Quaternion.dq (p + L u))) :
    ∑ j : Fin 4,
      ((∫ x in Icc (0 : Fin 3 → ℝ) 1,
          L.affineFluxPullback p (fun i y ↦ g (Quaternion.dq y) *
            QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i * f (Quaternion.dq y)) j
            (j.insertNth 1 x)) -
        ∫ x in Icc (0 : Fin 3 → ℝ) 1,
          L.affineFluxPullback p (fun i y ↦ g (Quaternion.dq y) *
            QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i * f (Quaternion.dq y)) j
            (j.insertNth 0 x)) = 0 := by
  let F : Fin 4 → (Fin 4 → ℝ) → ℍ := fun i y ↦ g (Quaternion.dq y) *
    QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i * f (Quaternion.dq y)
  let F' := fun i y ↦ fderiv ℝ (F i) y
  have hd u (hu : u ∈ univ.pi (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) i :
      DifferentiableAt ℝ (F i) (p + L u) :=
    (((hgr u hu).differentiableAt.comp _ Quaternion.dq.differentiableAt).mul_const _).mul
      ((hfl u hu).differentiableAt.comp _ Quaternion.dq.differentiableAt)
  -- Transport the ordered quaternionic divergence identity to the tuple coordinates.
  have hdiv u (hu : u ∈ univ.pi (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
      ∑ i, F' i (p + L u) (Pi.single i 1) = 0 := by
    have hcomp i :=
      ((((hgr u hu).differentiableAt.mul_const
        (QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i)).mul
          (hfl u hu).differentiableAt).hasFDerivAt.comp (p + L u)
            Quaternion.dq.hasFDerivAt).fderiv
    simp only [Function.comp_def, Pi.mul_def] at hcomp
    simpa only [F', F, hcomp, ContinuousLinearMap.comp_apply,
      Quaternion.dq_single, one_smul] using
      (hgr u hu).sum_fderiv_mul_leftFueterAt (hfl u hu)
  -- The open and closed cubes agree almost everywhere, so no boundary derivatives
  -- or integrability assumption on the (possibly discontinuous) derivative are needed.
  have hae : (fun u ↦ ∑ i, F' i (p + L u) (Pi.single i 1)) =ᵐ[
      volume.restrict (Icc (0 : Fin 4 → ℝ) 1)] 0 := by
    rw [volume_pi, ← Measure.restrict_congr_set Measure.univ_pi_Ioo_ae_eq_Icc]
    exact (ae_restrict_mem (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo)).mono
      fun u hu ↦ hdiv u hu
  have h := L.integral_divergence_affineFluxPullback p F F' ∅ countable_empty
    (fun i ↦ (hg.mul continuousOn_const).mul hf)
    (fun u hu i ↦ (hd u hu.1 i).hasFDerivAt)
    ((integrable_zero _ _ _).congr hae.symm)
  rw [integral_congr_ae hae] at h
  simpa only [Pi.zero_apply, integral_zero, smul_zero] using h.symm

/-- The left Cauchy theorem on an affine parallelepiped, stated as vanishing cofactor
boundary flux with the ordered coefficients `eᵢ * f`. -/
theorem left_cauchy_affine_cofactor
    (hf : ContinuousOn (fun x ↦ f (Quaternion.dq x))
      ((fun u ↦ p + L u) '' Icc 0 1))
    (hfl : ∀ u ∈ univ.pi (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1),
      LeftFueterAt f (Quaternion.dq (p + L u))) :
    ∑ j : Fin 4,
      ((∫ x in Icc (0 : Fin 3 → ℝ) 1,
          L.affineFluxPullback p (fun i y ↦
            QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i * f (Quaternion.dq y)) j
            (j.insertNth 1 x)) -
        ∫ x in Icc (0 : Fin 3 → ℝ) 1,
          L.affineFluxPullback p (fun i y ↦
            QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i * f (Quaternion.dq y)) j
            (j.insertNth 0 x)) = 0 := by
  simpa only [one_mul] using cauchy_affine_cofactor L p
    (g := fun _ ↦ 1) continuousOn_const hf (fun _ _ ↦ rightFueterAt_const _ _) hfl

/-- The right Cauchy theorem on an affine parallelepiped, stated as vanishing cofactor
boundary flux with the ordered coefficients `f * eᵢ`. -/
theorem right_cauchy_affine_cofactor
    (hf : ContinuousOn (fun x ↦ f (Quaternion.dq x))
      ((fun u ↦ p + L u) '' Icc 0 1))
    (hfr : ∀ u ∈ univ.pi (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1),
      RightFueterAt f (Quaternion.dq (p + L u))) :
    ∑ j : Fin 4,
      ((∫ x in Icc (0 : Fin 3 → ℝ) 1,
          L.affineFluxPullback p (fun i y ↦ f (Quaternion.dq y) *
            QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i) j (j.insertNth 1 x)) -
        ∫ x in Icc (0 : Fin 3 → ℝ) 1,
          L.affineFluxPullback p (fun i y ↦ f (Quaternion.dq y) *
            QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i) j (j.insertNth 0 x)) = 0 := by
  simpa only [mul_one] using cauchy_affine_cofactor L p hf
    (f := fun _ ↦ 1) continuousOn_const hfr (fun _ _ ↦ leftFueterAt_const _ _)

/-- The two-sided Cauchy theorem on an affine parallelepiped, stated as vanishing of the
geometrically parametrized surface integral `rawAffineBoundary` of `g * Dq * f` for a right
Fueter regular `g` and a left Fueter regular `f`. Both orientations of `L` are allowed. -/
theorem cauchy_affine
    (hg : ContinuousOn (fun x ↦ g (Quaternion.dq x))
      ((fun u ↦ p + L u) '' Icc 0 1))
    (hf : ContinuousOn (fun x ↦ f (Quaternion.dq x))
      ((fun u ↦ p + L u) '' Icc 0 1))
    (hgr : ∀ u ∈ univ.pi (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1),
      RightFueterAt g (Quaternion.dq (p + L u)))
    (hfl : ∀ u ∈ univ.pi (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1),
      LeftFueterAt f (Quaternion.dq (p + L u))) :
    ContinuousLinearMap.rawAffineBoundary L.toContinuousLinearMap p
      (fun x ↦ ContinuousLinearMap.mulLeftRight ℝ ℍ
        (g (Quaternion.dq x)) (f (Quaternion.dq x))) = 0 := by
  rw [L.rawAffineBoundary_eq_cofactor]
  simpa only [ContinuousLinearMap.mulLeftRight_apply, Quaternion.dq_single, one_smul] using
    cauchy_affine_cofactor L p hg hf hgr hfl

/-- The left Cauchy theorem on an affine parallelepiped, stated as vanishing of the
geometrically parametrized surface integral `rawAffineBoundary` of `Dq * f` for a left
Fueter regular `f`. Both orientations of `L` are allowed. -/
theorem left_cauchy_affine
    (hf : ContinuousOn (fun x ↦ f (Quaternion.dq x))
      ((fun u ↦ p + L u) '' Icc 0 1))
    (hfl : ∀ u ∈ univ.pi (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1),
      LeftFueterAt f (Quaternion.dq (p + L u))) :
    ContinuousLinearMap.rawAffineBoundary L.toContinuousLinearMap p
      (fun x ↦ (ContinuousLinearMap.mul ℝ ℍ).flip (f (Quaternion.dq x))) = 0 := by
  have hmul : (fun x ↦ (ContinuousLinearMap.mul ℝ ℍ).flip (f (Quaternion.dq x))) =
      fun x ↦ ContinuousLinearMap.mulLeftRight ℝ ℍ 1 (f (Quaternion.dq x)) :=
    funext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp
  rw [hmul]
  exact cauchy_affine L p (g := fun _ ↦ 1) continuousOn_const hf
    (fun _ _ ↦ rightFueterAt_const _ _) hfl

/-- The right Cauchy theorem on an affine parallelepiped, stated as vanishing of the
geometrically parametrized surface integral `rawAffineBoundary` of `f * Dq` for a right
Fueter regular `f`. Both orientations of `L` are allowed. -/
theorem right_cauchy_affine
    (hf : ContinuousOn (fun x ↦ f (Quaternion.dq x))
      ((fun u ↦ p + L u) '' Icc 0 1))
    (hfr : ∀ u ∈ univ.pi (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1),
      RightFueterAt f (Quaternion.dq (p + L u))) :
    ContinuousLinearMap.rawAffineBoundary L.toContinuousLinearMap p
      (fun x ↦ ContinuousLinearMap.mul ℝ ℍ (f (Quaternion.dq x))) = 0 := by
  have hmul : (fun x ↦ ContinuousLinearMap.mul ℝ ℍ (f (Quaternion.dq x))) =
      fun x ↦ ContinuousLinearMap.mulLeftRight ℝ ℍ (f (Quaternion.dq x)) 1 :=
    funext fun _ ↦ ContinuousLinearMap.ext fun _ ↦ by simp
  rw [hmul]
  exact cauchy_affine L p hf (f := fun _ ↦ 1) continuousOn_const hfr
    (fun _ _ ↦ leftFueterAt_const _ _)

end TauCeti
