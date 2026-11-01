/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Fueter
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Box

/-!
# The quaternionic box Cauchy theorems

The left and right Cauchy theorems assert that the boundary fluxes with ordered coefficients
`eᵢ * f` and `f * eᵢ` vanish for left and right Fueter regular functions, respectively.
Here `eᵢ = dq (Pi.single i 1)` runs through `1, i, j, k`, and `dq` converts real coordinates
in `Fin 4 → ℝ` to quaternions.

The hypotheses are continuity on the closed box and pointwise Fueter regularity in its
open interior. In particular no continuity of the real derivative is assumed. The result
is obtained from Mathlib's Bochner divergence theorem, using the identities expressing the
Fueter operators as the divergences of these ordered fields. The boundary functional is
`boxBoundarySum`, whose front-minus-back signs are the outward flux convention.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  arXiv:0711.2699v5, §2.2, Proposition 4 and Corollary 8. Their statement assumes `C¹`
  regularity; the pointwise version here uses Mathlib's divergence theorem.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Quaternion Set

namespace TauCeti

open Quaternion

/-- The box Cauchy theorem for a left Fueter regular function. The coefficients are ordered
`eᵢ * f`, where `eᵢ` runs through `1, i, j, k`. Only pointwise regularity in the open box and
continuity on the closed box are required, including when the box is degenerate. -/
theorem left_cauchy_box {a b : Fin 4 → ℝ} (hab : a ≤ b) {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : LeftFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i)))) :
    boxBoundarySum a b (fun i x ↦ dq (Pi.single i 1) * f (dq x)) = 0 := by
  have hf := leftFueterOn_iff.mp hf
  let D (i : Fin 4) (x : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℍ :=
    (ContinuousLinearMap.mul ℝ ℍ (dq (Pi.single i 1))).comp
      ((fderiv ℝ f (dq x)).comp dq)
  apply boxBoundarySum_eq_zero_of_hasFDerivAt (D := D) hab
  · intro i
    exact continuousOn_const.mul
      (hc.comp dq.continuous.continuousOn (fun x hx ↦ mem_image_of_mem _ hx))
  · intro x hx i
    exact (ContinuousLinearMap.mul ℝ ℍ (dq (Pi.single i 1))).hasFDerivAt.comp x
      (((hf (dq x) (mem_image_of_mem _ hx)).differentiableAt.hasFDerivAt).comp x
        dq.hasFDerivAt)
  · intro x hx
    simpa only [D, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
      fueterLeft_eq_sum] using (hf (dq x) (mem_image_of_mem _ hx)).fueterLeft_fderiv

/-- The box Cauchy theorem for a right Fueter regular function. The coefficients are ordered
`f * eᵢ`, not `eᵢ * f`. No continuity of the real derivative is required. -/
theorem right_cauchy_box {a b : Fin 4 → ℝ} (hab : a ≤ b) {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : RightFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i)))) :
    boxBoundarySum a b (fun i x ↦ f (dq x) * dq (Pi.single i 1)) = 0 := by
  have hf := rightFueterOn_iff.mp hf
  let D (i : Fin 4) (x : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℍ :=
    ((ContinuousLinearMap.mul ℝ ℍ).flip (dq (Pi.single i 1))).comp
      ((fderiv ℝ f (dq x)).comp dq)
  apply boxBoundarySum_eq_zero_of_hasFDerivAt (D := D) hab
  · intro i
    exact (hc.comp dq.continuous.continuousOn (fun x hx ↦ mem_image_of_mem _ hx)).mul
      continuousOn_const
  · intro x hx i
    exact ((ContinuousLinearMap.mul ℝ ℍ).flip (dq (Pi.single i 1))).hasFDerivAt.comp x
      (((hf (dq x) (mem_image_of_mem _ hx)).differentiableAt.hasFDerivAt).comp x
        dq.hasFDerivAt)
  · intro x hx
    simpa only [D, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply', fueterRight_eq_sum]
      using (hf (dq x) (mem_image_of_mem _ hx)).fueterRight_fderiv

end TauCeti
