/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Fueter
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Box
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The quaternionic box Cauchy theorems

The left and right Cauchy theorems assert that the boundary fluxes with ordered coefficients
`eᵢ * f` and `f * eᵢ` vanish for left and right Fueter regular functions, respectively.
Here `eᵢ = dq (Pi.single i 1)` runs through `1, i, j, k`, and `dq` converts real coordinates
in `Fin 4 → ℝ` to quaternions.

More generally, `cauchy_box` gives zero flux for the ordered coefficients `g * eᵢ * f`
when `g` is right regular and `f` is left regular.

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

/-- The two-sided box Cauchy theorem: the ordered field `g * eᵢ * f` has zero boundary
flux when `g` is right Fueter regular and `f` is left Fueter regular in the open box.
Only continuity on the closed box and pointwise regularity in its interior are required. -/
theorem cauchy_box {a b : Fin 4 → ℝ} (hab : a ≤ b) {f g : ℍ → ℍ}
    (hg : ContinuousOn g (dq '' Icc a b)) (hf : ContinuousOn f (dq '' Icc a b))
    (hgr : RightFueterOn g (dq '' pi univ (fun i ↦ Ioo (a i) (b i))))
    (hfl : LeftFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i)))) :
    boxBoundarySum a b (fun i x ↦ g (dq x) * dq (Pi.single i 1) * f (dq x)) = 0 := by
  have hgr := rightFueterOn_iff.mp hgr
  have hfl := leftFueterOn_iff.mp hfl
  let F (i : Fin 4) (q : ℍ) :=
    g q * QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i * f q
  have hd x (hx : x ∈ pi univ (fun i ↦ Ioo (a i) (b i))) i :
      DifferentiableAt ℝ (F i) (dq x) :=
    (((hgr _ (mem_image_of_mem _ hx)).differentiableAt.mul_const _).mul
      (hfl _ (mem_image_of_mem _ hx)).differentiableAt)
  simp only [dq_single, one_smul]
  apply boxBoundarySum_eq_zero_of_hasFDerivAt
    (D := fun i x ↦ (fderiv ℝ (F i) (dq x)).comp dq) hab
  · intro i
    exact ((hg.comp dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx)).mul
      continuousOn_const).mul
        (hf.comp dq.continuous.continuousOn (fun _ hx ↦ mem_image_of_mem _ hx))
  · intro x hx i
    exact (hd x hx i).hasFDerivAt.comp x dq.hasFDerivAt
  · intro x hx
    have hsum := (hgr _ (mem_image_of_mem _ hx)).sum_fderiv_mul_leftFueterAt
      (hfl _ (mem_image_of_mem _ hx))
    apply Eq.trans _ hsum
    apply Finset.sum_congr rfl
    intro i hi
    rw [ContinuousLinearMap.comp_apply, dq_single, one_smul]

/-- The box Cauchy theorem for a left Fueter regular function. The coefficients are ordered
`eᵢ * f`, where `eᵢ` runs through `1, i, j, k`. Only pointwise regularity in the open box and
continuity on the closed box are required, including when the box is degenerate. -/
theorem left_cauchy_box {a b : Fin 4 → ℝ} (hab : a ≤ b) {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : LeftFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i)))) :
    boxBoundarySum a b (fun i x ↦ dq (Pi.single i 1) * f (dq x)) = 0 := by
  simpa only [one_mul] using cauchy_box hab (g := fun _ ↦ 1) continuousOn_const hc
    (rightFueterOn_iff.mpr fun _ _ ↦ rightFueterAt_const _ _) hf

/-- The box Cauchy theorem for a right Fueter regular function. The coefficients are ordered
`f * eᵢ`, not `eᵢ * f`. No continuity of the real derivative is required. -/
theorem right_cauchy_box {a b : Fin 4 → ℝ} (hab : a ≤ b) {f : ℍ → ℍ}
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : RightFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i)))) :
    boxBoundarySum a b (fun i x ↦ f (dq x) * dq (Pi.single i 1)) = 0 := by
  simpa only [mul_one] using cauchy_box hab hc (f := fun _ ↦ 1) continuousOn_const hf
    (leftFueterOn_iff.mpr fun _ _ ↦ leftFueterAt_const _ _)

end TauCeti
