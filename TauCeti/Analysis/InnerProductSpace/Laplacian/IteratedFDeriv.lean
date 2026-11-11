/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The Laplacian commutes with differentiation

Let `E` be a finite-dimensional real inner product space and `f : E → F` a map into a real normed
space. The Laplacian `Δ` is defined for vector-valued maps, so it applies to the derivative
`fderiv ℝ f : E → E →L[ℝ] F` and to the iterated derivatives `iteratedFDeriv ℝ n f`. This file
proves that it commutes with them:

* `ContDiffAt.laplacian_fderiv`: if `f` is `C³` at `x`, then `Δ (fderiv f) x = fderiv (Δ f) x`;
* `ContDiff.laplacian_iteratedFDeriv`: if `f` is `C^(n+2)`, then
  `Δ (iteratedFDeriv n f) = iteratedFDeriv n (Δ f)`.

In an orthonormal basis `(eᵢ)` the first identity reads
`∑ᵢ D³f(x)(eᵢ, eᵢ, h) = ∑ᵢ D³f(x)(h, eᵢ, eᵢ)`,
which holds term by term because the third derivative of a `C³` map is symmetric. The second
follows by induction, since `iteratedFDeriv (n + 1) f` is `fderiv (iteratedFDeriv n f)` up to a
linear isometry, which commutes with `Δ`.

These identities let one differentiate a semilinear elliptic equation `Δ u = F(u)`: the derivatives
of `u` solve the differentiated equations, to which maximum principles and comparison arguments
apply.
-/

public section

noncomputable section

open InnerProductSpace Laplacian

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Laplacian commutes with left composition by a linear isometry equivalence. -/
private theorem laplacian_linearIsometryEquiv_comp {G H : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G ≃ₗᵢ[ℝ] H) (g : E → G) :
    Δ (L ∘ g) = L ∘ Δ g := by
  have h := laplacian_CLE_comp_left (f := g) (l := L.toContinuousLinearEquiv)
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] at h
  exact h

/-- In an orthonormal basis the Laplacian is the trace of the second derivative. -/
private theorem laplacian_eq_sum_fderiv_fderiv {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (g : E → G) (x : E) :
    Δ g x = ∑ i, fderiv ℝ (fderiv ℝ g) x (stdOrthonormalBasis ℝ E i)
      (stdOrthonormalBasis ℝ E i) := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply]

/-- **The Laplacian commutes with the derivative.** If `f` is `C³` at `x`, then the Laplacian of
the derivative field `fderiv ℝ f : E → E →L[ℝ] F` at `x` is the derivative of `Δ f` at `x`. -/
theorem ContDiffAt.laplacian_fderiv {f : E → F} {x : E} (hf : ContDiffAt ℝ 3 f x) :
    Δ (fderiv ℝ f) x = fderiv ℝ (Δ f) x := by
  set v := stdOrthonormalBasis ℝ E
  have hD2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hterm (i : _) : DifferentiableAt ℝ (fun y ↦ fderiv ℝ (fderiv ℝ f) y (v i) (v i)) x :=
    (hD2.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  have hsymm := (hf.fderiv_right (m := 2) (by norm_num)).isSymmSndFDerivAt
    (by norm_num [minSmoothness_of_isRCLikeNormedField])
  ext h
  rw [laplacian_eq_sum_fderiv_fderiv, funext (laplacian_eq_sum_fderiv_fderiv f),
    fderiv_fun_sum fun i _ ↦ hterm i, sum_apply, sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- `D³f(x)(eᵢ, eᵢ, h) = D³f(x)(eᵢ, h, eᵢ) = D³f(x)(h, eᵢ, eᵢ)`.
  rw [TauCeti.fderiv_clm_apply_const_apply₂ hD2, TauCeti.fderiv_fderiv_fderiv_apply_comm hf
    (by norm_num [minSmoothness_of_isRCLikeNormedField]) (v i) (v i) h, hsymm (v i) h]

/-- **The Laplacian commutes with the iterated derivatives.** For a `C^(n+2)` map `f`, the
Laplacian of the field `iteratedFDeriv ℝ n f` of continuous multilinear maps is
`iteratedFDeriv ℝ n (Δ f)`. -/
theorem ContDiff.laplacian_iteratedFDeriv {f : E → F} {n : ℕ} (hf : ContDiff ℝ (n + 2) f) :
    Δ (iteratedFDeriv ℝ n f) = iteratedFDeriv ℝ n (Δ f) := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp,
      laplacian_linearIsometryEquiv_comp]
  | succ n ih =>
    have h3 : ContDiff ℝ 3 (iteratedFDeriv ℝ n f) :=
      hf.iteratedFDeriv_right (by norm_cast; omega)
    have hL := laplacian_linearIsometryEquiv_comp
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) F).symm
      (fderiv ℝ (iteratedFDeriv ℝ n f))
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, hL,
      funext fun x ↦ (h3.contDiffAt (x := x)).laplacian_fderiv,
      ih (hf.of_le (by norm_cast; omega))]
