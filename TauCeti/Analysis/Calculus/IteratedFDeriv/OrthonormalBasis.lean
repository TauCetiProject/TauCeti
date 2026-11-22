/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear

/-!
# Iterated derivatives of directional derivatives in an orthonormal basis

The derivatives of the coordinate `x ↦ (b.repr (Dg(x) v))ᵢ` of a directional derivative in an
orthonormal basis `b` are bounded by those of `g` of one order higher. These coordinates are the
coefficients of the chain rule for composition with `g`, and the bound feeds the Sobolev estimates
for changes of variables.

Conversely, the Hessian entries `D²u(x) (b i) (b j)` on vectors of an orthonormal basis are bounded
by `‖D²u(x)‖`, the second-order counterpart of `ContinuousLinearMap.unit_le_opNorm` for the partial
derivatives `Du(x) (b i)`. For the standard basis of `EuclideanSpace`, this turns a norm bound on
the second derivative into bounds on the second coordinate partial derivatives.

## Main declarations

* `TauCeti.norm_fderiv_fderiv_apply_orthonormalBasis_le`: `‖D²u(x) (b i) (b j)‖ ≤ ‖D²u(x)‖`.
* `ContDiff.norm_iteratedFDeriv_basis_repr_fderiv_apply_le`: the derivatives of the chain-rule
  coefficient `x ↦ (b.repr (Dg(x) v))ᵢ` in an orthonormal basis are bounded by those of `g`.
-/

public section

/-- The derivatives of the coordinate `x ↦ (b.repr (Dg(x) v))ᵢ` of a directional derivative in an
orthonormal basis `b`, the coefficient of the chain rule for composition with `g`, are bounded by
those of `g`: `‖Dⁿ (x ↦ (b.repr (Dg(x) v))ᵢ)(x)‖ ≤ ‖D^{n+1} g(x)‖ ‖v‖`. -/
theorem ContDiff.norm_iteratedFDeriv_basis_repr_fderiv_apply_le {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fintype ι] {g : E → F} {N : WithTop ℕ∞} (hg : ContDiff ℝ N g) {n : ℕ} (hn : n + 1 ≤ N)
    (b : OrthonormalBasis ι ℝ F) (v : E) (i : ι) (x : E) :
    ‖iteratedFDeriv ℝ n (fun x ↦ ((b.toBasis.repr (fderiv ℝ g x v) i : ℝ) : ℂ)) x‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) g x‖ * ‖v‖ := by
  set A : F →L[ℝ] ℂ := Complex.ofRealCLM.comp (innerSL ℝ (b i))
  have hA : ‖A‖ ≤ 1 := by
    refine A.opNorm_le_bound zero_le_one fun y ↦ ?_
    simpa [A, b.orthonormal.1 i] using norm_inner_le_norm (𝕜 := ℝ) (b i) y
  have hfun : (fun x ↦ ((b.toBasis.repr (fderiv ℝ g x v) i : ℝ) : ℂ)) =
      A ∘ fun x ↦ fderiv ℝ g x v := by
    ext x
    simp [A, b.repr_apply_apply]
  have hd : ContDiff ℝ n (fun x ↦ fderiv ℝ g x v) :=
    (hg.fderiv_right (mod_cast hn)).clm_apply contDiff_const
  rw [hfun]
  refine (A.norm_iteratedFDeriv_comp_left hd.contDiffAt le_rfl).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg _) hA).trans ?_
  exact hg.norm_iteratedFDeriv_fderiv_apply_le (by simpa using hn) v x

namespace TauCeti

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Fintype ι]

/-- The Hessian entry `D²u(x) (b i) (b j)` of `u` on vectors of an orthonormal basis `b` has norm at
most `‖D²u(x)‖`. -/
theorem norm_fderiv_fderiv_apply_orthonormalBasis_le (u : E → F)
    (b : OrthonormalBasis ι 𝕜 E) (i j : ι) (x : E) :
    ‖fderiv 𝕜 (fderiv 𝕜 u) x (b i) (b j)‖ ≤ ‖iteratedFDeriv 𝕜 2 u x‖ := by
  simpa [iteratedFDeriv_two_apply] using
    (iteratedFDeriv 𝕜 2 u x).norm_apply_orthonormalBasis_le b i j

end TauCeti
