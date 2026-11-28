/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Analysis.InnerProductSpace.Euclidean.Space

/-!
# Skew-Hermitian matrices move points of the complex unit sphere tangentially

A skew-Hermitian matrix `A`, `Aᴴ = -A`, acts on `ℂⁱ` by a skew-adjoint operator, so the
quadratic form `⟪y, A y⟫` has zero real part
(`Matrix.re_inner_toEuclideanCLM_self_eq_zero_of_conjTranspose_eq_neg`). The real inner product
of `ℂⁱ` is the real part of the complex one, so `A y` is real orthogonal to `y`: it is a tangent
vector of the unit sphere at `y`
(`Matrix.exists_mvfderiv_coe_sphere_eq_toEuclideanCLM_of_conjTranspose_eq_neg`).
-/

public section

open Metric
open scoped Manifold InnerProductSpace

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
  [Fact (Module.finrank ℝ (EuclideanSpace ℂ ι) = n + 1)]

/-- For a skew-Hermitian matrix `A`, `Aᴴ = -A`, and a point `y` of the unit sphere of `ℂⁱ`, the
vector `A y` is the image in `ℂⁱ` of a tangent vector of the sphere at `y`: it is real orthogonal
to `y`. -/
theorem exists_mvfderiv_coe_sphere_eq_toEuclideanCLM_of_conjTranspose_eq_neg
    {A : Matrix ι ι ℂ} (hA : Aᴴ = -A) (y : sphere (0 : EuclideanSpace ℂ ι) 1) :
    ∃ u : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) ((↑) : sphere (0 : EuclideanSpace ℂ ι) 1 → EuclideanSpace ℂ ι) y u =
        toEuclideanCLM (𝕜 := ℂ) A y := by
  refine TauCeti.exists_mvfderiv_coe_sphere_eq y ?_
  rw [EuclideanSpace.real_inner_eq_re_inner]
  exact re_inner_toEuclideanCLM_self_eq_zero_of_conjTranspose_eq_neg hA _

end Matrix
