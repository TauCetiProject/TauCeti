/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import TauCeti.Analysis.InnerProductSpace.Euclidean.IntegerPoints
import TauCeti.Analysis.Fourier.Monomial

/-!
# The projection from Euclidean space onto the torus

The projection `π : ℝᵈ → 𝕋ᵈ` (`TauCeti.UnitAddTorus.proj`) reduces each coordinate of a point of
`EuclideanSpace ℝ d` modulo one. It is the map `x ↦ fun i ↦ (x i : UnitAddCircle)` on `d → ℝ` of
`TauCeti.UnitAddTorus.isOpenQuotientMap_coe`, read on the Euclidean space, whose inner product
turns the Fourier modes of the torus into plane waves: `eₙ (π y) = 𝐞 ⟪y, n⟫` for the lattice point
`n ∈ ℤᵈ` (`TauCeti.UnitAddTorus.mFourier_proj`). This is how Fourier multipliers on `ℝᵈ` with
Schwartz kernels are transferred to the torus.

## Main declarations

* `TauCeti.UnitAddTorus.proj`: the projection `ℝᵈ → 𝕋ᵈ`.
* `TauCeti.UnitAddTorus.proj_add`, `TauCeti.UnitAddTorus.continuous_proj`: it is additive and
  continuous.
* `TauCeti.UnitAddTorus.mFourier_proj`: the Fourier modes read on `ℝᵈ` are plane waves.
-/

public section

noncomputable section

open Complex
open scoped Real RealInnerProductSpace FourierTransform

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*}

/-- The projection `π : ℝᵈ → 𝕋ᵈ`, reducing each coordinate modulo one. -/
def proj (v : EuclideanSpace ℝ d) : UnitAddTorus d := fun i ↦ (v i : UnitAddCircle)

@[simp]
theorem proj_apply (v : EuclideanSpace ℝ d) (i : d) : proj v i = (v i : UnitAddCircle) :=
  (rfl)

theorem proj_add (v w : EuclideanSpace ℝ d) : proj (v + w) = proj v + proj w := by
  ext i
  simp

theorem continuous_proj : Continuous (proj (d := d)) :=
  continuous_pi fun i ↦ (AddCircle.continuous_mk' 1).comp (PiLp.continuous_apply 2 _ i)

/-- The Fourier mode `eₙ`, read on `ℝᵈ`, is the plane wave `y ↦ 𝐞 ⟪y, n⟫`. -/
theorem mFourier_proj [Fintype d] (n : d → ℤ) (y : EuclideanSpace ℝ d) :
    mFourier n (proj y) = (𝐞 ⟪y, latticePoint n⟫ : ℂ) := by
  have h := mFourier_coe_apply n (WithLp.ofLp y)
  rw [Real.fourierChar_apply]
  refine h.trans (congrArg cexp ?_)
  simp only [PiLp.inner_apply, latticePoint_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

end TauCeti.UnitAddTorus
