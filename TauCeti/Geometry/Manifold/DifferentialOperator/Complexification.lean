/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
public import TauCeti.RingTheory.Derivation.DifferentialOperator

/-!
# Complexification of differential operators on manifolds

For a real manifold `N`, the complexification `ContMDiffMap.complexifyLinearMap D` of a real-linear
operator `D` on the real-valued `C^r` functions acts on complex-valued functions by `D` on real
and imaginary parts. This file relates it to differential operators in Grothendieck's sense of
iterated commutators with multiplication operators (`TauCeti.differentialOperators`).

## Main results

* `TauCeti.smulCommutator_ofReal_complexifyLinearMap`: complexification commutes with commutators
  with multiplication by real-valued functions;
  `TauCeti.smulCommutator_ofReal_pow_complexifyLinearMap` is the iterated form.
* `TauCeti.re_comp_restrictScalars_comp_ofReal_mem_differentialOperators`,
  `TauCeti.im_comp_restrictScalars_comp_ofReal_mem_differentialOperators`: for a complex
  differential operator `Q` of order at most `m` on the complex-valued functions, the real and
  imaginary parts `u ↦ Re (Q u)` and `u ↦ Im (Q u)` on real-valued functions are real
  differential operators of order at most `m`.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} {N : Type*} [TopologicalSpace N] [ChartedSpace HM N] {r : ℕ∞ω}

/-- **Commutators with real functions commute with complexification.** The commutator of the
complexification of `D` with multiplication by a real-valued smooth function `f`, viewed as a
complex-valued function, is the complexification of the commutator of `D` with `f`. -/
@[simp]
theorem smulCommutator_ofReal_complexifyLinearMap (f : C^r⟮I, N; ℝ⟯)
    (D : C^r⟮I, N; ℝ⟯ →ₗ[ℝ] C^r⟮I, N; ℝ⟯) :
    smulCommutator ℂ (ContMDiffMap.ofReal f) (ContMDiffMap.complexifyLinearMap D) =
      ContMDiffMap.complexifyLinearMap (smulCommutator ℝ f D) := by
  ext u x
  apply Complex.ext <;> simp [ContMDiffMap.mul_re, ContMDiffMap.mul_im]

/-- The iterated form of `TauCeti.smulCommutator_ofReal_complexifyLinearMap`. -/
@[simp]
theorem smulCommutator_ofReal_pow_complexifyLinearMap (f : C^r⟮I, N; ℝ⟯)
    (D : C^r⟮I, N; ℝ⟯ →ₗ[ℝ] C^r⟮I, N; ℝ⟯) (j : ℕ) :
    (smulCommutator ℂ (ContMDiffMap.ofReal f) ^ j) (ContMDiffMap.complexifyLinearMap D) =
      ContMDiffMap.complexifyLinearMap ((smulCommutator ℝ f ^ j) D) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, smulCommutator_ofReal_complexifyLinearMap, pow_succ',
      mul_apply_eq_comp]

/-- Reading a complex differential operator `Q` on real-valued functions and composing with a
real-linear map `σ` to real-valued functions that is linear over the real-valued functions gives a
real differential operator of the same order. -/
private theorem comp_restrictScalars_comp_ofReal_mem_differentialOperators {m : ℕ}
    {Q : C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯}
    (hQ : Q ∈ differentialOperators ℂ C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯ C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯
      C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯ m)
    {σ : C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℝ] C^r⟮I, N; ℝ⟯}
    (hσ : ∀ (b : C^r⟮I, N; ℝ⟯) y, σ (ContMDiffMap.ofReal b * y) = b * σ y) :
    σ ∘ₗ Q.restrictScalars ℝ ∘ₗ ContMDiffMap.ofReal.toLinearMap ∈
      differentialOperators ℝ C^r⟮I, N; ℝ⟯ C^r⟮I, N; ℝ⟯ C^r⟮I, N; ℝ⟯ m :=
  -- The inclusion of real functions and `σ` intertwine multiplication by a real function `b` with
  -- multiplication by `b` as a complex function.
  comp_comp_mem_differentialOperators
    (fun b ↦ ⟨ContMDiffMap.ofReal b, fun x ↦ map_mul ContMDiffMap.ofReal b x, hσ b⟩)
    (restrictScalars_mem_differentialOperators hQ)

/-- **The real part of a complex differential operator.** If `Q` is a complex-linear differential
operator of order at most `m` on the complex-valued smooth functions, for commutators with
complex-valued functions, then `u ↦ Re (Q u)` on the real-valued smooth functions is a real
differential operator of order at most `m`. -/
theorem re_comp_restrictScalars_comp_ofReal_mem_differentialOperators {m : ℕ}
    {Q : C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯}
    (hQ : Q ∈ differentialOperators ℂ C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯ C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯
      C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯ m) :
    ContMDiffMap.re ∘ₗ Q.restrictScalars ℝ ∘ₗ ContMDiffMap.ofReal.toLinearMap ∈
      differentialOperators ℝ C^r⟮I, N; ℝ⟯ C^r⟮I, N; ℝ⟯ C^r⟮I, N; ℝ⟯ m :=
  comp_restrictScalars_comp_ofReal_mem_differentialOperators hQ fun b y ↦ by
    ext x
    simp [ContMDiffMap.re_apply]

/-- **The imaginary part of a complex differential operator.** If `Q` is a complex-linear
differential operator of order at most `m` on the complex-valued smooth functions, for commutators
with complex-valued functions, then `u ↦ Im (Q u)` on the real-valued smooth functions is a real
differential operator of order at most `m`. -/
theorem im_comp_restrictScalars_comp_ofReal_mem_differentialOperators {m : ℕ}
    {Q : C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯}
    (hQ : Q ∈ differentialOperators ℂ C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯ C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯
      C^r⟮I, N; 𝓘(ℝ, ℂ), ℂ⟯ m) :
    ContMDiffMap.im ∘ₗ Q.restrictScalars ℝ ∘ₗ ContMDiffMap.ofReal.toLinearMap ∈
      differentialOperators ℝ C^r⟮I, N; ℝ⟯ C^r⟮I, N; ℝ⟯ C^r⟮I, N; ℝ⟯ m :=
  comp_restrictScalars_comp_ofReal_mem_differentialOperators hQ fun b y ↦ by
    ext x
    simp [ContMDiffMap.im_apply]
end TauCeti
