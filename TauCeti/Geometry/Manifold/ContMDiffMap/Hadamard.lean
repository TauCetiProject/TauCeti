/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.LinearAlgebra.Basis.Defs
import TauCeti.Analysis.Calculus.Hadamard

/-!
# Hadamard's lemma for smooth functions on a normed space

Subtracting its value at `x`, a smooth real function on a real normed space is a combination of
the coordinate functions of a finite basis, each relative to its value at `x`, with smooth
coefficients whose values at `x` are the directional derivatives along the basis.

More generally, a smooth function whose iterated derivatives of every order below `n` vanish at
`x` is a combination of products of `n` such relative coordinate functions with smooth
coefficients.

## Main results

* `ContMDiffMap.exists_hadamard_coords`: Hadamard's lemma in the coordinates of a finite basis.
* `ContMDiffMap.exists_hadamard_coords_of_iteratedFDeriv_eq_zero`: the higher-order Hadamard
  lemma in the coordinates of a finite basis.
-/

public section

open scoped ContDiff Manifold Nat

noncomputable section

namespace ContMDiffMap

/-- **Hadamard's lemma in coordinates.** Subtracting its value at `x` writes a smooth real
function as a combination of the coordinate functions of any finitely-indexed basis, each taken
relative to its own value at `x`, with smooth coefficients. At the base point those coefficients
are the directional derivatives along the basis. -/
theorem exists_hadamard_coords {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
    (f : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯) (x : E) (b : Module.Basis ι ℝ E) :
    ∃ a : ι → C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯,
      (∀ i, a i x = fderiv ℝ f x (b i)) ∧
        ∀ y, f y - f x = ∑ i, a i y * (b.coord i y - b.coord i x) := by
  refine ⟨fun i ↦ ⟨fun y ↦ hadamardFactor f x y (b i), ?_⟩, fun i ↦ ?_, ?_⟩
  · have hfac : ContDiff ℝ ∞ (hadamardFactor f x) :=
      f.contMDiff.contDiff.contDiff_hadamardFactor f x
    -- Applying a smooth continuous-linear-map-valued function to the constant vector `b i`
    -- is the available API for smoothness of each scalar Hadamard factor.
    exact (hfac.clm_apply (show ContDiff ℝ ∞ (fun _ : E ↦ b i) from contDiff_const)).contMDiff
  · simp
  · intro y
    calc
      f y - f x = hadamardFactor f x y (y - x) :=
        (f.contMDiff.contDiff.of_le (by norm_num)).sub_eq_hadamardFactor_apply f x y
      _ = ∑ i, hadamardFactor f x y (b i) * (b.coord i y - b.coord i x) := by
        rw [← b.sum_repr (y - x), map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
        simp [mul_comm]

/-- **The higher-order Hadamard lemma in coordinates.** If the iterated derivatives of a smooth
real function `f` of every order `k < n` vanish at `x`, then `f` is a combination of the products
of `n` coordinate functions of a finitely-indexed basis, each taken relative to its own value at
`x`, with smooth coefficients. At `x` the coefficients are `(n!)⁻¹` times the values of the
`n`-th iterated derivative of `f` on basis vectors. For `n = 1` this is `exists_hadamard_coords`
at a zero of `f`. -/
theorem exists_hadamard_coords_of_iteratedFDeriv_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
    (f : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯) (x : E) (b : Module.Basis ι ℝ E) {n : ℕ}
    (hf : ∀ k < n, iteratedFDeriv ℝ k f x = 0) :
    ∃ a : (Fin n → ι) → C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯,
      (∀ σ, a σ x = (n ! : ℝ)⁻¹ * iteratedFDeriv ℝ n f x (fun j ↦ b (σ j))) ∧
        ∀ y, f y = ∑ σ, a σ y * ∏ j, (b.coord (σ j) y - b.coord (σ j) x) := by
  cases n with
  | zero => exact ⟨fun _ ↦ f, fun σ ↦ by simp, fun y ↦ by simp⟩
  | succ m =>
    have hf' : ContDiff ℝ (↑(⊤ : ℕ∞) + (m + 1 : ℕ)) f :=
      f.contMDiff.contDiff.of_le (by exact_mod_cast le_top)
    have hR := ContDiff.contDiff_taylorRemainderFactor (m := ⊤) hf' x
    -- The coefficients are the values of the Taylor remainder factor on basis vectors.
    refine ⟨fun σ ↦ ⟨fun y ↦ TauCeti.taylorRemainderFactor m f x y (fun j ↦ b (σ j)),
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin (m + 1) ↦ E) ℝ
        fun j ↦ b (σ j)).contDiff.comp hR).contMDiff⟩, fun σ ↦ ?_, fun y ↦ ?_⟩
    · have h := congrArg (fun L ↦ L fun j ↦ b (σ j)) (TauCeti.taylorRemainderFactor_self m f x)
      simp only [smul_apply, smul_eq_mul] at h
      -- The bundled coefficient `a σ` applied at `x` unfolds to the left side of `h`.
      exact h
    have hv : y - x = ∑ i, (b.coord i y - b.coord i x) • b i := by
      simp_rw [← map_sub, Module.Basis.coord_apply, b.sum_repr]
    have hf'' : ContDiff ℝ (m + 1) f := f.contMDiff.contDiff.of_le (by exact_mod_cast le_top)
    -- The Taylor polynomial vanishes, and the remainder expands multilinearly in the basis.
    rw [ContDiff.eq_sum_add_taylorRemainderFactor_apply hf'' x y,
      Finset.sum_eq_zero (fun k hk ↦ by rw [hf k (Finset.mem_range.mp hk)]; simp), zero_add, hv,
      ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]
    -- The right side applies the bundled coefficient `a σ`, whose underlying function is the
    -- evaluated remainder factor on the left.
    rfl

end ContMDiffMap
