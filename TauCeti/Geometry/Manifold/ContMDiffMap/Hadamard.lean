/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Calculus.Hadamard

/-!
# Hadamard's lemma for smooth functions

Hadamard's lemma factors a smooth real function `f` on a finite-dimensional real vector space
through the coordinate functions of a basis, centred at a base point, with smooth coefficients:
`f y - f x = ∑ i, a i y * (b.coord i y - b.coord i x)`. This file states it for bundled smooth
maps and transports such pointwise factorizations into identities in the algebra of smooth
functions.

## Main results

* `ContMDiffMap.exists_hadamard_coords`: Hadamard's lemma in the coordinates of a basis.
* `TauCeti.sub_algebraMap_eq_sum_mul_sub_algebraMap`: a pointwise factorization of `g - g x` is an
  identity between bundled smooth maps.
-/

public section

open scoped ContDiff Manifold

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

end ContMDiffMap

namespace TauCeti

/-- **Hadamard's identity in the algebra of smooth functions.** A pointwise factorization of
`g - g x` through the functions `c i`, with coefficients `a i`, is an identity between the bundled
smooth maps themselves, the constants appearing as the images of `algebraMap`.

This is the pointwise-to-bundled transport: the hypothesis speaks of values, the conclusion of
elements of `C^∞⟮…⟯`, and the two are related by evaluation being a ring homomorphism. -/
theorem sub_algebraMap_eq_sum_mul_sub_algebraMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {ι : Type*} [Fintype ι] (x : M)
    (g : C^∞⟮I, M; ℝ⟯) (a c : ι → C^∞⟮I, M; ℝ⟯)
    (h : ∀ y, g y - g x = ∑ i, a i y * (c i y - c i x)) :
    g - algebraMap ℝ C^∞⟮I, M; ℝ⟯ (g x) = ∑ i, a i * (c i - algebraMap ℝ C^∞⟮I, M; ℝ⟯ (c i x)) := by
  ext y
  calc
    (g - algebraMap ℝ C^∞⟮I, M; ℝ⟯ (g x)) y = g y - g x := rfl
    _ = ∑ i, a i y * (c i y - c i x) := h y
    _ = _ := by
      -- Evaluation of bundled smooth maps is a ring homomorphism, but the pointwise coercion on
      -- the left does not expose that homomorphism to `rw` automatically.
      change _ = ContMDiffMap.evalRingHom y _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ rfl

end TauCeti
