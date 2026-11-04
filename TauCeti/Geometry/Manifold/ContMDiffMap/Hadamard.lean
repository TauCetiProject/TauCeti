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
coefficients whose values at `x` are the directional derivatives along the basis. In the algebra
of smooth functions this becomes an identity between bundled smooth maps.

## Main results

* `ContMDiffMap.coe_sum`: the coercion of a finite sum of smooth maps is the sum of the coercions.
* `ContMDiffMap.exists_hadamard_coords`: Hadamard's lemma in the coordinates of a finite basis.
* `TauCeti.sub_algebraMap_eq_sum_mul_sub_algebraMap`: the bundled form of such a factorization in
  the algebra of smooth functions.
-/

public section

open scoped ContDiff Manifold

noncomputable section

namespace ContMDiffMap

/-- The coercion of a finite sum of smooth maps into a commutative additive Lie group is the
pointwise sum. -/
@[simp]
theorem coe_sum {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {n : ℕ∞ω}
    {G : Type*} [AddCommMonoid G] [TopologicalSpace G] [ChartedSpace H' G] [ContMDiffAdd I' n G]
    {ι : Type*} (s : Finset ι) (f : ι → C^n⟮I, N; I', G⟯) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) :=
  map_sum coeFnAddMonoidHom f s

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
    [NormedSpace ℝ E] {ι : Type*} [Fintype ι] (x : E)
    (g : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯)
    (a c : ι → C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯)
    (h : ∀ y, g y - g x = ∑ i, a i y * (c i y - c i x)) :
    g - algebraMap ℝ C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ (g x) =
      ∑ i, a i * (c i - algebraMap ℝ C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ (c i x)) := by
  ext y
  calc
    (g - algebraMap ℝ C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯ (g x)) y = g y - g x := rfl
    _ = ∑ i, a i y * (c i y - c i x) := h y
    _ = _ := by simp [Algebra.algebraMap_eq_smul_one]

end TauCeti
