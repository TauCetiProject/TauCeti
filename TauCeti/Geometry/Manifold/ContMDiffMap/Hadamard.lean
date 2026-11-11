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
coefficients whose values at `x` are the directional derivatives along the basis. More generally,
subtracting its Taylor polynomial of order `n` at `x`, it is a combination of the products of
`n + 1` such relative coordinate functions, with smooth coefficients.

## Main results

* `ContMDiffMap.exists_hadamard_coords`: Hadamard's lemma in the coordinates of a finite basis.
* `ContMDiffMap.exists_taylor_coords`: Taylor's formula of order `n` with the remainder written
  in the same coordinates.
-/

public section

open scoped ContDiff Manifold

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

open scoped Nat in
/-- **Taylor's formula in coordinates.** A smooth real function on a finite-dimensional space is
its Taylor polynomial of order `n` at `x` plus a combination of the products of `n + 1`
coordinate functions of any finitely-indexed basis, each taken relative to its value at `x`, with
smooth coefficients. When the derivatives of order at most `n` vanish at `x`, this writes the
function as a sum of products of `n + 1` functions vanishing at `x` with smooth functions. -/
theorem exists_taylor_coords {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (f : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯) (x : E)
    (b : Module.Basis ι ℝ E) (n : ℕ) :
    ∃ a : (Fin (n + 1) → ι) → C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯,
      ∀ y, f y = ∑ k ∈ Finset.range (n + 1), (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k f x (fun _ ↦ y - x) +
        ∑ r, a r y * ∏ j, (b.coord (r j) y - b.coord (r j) x) := by
  have hf : ContDiff ℝ ∞ f := f.contMDiff.contDiff
  refine ⟨fun r ↦ ⟨fun y ↦ TauCeti.taylorRemainderFactor n f x y (fun j ↦ b (r j)), ?_⟩,
    fun y ↦ ?_⟩
  · exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin (n + 1) ↦ E) ℝ
      (fun j ↦ b (r j))).contDiff.comp
        ((hf.of_le (by simp)).contDiff_taylorRemainderFactor (k := ⊤) x)).contMDiff
  · rw [(hf.of_le (by simp)).eq_sum_add_taylorRemainderFactor_apply (n := n) x y]
    simp only [smul_eq_mul]
    congr 1
    -- Expand the increment in the basis and use multilinearity of the remainder factor.
    set T := TauCeti.taylorRemainderFactor n f x y
    conv_lhs => rw [← b.sum_repr (y - x)]
    rw [T.map_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [T.map_smul_univ, smul_eq_mul, mul_comm]
    congr 1
    simp [Module.Basis.coord_apply]

end ContMDiffMap
