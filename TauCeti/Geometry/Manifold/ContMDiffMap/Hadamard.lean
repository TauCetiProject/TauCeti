/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Calculus.Hadamard

/-!
# Hadamard's lemma for smooth functions on a normed space

Subtracting its value at `x`, a smooth real function on a real normed space is a combination of
the coordinate functions of a finite basis, each relative to its value at `x`, with smooth
coefficients whose values at `x` are the directional derivatives along the basis.

More generally, if all derivatives of order less than `n` of such a function vanish at `x`, then it
is a combination of products of `n` of these relative coordinate functions, again with smooth
coefficients. The coefficients come from Taylor's formula with integral remainder: they are
weighted averages of the `n`-th derivative along the segment from `x`.

## Main results

* `ContMDiffMap.exists_hadamard_coords`: Hadamard's lemma in the coordinates of a finite basis.
* `ContMDiffMap.exists_hadamard_coords_of_iteratedFDeriv_eq_zero`: its higher-order form for a
  function whose derivatives of order less than `n` vanish at `x`.
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

/-- **Higher-order Hadamard lemma in coordinates.** If the derivatives of order less than `n` of a
smooth real function vanish at `x`, then the function is a combination, with smooth coefficients,
of products of `n` coordinate functions of a finitely-indexed basis, each taken relative to its
own value at `x`. At the base point the coefficient of a product is the `n`-th derivative on the
corresponding basis vectors, divided by `n!`. -/
theorem exists_hadamard_coords_of_iteratedFDeriv_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} [Fintype ι]
    (f : C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯) {x : E} {n : ℕ}
    (hfx : ∀ k < n, iteratedFDeriv ℝ k f x = 0) (b : Module.Basis ι ℝ E) :
    ∃ a : (Fin n → ι) → C^∞⟮modelWithCornersSelf ℝ E, E; ℝ⟯,
      (∀ r, a r x = (n.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ n f x (fun k ↦ b (r k))) ∧
        ∀ y, f y = ∑ r, a r y * ∏ k, (b.coord (r k) y - b.coord (r k) x) := by
  classical
  rcases n with _ | m
  · exact ⟨fun _ ↦ f, fun _ ↦ by simp, fun y ↦ by simp⟩
  have hf : ContDiff ℝ ∞ f := f.contMDiff.contDiff
  -- The `(m + 1)`-st derivative of `f` evaluated on a fixed tuple of basis vectors.
  let g (r : Fin (m + 1) → ι) (z : E) : ℝ := iteratedFDeriv ℝ (m + 1) f z (fun k ↦ b (r k))
  have hg (r) : ContDiff ℝ ∞ (g r) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (m + 1) ↦ E) ℝ (fun k ↦ b (r k))).contDiff.comp
      (hf.iteratedFDeriv_right (by simp))
  -- The weight of the integral remainder in Taylor's formula of order `m`.
  let w : ℝ → ℝ := fun t ↦ (m.factorial : ℝ)⁻¹ * (1 - t) ^ m
  refine ⟨fun r ↦ ⟨fun y ↦ segmentAverage w (g r) x (y - x), ?_⟩, fun r ↦ ?_, fun y ↦ ?_⟩
  · have := (hg r).contDiff_segmentAverage (n := ⊤) (w := w)
      ((by fun_prop : Continuous w).intervalIntegrable 0 1) x
    exact (by simpa using this : ContDiff ℝ ∞ _).comp (contDiff_id.sub contDiff_const) |>.contMDiff
  · -- At the base point the coefficient is the integral `1 / (m + 1)!` of the weight times `g r x`.
    have hw : ∫ t in (0 : ℝ)..1, w t = ((m + 1).factorial : ℝ)⁻¹ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun t ↦ t ^ m), integral_pow]
      push_cast [Nat.factorial_succ]
      field_simp
      ring
    simp [hw, g]
  -- Taylor's formula at `x` reduces to its integral remainder, since the lower derivatives vanish.
  have hT := map_add_eq_sum_add_integral_iteratedFDeriv (n := m) (x := x) (y := y - x)
    (fun _ _ ↦ hf.contDiffAt.of_le (by simp))
  rw [add_sub_cancel] at hT
  rw [hT, Finset.sum_eq_zero fun k hk ↦ by
    simp [hfx k (Nat.lt_succ_of_le (Finset.mem_range_succ_iff.mp hk))], zero_add]
  -- Expand the displacement `y - x` in the basis inside the multilinear remainder.
  have hexp (t : ℝ) : iteratedFDeriv ℝ (m + 1) f (x + t • (y - x)) (fun _ ↦ y - x) =
      ∑ r, (∏ k, (b.coord (r k) y - b.coord (r k) x)) * g r (x + t • (y - x)) := by
    rw [show (fun _ : Fin (m + 1) ↦ y - x) = fun _ ↦ ∑ i, b.repr (y - x) i • b i from
      funext fun _ ↦ (b.sum_repr _).symm, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp [g, smul_eq_mul, map_sub]
  have hcont (r : Fin (m + 1) → ι) : Continuous fun t : ℝ ↦ g r (x + t • (y - x)) :=
    (hg r).continuous.comp (by fun_prop)
  simp_rw [hexp, smul_eq_mul, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum fun r _ ↦ by
    exact (Continuous.intervalIntegrable (by fun_prop) 0 1), Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  simp only [ContMDiffMap.coeFn_mk, segmentAverage_def, w, smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_mul_const]
  congr 1 with t
  ring

end ContMDiffMap
