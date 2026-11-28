/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.Calculus.Sard.OutermostStratum
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Checks of the sharp Sard theorem

The Morse–Sard theorem `TauCeti.addHaar_image_criticalPoints_eq_zero` says that for a `C^k` map
`f` from an `m`-dimensional to an `n`-dimensional real normed space, with `k > max (m - n, 0)`, the
values taken at the points where the derivative of `f` is not surjective form a null set. Its
hypothesis is written `m - n + 1 ≤ k` in natural-number subtraction. This file tests the statement
on the boundary cases of its hypotheses, where a wrong threshold, a wrong notion of critical point
or a dependence on values outside the domain would show.

* **The threshold is sharp in the dimensions, not in their square.** For a constant map
  `ℝ³ → ℝ`, every point is critical and the critical image is a single point. The theorem applies
  at `k = 3`, since `m - n = 2 < 3`, and exactly from `k = 3` on
  (`TauCeti.SardExample.sard_hypothesis_euclideanSpace_three_real_iff`); a bound `k ≥ m² + 1` from
  a cruder rank stratification would demand `k ≥ 10`.
* **Critical means non-surjective, not rank-deficient.** For the line `t ↦ (t, 0)` of the plane,
  the derivative at every point has rank `1 = min (1, 2)`, the largest possible, and is still not
  onto (`TauCeti.SardExample.finrank_range_fderiv_line`,
  `TauCeti.SardExample.not_surjective_fderiv_line`). So every value is critical, the critical
  image is the whole line, and the theorem at `k = 1` says that it has area zero. Counting only
  derivatives of rank below `min (m, n)` would find no critical points at all.
* **Dimension zero.** For a map `ℝ⁰ → ℝ⁰` the unique derivative is surjective, so the critical
  image is empty (`TauCeti.SardExample.image_criticalPoints_euclideanSpace_zero`). For a map
  `ℝ⁰ → ℝ` the unique derivative is zero, so the critical image is the single value of the map
  (`TauCeti.SardExample.image_criticalPoints_euclideanSpace_zero_real`), which is null.
* **Only the domain matters.** The identity of `ℝ` has no critical points
  (`TauCeti.SardExample.criticalPoints_id`), and the theorem applies to it at `k = 1`. On the
  empty domain `U = ∅` the critical image is empty whatever `f` does elsewhere, and the theorem
  holds for every `f : ℝ → ℝ` without any regularity assumption.

## References

* A. Sard, *The measure of the critical values of differentiable maps*, Bull. Amer. Math. Soc.
  **48** (1942), 883–890.
-/

public section

open Function MeasureTheory Module Set
open scoped ContDiff

namespace TauCeti.SardExample

/-! ### A constant map `ℝ³ → ℝ` -/

/-- A constant map `ℝ³ → ℝ` has no regular points: its derivative is zero, which is not onto
`ℝ`. Its critical image is the single value `c`. -/
theorem image_criticalPoints_const (c : ℝ) :
    (fun _ : EuclideanSpace ℝ (Fin 3) ↦ c) ''
        {x | ¬ Surjective (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) ↦ c) x)} = {c} := by
  have hcrit : {x | ¬ Surjective (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) ↦ c) x)} = univ := by
    refine eq_univ_of_forall fun x hsurj ↦ ?_
    obtain ⟨v, hv⟩ := hsurj 1
    simp at hv
  rw [hcrit, image_univ, range_const]

/-- For maps `ℝ³ → ℝ` the hypothesis `m - n + 1 ≤ k` of the sharp Sard theorem reads `3 ≤ k`:
here `m - n = 2`. -/
theorem sard_hypothesis_euclideanSpace_three_real_iff {k : ℕ∞ω} :
    ((finrank ℝ (EuclideanSpace ℝ (Fin 3)) - finrank ℝ ℝ + 1 : ℕ) : ℕ∞ω) ≤ k ↔ 3 ≤ k := by
  simp only [finrank_euclideanSpace_fin, finrank_self]
  norm_num

/-- The sharp Sard theorem applies to a constant map `ℝ³ → ℝ` at `k = 3`, and says that its
critical image, the single value `c`, is null. -/
example (c : ℝ) :
    volume ((fun _ : EuclideanSpace ℝ (Fin 3) ↦ c) ''
      {x | ¬ Surjective (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 3) ↦ c) x)}) = 0 :=
  (contDiff_const (n := 3)).addHaar_image_criticalPoints_eq_zero volume
    (sard_hypothesis_euclideanSpace_three_real_iff.2 le_rfl)

/-- At `k = 2` the hypothesis of the sharp Sard theorem fails for maps `ℝ³ → ℝ`. -/
example : ¬ ((finrank ℝ (EuclideanSpace ℝ (Fin 3)) - finrank ℝ ℝ + 1 : ℕ) : ℕ∞ω) ≤ 2 := by
  rw [sard_hypothesis_euclideanSpace_three_real_iff]
  decide

/-- A threshold `k ≥ m² + 1` would ask for `k ≥ 10` on `ℝ³`, where the sharp one asks for
`k ≥ 3`. -/
example : finrank ℝ (EuclideanSpace ℝ (Fin 3)) - finrank ℝ ℝ + 1 <
    finrank ℝ (EuclideanSpace ℝ (Fin 3)) ^ 2 + 1 := by
  simp

/-! ### The line `t ↦ (t, 0)` in the plane -/

/-- No derivative of the line `t ↦ (t, 0)` is onto the plane: `(0, 1)` is not in its range. -/
theorem not_surjective_fderiv_line (t : ℝ) :
    ¬ Surjective (fderiv ℝ (fun s : ℝ ↦ (s, (0 : ℝ))) t) := by
  rw [(hasFDerivAt_prodMk_left t (0 : ℝ)).fderiv]
  intro hsurj
  obtain ⟨s, hs⟩ := hsurj (0, 1)
  simp at hs

/-- The derivative of the line `t ↦ (t, 0)` has rank `1 = min (1, 2)` at every point: it is
injective. The critical points of a map in the sense of Sard are those with non-surjective
derivative, not those of rank below `min (m, n)`. -/
theorem finrank_range_fderiv_line (t : ℝ) :
    finrank ℝ (LinearMap.range (fderiv ℝ (fun s : ℝ ↦ (s, (0 : ℝ))) t : ℝ →ₗ[ℝ] ℝ × ℝ)) =
      min (finrank ℝ ℝ) (finrank ℝ (ℝ × ℝ)) := by
  rw [(hasFDerivAt_prodMk_left t (0 : ℝ)).fderiv,
    LinearMap.finrank_range_of_inj fun a b h ↦ by simpa using h]
  simp

/-- Every point of the line `t ↦ (t, 0)` is critical, so its critical image is the whole line
`ℝ × {0}`. -/
theorem image_criticalPoints_line :
    (fun s : ℝ ↦ (s, (0 : ℝ))) '' {t | ¬ Surjective (fderiv ℝ (fun s : ℝ ↦ (s, (0 : ℝ))) t)} =
      univ ×ˢ {0} := by
  have hcrit : {t | ¬ Surjective (fderiv ℝ (fun s : ℝ ↦ (s, (0 : ℝ))) t)} = univ :=
    eq_univ_of_forall not_surjective_fderiv_line
  rw [hcrit, image_univ]
  ext ⟨a, b⟩
  simp [eq_comm]

/-- The sharp Sard theorem applies to the line `t ↦ (t, 0)` at `k = 1`, since `1 - 2 + 1 = 1` in
natural-number subtraction, and says that the line has area zero. -/
example : volume (univ ×ˢ {0} : Set (ℝ × ℝ)) = 0 := by
  rw [← image_criticalPoints_line, Measure.volume_eq_prod]
  exact (contDiff_prodMk_left (0 : ℝ) (n := 1)).addHaar_image_criticalPoints_eq_zero
    ((volume : Measure ℝ).prod volume) (by simp)

/-! ### Dimension zero -/

/-- A map `ℝ⁰ → ℝ⁰` has surjective derivatives, since its target has one point, so its critical
image is empty. -/
theorem image_criticalPoints_euclideanSpace_zero
    (f : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0)) :
    f '' {x | ¬ Surjective (fderiv ℝ f x)} = ∅ :=
  image_eq_empty.2 (eq_empty_of_forall_notMem fun _ hx ↦ hx (surjective_to_subsingleton _))

/-- The sharp Sard theorem applies to every map `ℝ⁰ → ℝ⁰`: the critical image is null, and is in
fact empty. -/
example (f : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0)) :
    volume (f '' {x | ¬ Surjective (fderiv ℝ f x)}) = 0 := by
  have hf : f = fun _ ↦ 0 := Subsingleton.elim _ _
  subst hf
  exact (contDiff_const (n := 1)).addHaar_image_criticalPoints_eq_zero volume (by simp)

/-- A map `ℝ⁰ → ℝ` has zero derivative, which is not onto `ℝ`, so its critical image is its single
value. -/
theorem image_criticalPoints_euclideanSpace_zero_real (f : EuclideanSpace ℝ (Fin 0) → ℝ) :
    f '' {x | ¬ Surjective (fderiv ℝ f x)} = {f 0} := by
  have hcrit : {x | ¬ Surjective (fderiv ℝ f x)} = univ := by
    refine eq_univ_of_forall fun x hsurj ↦ ?_
    obtain ⟨v, hv⟩ := hsurj 1
    rw [Subsingleton.elim v 0, map_zero] at hv
    exact zero_ne_one hv
  rw [hcrit, image_univ]
  ext y
  exact ⟨fun ⟨x, hx⟩ ↦ mem_singleton_iff.2 (by rw [← hx, Subsingleton.elim x 0]),
    fun h ↦ ⟨0, h.symm⟩⟩

/-- The sharp Sard theorem applies to every map `ℝ⁰ → ℝ` at `k = 1`, and says that its single
value is null. -/
example (f : EuclideanSpace ℝ (Fin 0) → ℝ) :
    volume (f '' {x | ¬ Surjective (fderiv ℝ f x)}) = 0 := by
  have hf : f = fun _ ↦ f 0 := funext fun x ↦ congrArg f (Subsingleton.elim x 0)
  rw [hf]
  exact (contDiff_const (n := 1)).addHaar_image_criticalPoints_eq_zero volume (by simp)

/-! ### The identity and the empty domain -/

/-- The identity of `ℝ` has no critical points. -/
theorem criticalPoints_id : {x : ℝ | ¬ Surjective (fderiv ℝ id x)} = ∅ := by
  simp only [fderiv_id]
  exact eq_empty_of_forall_notMem fun _ h ↦ h surjective_id

/-- The sharp Sard theorem applies to the identity of `ℝ` at `k = 1`; its critical image is
empty. -/
example : volume (id '' {x : ℝ | ¬ Surjective (fderiv ℝ id x)}) = 0 :=
  (contDiff_id (n := 1)).addHaar_image_criticalPoints_eq_zero volume (by simp)

/-- On the empty domain the sharp Sard theorem holds for every map `ℝ → ℝ`, without any
regularity: only the points of the domain `U` contribute critical values, whatever `f` does
outside `U`. -/
example (f : ℝ → ℝ) : volume (f '' (∅ ∩ {x | ¬ Surjective (fderiv ℝ f x)})) = 0 :=
  addHaar_image_criticalPoints_eq_zero (U := ∅) (n := 1) volume (fun _ h ↦ h.elim) (by simp)

end TauCeti.SardExample
