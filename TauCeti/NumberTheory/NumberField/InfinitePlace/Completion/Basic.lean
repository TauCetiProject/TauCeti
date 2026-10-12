/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import TauCeti.Analysis.Normed.Ring.WithAbs

/-!
# Normalized absolute values on archimedean completions

`NumberField.InfinitePlace.completionNormalizedAbsValue` is the norm on `w.Completion` raised to
`w.mult`, as a multiplicative map with zero. The exponent is one at real places and two at complex
places. For a number field, its restriction agrees with the normalization in
`NumberField.prod_abs_eq_one`; these completion-side maps supply the archimedean factors of the
idele norm.

`NumberField.InfinitePlace.Completion.norm_algebraMap` compares the completion norm with the place
absolute value on the dense base field, and
`NumberField.InfinitePlace.Completion.funext_of_continuous` says that continuous maps out of the
completion are determined by their values on it. The normalized value is continuous and takes
every nonnegative real value.

Archimedean completions are nontrivially normed fields, and the diagonal embeddings form scalar
towers over any commutative semiring base.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II.
-/

public section
noncomputable section

namespace NumberField.InfinitePlace

open NumberField
open scoped WithZero

variable {K : Type*} [Field K]

/-- An archimedean completion is a nontrivially normed field. -/
instance Completion.instNontriviallyNormedField (v : InfinitePlace K) :
    NontriviallyNormedField v.Completion where
  non_trivial := by
    refine ⟨2, ?_⟩
    rw [← (Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
      (map_zero _), map_ofNat]
    norm_num

/-- The diagonal algebra structures on an archimedean completion form a scalar tower. -/
instance {R : Type*} [CommSemiring R] [Algebra R K] (w : InfinitePlace K) :
    IsScalarTower R K w.Completion :=
  (Completion.equiv w).isScalarTower R K

/-- The normalized absolute value on the completion at an infinite place. -/
def completionNormalizedAbsValue (w : InfinitePlace K) : w.Completion →*₀ ℝ :=
  (powMonoidWithZeroHom (InfinitePlace.mult_ne_zero (w := w))).comp normHom

/-- Evaluating the normalized absolute value at `x` gives `‖x‖ ^ w.mult`. -/
@[simp]
theorem completionNormalizedAbsValue_apply (w : InfinitePlace K) (x : w.Completion) :
    completionNormalizedAbsValue w x = ‖x‖ ^ w.mult :=
  (rfl)

/-- The norm of a field element in its archimedean completion is its place absolute value. -/
@[simp↓]
theorem Completion.norm_algebraMap (w : InfinitePlace K) (x : K) :
    ‖algebraMap K w.Completion x‖ = w x := by
  rw [Completion.algebraMap_apply]
  exact Completion.norm_coe w (WithAbs.toAbs w.1 x)

/-- Two continuous maps out of an archimedean completion `K_w` into a Hausdorff space agree once
they agree on `K`. -/
theorem Completion.funext_of_continuous {w : InfinitePlace K} {B : Type*} [TopologicalSpace B]
    [T2Space B] {f g : w.Completion → B} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : K, f (algebraMap K w.Completion x) = g (algebraMap K w.Completion x)) : f = g := by
  funext a
  induction a using Completion.induction_on with
  | hp => exact isClosed_eq hf hg
  | ih a => exact h a.ofAbs

/-- On the dense copy of `K`, the infinite completion value is the normalized
infinite-place value. -/
theorem completionNormalizedAbsValue_algebraMap (w : InfinitePlace K) (x : K) :
    completionNormalizedAbsValue w (algebraMap K w.Completion x) = w x ^ w.mult := by
  rw [completionNormalizedAbsValue_apply, Completion.norm_algebraMap]

/-- On the dense copy of `K`, a real place contributes its ordinary absolute value. -/
theorem completionNormalizedAbsValue_algebraMap_of_isReal
    (w : InfinitePlace K) (hw : w.IsReal) (x : K) :
    completionNormalizedAbsValue w (algebraMap K w.Completion x) = w x := by
  rw [completionNormalizedAbsValue_algebraMap, hw.mult_eq_one, pow_one]

/-- On the dense copy of `K`, a complex place contributes the square of its absolute value. -/
theorem completionNormalizedAbsValue_algebraMap_of_isComplex
    (w : InfinitePlace K) (hw : w.IsComplex) (x : K) :
    completionNormalizedAbsValue w (algebraMap K w.Completion x) = w x ^ 2 := by
  rw [completionNormalizedAbsValue_algebraMap, hw.mult_eq_two]

/-- At a real place the completion value is the ordinary absolute value. -/
theorem completionNormalizedAbsValue_of_isReal
    (w : InfinitePlace K) (hw : w.IsReal) (x : w.Completion) :
    completionNormalizedAbsValue w x = ‖x‖ := by
  rw [completionNormalizedAbsValue_apply, hw.mult_eq_one, pow_one]

/-- At a complex place the completion value is the square of the ordinary absolute value. -/
theorem completionNormalizedAbsValue_of_isComplex
    (w : InfinitePlace K) (hw : w.IsComplex) (x : w.Completion) :
    completionNormalizedAbsValue w x = ‖x‖ ^ 2 := by
  rw [completionNormalizedAbsValue_apply, hw.mult_eq_two]

/-- The infinite completion value is continuous. -/
@[fun_prop]
theorem continuous_completionNormalizedAbsValue (w : InfinitePlace K) :
    Continuous (completionNormalizedAbsValue w : w.Completion → ℝ) := by
  -- Rewrite the bundled hom as a function before applying continuity of powers of the norm.
  convert continuous_norm.pow w.mult using 1
  ext x
  exact completionNormalizedAbsValue_apply w x

/-- Every nonnegative real number is the normalized absolute value of an element of the completion
at an infinite place. -/
theorem exists_completionNormalizedAbsValue_eq (w : InfinitePlace K) {t : ℝ} (ht : 0 ≤ t) :
    ∃ x : w.Completion, completionNormalizedAbsValue w x = t := by
  rcases w.isReal_or_isComplex with hw | hw
  · obtain ⟨x, hx⟩ := Completion.surjective_extensionEmbeddingOfIsReal hw t
    refine ⟨x, ?_⟩
    rw [completionNormalizedAbsValue_of_isReal w hw,
      ← (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), hx,
      Real.norm_of_nonneg ht]
  · obtain ⟨x, hx⟩ := Completion.surjective_extensionEmbedding_of_isComplex hw (√t : ℂ)
    refine ⟨x, ?_⟩
    rw [completionNormalizedAbsValue_of_isComplex w hw,
      ← (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), hx,
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t), Real.sq_sqrt ht]

end NumberField.InfinitePlace
