/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.Ramification

/-!
# Normalized absolute values on number-field completions

The finite and infinite completions of a number field carry their usual norm, but the global
product formula uses the normalized local absolute value: the norm at a real place and the square
of the norm at a complex place.  This file packages those values as multiplicative maps with zero.

At a finite place the required map is already Mathlib's `normHom` on `v.adicCompletion K`, and its
comparison with `HeightOneSpectrum.adicAbv` is Mathlib's `FinitePlace.norm_embedding`.  The new
infinite-place map is the norm on `w.Completion` raised to `w.mult`.  The latter exponent is one at
real places and two at complex places, so its restriction to the number field agrees with the
normalization used by `NumberField.prod_abs_eq_one`.  These completion-side maps are the local
factors used by the global idele norm; the single all-places carrier is developed separately.

The archimedean completions also carry a nontrivial norm. Completed extensions at infinite
places are finite dimensional, and the diagonal embeddings form scalar towers. These instances
allow finite-dimensional topological algebra to be used with the canonical completion maps.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II.
-/

public section
noncomputable section

namespace NumberField.InfinitePlace

open NumberField
open scoped WithZero NumberField.LiesOver

variable {K : Type*} [Field K]

/-- An archimedean completion is a nontrivially normed field. -/
instance Completion.instNontriviallyNormedField (v : InfinitePlace K) :
    NontriviallyNormedField v.Completion where
  non_trivial := by
    refine ⟨2, ?_⟩
    rw [← (Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
      (map_zero _), map_ofNat]
    norm_num

variable {L : Type*} [Field L] [Algebra K L]

/-- A place indexed by the places above `v` carries its proof of lying over `v` as an instance. -/
instance instLiesOverSubtype (v : InfinitePlace K)
    (w : {w : InfinitePlace L // w.LiesOver v}) : w.1.LiesOver v := w.2

/-- A completed extension at an infinite place is finite dimensional: its degree is one or two. -/
instance (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v] :
    FiniteDimensional v.Completion w.Completion := by
  apply Module.finite_of_finrank_pos
  have h := mult_ne_zero (w := w)
  rw [← mult_mul_finrank v w, mul_ne_zero_iff] at h
  exact Nat.pos_of_ne_zero h.2

/-- The diagonal algebra structures on an archimedean completion form a scalar tower. -/
instance {R : Type*} [CommRing R] [Algebra R L] (w : InfinitePlace L) :
    IsScalarTower R L w.Completion :=
  (Completion.equiv w).isScalarTower R L

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
