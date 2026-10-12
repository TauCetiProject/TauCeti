/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Extension
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Complex

/-!
# Local norms at the infinite places

Let `L / K` be an extension of fields and let `w` be an infinite place of `L` lying over the
infinite place `v` of `K`. Through the extension embeddings `K_v → ℂ` and `L_w → ℂ`, the norm
`N_{L_w/K_v}` of the completed extension is one of three explicit maps.

* If `w` is unramified over `v`, then `L_w = K_v` and the norm is the inverse of the completion
  map. Read in `ℂ`, it is the identity when `w.embedding` extends `v.embedding`, and complex
  conjugation when the conjugate of `w.embedding` extends it.
* If `w` is ramified over `v`, so that `w` is complex and `v` is real, then the norm is
  `z ↦ |z|²`.

These formulas compute the archimedean components of the norm map of ideles. The norm preserves
the normalized absolute value: at a complex place over a real place the source uses the square
of the ordinary absolute value, exactly as the norm does.

## Main results

* `NumberField.InfinitePlace.completionNormalizedAbsValue_norm`: the norm preserves normalized
  absolute values at infinite places.
* `NumberField.InfinitePlace.Completion.extensionEmbedding_norm_of_isUnramified`: at an
  unramified place, the norm is the identity in `ℂ`.
* `NumberField.InfinitePlace.Completion.extensionEmbedding_norm_of_isUnramified_conjugate`: the
  same, when the conjugate of `w.embedding` extends `v.embedding`; the norm is then complex
  conjugation.
* `NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_norm_of_isReal`: at a real
  place over a real place, the norm is the identity of `ℝ`.
* `NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_norm_of_isRamified`: at a
  complex place over a real place, the norm is `Complex.normSq`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §8.
-/

public section

open NumberField NumberField.ComplexEmbedding ComplexConjugate
open scoped NumberField.LiesOver

namespace NumberField.InfinitePlace.Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K}
  {w : InfinitePlace L} [w.LiesOver v]

/-- At an unramified place every element of `L_w` comes from `K_v`, and its norm is that
element. -/
private theorem exists_algebraMap_eq_and_norm_eq (h : w.IsUnramified K) (y : w.Completion) :
    ∃ a : v.Completion, algebraMap v.Completion w.Completion a = y ∧
      Algebra.norm v.Completion y = a := by
  obtain ⟨a, rfl⟩ :=
    (Module.Free.bijective_algebraMap_of_finrank_eq_one (h.finrank_eq_one v)).2 y
  exact ⟨a, rfl, by rw [Algebra.norm_algebraMap, h.finrank_eq_one v, pow_one]⟩

/-- **The local norm at an unramified infinite place.** If `w.embedding` extends `v.embedding`,
the norm `N_{L_w/K_v}` is the identity when read in `ℂ` through the extension embeddings. -/
theorem extensionEmbedding_norm_of_isUnramified (h : w.IsUnramified K)
    [ComplexEmbedding.LiesOver w.embedding v.embedding] (y : w.Completion) :
    extensionEmbedding v (Algebra.norm v.Completion y) = extensionEmbedding w y := by
  obtain ⟨a, rfl, ha⟩ := exists_algebraMap_eq_and_norm_eq (v := v) h y
  have := liesOver_extensionEmbedding w v
  rw [ha, liesOver_extensionEmbedding_apply]

/-- **The local norm at an unramified infinite place, conjugate case.** If the conjugate of
`w.embedding` extends `v.embedding`, the norm `N_{L_w/K_v}` is complex conjugation when read in
`ℂ` through the extension embeddings. -/
theorem extensionEmbedding_norm_of_isUnramified_conjugate (h : w.IsUnramified K)
    [ComplexEmbedding.LiesOver (conjugate w.embedding) v.embedding] (y : w.Completion) :
    extensionEmbedding v (Algebra.norm v.Completion y) = conj (extensionEmbedding w y) := by
  obtain ⟨a, rfl, ha⟩ := exists_algebraMap_eq_and_norm_eq (v := v) h y
  have := liesOver_conjugate_extensionEmbedding w v
  rw [ha, ← conjugate_coe_eq, liesOver_extensionEmbedding_apply]

/-- **The local norm at a real place over a real place** is the identity of `ℝ`, read through
the real extension embeddings. -/
theorem extensionEmbeddingOfIsReal_norm_of_isReal (hv : v.IsReal) (hw : w.IsReal)
    (y : w.Completion) :
    extensionEmbeddingOfIsReal hv (Algebra.norm v.Completion y) =
      extensionEmbeddingOfIsReal hw y := by
  have := LiesOver.embedding_liesOver_of_isReal w hv
  exact_mod_cast (extensionEmbeddingOfIsReal_apply hv _).trans
    ((extensionEmbedding_norm_of_isUnramified (hw.isUnramified (k := K)) y).trans
      (extensionEmbeddingOfIsReal_apply hw y).symm)

/-- **The local norm at a complex place over a real place** is `z ↦ |z|²`, read through the
extension embeddings `K_v → ℝ` and `L_w → ℂ`. -/
theorem extensionEmbeddingOfIsReal_norm_of_isRamified (h : w.IsRamified K) (hv : v.IsReal)
    (y : w.Completion) :
    extensionEmbeddingOfIsReal hv (Algebra.norm v.Completion y) =
      Complex.normSq (extensionEmbedding w y) := by
  have := LiesOver.extensionEmbedding_liesOver_of_isReal w hv
  rw [Algebra.norm_eq_of_equiv_equiv (ringEquivRealOfIsReal hv)
      (ringEquivComplexOfIsComplex h.isComplex) (by ext; simp) y,
    ← ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply, ringEquivComplexOfIsComplex_apply,
    Algebra.norm_complex_apply]

end NumberField.InfinitePlace.Completion

namespace NumberField.InfinitePlace

open Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The local field norm preserves the normalized absolute value, including the squared
normalization at complex places. -/
@[simp↓]
theorem completionNormalizedAbsValue_norm (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] (x : w.Completion) :
    completionNormalizedAbsValue v (Algebra.norm v.Completion x) =
      completionNormalizedAbsValue w x := by
  by_cases hw : w.IsUnramified K
  · obtain ⟨a, rfl⟩ :=
      (Module.Free.bijective_algebraMap_of_finrank_eq_one (hw.finrank_eq_one v)).2 x
    rw [Algebra.norm_algebraMap, hw.finrank_eq_one v, pow_one, RingHom.algebraMap_toAlgebra]
    simpa only [hw.finrank_eq_one v, pow_one] using
      (completionNormalizedAbsValue_completionMap (w := w) a).symm
  · have hr : w.IsRamified K := hw
    have hv' : v.IsReal := (LiesOver.comap_eq w v) ▸ hr.isReal
    rw [completionNormalizedAbsValue_of_isReal v hv',
      completionNormalizedAbsValue_of_isComplex w hr.isComplex,
      ← (isometry_extensionEmbeddingOfIsReal hv').norm_map_of_map_zero (map_zero _),
      extensionEmbeddingOfIsReal_norm_of_isRamified hr hv',
      Real.norm_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq,
      (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]

end NumberField.InfinitePlace
