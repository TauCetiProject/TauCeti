/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Four-fold pairings of an alternating product and the indices of inertia

Let `B` be a bilinear form on a vector space `U` over a field, and let `m : H → H → U` be an
alternating bilinear product. Suppose that `B (m a b) (m b c) = 0` for all
`a b c`. The model is the cup product `H¹(X; ℝ) × H¹(X; ℝ) → H²(X; ℝ)` of a closed oriented
four-manifold, paired by the intersection form: then `B (m a b) (m c d) = ⟨a ∪ b ∪ c ∪ d, [X]⟩`,
and `B (m a b) (m b c)` vanishes because `b ∪ b = 0` in real cohomology. Under these hypotheses
the four-fold pairing `(a, b, c, d) ↦ B (m a b) (m c d)` is alternating in all four arguments.

Suppose the four-fold pairing takes a nonzero value `p = B (m a b) (m c d)`. Pairing a linear
relation against the six products of `a, b, c, d` shows that they span a subspace `W` of dimension
`6`, over any field. Over an ordered field, `B` restricted to `W` has signature `(3, 3)`, the
signature of the wedge pairing on the two-vectors of a four-dimensional space. Indeed, for any
scalar `s` the three vectors

`m a b + s • m c d`, `m a c + s • m d b`, `m a d + s • m b c`

are pairwise `B`-orthogonal, each of square `2 s p`; the choices `s = p` and `s = -p` give a
positive-definite and a negative-definite three-dimensional subspace of `W`.

When `U` is finite-dimensional, this forces both indices of inertia of `B` to be at least `3`.
Consequently, if `U` is finite-dimensional and either index of `B` is at most `2`, every four-fold
pairing vanishes. For a closed oriented four-manifold with `b₂⁺ = 1` this says that
`⟨a ∪ b ∪ c ∪ d, [X]⟩ = 0` for all `a b c d ∈ H¹(X; ℝ)`.

## Main results

* `LinearMap.BilinForm.finrank_span_eq_six_of_apply_ne_zero`: the six products of `a, b, c, d`
  are linearly independent when `B (m a b) (m c d) ≠ 0`, over any field.
* `LinearMap.BilinForm.sigPos_restrict_span_eq_three_of_apply_ne_zero` and
  `LinearMap.BilinForm.sigNeg_restrict_span_eq_three_of_apply_ne_zero`: over an ordered field,
  `B` has signature `(3, 3)` on their span.
* `LinearMap.BilinForm.three_le_sigPos_toQuadraticMap_of_apply_ne_zero` and
  `LinearMap.BilinForm.three_le_sigNeg_toQuadraticMap_of_apply_ne_zero`: for finite-dimensional
  `U`, both indices of inertia of `B` are at least `3`.
* `LinearMap.BilinForm.apply_eq_zero_of_sigPos_toQuadraticMap_le_two` and
  `LinearMap.BilinForm.apply_eq_zero_of_sigNeg_toQuadraticMap_le_two`: for finite-dimensional
  `U`, if either index of `B` is at most `2`, the four-fold pairing vanishes identically.
-/

public section

open Module

namespace LinearMap.BilinForm

variable {K H U : Type*} [Field K] [AddCommGroup H] [Module K H] [AddCommGroup U] [Module K U]
  (B : LinearMap.BilinForm K U) {m : H →ₗ[K] H →ₗ[K] U}

section Alternating

variable (hm : m.IsAlt) (hm' : ∀ a b c, B (m a b) (m b c) = 0)
include hm

private theorem apply_swap_left (a b c d : H) : B (m b a) (m c d) = -B (m a b) (m c d) := by
  rw [← hm.neg a b, map_neg, LinearMap.neg_apply]

private theorem apply_swap_right (a b c d : H) : B (m a b) (m d c) = -B (m a b) (m c d) := by
  rw [← hm.neg c d, map_neg]

include hm'

omit hm in
/-- Exchanging the middle two arguments negates the four-fold pairing. -/
private theorem apply_swap_mid (a b c d : H) : B (m a c) (m b d) = -B (m a b) (m c d) := by
  have h := hm' a (b + c) d
  simp only [map_add, LinearMap.add_apply, hm' a b d, hm' a c d, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem apply_eq_zero_of_eq_left (a b c : H) : B (m a b) (m a c) = 0 := by
  rw [apply_swap_left B hm, hm', neg_zero]

private theorem apply_eq_zero_of_eq_right (a b c : H) : B (m a b) (m c b) = 0 := by
  rw [apply_swap_right B hm, hm', neg_zero]

private theorem apply_eq_zero_of_eq_outer (a b c : H) : B (m a b) (m c a) = 0 := by
  rw [apply_swap_right B hm, apply_eq_zero_of_eq_left B hm hm', neg_zero]

/-- Cycling the last three arguments preserves the four-fold pairing. -/
private theorem apply_cycle (a b c d : H) : B (m a c) (m d b) = B (m a b) (m c d) := by
  rw [apply_swap_right B hm, apply_swap_mid B hm', neg_neg]

/-- Exchanging the two products preserves the four-fold pairing. -/
private theorem apply_comm (a b c d : H) : B (m c d) (m a b) = B (m a b) (m c d) := by
  rw [apply_swap_mid B hm' c a d b, apply_swap_left B hm, neg_neg, apply_cycle B hm hm']

/-- The three vectors `m a b + s • m c d`, `m a c + s • m d b`, `m a d + s • m b c` are pairwise
orthogonal, each of square `2 s B (m a b) (m c d)`. -/
private theorem apply_triple (a b c d : H) (s : K) (i j : Fin 3) :
    B (![m a b + s • m c d, m a c + s • m d b, m a d + s • m b c] i)
      (![m a b + s • m c d, m a c + s • m d b, m a d + s • m b c] j) =
      if i = j then 2 * s * B (m a b) (m c d) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [hm', apply_eq_zero_of_eq_left B hm hm', apply_eq_zero_of_eq_right B hm hm',
      apply_eq_zero_of_eq_outer B hm hm', apply_comm B hm hm' a b c d,
      apply_comm B hm hm' a c d b, apply_comm B hm hm' a d b c, apply_cycle B hm hm'] <;>
    ring

/-- If the four-fold pairing `B (m a b) (m c d)` is nonzero, the six products of `a, b, c, d` are
linearly independent: their span has dimension `6`. -/
theorem finrank_span_eq_six_of_apply_ne_zero {a b c d : H} (h : B (m a b) (m c d) ≠ 0) :
    finrank K (Submodule.span K {m a b, m a c, m a d, m b c, m b d, m c d}) = 6 := by
  have h₂ : B (m a d) (m b c) = B (m a b) (m c d) :=
    (apply_cycle B hm hm' a c d b).trans (apply_cycle B hm hm' a b c d)
  have hli : LinearIndependent K ![m a b, m a c, m a d, m b c, m b d, m c d] := by
    refine Fintype.linearIndependent_iff.mpr fun g hg i ↦ ?_
    -- Pair the relation against the product complementary to the `i`-th one.
    have := congrArg (fun y ↦ B y (![m c d, m b d, m b c, m a d, m a c, m a b] i)) hg
    fin_cases i <;>
      simpa [Fin.sum_univ_six, hm', apply_eq_zero_of_eq_left B hm hm',
        apply_eq_zero_of_eq_right B hm hm', apply_eq_zero_of_eq_outer B hm hm',
        apply_swap_mid B hm' a b c d, apply_comm B hm hm' a b c d, apply_comm B hm hm' a d b c,
        apply_comm B hm hm' a c b d, h₂, h] using this
  have hrange : Set.range ![m a b, m a c, m a d, m b c, m b d, m c d] =
      {m a b, m a c, m a d, m b c, m b d, m c d} := by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rw [← hrange, finrank_span_eq_card hli, Fintype.card_fin]

/-- For every scalar `s`, the span of the six products of `a, b, c, d` contains three pairwise
orthogonal vectors, each of square `2 s B (m a b) (m c d)`. -/
private theorem exists_iIsOrtho_restrict_span (a b c d : H) (s : K) :
    ∃ v : Fin 3 → Submodule.span K {m a b, m a c, m a d, m b c, m b d, m c d},
      (B.restrict (Submodule.span K {m a b, m a c, m a d, m b c, m b d, m c d})).iIsOrtho v ∧
      ∀ i, B (v i) (v i) = 2 * s * B (m a b) (m c d) := by
  set W := Submodule.span K {m a b, m a c, m a d, m b c, m b d, m c d}
  have hmem : ∀ x ∈ ({m a b, m a c, m a d, m b c, m b d, m c d} : Set U), x ∈ W :=
    fun x hx ↦ Submodule.subset_span hx
  have hdb : m d b ∈ W := by
    rw [← hm.neg]
    exact W.neg_mem (hmem _ (by simp))
  let t : Fin 3 → U := ![m a b + s • m c d, m a c + s • m d b, m a d + s • m b c]
  have ht : ∀ i, t i ∈ W := by
    intro i
    fin_cases i
    · exact W.add_mem (hmem _ (by simp)) (W.smul_mem _ (hmem _ (by simp)))
    · exact W.add_mem (hmem _ (by simp)) (W.smul_mem _ hdb)
    · exact W.add_mem (hmem _ (by simp)) (W.smul_mem _ (hmem _ (by simp)))
  have htri := apply_triple B hm hm' a b c d s
  exact ⟨fun i ↦ ⟨t i, ht i⟩, iIsOrtho_def.mpr fun i j hij ↦ by simpa [hij] using htri i j,
    fun i ↦ by simpa using htri i i⟩

end Alternating

variable [LinearOrder K] [IsStrictOrderedRing K]

section Span

variable (hm : m.IsAlt) (hm' : ∀ a b c, B (m a b) (m b c) = 0)
include hm hm'

/-- A nonzero four-fold pairing gives a positive-definite and a negative-definite
three-dimensional subspace inside the span of the six products. -/
private theorem three_le_sigPos_and_three_le_sigNeg_restrict_span {a b c d : H}
    (h : B (m a b) (m c d) ≠ 0) :
    3 ≤ sigPos (B.restrict
        (Submodule.span K {m a b, m a c, m a d, m b c, m b d, m c d})).toQuadraticMap ∧
      3 ≤ sigNeg (B.restrict
        (Submodule.span K {m a b, m a c, m a d, m b c, m b d, m c d})).toQuadraticMap := by
  have : FiniteDimensional K (Submodule.span K {m a b, m a c, m a d, m b c, m b d, m c d}) :=
    FiniteDimensional.span_of_finite K (Set.toFinite _)
  have hp := mul_self_pos.mpr h
  obtain ⟨v, hv, hvv⟩ := exists_iIsOrtho_restrict_span B hm hm' a b c d (B (m a b) (m c d))
  obtain ⟨w, hw, hww⟩ := exists_iIsOrtho_restrict_span B hm hm' a b c d (-B (m a b) (m c d))
  constructor
  · simpa using card_le_sigPos_toQuadraticMap_of_iIsOrtho _ hv fun i ↦ by
      rw [restrict_apply, LinearMap.domRestrict_apply, hvv]
      linarith
  · simpa using card_le_sigNeg_toQuadraticMap_of_iIsOrtho _ hw fun i ↦ by
      rw [restrict_apply, LinearMap.domRestrict_apply, hww]
      linarith

/-- A nonzero four-fold pairing gives `B` signature `(3, 3)` on the span of the six products:
both indices are at least `3` and add up to at most the dimension `6`. -/
private theorem signature_restrict_span {a b c d : H} (h : B (m a b) (m c d) ≠ 0) :
    sigPos (B.restrict
        (Submodule.span K {m a b, m a c, m a d, m b c, m b d, m c d})).toQuadraticMap = 3 ∧
      sigNeg (B.restrict
        (Submodule.span K {m a b, m a c, m a d, m b c, m b d, m c d})).toQuadraticMap = 3 := by
  have hsig := three_le_sigPos_and_three_le_sigNeg_restrict_span B hm hm' h
  have hdim := finrank_span_eq_six_of_apply_ne_zero B hm hm' h
  have : FiniteDimensional K (Submodule.span K {m a b, m a c, m a d, m b c, m b d, m c d}) :=
    FiniteDimensional.span_of_finite K (Set.toFinite _)
  have hsum := _root_.QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (B.restrict (Submodule.span K {m a b, m a c, m a d, m b c, m b d, m c d})).toQuadraticMap)
  constructor <;> omega

/-- If the four-fold pairing `B (m a b) (m c d)` is nonzero, the restriction of `B` to the span of
the six products of `a, b, c, d` has positive index `3`. -/
theorem sigPos_restrict_span_eq_three_of_apply_ne_zero {a b c d : H}
    (h : B (m a b) (m c d) ≠ 0) :
    sigPos (B.restrict
      (Submodule.span K {m a b, m a c, m a d, m b c, m b d, m c d})).toQuadraticMap = 3 :=
  (signature_restrict_span B hm hm' h).1

/-- If the four-fold pairing `B (m a b) (m c d)` is nonzero, the restriction of `B` to the span of
the six products of `a, b, c, d` has negative index `3`. -/
theorem sigNeg_restrict_span_eq_three_of_apply_ne_zero {a b c d : H}
    (h : B (m a b) (m c d) ≠ 0) :
    sigNeg (B.restrict
      (Submodule.span K {m a b, m a c, m a d, m b c, m b d, m c d})).toQuadraticMap = 3 :=
  (signature_restrict_span B hm hm' h).2

variable [FiniteDimensional K U]

/-- A nonzero four-fold pairing `B (m a b) (m c d)` forces the positive index of `B` to be at
least `3`. -/
theorem three_le_sigPos_toQuadraticMap_of_apply_ne_zero {a b c d : H}
    (h : B (m a b) (m c d) ≠ 0) : 3 ≤ sigPos B.toQuadraticMap := by
  rw [← sigPos_restrict_span_eq_three_of_apply_ne_zero B hm hm' h]
  exact _root_.QuadraticForm.sigPos_restrict_le B.toQuadraticMap _

/-- A nonzero four-fold pairing `B (m a b) (m c d)` forces the negative index of `B` to be at
least `3`. -/
theorem three_le_sigNeg_toQuadraticMap_of_apply_ne_zero {a b c d : H}
    (h : B (m a b) (m c d) ≠ 0) : 3 ≤ sigNeg B.toQuadraticMap := by
  rw [← sigNeg_restrict_span_eq_three_of_apply_ne_zero B hm hm' h]
  exact _root_.QuadraticForm.sigNeg_restrict_le B.toQuadraticMap _

/-- If the positive index of `B` is at most `2`, the four-fold pairing `B (m a b) (m c d)`
vanishes. For the intersection form of a closed oriented four-manifold with `b₂⁺ = 1` and the cup
product on `H¹`, this is the vanishing of all four-fold products of degree-one classes. -/
theorem apply_eq_zero_of_sigPos_toQuadraticMap_le_two (h : sigPos B.toQuadraticMap ≤ 2)
    (a b c d : H) : B (m a b) (m c d) = 0 := by
  by_contra hne
  have := three_le_sigPos_toQuadraticMap_of_apply_ne_zero B hm hm' hne
  omega

/-- If the negative index of `B` is at most `2`, the four-fold pairing `B (m a b) (m c d)`
vanishes. -/
theorem apply_eq_zero_of_sigNeg_toQuadraticMap_le_two (h : sigNeg B.toQuadraticMap ≤ 2)
    (a b c d : H) : B (m a b) (m c d) = 0 := by
  by_contra hne
  have := three_le_sigNeg_toQuadraticMap_of_apply_ne_zero B hm hm' hne
  omega

end Span

end LinearMap.BilinForm
