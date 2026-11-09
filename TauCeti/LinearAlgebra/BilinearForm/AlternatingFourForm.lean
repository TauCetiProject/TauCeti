/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Pairings of products through an alternating four-form

Let `B` be a bilinear form on a finite-dimensional space `N` over an ordered field, and let
`m : V → V → N` be a product whose pairings are an alternating four-form `F` on `V`:
`B (m a b) (m c d) = F ![a, b, c, d]`. The model is the cohomology of a closed oriented
four-manifold `X`: `V = H¹(X; ℝ)`, `N = H²(X; ℝ)`, `m` is the cup product, `B` is the intersection
pairing and `F a b c d = ⟨a ∪ b ∪ c ∪ d, [X]⟩`.

If `F` is nonzero, say `t = F ![a, b, c, d] ≠ 0`, then the six products of `a, b, c, d` span a
subspace of `N` on which the intersection form has both indices of inertia at least three. Indeed
the three vectors `m a b + t • m c d`, `m a d + t • m b c`, `m a c - t • m b d` are pairwise
orthogonal for `B`, and `B` takes the value `2 t²` on each of them; the negative index follows by
applying this to `-B`.

Consequently, if the positive (or negative) index of inertia of `B` is at most two, every
fourfold pairing `B (m a b) (m c d)` vanishes. For a closed oriented four-manifold with `b₂⁺ ≤ 2`,
in particular `b₂⁺ = 1`, the fourfold cup products of degree-one classes therefore pair to zero
with the fundamental class.

## Main results

* `LinearMap.BilinForm.three_le_sigPos_toQuadraticMap_of_alternatingMap`,
  `LinearMap.BilinForm.three_le_sigNeg_toQuadraticMap_of_alternatingMap`: a nonzero alternating
  four-form of pairings forces both indices of inertia of `B` to be at least three.
* `LinearMap.BilinForm.apply_eq_zero_of_alternatingMap_of_sigPos_lt_three`,
  `LinearMap.BilinForm.apply_eq_zero_of_alternatingMap_of_sigNeg_lt_three`: if either index of
  inertia of `B` is at most two, all such pairings vanish.

## References

This vanishing enters the wall-crossing formula for Seiberg–Witten invariants of four-manifolds
with `b₂⁺ = 1`, see

* C. Okonek and A. Teleman, *Seiberg–Witten invariants for manifolds with `b₊ = 1` and the
  universal wall crossing formula*, Internat. J. Math. 7 (1996), 811–832.
-/

public section

open QuadraticMap

namespace LinearMap.BilinForm

variable {K V N : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup N] [Module K N]

section FourForm

variable (F : V [⋀^Fin 4]→ₗ[K] K)

/-- An alternating four-form changes sign when two of its arguments are exchanged. -/
private theorem apply_eq_neg_of_comp_swap {v w : Fin 4 → V} {i j : Fin 4} (hij : i ≠ j)
    (hw : v ∘ Equiv.swap i j = w) : F v = -F w := by
  rw [← hw, F.map_swap v hij, neg_neg]

/-- An alternating four-form changes sign when its first two arguments are exchanged. -/
private theorem apply_swap_zero_one (x y z w : V) : F ![x, y, z, w] = -F ![y, x, z, w] :=
  apply_eq_neg_of_comp_swap F (i := 0) (j := 1) (by decide) (by
    ext k; fin_cases k <;> simp [Equiv.swap_apply_of_ne_of_ne])

/-- An alternating four-form changes sign when its middle two arguments are exchanged. -/
private theorem apply_swap_one_two (x y z w : V) : F ![x, y, z, w] = -F ![x, z, y, w] :=
  apply_eq_neg_of_comp_swap F (i := 1) (j := 2) (by decide) (by
    ext k; fin_cases k <;> simp [Equiv.swap_apply_of_ne_of_ne])

/-- An alternating four-form changes sign when its last two arguments are exchanged. -/
private theorem apply_swap_two_three (x y z w : V) : F ![x, y, z, w] = -F ![x, y, w, z] :=
  apply_eq_neg_of_comp_swap F (i := 2) (j := 3) (by decide) (by
    ext k; fin_cases k <;> simp [Equiv.swap_apply_of_ne_of_ne])

/-- An alternating four-form is unchanged when its two pairs of arguments are exchanged. -/
private theorem apply_swap_pairs (x y z w : V) : F ![x, y, z, w] = F ![z, w, x, y] := by
  rw [apply_swap_one_two, apply_swap_zero_one, apply_swap_two_three, apply_swap_one_two]
  ring

end FourForm

variable {B : LinearMap.BilinForm K N} {m : V → V → N} {F : V [⋀^Fin 4]→ₗ[K] K}

/-- If the pairings `B (m a b) (m c d)` form an alternating four-form `F` and
`t = F ![a, b, c, d]`, then the vectors `m a b + t • m c d`, `m a d + t • m b c` and
`m a c - t • m b d` are pairwise orthogonal for `B`, and the quadratic form of `B` takes the value
`2 t²` on each of them. -/
private theorem isOrthoᵢ_and_toQuadraticMap_apply
    (hF : ∀ a b c d, B (m a b) (m c d) = F ![a, b, c, d]) (a b c d : V) :
    letI t := F ![a, b, c, d]
    (polarBilin B.toQuadraticMap).IsOrthoᵢ
        ![m a b + t • m c d, m a d + t • m b c, m a c - t • m b d] ∧
      ∀ i, B.toQuadraticMap (![m a b + t • m c d, m a d + t • m b c, m a c - t • m b d] i) =
        2 * (t * t) := by
  -- A pairing in which a vector occurs in both factors vanishes.
  have h₀₂ (x y z : V) : B (m x y) (m x z) = 0 := by
    rw [hF]; exact F.map_eq_zero_of_eq _ (i := 0) (j := 2) rfl (by decide)
  have h₀₃ (x y z : V) : B (m x y) (m z x) = 0 := by
    rw [hF]; exact F.map_eq_zero_of_eq _ (i := 0) (j := 3) rfl (by decide)
  have h₁₂ (x y z : V) : B (m y x) (m x z) = 0 := by
    rw [hF]; exact F.map_eq_zero_of_eq _ (i := 1) (j := 2) rfl (by decide)
  have h₁₃ (x y z : V) : B (m y x) (m z x) = 0 := by
    rw [hF]; exact F.map_eq_zero_of_eq _ (i := 1) (j := 3) rfl (by decide)
  -- The pairings of complementary products, in terms of `t = F ![a, b, c, d]`.
  have hcdab : B (m c d) (m a b) = F ![a, b, c, d] := by rw [hF, apply_swap_pairs]
  have hadbc : B (m a d) (m b c) = F ![a, b, c, d] := by
    rw [hF, apply_swap_one_two, apply_swap_two_three, neg_neg]
  have hbcad : B (m b c) (m a d) = F ![a, b, c, d] := by
    rw [hF, apply_swap_pairs, ← hF, hadbc]
  have hacbd : B (m a c) (m b d) = -F ![a, b, c, d] := by rw [hF, apply_swap_one_two]
  have hbdac : B (m b d) (m a c) = -F ![a, b, c, d] := by
    rw [hF, apply_swap_pairs, ← hF, hacbd]
  refine ⟨LinearMap.isOrthoᵢ_def.2 fun i j hij ↦ ?_, fun i ↦ ?_⟩
  · rw [polarBilin_apply_apply, BilinMap.polar_toQuadraticMap]
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | simp [h₀₂, h₀₃, h₁₂, h₁₃]
  · fin_cases i <;>
      simp [BilinMap.toQuadraticMap_apply, h₀₂, hF a b c d, hcdab, hadbc, hbcad, hacbd, hbdac] <;>
      ring

/-- The pairings of `-B` are the alternating four-form `-F`. -/
private theorem neg_apply_apply_eq (hF : ∀ a b c d, B (m a b) (m c d) = F ![a, b, c, d])
    (a b c d : V) : (-B) (m a b) (m c d) = (-F) ![a, b, c, d] := by
  simp [hF]

variable (B) [LinearOrder K] [IsStrictOrderedRing K] [FiniteDimensional K N]

/-- **A nonzero alternating four-form of pairings forces a positive index of inertia of at least
three.** If the pairings `B (m a b) (m c d)` of a product `m : V → V → N` form a nonzero alternating
four-form on `V`, then the quadratic form of `B` is positive definite on a three-dimensional
subspace of `N`. -/
theorem three_le_sigPos_toQuadraticMap_of_alternatingMap
    (hF : ∀ a b c d, B (m a b) (m c d) = F ![a, b, c, d])
    (hF₀ : F ≠ 0) : 3 ≤ sigPos B.toQuadraticMap := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 hF₀
  have hv' : ![v 0, v 1, v 2, v 3] = v := by
    ext i
    fin_cases i <;> rfl
  have ht₀ : F ![v 0, v 1, v 2, v 3] ≠ 0 := by simpa [hv'] using hv
  obtain ⟨horth, hval⟩ := isOrthoᵢ_and_toQuadraticMap_apply hF (v 0) (v 1) (v 2) (v 3)
  simpa using QuadraticForm.card_le_sigPos_of_isOrthoᵢ horth fun i ↦ by
    rw [hval]
    exact mul_pos two_pos (mul_self_pos.2 ht₀)

/-- **A nonzero alternating four-form of pairings forces a negative index of inertia of at least
three.** If the pairings `B (m a b) (m c d)` of a product `m : V → V → N` form a nonzero alternating
four-form on `V`, then the quadratic form of `B` is negative definite on a three-dimensional
subspace of `N`. -/
theorem three_le_sigNeg_toQuadraticMap_of_alternatingMap
    (hF : ∀ a b c d, B (m a b) (m c d) = F ![a, b, c, d])
    (hF₀ : F ≠ 0) : 3 ≤ sigNeg B.toQuadraticMap := by
  simpa [BilinMap.toQuadraticMap_neg] using
    three_le_sigPos_toQuadraticMap_of_alternatingMap (-B) (neg_apply_apply_eq hF)
      (neg_ne_zero.2 hF₀)

/-- **Vanishing of fourfold pairings when the positive index of inertia is small.** If the
pairings `B (m a b) (m c d)` of a product `m : V → V → N` form an alternating four-form and the
positive index of inertia of `B` is at most two, then all of these pairings vanish. -/
theorem apply_eq_zero_of_alternatingMap_of_sigPos_lt_three
    (hF : ∀ a b c d, B (m a b) (m c d) = F ![a, b, c, d])
    (hsig : sigPos B.toQuadraticMap < 3) (a b c d : V) : B (m a b) (m c d) = 0 := by
  have hF₀ : F = 0 := by
    by_contra hF₀
    exact (B.three_le_sigPos_toQuadraticMap_of_alternatingMap hF hF₀).not_gt hsig
  rw [hF, hF₀, _root_.zero_apply]

/-- **Vanishing of fourfold pairings when the negative index of inertia is small.** If the
pairings `B (m a b) (m c d)` of a product `m : V → V → N` form an alternating four-form and the
negative index of inertia of `B` is at most two, then all of these pairings vanish. -/
theorem apply_eq_zero_of_alternatingMap_of_sigNeg_lt_three
    (hF : ∀ a b c d, B (m a b) (m c d) = F ![a, b, c, d])
    (hsig : sigNeg B.toQuadraticMap < 3) (a b c d : V) : B (m a b) (m c d) = 0 := by
  simpa using apply_eq_zero_of_alternatingMap_of_sigPos_lt_three (-B) (neg_apply_apply_eq hF)
    (by simpa [BilinMap.toQuadraticMap_neg] using hsig) a b c d

end LinearMap.BilinForm
