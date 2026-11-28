/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Fintype.Sigma

/-!
# Scalar-coset contributions to second moments

In a product of general linear groups over residue fields, a scalar translate of a
reduced Bessel subgroup element is determined by that element and by the scalar at
each place. Counting scalar tuples bounds the total second-moment contribution of
these cosets without requiring that the cosets be disjoint or that every tuple be
realized by a global scalar.

The estimates correspond to `New.Filling.card_inScalarCoset_le` and
`New.Filling.sum_secondMoment_inScalarCoset_le` in
`grh/src/New/Spanning/Unfolding/MomentBounds.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at revision `72fead1`.
-/

public section

open Matrix

namespace TauCeti

/-- If each element of `s` is a componentwise scalar translate of an element of `t`, the
cardinality of `s` is bounded by the number of scalar tuples times `t.card`. -/
theorem card_le_prod_card_mul_card_of_forall_exists_scalar_smul
    {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    {R : ι → Type*} [∀ i, Semiring (R i)] [∀ i, Fintype (R i)]
    {s t : Finset (∀ i, GL n (R i))}
    (h : ∀ g ∈ s, ∃ u : ∀ i, R i, ∃ a ∈ t,
      ∀ i, (↑(g i) : Matrix n n (R i)) = u i • (↑(a i) : Matrix n n (R i))) :
    s.card ≤ (∏ i, Fintype.card (R i)) * t.card := by
  classical
  let e : (∀ i, GL n (R i)) ↪ (∀ i, Matrix n n (R i)) :=
    ⟨fun g i ↦ g i, fun _ _ heq ↦ funext fun i ↦ Units.ext (congrFun heq i)⟩
  let f (u : ∀ i, R i) (a : ∀ i, GL n (R i)) (i : ι) :=
    u i • (↑(a i) : Matrix n n (R i))
  have hs : s.map e ⊆ Finset.image₂ f Finset.univ t := by
    intro X hX
    obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hX
    obtain ⟨u, a, ha, heq⟩ := h g hg
    exact Finset.mem_image₂.mpr ⟨u, Finset.mem_univ _, a, ha, (funext heq).symm⟩
  rw [← Finset.card_map e]
  exact (Finset.card_le_card hs).trans (by simpa using Finset.card_image₂_le f Finset.univ t)

/-- At two level primes, suppose each block has `f` places, with residue-field cardinality
at most `p i` on block `i`. A moment bounded pointwise by `2 D` contributes at most
`2 (p 0 * p 1)^f (t.card * D)` on the scalar translates of `t`. In the Bessel application,
`t.card * D` is the identity second moment and `t` enumerates the reduced Bessel subgroup. -/
theorem sum_secondMoment_inScalarCoset_le {n : Type*} [Fintype n] [DecidableEq n]
    {W : Fin 2 → Type*} [∀ i, Fintype (W i)]
    {F : (Σ i, W i) → Type*} [∀ w, Semiring (F w)] [∀ w, Fintype (F w)]
    {s t : Finset (∀ w, GL n (F w))} {p : Fin 2 → ℕ} {f D : ℕ}
    (hW : ∀ i, Fintype.card (W i) = f) (hF : ∀ w, Fintype.card (F w) ≤ p w.1)
    (h : ∀ g ∈ s, ∃ u : ∀ w, F w, ∃ a ∈ t,
      ∀ w, (↑(g w) : Matrix n n (F w)) = u w • (↑(a w) : Matrix n n (F w)))
    {β : (∀ w, GL n (F w)) → ℝ} (hβ : ∀ g ∈ s, β g ≤ 2 * D) :
    ∑ g ∈ s, β g ≤ 2 * (↑(p 0 * p 1) : ℝ) ^ f * (t.card * D) := by
  classical
  have hcard : s.card ≤ (p 0 * p 1) ^ f * t.card := by
    refine (card_le_prod_card_mul_card_of_forall_exists_scalar_smul h).trans ?_
    gcongr
    calc
      ∏ w, Fintype.card (F w) ≤ ∏ w : Σ i, W i, p w.1 :=
        Finset.prod_le_prod fun w _ ↦ hF w
      _ = (p 0 * p 1) ^ f := by
        simp [Fintype.prod_sigma, hW, Fin.prod_univ_two, mul_pow]
  calc
    ∑ g ∈ s, β g ≤ (s.card : ℝ) * (2 * D) := by
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul s β (2 * (D : ℝ)) hβ
    _ ≤ (((p 0 * p 1) ^ f * t.card : ℕ) : ℝ) * (2 * D) := by gcongr
    _ = _ := by push_cast; ring

end TauCeti
