/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.RingTheory.Polynomial.GaussianBinomial
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The number of subspaces of a given dimension over a finite field

For a finite division ring `K` with `q` elements and a finite `K`-vector space `V` of dimension
`n`, the number of `k`-dimensional subspaces of `V` is the Gaussian binomial coefficient
`[n k]_q`, evaluated at the integer `q` (not at its image in `K`). For `k > n` both sides are `0`.

The linearly independent `k`-tuples of `V` are counted by `card_linearIndependent`; sending a
tuple to its span partitions them according to the `k`-dimensional subspace they span, and the
tuples spanning a given subspace `W` are exactly the linearly independent `k`-tuples of `W`. The
count follows from the product formula `TauCeti.gaussianBinomial_mul_prod_pow_sub_pow`.

## Main results

* `TauCeti.card_submodule_finrank_eq_gaussianBinomial`: the number of `k`-dimensional subspaces
  of `V` is `[finrank K V k]_q`.

## References

* R. P. Stanley, *Enumerative Combinatorics, Volume 1*, 2nd ed., Proposition 1.7.2.
-/

public section

open Finset Module Submodule

namespace TauCeti

variable {K V : Type*} [DivisionRing K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]

/-- The linearly independent `k`-tuples of `V` spanning a `k`-dimensional subspace `W` are the
linearly independent `k`-tuples of `W`. -/
private def fiberEquiv {k : ℕ} (W : {W : Submodule K V // finrank K W = k}) :
    {s : {s : Fin k → V // LinearIndependent K s} // span K (Set.range s.val) = W.val} ≃
      {t : Fin k → W.val // LinearIndependent K t} where
  toFun s := ⟨fun i ↦ ⟨s.val.val i, s.property.le (subset_span (Set.mem_range_self i))⟩,
    LinearIndependent.of_comp W.val.subtype s.val.property⟩
  invFun t := ⟨⟨W.val.subtype ∘ t.val, t.property.map' _ (ker_subtype _)⟩, by
    rw [Set.range_comp, span_image, t.property.span_eq_top_of_card_eq_finrank'
      (by rw [Fintype.card_fin, W.property]), map_subtype_top]⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The number of `k`-dimensional subspaces** of a finite vector space `V` over a finite
division ring `K` with `q` elements is the Gaussian binomial coefficient `[finrank K V k]_q`. -/
theorem card_submodule_finrank_eq_gaussianBinomial (k : ℕ) :
    Nat.card {W : Submodule K V // finrank K W = k} =
      gaussianBinomial (Fintype.card K) (finrank K V) k := by
  classical
  have := Fintype.ofFinite V
  set q := Fintype.card K
  set n := finrank K V
  rcases lt_or_ge n k with hnk | hkn
  · rw [gaussianBinomial_eq_zero_of_lt _ hnk, Nat.card_eq_zero]
    exact .inl ⟨fun W ↦ (W.val.finrank_le.trans_lt hnk).ne W.property⟩
  let Sub := {W : Submodule K V // finrank K W = k}
  let span' : {s : Fin k → V // LinearIndependent K s} → Sub := fun s ↦
    ⟨span K (Set.range s.val), by rw [finrank_span_eq_card s.property, Fintype.card_fin]⟩
  -- Every subspace in the image is spanned by as many tuples as there are independent
  -- `k`-tuples in a `k`-dimensional space.
  have hfiber (W : Sub) : Nat.card {s // span' s = W} = ∏ i : Fin k, (q ^ k - q ^ i.val) := by
    rw [Nat.card_congr ((Equiv.subtypeEquivRight fun s ↦ Subtype.ext_iff).trans (fiberEquiv W)),
      card_linearIndependent W.property.ge, W.property]
  have hcount : Nat.card Sub * ∏ i : Fin k, (q ^ k - q ^ i.val) =
      ∏ i : Fin k, (q ^ n - q ^ i.val) := by
    rw [← card_linearIndependent hkn, Nat.card_congr (Equiv.sigmaFiberEquiv span').symm,
      Nat.card_sigma, sum_congr rfl fun W _ ↦ hfiber W]
    simp [Nat.card_eq_fintype_card]
  have hq : 1 < q := Fintype.one_lt_card
  have hle {m : ℕ} (hm : k ≤ m) (i : Fin k) : q ^ i.val ≤ q ^ m :=
    Nat.pow_le_pow_right hq.le (i.isLt.le.trans hm)
  have hpos : 0 < ∏ i : Fin k, (q ^ k - q ^ i.val) :=
    prod_pos fun i _ ↦ Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hq i.isLt)
  refine Nat.eq_of_mul_eq_mul_right hpos (hcount.trans ?_)
  -- Compare with the product formula for the Gaussian coefficient in `ℤ`.
  have key := gaussianBinomial_mul_prod_pow_sub_pow (q : ℤ) n k
  rw [← Fin.prod_univ_eq_prod_range, ← Fin.prod_univ_eq_prod_range] at key
  have hG : ((gaussianBinomial q n k : ℕ) : ℤ) = gaussianBinomial (q : ℤ) n k :=
    map_gaussianBinomial (Nat.castRingHom ℤ) q n k
  apply Nat.cast_injective (R := ℤ)
  push_cast [hG, Nat.cast_sub, hle le_rfl, hle hkn]
  exact key.symm

end TauCeti
