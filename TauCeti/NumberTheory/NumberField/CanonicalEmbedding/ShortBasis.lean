/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.House
import Mathlib.Algebra.Algebra.Hom.Rat
import TauCeti.Algebra.Algebra.ProductSpan
import TauCeti.Algebra.Order.BigOperators.Fin
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Basic
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IntegerLattice

/-!
# A rational basis of short algebraic integers

Let `K` be a number field of degree `n` with root discriminant `δ = |discr K| ^ (1 / n)`. This file
shows that `K` has a basis over `ℚ` made of algebraic integers whose houses are at most `δ ^ 2`
(`TauCeti.NumberField.exists_basis_isIntegral_house_le_rootDiscr_sq`). The basis need not be a
`ℤ`-basis of `𝓞 K`: house bounds do not control the index of its `ℤ`-span.

The first step applies Minkowski's second theorem to the lattice `𝓞 K` in the mixed space and the
closed unit ball of its sup norm, whose gauge at `x : K` is the house of `x`. Independent lattice
vectors attaining the successive minima give `ℚ`-linearly independent algebraic integers
`ω 0, …, ω (n - 1)` with nondecreasing houses, each at least `1`, whose product is at most
`√|discr K| = δ ^ (n / 2)` (`TauCeti.NumberField.exists_linearIndependent_house_le_rootDiscr`).
Since `house (ω i) ^ (n - i)` is at most that product, every `ω i` with `2 * i ≤ n` has house at
most `δ`. There are `n / 2 + 1 > n / 2` such elements, so the products `ω i * ω j` of two of them
span `K` over `ℚ` (`Submodule.mul_eq_top_of_finrank_lt_add`). These products are algebraic integers
of house at most `δ ^ 2`, and a basis of `K` can be extracted from them.

## Main results

* `TauCeti.NumberField.exists_linearIndependent_house_le_rootDiscr`: `ℚ`-linearly independent
  algebraic integers `ω 0, …, ω (n - 1)` with nondecreasing houses, product of houses at most
  `√|discr K|`, and `house (ω i) ≤ rootDiscr K` whenever `2 * i ≤ n`.
* `TauCeti.NumberField.exists_basis_isIntegral_house_le_rootDiscr_sq`: a `ℚ`-basis of `K` made of
  algebraic integers of house at most `rootDiscr K ^ 2`.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. (2) **192** (2020), no. 2,
  487–497, §2, Proposition 1 and its proof.
-/

public section

open Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding Submodule
open scoped Pointwise

namespace TauCeti.NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **Short independent algebraic integers.** A number field `K` of degree `n` contains
`ℚ`-linearly independent algebraic integers `ω 0, …, ω (n - 1)` whose houses are nondecreasing,
whose product of houses is at most `√|discr K|`, and such that `house (ω i) ≤ rootDiscr K` for every
`i` with `2 * i ≤ n`, that is, for the first `n / 2 + 1` of them. The family need not be a
`ℤ`-basis of `𝓞 K`. -/
theorem exists_linearIndependent_house_le_rootDiscr :
    ∃ ω : Fin (finrank ℚ K) → 𝓞 K,
      LinearIndependent ℚ (fun i ↦ (ω i : K)) ∧
      Monotone (fun i ↦ house (ω i : K)) ∧
      ∏ i, house (ω i : K) ≤ √|(discr K : ℝ)| ∧
      ∀ i : Fin (finrank ℚ K), 2 * (i : ℕ) ≤ finrank ℚ K → house (ω i : K) ≤ rootDiscr K := by
  classical
  set n := finrank ℚ K
  let U : ConvexBody (mixedSpace K) := ConvexBody.closedBall 0 1 zero_le_one
  let L := mixedEmbedding.integerLattice K
  have hU : (0 : mixedSpace K) ∈ interior (U : Set (mixedSpace K)) :=
    ConvexBody.mem_interior_closedBall_self 0 zero_lt_one
  -- Independent lattice vectors attaining the successive minima, reindexed by `Fin n`.
  obtain ⟨a, ha, haL⟩ := ZLattice.exists_linearIndependent_gauge_eq_successiveMin L hU
  let e : Fin n ≃ Fin (finrank ℝ (mixedSpace K)) := finCongr (mixedEmbedding.finrank K).symm
  let ω : Fin n → 𝓞 K := fun i ↦ (integerLatticeEquiv K).symm ⟨a (e i), (haL (e i)).1⟩
  have hω (i : Fin n) : mixedEmbedding K (ω i : K) = a (e i) :=
    mixedEmbedding_integerLatticeEquiv_symm _
  have hhouse (i : Fin n) : house (ω i : K) = ZLattice.successiveMin L U (e i) := by
    rw [← norm_mixedEmbedding, hω, ← (haL (e i)).2, ConvexBody.coe_closedBall,
      gauge_closedBall zero_le_one, div_one]
  have hone (i : Fin n) : 1 ≤ house (ω i : K) :=
    (hhouse i).symm ▸ one_le_successiveMin_integerLattice K (e i)
  have hmono : Monotone fun i ↦ house (ω i : K) := fun i j hij ↦ by
    simp only [hhouse]
    exact ZLattice.monotone_successiveMin L hU (by simpa [e] using hij)
  have hprod : ∏ i, house (ω i : K) ≤ √|(discr K : ℝ)| := by
    simp only [hhouse]
    rw [e.prod_comp (ZLattice.successiveMin L U)]
    exact prod_successiveMin_integerLattice_le K
  refine ⟨ω, ?_, hmono, hprod, fun i hi ↦ ?_⟩
  · -- `ℝ`-independence of the mixed images gives `ℚ`-independence in `K`.
    refine LinearIndependent.of_comp (mixedEmbedding K).toRatAlgHom.toLinearMap ?_
    convert (ha.comp e e.injective).restrict_scalars' ℚ using 1
    exact funext hω
  · -- `house (ω i) ^ (n - i)` is at most the product of all houses, and `n ≤ 2 * (n - i)`.
    have htail := Fin.pow_sub_le_prod_of_monotone hone hmono i
    have hpow : house (ω i : K) ^ n ≤ |(discr K : ℝ)| :=
      calc house (ω i : K) ^ n ≤ house (ω i : K) ^ (2 * (n - i)) :=
            pow_le_pow_right₀ (hone i) (by omega)
        _ = (house (ω i : K) ^ (n - i)) ^ 2 := pow_mul' _ _ _
        _ ≤ √|(discr K : ℝ)| ^ 2 :=
            pow_le_pow_left₀ (pow_nonneg (house_nonneg _) _) (htail.trans hprod) 2
        _ = |(discr K : ℝ)| := Real.sq_sqrt (abs_nonneg _)
    have hn : (0 : ℝ) < n := Nat.cast_pos.2 finrank_pos
    rw [rootDiscr_def, Real.le_rpow_inv_iff_of_pos (house_nonneg _) (by positivity) hn,
      Real.rpow_natCast, Int.cast_abs]
    exact hpow

/-- **A rational basis of short algebraic integers** (Couveignes). Every number field `K` has a
basis over `ℚ` made of algebraic integers whose houses are at most `rootDiscr K ^ 2`. Its members
are `ℤ`-linearly independent, but their `ℤ`-span need not be `𝓞 K`. -/
theorem exists_basis_isIntegral_house_le_rootDiscr_sq :
    ∃ b : Basis (Fin (finrank ℚ K)) ℚ K,
      (∀ i, IsIntegral ℤ (b i)) ∧ ∀ i, house (b i) ≤ rootDiscr K ^ 2 := by
  obtain ⟨ω, hli, -, -, hshort⟩ := exists_linearIndependent_house_le_rootDiscr K
  have hn : 0 < finrank ℚ K := finrank_pos
  -- The first `m = finrank ℚ K / 2 + 1` members of `ω` have house at most `rootDiscr K`.
  have hmn : finrank ℚ K / 2 + 1 ≤ finrank ℚ K := by omega
  let ω' : Fin (finrank ℚ K / 2 + 1) → 𝓞 K := fun j ↦ ω (Fin.castLE hmn j)
  have hshort' (j : Fin (finrank ℚ K / 2 + 1)) : house (ω' j : K) ≤ rootDiscr K :=
    hshort _ (by simp only [Fin.val_castLE]; omega)
  -- They span a subspace `V` with `finrank ℚ K < 2 * dim V`, so their products span `K`.
  have hV : finrank ℚ (span ℚ (Set.range fun j ↦ (ω' j : K))) = finrank ℚ K / 2 + 1 := by
    have hli' : LinearIndependent ℚ fun j ↦ (ω' j : K) := hli.comp _ (Fin.castLE_injective hmn)
    rw [finrank_span_eq_card hli', Fintype.card_fin]
  have htop : span ℚ (Set.range fun j ↦ (ω' j : K)) * span ℚ (Set.range fun j ↦ (ω' j : K)) = ⊤ :=
    mul_eq_top_of_finrank_lt_add (by rw [hV]; omega)
  rw [span_mul_span] at htop
  -- Every such product is an algebraic integer of house at most `rootDiscr K ^ 2`.
  have hprod : ∀ x ∈ Set.range (fun j ↦ (ω' j : K)) * Set.range (fun j ↦ (ω' j : K)),
      IsIntegral ℤ x ∧ house x ≤ rootDiscr K ^ 2 := by
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    refine ⟨(ω' i).isIntegral_coe.mul (ω' j).isIntegral_coe, ?_⟩
    calc house ((ω' i : K) * ω' j) ≤ house (ω' i : K) * house (ω' j : K) := house_mul_le _ _
      _ ≤ rootDiscr K * rootDiscr K :=
          mul_le_mul (hshort' i) (hshort' j) (house_nonneg _) ((house_nonneg _).trans (hshort' i))
      _ = rootDiscr K ^ 2 := (sq _).symm
  -- Extract a basis from the spanning products and index it by `Fin (finrank ℚ K)`.
  let b := Basis.ofSpan htop.ge
  have hb (i : Fin (finrank ℚ K)) := hprod _ (Basis.ofSpan_subset htop.ge
    ⟨(b.indexEquiv (finBasis ℚ K)).symm i, rfl⟩)
  refine ⟨b.reindex (b.indexEquiv (finBasis ℚ K)), fun i ↦ ?_, fun i ↦ ?_⟩ <;>
    rw [Basis.reindex_apply]
  exacts [(hb i).1, (hb i).2]

end TauCeti.NumberField
