/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Topology.CWComplex.Classical.Subcomplex

/-!
# Additivity of the Euler characteristic along subcomplexes

Let `E` be a subcomplex of a finite relative CW complex `(C, D)`. The cells of `C` split into the
cells of `E` and the cells of `C` relative to `E`
(`Topology.RelCWComplex.Subcomplex.relCWComplex`), so the alternating cell counts add up. By
relative Euler--Poincaré, applied to the three pairs `(C, D)`, `(E, D)` and `(C, E)`, the
alternating sums of the dimensions of relative singular homology add up in the same way:

```text
χ(C, D) = χ(E, D) + χ(C, E).
```

For an absolute finite CW complex `C` this reads `χ(C) = χ(E) + χ(C, E)`, where `χ(C, E)` is the
alternating sum of the dimensions of `Hᵢ(C, E; k)` over a division ring `k`. Along a finite
filtration `E₀ ≤ E₁ ≤ ⋯ ≤ Eₘ` of `C` by subcomplexes, the Euler characteristic of `Eₘ` is that of
`E₀` plus the sum of the relative Euler characteristics of the strata `(Eⱼ₊₁, Eⱼ)`.

## Main results

* `TauCeti.cwEulerChar_eq_add_finsum_card_compl`: the alternating cell count of `C` is that of a
  subcomplex `E` plus the alternating count of the cells of `C` not in `E`.
* `TauCeti.finsum_finrank_singularHomology_subcomplexPair`: **relative Euler--Poincaré** for the
  pair `(C, E)`.
* `TauCeti.finsum_finrank_singularHomology_eq_add_subcomplexPair`: `χ(C, D) = χ(E, D) + χ(C, E)`
  for relative singular homology with finite-dimensional coefficients.
* `TauCeti.eulerChar_eq_add_finsum_finrank_singularHomology`: `χ(C) = χ(E) + χ(C, E)` for a finite
  CW complex `C`.
* `TauCeti.eulerChar_eq_add_sum_finsum_finrank_singularHomology`: additivity along a finite
  filtration by subcomplexes.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.44.
-/

public section

noncomputable section

open CategoryTheory Module Topology Topology.RelCWComplex AlgebraicTopology

universe w

namespace TauCeti

section Relative

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]

/-- The alternating cell count of a finite relative CW complex is that of a subcomplex `E` plus
the alternating count of the cells not in `E`, which are the cells of the CW structure on `C`
relative to `E`. -/
theorem cwEulerChar_eq_add_finsum_card_compl [RelCWComplex.Finite C] (E : Subcomplex C) :
    cwEulerChar C = cwEulerChar (E : Set X) + ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Nat.card ↥(E.I n)ᶜ := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D))
  have hcompl : ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Nat.card ↥(E.I n)ᶜ =
      ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * Nat.card ↥(E.I n)ᶜ :=
    finsum_eq_sum_of_support_subset _ fun n hn ↦ by
      by_contra hn'
      have := hN n (by simpa using hn')
      have : IsEmpty ↥(E.I n)ᶜ := ⟨fun i ↦ isEmptyElim (i : cell C n)⟩
      exact (Function.mem_support.1 hn) (by rw [Nat.card_of_isEmpty, Nat.cast_zero, mul_zero])
  rw [cwEulerChar_eq_sum_range C hN, cwEulerChar_eq_sum_range (E : Set X) fun n hn ↦ by
    have := hN n hn
    rw [Subcomplex.cell_def]
    infer_instance, hcompl, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have := FiniteType.finite_cell (C := C) (D := D) n
  rw [← mul_add, Subcomplex.cell_def, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    ← Nat.cast_add, Set.ncard_add_ncard_compl]

variable {k : Type w} [DivisionRing k] (M : ModuleCat.{w} k) [Module.Finite k M]

/-- **Relative Euler--Poincaré for a subcomplex.** For a subcomplex `E` of a finite relative CW
complex `C`, the alternating sum of the dimensions of `Hᵢ(C, E; M)` is `dim M` times the
alternating count of the cells of `C` not in `E`. -/
theorem finsum_finrank_singularHomology_subcomplexPair [RelCWComplex.Finite C]
    (E : Subcomplex C) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k
        ((TopPair.ofInclusion (X := TopCat.of X) E.subset_complex).singularHomology M i :
          ModuleCat k) =
      finrank k M * ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Nat.card ↥(E.I n)ᶜ := by
  have := @finsum_finrank_singularHomology_complexBasePair X _ _ (E : Set X) C E.relCWComplex
    k _ M _ E.finite_relCWComplex
  rw [@complexBasePair_eq_ofInclusion X _ _ (E : Set X) C E.relCWComplex,
    @cwEulerChar_def X _ (E : Set X) C E.relCWComplex] at this
  simpa only [Nat.card_congr (E.relCWComplexCellEquiv _)] using this

/-- **Additivity of the Euler characteristic along a subcomplex.** For a subcomplex `E` of a
finite relative CW complex `(C, D)` and finite-dimensional coefficients `M`, the alternating sum
of the dimensions of relative singular homology satisfies `χ(C, D) = χ(E, D) + χ(C, E)`. -/
theorem finsum_finrank_singularHomology_eq_add_subcomplexPair [RelCWComplex.Finite C]
    (E : Subcomplex C) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k
        ((TopPair.ofInclusion (X := TopCat.of X) (base_subset_complex (C := C))).singularHomology
          M i : ModuleCat k) =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k
          ((TopPair.ofInclusion (X := TopCat.of X) E.base_subset).singularHomology M i :
            ModuleCat k) +
        ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k
          ((TopPair.ofInclusion (X := TopCat.of X) E.subset_complex).singularHomology M i :
            ModuleCat k) := by
  have hC := finsum_finrank_singularHomology_complexBasePair C M
  have hE := finsum_finrank_singularHomology_complexBasePair (E : Set X) M
  rw [complexBasePair_eq_ofInclusion] at hC hE
  rw [hC, hE, finsum_finrank_singularHomology_subcomplexPair C M E, ← mul_add,
    cwEulerChar_eq_add_finsum_card_compl C E]

end Relative

section Absolute

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
  [RelCWComplex.Finite C] (k : Type w) [DivisionRing k]

/-- **Additivity of the Euler characteristic along a subcomplex.** For a subcomplex `E` of a
finite CW complex `C`, `χ(C) = χ(E) + χ(C, E)`, where the relative Euler characteristic `χ(C, E)`
is the alternating sum of the dimensions of `Hᵢ(C, E; k)` over any division ring `k`. -/
theorem eulerChar_eq_add_finsum_finrank_singularHomology (E : Subcomplex C) :
    eulerChar C = eulerChar (E : Set X) + ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k
      ((TopPair.ofInclusion (X := TopCat.of X) E.subset_complex).singularHomology
        (ModuleCat.of k k) i : ModuleCat k) := by
  have hk : finrank k (ModuleCat.of k k) = 1 := finrank_self k
  rw [eulerChar_cwComplex, eulerChar_cwComplex,
    finsum_finrank_singularHomology_subcomplexPair C (ModuleCat.of k k) E, hk, Nat.cast_one,
    one_mul]
  exact cwEulerChar_eq_add_finsum_card_compl C E

/-- **Additivity of the Euler characteristic along a filtration by subcomplexes.** For a finite
filtration `E₀ ≤ E₁ ≤ ⋯ ≤ Eₘ` by subcomplexes of a finite CW complex, the Euler characteristic
of `Eₘ` is that of `E₀` plus the relative Euler characteristics `χ(Eⱼ₊₁, Eⱼ)` of the strata,
computed by singular homology over any division ring `k`. -/
theorem eulerChar_eq_add_sum_finsum_finrank_singularHomology {E : ℕ → Subcomplex C} {m : ℕ}
    (hE : ∀ j < m, E j ≤ E (j + 1)) :
    eulerChar (E m : Set X) = eulerChar (E 0 : Set X) +
      ∑ j : Fin m, ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k
        ((TopPair.ofInclusion (X := TopCat.of X)
          (SetLike.coe_subset_coe.2 (hE j j.isLt))).singularHomology
            (ModuleCat.of k k) i : ModuleCat k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc, ← add_assoc, ← ih fun j hj ↦ hE j (by omega)]
    have h := eulerChar_eq_add_finsum_finrank_singularHomology (E (m + 1) : Set X) k
      (Subcomplex.ofLE (hE m m.lt_succ_self))
    rw [(Homeomorph.setCongr (Subcomplex.coe_ofLE (hE m m.lt_succ_self))).eulerChar_eq] at h
    have hpair : ∀ {A : Set X}, A = E m → ∀ hAE : A ⊆ E (m + 1),
        TopPair.ofInclusion (X := TopCat.of X) hAE =
          TopPair.ofInclusion (X := TopCat.of X)
            (SetLike.coe_subset_coe.2 (hE m m.lt_succ_self)) := by
      rintro _ rfl _
      rfl
    rwa [hpair (Subcomplex.coe_ofLE _)] at h

end Absolute

end TauCeti
