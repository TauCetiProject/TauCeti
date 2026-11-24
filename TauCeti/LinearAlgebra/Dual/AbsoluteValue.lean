/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Coordinates controlled by independent linear forms

Let `l` be a family of `#ι` linearly independent linear forms on `Kⁱ`. They span the dual space,
so each coordinate `x j` is a fixed linear combination of the values `l i x`
(`LinearIndependent.exists_sum_smul_eq_proj`). Consequently, at any absolute value `abv` on `K`,
a common bound `M` on the values `abv (l i x)` bounds every coordinate: `abv (x j) ≤ D * M`, with
`D` depending only on the forms and on `abv`.

This is how approximation domains, defined by bounds on the values of linear forms at finitely
many places, are turned into bounds on coordinates, and hence on heights.
-/

public section

namespace LinearIndependent

variable {K S ι : Type*} [Field K] [Semiring S] [PartialOrder S] [IsOrderedRing S] [Finite ι]

/-- **Coordinates are bounded by independent forms.** For `#ι` linearly independent linear forms
`l` on `Kⁱ` and an absolute value `abv` on `K`, there is `D ≥ 0` such that every coordinate of
every `x` satisfies `abv (x j) ≤ D * M` whenever `M` bounds all the values `abv (l i x)`. -/
theorem exists_forall_abv_apply_le_mul {l : ι → Module.Dual K (ι → K)}
    (hl : LinearIndependent K l) (abv : AbsoluteValue K S) :
    ∃ D : S, 0 ≤ D ∧ ∀ (x : ι → K) (M : S), (∀ i, abv (l i x) ≤ M) → ∀ j, abv (x j) ≤ D * M := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨a, ha⟩ := hl.exists_sum_smul_eq_proj
  refine ⟨∑ j, ∑ i, abv (a j i),
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abv.nonneg _, fun x M hM j ↦ ?_⟩
  have hM0 : 0 ≤ M := (abv.nonneg _).trans (hM j)
  have hxj : x j = ∑ i, a j i * l i x := by
    simpa using (LinearMap.congr_fun (ha j) x).symm
  calc abv (x j) ≤ ∑ i, abv (a j i) * abv (l i x) := by
        rw [hxj]
        exact (abv.sum_le _ _).trans_eq (by simp only [map_mul])
    _ ≤ (∑ i, abv (a j i)) * M := by
        rw [Finset.sum_mul]
        gcongr with i
        exact hM i
    _ ≤ (∑ j, ∑ i, abv (a j i)) * M := by
        gcongr ?_ * _
        exact Finset.single_le_sum (f := fun j ↦ ∑ i, abv (a j i))
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abv.nonneg _) (Finset.mem_univ j)

end LinearIndependent
