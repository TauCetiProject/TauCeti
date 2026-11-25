/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring

/-!
# Proper-face sums

For a finite index type `ι` and coefficients `c : Finset ι → R`, the *proper-face sum*

```text
B_c(x) = ∑_{s ⊊ ι} c_s ∏_{i ∈ s} x_i
```

runs over the proper subsets of `ι`: it is a multiaffine polynomial in `x` whose top monomial
`∏_i x_i` is missing (the coefficient `c univ` is never used). This file gives the definition and
its order-free API: linearity in the coefficients, single coefficients, reindexing and
translation of the variables.

## Main definitions

* `TauCeti.properFaceSum c x`: the proper-face sum `B_c(x)`.

## Main results

* `TauCeti.properFaceSum_add`, `TauCeti.properFaceSum_smul`, `TauCeti.properFaceSum_equiv`:
  linearity in the coefficients and invariance under reindexing.
* `TauCeti.properFaceSum_add_vec`: translating `x` by a vector `a` gives a proper-face sum
  with explicit new coefficients.

The order-theoretic bounds, including the saving at the smallest coordinate, are in
`TauCeti.Algebra.Order.BigOperators.ProperFace`, and the corresponding `MvPolynomial`,
`TauCeti.properFacePolynomial`, is in `TauCeti.Algebra.MvPolynomial.ProperFace`.

## References

* Weibo Fu, *Sharp bounds for multiplicities of Bianchi modular forms*, Ann. of Math. 200
  (2024), 123–152; arXiv:2201.11190, Theorem 1.2, Theorem 1.4 and §§6–7.
-/

public section

namespace TauCeti

open Finset

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- The proper-face sum `B_c(x) = ∑_{s ⊊ ι} c_s ∏_{i ∈ s} x_i`: the multiaffine polynomial with
coefficients `c` in which the top monomial `∏_i x_i` is omitted. The value `c univ` is never
used. -/
def properFaceSum (c : Finset ι → R) (x : ι → R) : R :=
  ∑ s ∈ (univ : Finset ι).ssubsets, c s * ∏ i ∈ s, x i

theorem properFaceSum_def (c : Finset ι → R) (x : ι → R) :
    properFaceSum c x = ∑ s ∈ (univ : Finset ι).ssubsets, c s * ∏ i ∈ s, x i := by
  rw [properFaceSum]

@[simp]
theorem properFaceSum_zero (x : ι → R) : properFaceSum (0 : Finset ι → R) x = 0 := by
  simp [properFaceSum]

@[simp]
theorem properFaceSum_add (c d : Finset ι → R) (x : ι → R) :
    properFaceSum (c + d) x = properFaceSum c x + properFaceSum d x := by
  simp [properFaceSum, add_mul, sum_add_distrib]

@[simp]
theorem properFaceSum_smul (a : R) (c : Finset ι → R) (x : ι → R) :
    properFaceSum (a • c) x = a * properFaceSum c x := by
  simp [properFaceSum, mul_sum, mul_assoc]

@[simp]
theorem properFaceSum_sum {α : Type*} (t : Finset α) (c : α → Finset ι → R) (x : ι → R) :
    properFaceSum (∑ j ∈ t, c j) x = ∑ j ∈ t, properFaceSum (c j) x := by
  simp only [properFaceSum, Finset.sum_apply, sum_mul]
  exact sum_comm

/-- A single coefficient at a proper subset `s` contributes exactly `a ∏_{i ∈ s} x_i`; at the
full subset it contributes nothing. -/
theorem properFaceSum_single (s : Finset ι) (a : R) (x : ι → R) :
    properFaceSum (Pi.single s a) x = if s = univ then 0 else a * ∏ i ∈ s, x i := by
  rw [properFaceSum]
  split_ifs with hs
  · exact sum_eq_zero fun t ht ↦ by
      rw [Pi.single_eq_of_ne (hs ▸ (mem_ssubsets.1 ht).ne), zero_mul]
  · rw [sum_eq_single_of_mem s (mem_ssubsets.2 (ssubset_univ_iff.2 hs)) fun t _ hts ↦ by
      rw [Pi.single_eq_of_ne hts, zero_mul], Pi.single_eq_same]

/-- The coefficient at the full subset does not affect the proper-face sum. -/
@[simp]
theorem properFaceSum_update_univ (c : Finset ι → R) (a : R) (x : ι → R) :
    properFaceSum (Function.update c univ a) x = properFaceSum c x :=
  sum_congr rfl fun s hs ↦ by rw [Function.update_of_ne (mem_ssubsets.1 hs).ne]

/-- Transporting the coefficients and the variables along a bijection of index types does not
change the proper-face sum. -/
theorem properFaceSum_equiv [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (c : Finset κ → R)
    (x : κ → R) : properFaceSum (c ∘ e.finsetCongr) (x ∘ e) = properFaceSum c x := by
  refine sum_equiv e.finsetCongr (fun s ↦ ?_) fun s _ ↦ ?_
  · simp only [mem_ssubsets, Equiv.finsetCongr_apply]
    rw [← map_univ_equiv e, map_ssubset_map]
  · simp [Equiv.finsetCongr_apply, prod_map]

/-- Translating the variables by a vector `a` gives a proper-face sum again: the coefficient at
`t` is `∑_{t ⊆ s ⊊ ι} c_s ∏_{i ∈ s \ t} a_i`. -/
theorem properFaceSum_add_vec (c : Finset ι → R) (x a : ι → R) :
    properFaceSum c (x + a) =
      properFaceSum
        (fun t ↦ ∑ s ∈ (univ : Finset ι).ssubsets with t ⊆ s, c s * ∏ i ∈ s \ t, a i) x := by
  simp only [properFaceSum, Pi.add_apply, prod_add, mul_sum, sum_mul]
  refine sum_comm' (fun s t ↦ ?_) |>.trans (sum_congr rfl fun t _ ↦ sum_congr rfl fun s _ ↦ ?_)
  · simp only [mem_ssubsets, mem_powerset, mem_filter]
    exact ⟨fun h ↦ ⟨⟨h.1, h.2⟩, h.2.trans_ssubset h.1⟩, fun h ↦ ⟨h.1.1, h.1.2⟩⟩
  · ring

end TauCeti
