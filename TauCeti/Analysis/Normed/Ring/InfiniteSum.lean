/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Finite products of absolutely convergent series

Let `R` be a normed commutative ring and `f i : β → R`, for `i` in a finite type `ι`, a finite
family of absolutely summable series. The products `∏ i, f i (x i)` over all tuples `x : ι → β`
are again absolutely summable, and if `f i` sums to `s i` for each `i`, they sum to `∏ i, s i`.
In a complete ring this reads
```text
∏ i, ∑' b, f i b = ∑' x : ι → β, ∏ i, f i (x i).
```
This is the finite-family version of Mathlib's `Summable.mul_norm`, `HasSum.mul` and
`tsum_mul_tsum_of_summable_norm`, which treat two factors, and it is proved from them by induction
on the number of factors. It computes a series over a lattice `ℤⁿ` whose terms factor over the
coordinates, such as the theta series of the lattice spanned by an orthonormal basis, or a
product of geometric series.

## Main statements

* `TauCeti.summable_norm_prod_of_summable_norm`: the products `∏ i, f i (x i)` are absolutely
  summable over `x : ι → β`.
* `TauCeti.hasSum_prod_of_summable_norm`: the products sum to the product of the sums.
* `TauCeti.prod_tsum_of_summable_norm`: the same statement for `tsum` in a complete ring.
-/

public section

namespace TauCeti

variable {R : Type*} [NormedCommRing R] {β : Type*}

/-- Splitting a tuple indexed by `Fin (n + 1)` into its first entry and the remaining ones. -/
private theorem prod_consEquiv {n : ℕ} (f : Fin (n + 1) → β → R) (z : β × (Fin n → β)) :
    ∏ i, f i (Fin.consEquiv (fun _ ↦ β) z i) = f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i) := by
  simp [Fin.prod_univ_succ]

/-- Reindexing a product over tuples along an equivalence `ι ≃ Fin n`. -/
private theorem prod_arrowCongr {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin n)
    (f : ι → β → R) (x : ι → β) :
    ∏ j, f (e.symm j) ((e.arrowCongr (.refl β)) x j) = ∏ i, f i (x i) := by
  simp [Equiv.arrowCongr_apply, e.symm.prod_comp (fun i ↦ f i (x i))]

/-- `summable_norm_prod_of_summable_norm` for a family indexed by `Fin n`. -/
private theorem summable_norm_prod_fin (n : ℕ) :
    ∀ f : Fin n → β → R, (∀ i, Summable fun b ↦ ‖f i b‖) →
      Summable fun x : Fin n → β ↦ ‖∏ i, f i (x i)‖ := by
  induction n with
  | zero => exact fun _ _ ↦ .of_finite
  | succ n ih =>
    intro f hf
    refine (Fin.consEquiv fun _ ↦ β).summable_iff.mp ?_
    simpa only [Function.comp_def, prod_consEquiv] using
      (hf 0).mul_norm (ih (fun i ↦ f i.succ) fun i ↦ hf i.succ)

/-- `hasSum_prod_of_summable_norm` for a family indexed by `Fin n`. -/
private theorem hasSum_prod_fin (n : ℕ) :
    ∀ (f : Fin n → β → R) (s : Fin n → R), (∀ i, HasSum (f i) (s i)) →
      (∀ i, Summable fun b ↦ ‖f i b‖) →
        HasSum (fun x : Fin n → β ↦ ∏ i, f i (x i)) (∏ i, s i) := by
  induction n with
  | zero => intro f s _ _; simp
  | succ n ih =>
    intro f s hf hn
    have ht := ih (fun i ↦ f i.succ) (fun i ↦ s i.succ) (fun i ↦ hf i.succ) fun i ↦ hn i.succ
    have hm := summable_mul_of_summable_norm' (hn 0) (hf 0).summable
      (summable_norm_prod_fin n _ fun i ↦ hn i.succ) ht.summable
    rw [Fin.prod_univ_succ]
    refine (Fin.consEquiv fun _ ↦ β).hasSum_iff.mp ?_
    simpa only [Function.comp_def, prod_consEquiv] using (hf 0).mul ht hm

/-- **Products of absolutely convergent series are absolutely convergent**: if `f i` is
absolutely summable for each `i` in a finite type `ι`, then so is `x ↦ ∏ i, f i (x i)` over the
tuples `x : ι → β`. -/
theorem summable_norm_prod_of_summable_norm {ι : Type*} [Fintype ι] {f : ι → β → R}
    (hf : ∀ i, Summable fun b ↦ ‖f i b‖) : Summable fun x : ι → β ↦ ‖∏ i, f i (x i)‖ := by
  let e := Fintype.equivFin ι
  simpa only [Function.comp_def, prod_arrowCongr] using (e.arrowCongr (.refl β)).summable_iff.mpr
    (summable_norm_prod_fin _ (fun j ↦ f (e.symm j)) fun j ↦ hf _)

/-- **The product of finitely many absolutely convergent series** is the sum of the products of
their terms: if `f i` is absolutely summable with sum `s i` for each `i` in a finite type `ι`,
then `x ↦ ∏ i, f i (x i)` sums to `∏ i, s i` over the tuples `x : ι → β`. This is the
finite-family version of `HasSum.mul`. -/
theorem hasSum_prod_of_summable_norm {ι : Type*} [Fintype ι] {f : ι → β → R} {s : ι → R}
    (hf : ∀ i, HasSum (f i) (s i)) (hn : ∀ i, Summable fun b ↦ ‖f i b‖) :
    HasSum (fun x : ι → β ↦ ∏ i, f i (x i)) (∏ i, s i) := by
  let e := Fintype.equivFin ι
  rw [← e.symm.prod_comp]
  simpa only [Function.comp_def, prod_arrowCongr] using (e.arrowCongr (.refl β)).hasSum_iff.mpr
    (hasSum_prod_fin _ (fun j ↦ f (e.symm j)) _ (fun j ↦ hf _) fun j ↦ hn _)

/-- **The product of finitely many absolutely convergent series** in a complete ring:
`∏ i, ∑' b, f i b = ∑' x : ι → β, ∏ i, f i (x i)`. This is the finite-family version
of `tsum_mul_tsum_of_summable_norm`. -/
theorem prod_tsum_of_summable_norm [CompleteSpace R] {ι : Type*} [Fintype ι] {f : ι → β → R}
    (hf : ∀ i, Summable fun b ↦ ‖f i b‖) :
    ∏ i, ∑' b, f i b = ∑' x : ι → β, ∏ i, f i (x i) :=
  (hasSum_prod_of_summable_norm (fun i ↦ (hf i).of_norm.hasSum) hf).tsum_eq.symm

end TauCeti
