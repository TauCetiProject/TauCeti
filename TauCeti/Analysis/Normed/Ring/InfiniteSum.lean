/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite products of absolutely convergent series

Let `R` be a complete normed commutative ring and `f i : β → R`, for `i` in a finite type `ι`, a
finite family of absolutely summable series. Expanding the product of their sums gives the sum of
the products `∏ i, f i (x i)` over all tuples `x : ι → β`, and this sum again converges absolutely:
```text
∏ i, ∑' b, f i b = ∑' x : ι → β, ∏ i, f i (x i).
```
This is the finite-family version of Mathlib's `tsum_mul_tsum_of_summable_norm`, which treats two
factors, and it is proved from it by induction on the number of factors. It computes a series
over a lattice `ℤⁿ` whose terms factor over the coordinates, such as the theta series of the
lattice spanned by an orthonormal basis.

## Main statements

* `TauCeti.summable_norm_prod_of_summable_norm`: the products `∏ i, f i (x i)` are absolutely
  summable over `x : ι → β`.
* `TauCeti.prod_tsum_of_summable_norm`: the product of the sums is the sum of the products.
-/

public section

open Finset

namespace TauCeti

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] {β : Type*}

/-- The two statements for a family indexed by `Fin n`, proved together by induction on `n`. -/
private theorem summable_prod_and_prod_tsum_fin (n : ℕ) :
    ∀ f : Fin n → β → R, (∀ i, Summable fun b ↦ ‖f i b‖) →
      (Summable fun x : Fin n → β ↦ ‖∏ i, f i (x i)‖) ∧
        ∏ i, ∑' b, f i b = ∑' x : Fin n → β, ∏ i, f i (x i) := by
  induction n with
  | zero =>
    intro f _
    refine ⟨.of_finite, ?_⟩
    rw [tsum_eq_single (fun i ↦ i.elim0) fun x hx ↦ (hx (Subsingleton.elim _ _)).elim]
    simp
  | succ n ih =>
    intro f hf
    obtain ⟨hs, he⟩ := ih (fun i ↦ f i.succ) fun i ↦ hf i.succ
    -- Split a tuple indexed by `Fin (n + 1)` into its first entry and the remaining ones.
    have hprod (z : β × (Fin n → β)) :
        ∏ i, f i (Fin.consEquiv (fun _ ↦ β) z i) = f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i) := by
      rw [Fin.prod_univ_succ]
      simp
    have hs' : Summable fun z ↦ ‖∏ i, f i (Fin.consEquiv (fun _ ↦ β) z i)‖ := by
      simpa only [hprod] using (hf 0).mul_norm hs
    refine ⟨(Fin.consEquiv fun _ ↦ β).summable_iff.mp hs', ?_⟩
    rw [Fin.prod_univ_succ, he, tsum_mul_tsum_of_summable_norm (hf 0) hs,
      ← (Fin.consEquiv fun _ ↦ β).tsum_eq]
    exact tsum_congr fun z ↦ (hprod z).symm

/-- **Products of absolutely convergent series are absolutely convergent**: if `f i` is
absolutely summable for each `i` in a finite type `ι`, then so is `x ↦ ∏ i, f i (x i)` over the
tuples `x : ι → β`. -/
theorem summable_norm_prod_of_summable_norm {ι : Type*} [Fintype ι] {f : ι → β → R}
    (hf : ∀ i, Summable fun b ↦ ‖f i b‖) : Summable fun x : ι → β ↦ ‖∏ i, f i (x i)‖ := by
  let e := Fintype.equivFin ι
  have h := (summable_prod_and_prod_tsum_fin _ (fun j ↦ f (e.symm j)) fun j ↦ hf _).1
  refine ((e.arrowCongr (.refl β)).summable_iff
    (f := fun y : Fin _ → β ↦ ‖∏ j, f (e.symm j) (y j)‖)).mpr h |>.congr fun x ↦ ?_
  simp [Equiv.arrowCongr_apply, e.symm.prod_comp (fun i ↦ f i (x i))]

/-- **The product of finitely many absolutely convergent series** is the sum of the products of
their terms: `∏ i, ∑' b, f i b = ∑' x : ι → β, ∏ i, f i (x i)`. This is the finite-family version
of `tsum_mul_tsum_of_summable_norm`. -/
theorem prod_tsum_of_summable_norm {ι : Type*} [Fintype ι] {f : ι → β → R}
    (hf : ∀ i, Summable fun b ↦ ‖f i b‖) :
    ∏ i, ∑' b, f i b = ∑' x : ι → β, ∏ i, f i (x i) := by
  let e := Fintype.equivFin ι
  have h := (summable_prod_and_prod_tsum_fin _ (fun j ↦ f (e.symm j)) fun j ↦ hf _).2
  rw [← e.symm.prod_comp, h, ← (e.arrowCongr (.refl β)).tsum_eq]
  congr 1 with x
  simp [Equiv.arrowCongr_apply, e.symm.prod_comp (fun i ↦ f i (x i))]

end TauCeti
