/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
import TauCeti.Topology.Algebra.InfiniteSum.Group

/-!
# Positivity and finite-level splitting of convergent real infinite products

For a positive real family `f` satisfying `Summable fun a ↦ |f a - 1|`, the logarithms
`Real.log (f a)` are summable, so `∏' a, f a = Real.exp (∑' a, Real.log (f a)) > 0`.

## Main results

* `TauCeti.summable_log_of_summable_abs_sub_one`,
  `TauCeti.tprod_eq_rexp_tsum_log_of_summable_abs_sub_one`,
  `TauCeti.tprod_pos_of_summable_abs_sub_one`: summability of `Real.log (f a)`, exponential
  formula, and positivity of `∏' a, f a`.
* `TauCeti.tprod_split_finset`: for `S ⊆ T`,
  `(∏' i : {i // i ∉ S}, f i.1) = (∏ i ∈ T \ S, f i) * (∏' i : {i // i ∉ T}, f i.1)`.
-/

public section

namespace TauCeti

/-- If `∑' a, |f a - 1|` converges, then `∑' a, Real.log (f a)` converges. -/
theorem summable_log_of_summable_abs_sub_one {α : Type*} {f : α → ℝ}
    (hconv : Summable fun a ↦ |f a - 1|) :
    Summable fun a ↦ Real.log (f a) := by
  simpa only [add_sub_cancel] using Real.summable_log_one_add_of_summable hconv.of_abs

/-- For a positive real family `f` with `Summable fun a ↦ |f a - 1|`, the infinite product
`∏' a, f a` equals `Real.exp (∑' a, Real.log (f a))`. -/
theorem tprod_eq_rexp_tsum_log_of_summable_abs_sub_one {α : Type*} {f : α → ℝ}
    (hf : ∀ a, 0 < f a) (hconv : Summable fun a ↦ |f a - 1|) :
    ∏' a, f a = Real.exp (∑' a, Real.log (f a)) :=
  (Real.rexp_tsum_eq_tprod hf (summable_log_of_summable_abs_sub_one hconv)).symm

/-- For a positive real family `f` with `Summable fun a ↦ |f a - 1|`, the infinite product
`∏' a, f a` is strictly positive. -/
theorem tprod_pos_of_summable_abs_sub_one {α : Type*} {f : α → ℝ}
    (hf : ∀ a, 0 < f a) (hconv : Summable fun a ↦ |f a - 1|) :
    0 < ∏' a, f a :=
  tprod_eq_rexp_tsum_log_of_summable_abs_sub_one hf hconv ▸ Real.exp_pos _

/-- For finite index sets `S ⊆ T` and a real family `f` that is positive outside `S` with
`Summable fun i : {i // i ∉ S} ↦ |f i.1 - 1|`, the tail product outside `S` splits into the finite
product over `T \ S` times the tail product outside `T`. -/
theorem tprod_split_finset {ι : Type*} [DecidableEq ι] {S T : Finset ι} (hST : S ⊆ T)
    (f : ι → ℝ) (hf : ∀ i ∉ S, 0 < f i)
    (hconv : Summable fun i : {i // i ∉ S} ↦ |f i.val - 1|) :
    (∏' i : {i // i ∉ S}, f i.val) =
      (∏ i ∈ T \ S, f i) * (∏' i : {i // i ∉ T}, f i.val) := by
  have hconvT := summable_notMem_of_subset hST (fun i ↦ |f i - 1|) hconv
  let s : Set {i // i ∉ S} := {x | x.val ∈ T}
  let e₁ : s ≃ ↥(T \ S) :=
    { toFun x := ⟨x.val.val, Finset.mem_sdiff.mpr ⟨x.property, x.val.property⟩⟩
      invFun y := ⟨⟨y.val, (Finset.mem_sdiff.mp y.property).2⟩, (Finset.mem_sdiff.mp y.property).1⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  let e₂ : ↑sᶜ ≃ {i // i ∉ T} :=
    { toFun x := ⟨x.val.val, x.property⟩
      invFun y := ⟨⟨y.val, fun h ↦ y.property (hST h)⟩, y.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have _ : Fintype s := Fintype.ofEquiv _ e₁.symm
  have hsc : Multipliable (fun x : ↑sᶜ ↦ f x.val.val) := e₂.multipliable_iff.mpr <|
    Real.multipliable_of_summable_log (fun y ↦ hf y.val fun h ↦ y.property (hST h))
      (summable_log_of_summable_abs_sub_one hconvT)
  rw [← Multipliable.tprod_mul_tprod_compl (f := fun x : {i // i ∉ S} ↦ f x.val)
    (hasProd_fintype _).multipliable hsc]
  exact congrArg₂ (· * ·)
    ((tprod_fintype _).trans ((e₁.prod_comp fun y : ↥(T \ S) ↦ f y.val).trans
      (Finset.prod_coe_sort (T \ S) f)))
    (e₂.tprod_eq fun y ↦ f y.val)

end TauCeti
