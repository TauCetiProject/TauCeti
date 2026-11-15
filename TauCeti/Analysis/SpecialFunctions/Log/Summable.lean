/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Positivity and finite-level splitting of convergent real infinite products

When a positive real family `f` satisfies `Summable fun a ↦ |f a - 1|`, the logarithms
`Real.log (f a)` are summable (`TauCeti.summable_log_of_summable_abs_sub_one`), so the infinite
product `∏' a, f a` equals `Real.exp (∑' a, Real.log (f a))` and is strictly positive
(`TauCeti.tprod_pos_of_summable_abs_sub_one`). Over complements of finite sets `S ⊆ T`, the tail
product outside `S` splits into the finite product on `T \ S` times the tail product outside `T`
(`TauCeti.tprod_split_finset`).

## Main results

* `TauCeti.multipliable_notMem_of_subset`, `TauCeti.summable_notMem_of_subset`: restricting a
  multipliable or summable family from `{i // i ∉ S}` to `{i // i ∉ T}` for `S ⊆ T` preserves
  convergence.
* `TauCeti.summable_log_of_summable_abs_sub_one`: summability of `|f a - 1|` implies summability of
  `Real.log (f a)`.
* `TauCeti.tprod_eq_rexp_tsum_log_of_summable_abs_sub_one`,
  `TauCeti.tprod_pos_of_summable_abs_sub_one`: exponential formula and strict positivity for
  `∏' a, f a` when `f a > 0` and `|f a - 1|` is summable.
* `TauCeti.tprod_split_finset`: for `S ⊆ T`,
  `(∏' i : {i // i ∉ S}, f i.1) = (∏ i ∈ T \ S, f i) * (∏' i : {i // i ∉ T}, f i.1)`.
-/

public section

namespace TauCeti

/-- Multipliability outside a finite set `S` implies multipliability outside any larger finite set
`T ⊇ S`. -/
@[to_additive /-- Summability outside a finite set `S` implies summability outside any larger
finite set `T ⊇ S`. -/]
theorem multipliable_notMem_of_subset {ι α : Type*} [CommGroup α] [UniformSpace α]
    [IsUniformGroup α] [CompleteSpace α] {S T : Finset ι} (hST : S ⊆ T) (g : ι → α)
    (hconv : Multipliable fun i : {i // i ∉ S} ↦ g i.1) :
    Multipliable fun i : {i // i ∉ T} ↦ g i.1 := by
  refine hconv.comp_injective (i := fun i : {i // i ∉ T} ↦ ⟨i.1, fun hiS ↦ i.2 (hST hiS)⟩) ?_
  intro a b h
  exact Subtype.ext (Subtype.mk.inj h)

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
    0 < ∏' a, f a := by
  rw [tprod_eq_rexp_tsum_log_of_summable_abs_sub_one hf hconv]
  exact Real.exp_pos _

/-- For finite index sets `S ⊆ T` and a real family `f` that is positive outside `S` with
`Summable fun i : {i // i ∉ S} ↦ |f i.1 - 1|`, the tail product outside `S` splits into the finite
product over `T \ S` times the tail product outside `T`. -/
theorem tprod_split_finset {ι : Type*} [DecidableEq ι] {S T : Finset ι} (hST : S ⊆ T)
    (f : ι → ℝ) (hf : ∀ i ∉ S, 0 < f i)
    (hconv : Summable fun i : {i // i ∉ S} ↦ |f i.1 - 1|) :
    (∏' i : {i // i ∉ S}, f i.1) =
      (∏ i ∈ T \ S, f i) * (∏' i : {i // i ∉ T}, f i.1) := by
  have hconvT : Summable fun i : {i // i ∉ T} ↦ |f i.1 - 1| :=
    summable_notMem_of_subset hST (fun i ↦ |f i - 1|) hconv
  let s : Set {i // i ∉ S} := {x | x.1 ∈ T}
  let e₁ : s ≃ ↥(T \ S) :=
    { toFun x := ⟨x.1.1, Finset.mem_sdiff.mpr ⟨x.2, x.1.2⟩⟩
      invFun y := ⟨⟨y.1, (Finset.mem_sdiff.mp y.2).2⟩, (Finset.mem_sdiff.mp y.2).1⟩
      left_inv _ := by ext; rfl
      right_inv _ := by ext; rfl }
  let e₂ : ↑sᶜ ≃ {i // i ∉ T} :=
    { toFun x := ⟨x.1.1, x.2⟩
      invFun y := ⟨⟨y.1, fun hiS ↦ y.2 (hST hiS)⟩, y.2⟩
      left_inv _ := by ext; rfl
      right_inv _ := by ext; rfl }
  have _ : Fintype s := Fintype.ofEquiv _ e₁.symm
  have hs : Multipliable (fun x : s ↦ f x.1.1) := (hasProd_fintype _).multipliable
  have hT_mult : Multipliable (fun y : {i // i ∉ T} ↦ f y.1) :=
    Real.multipliable_of_summable_log (fun y ↦ hf y.1 fun hiS ↦ y.2 (hST hiS))
      (summable_log_of_summable_abs_sub_one hconvT)
  have hsc : Multipliable (fun x : ↑sᶜ ↦ f x.1.1) := e₂.multipliable_iff.mpr hT_mult
  rw [← Multipliable.tprod_mul_tprod_compl (f := fun x : {i // i ∉ S} ↦ f x.1) hs hsc]
  congr 1
  · rw [tprod_fintype]
    exact (e₁.prod_comp (fun y : ↥(T \ S) ↦ f y.1)).trans (Finset.prod_coe_sort (T \ S) f)
  · exact e₂.tprod_eq fun y ↦ f y.1

end TauCeti
