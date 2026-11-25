/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Int.Cast.Basic

/-!
# Single-coordinate casting, singleton sums, and coordinate erasing for finitely supported functions

`Finsupp.intCast_single_apply` commutes integer casts with evaluating a one-point finitely supported
function. Evaluating a finitely supported sum of singletons `f.sum fun a m ↦ single (φ a) (ψ a m)`
recovers `ψ a₀ (f a₀)` at `φ a₀` when `φ` is injective (`Finsupp.sum_single_apply_of_injective`) and
vanishes outside the image of `f.support` (`Finsupp.sum_single_eq_zero_of_forall_ne`). Support and
`Finsupp.erase` helpers (`Finsupp.eq_zero_of_support_mem_nil`, `Finsupp.mem_of_mem_support_erase`,
`Finsupp.list_map_erase_of_notMem`) step through list inductions on `f.support`. Over any additive
commutative monoid and decidable index type, `Finsupp.eraseSingleEquiv k` decomposes `α →₀ M` into
its value at `k` and `{ a : α →₀ M // a k = 0 }`.
-/

public section

namespace Finsupp

/-- The cast of a value of `Finsupp.single a n` is the value of `Finsupp.single a (n : R)`. -/
@[simp, norm_cast]
theorem intCast_single_apply {α R : Type*} [AddGroupWithOne R] (a : α) (n : ℤ) (b : α) :
    ((single a n b : ℤ) : R) = single a (n : R) b :=
  apply_single' Int.cast Int.cast_zero a n b

/-- Evaluating `f.sum fun a m ↦ single (φ a) (ψ a m)` at `φ a₀` for injective `φ` recovers
`ψ a₀ (f a₀)` when `ψ a₀ 0 = 0`. -/
theorem sum_single_apply_of_injective {α β M N : Type*} [Zero M] [AddCommMonoid N] (f : α →₀ M)
    {φ : α → β} (hφ : Function.Injective φ) (ψ : α → M → N) {a₀ : α} (hψ : ψ a₀ 0 = 0) :
    (f.sum fun a m ↦ single (φ a) (ψ a m)) (φ a₀) = ψ a₀ (f a₀) := by
  classical
  rw [sum_apply, Finsupp.sum]
  by_cases ha₀ : a₀ ∈ f.support
  · rw [Finset.sum_eq_single_of_mem a₀ ha₀ (fun _ _ hne ↦ single_eq_of_ne (hφ.ne hne.symm)),
      single_eq_same]
  · rw [Finset.sum_eq_zero fun a ha ↦ single_eq_of_ne (hφ.ne (by rintro rfl; exact ha₀ ha)),
      notMem_support_iff.mp ha₀, hψ]

/-- Evaluating `f.sum fun a m ↦ single (φ a) (ψ a m)` at `b` gives `0` when `φ a ≠ b` across
`f.support`. -/
theorem sum_single_eq_zero_of_forall_ne {α β M N : Type*} [Zero M] [AddCommMonoid N]
    (f : α →₀ M) (φ : α → β) (ψ : α → M → N) {b : β} (hb : ∀ a ∈ f.support, φ a ≠ b) :
    (f.sum fun a m ↦ single (φ a) (ψ a m)) b = 0 := by
  rw [sum_apply, Finsupp.sum]
  exact Finset.sum_eq_zero fun a ha ↦ single_eq_of_ne (hb a ha).symm

/-- A finitely supported function whose support lies in `[]` is `0`. -/
theorem eq_zero_of_support_mem_nil {α M : Type*} [Zero M] {f : α →₀ M}
    (hf : ∀ j ∈ f.support, j ∈ ([] : List α)) : f = 0 :=
  support_eq_empty.mp (Finset.eq_empty_of_forall_notMem fun j hj ↦ List.not_mem_nil (hf j hj))

/-- If `f.support` lies in `i :: tl`, then `(f.erase i).support` lies in `tl`. -/
theorem mem_of_mem_support_erase {α M : Type*} [Zero M] {i j : α} {tl : List α} {f : α →₀ M}
    (hf : ∀ k ∈ f.support, k ∈ i :: tl) (hj : j ∈ (f.erase i).support) : j ∈ tl := by
  classical
  have hj0 := mem_support_iff.mp hj
  have hji : j ≠ i := fun h ↦ hj0 (by simp [h])
  exact (List.mem_cons.mp
    (hf j (mem_support_iff.mpr (by simpa [hji] using hj0)))).resolve_left hji

/-- Mapping `j ↦ g j ((f.erase i) j)` over a list `l` not containing `i` agrees with mapping
`j ↦ g j (f j)`. -/
theorem list_map_erase_of_notMem {α M β : Type*} [Zero M] (f : α →₀ M) {i : α} {l : List α}
    (hi : i ∉ l) (g : α → M → β) :
    l.map (fun j ↦ g j ((f.erase i) j)) = l.map (fun j ↦ g j (f j)) :=
  List.map_congr_left fun j hj ↦ by
    classical
    rw [erase_ne (ne_of_mem_of_not_mem hj hi)]

section EraseSingle

variable {α M : Type*} [DecidableEq α] [AddCommMonoid M]

/-- Equivalence splitting `a : α →₀ M` into `(a k, a.erase k)` with inverse
`(m, a₀) ↦ a₀.val + single k m`. -/
noncomputable def eraseSingleEquiv (k : α) : (α →₀ M) ≃ M × { a : α →₀ M // a k = 0 } where
  toFun a := (a k, ⟨a.erase k, erase_same⟩)
  invFun p := p.2.val + single k p.1
  left_inv a := erase_add_single k a
  right_inv := fun ⟨_, a₀⟩ ↦ Prod.ext (by simp [a₀.property]) <| Subtype.ext <| ext fun i ↦ by
    by_cases hik : i = k <;> simp [hik, a₀.property]

@[simp]
theorem eraseSingleEquiv_apply_fst (k : α) (a : α →₀ M) :
    (eraseSingleEquiv k a).1 = a k :=
  (rfl)

@[simp]
theorem coe_eraseSingleEquiv_apply_snd (k : α) (a : α →₀ M) :
    ((eraseSingleEquiv k a).2 : α →₀ M) = a.erase k :=
  (rfl)

@[simp]
theorem eraseSingleEquiv_symm_apply (k : α) (p : M × { a : α →₀ M // a k = 0 }) :
    (eraseSingleEquiv k).symm p = p.2.val + single k p.1 :=
  (rfl)

end EraseSingle

end Finsupp
