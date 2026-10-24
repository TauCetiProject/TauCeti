/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Mittag-Leffler towers of modules

A tower of modules `A₀ ← A₁ ← A₂ ← ⋯` is *Mittag-Leffler* if, for every `n`, the images of the
composite transitions `Aₖ → Aₙ` stabilise as `k` grows. We take this to be Mathlib's
`CategoryTheory.Functor.IsMittagLeffler` for the underlying functor `ℕᵒᵖ ⥤ Type`, and show that it
is the eventual constancy of the images, which are submodules. Towers with surjective transitions
and towers of modules with finitely many elements are Mittag-Leffler.

The main result is that a Mittag-Leffler tower has vanishing `lim¹` (Stacks, Tag 07KW). This
feeds the exactness of `lim` on short exact sequences of towers whose kernel is Mittag-Leffler,
the vanishing of the `lim¹` term in Milnor sequences, and derived limits of towers of complexes.

## Implementation notes

Writing `Bₙ ⊆ Aₙ` for the stable image, the transitions map `Bₙ₊₁` onto `Bₙ`, and every composite
transition `Aₖ → Aₙ` with `k` large has image in `Bₙ`. Finite partial sums of the composite
transitions reduce a family in `∏ₙ Aₙ`, modulo the image of the shift, to a family in `∏ₙ Bₙ`;
`ModuleTower.mem_range_shift_of_le_map` handles the latter.

## Main declarations

* `TauCeti.ModuleTower.IsMittagLeffler`: the Mittag-Leffler condition on a tower of modules.
* `TauCeti.ModuleTower.isMittagLeffler_iff_ranges`: it holds exactly when, for every `n`, the
  images `range (Aₖ → Aₙ)` are eventually constant.
* `TauCeti.ModuleTower.isMittagLeffler_of_surjective`,
  `TauCeti.ModuleTower.isMittagLeffler_of_finite`: towers with surjective transitions, and towers
  whose terms are finite sets, are Mittag-Leffler.
* `TauCeti.ModuleTower.shift_surjective_of_isMittagLeffler`,
  `TauCeti.ModuleTower.subsingleton_limOne_of_isMittagLeffler`: Mittag-Leffler towers have
  surjective shift map, hence vanishing `lim¹`.

## References

* [Stacks: Algebra, Definition 10.86.1, Tag 0594](https://stacks.math.columbia.edu/tag/0594)
* [Stacks: More on Algebra, Lemma 15.88.1, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
-/

public section

noncomputable section

namespace TauCeti

namespace ModuleTower

open CategoryTheory Opposite

universe v u

variable {R : Type u} [Ring R] (F : ModuleTower.{v} R)

/-- A tower of modules is *Mittag-Leffler* if, for every `n`, the images of the composite
transitions `Aₖ → Aₙ` stabilise as `k` grows: Mathlib's `Functor.IsMittagLeffler` for the
underlying functor `ℕᵒᵖ ⥤ Type`. See `isMittagLeffler_iff_ranges` for the formulation in terms of
the ranges of `transitionOfLE`. -/
abbrev IsMittagLeffler : Prop :=
  (F ⋙ forget (ModuleCat R)).IsMittagLeffler

/-- The image of the map of types underlying `F.map f` is the range of the composite
transition. -/
private theorem range_forget_map {n k : ℕ} (f : op k ⟶ op n) :
    Set.range ((F ⋙ forget (ModuleCat R)).map f) =
      (LinearMap.range (F.transitionOfLE (leOfHom f.unop)) : Set (F.obj (op n))) := by
  simp [LinearMap.coe_range]

/-- **Eventual-range form of the Mittag-Leffler condition**: a tower is Mittag-Leffler if and
only if, for every `n`, the images of the composite transitions `Aₖ → Aₙ` are constant for all
`k` beyond some `m ≥ n`. -/
theorem isMittagLeffler_iff_ranges : F.IsMittagLeffler ↔
    ∀ n, ∃ m, ∃ hnm : n ≤ m, ∀ k (hmk : m ≤ k),
      LinearMap.range (F.transitionOfLE (hnm.trans hmk)) =
        LinearMap.range (F.transitionOfLE hnm) := by
  constructor
  · intro h n
    obtain ⟨⟨m⟩, f, hf⟩ := h (op n)
    have hnm : n ≤ m := leOfHom f.unop
    refine ⟨m, hnm, fun k hmk ↦ le_antisymm (F.range_transitionOfLE_le hnm hmk) ?_⟩
    have := hf (homOfLE (hnm.trans hmk)).op
    rwa [range_forget_map, range_forget_map, SetLike.coe_subset_coe] at this
  · intro h j
    obtain ⟨n⟩ := j
    obtain ⟨m, hnm, hm⟩ := h n
    refine ⟨op m, (homOfLE hnm).op, fun ⟨k⟩ g ↦ ?_⟩
    have hnk : n ≤ k := leOfHom g.unop
    rw [range_forget_map, range_forget_map, SetLike.coe_subset_coe,
      ← hm (max m k) (le_max_left m k)]
    exact F.range_transitionOfLE_le hnk (le_max_right m k)

/-- **Towers with surjective transitions are Mittag-Leffler.** -/
theorem isMittagLeffler_of_surjective (h : ∀ n, Function.Surjective (F.transition n)) :
    F.IsMittagLeffler :=
  (F.isMittagLeffler_iff_ranges).2 fun n ↦ ⟨n, le_rfl, fun k hnk ↦ by
    rw [LinearMap.range_eq_top.2 (F.transitionOfLE_surjective h _),
      LinearMap.range_eq_top.2 (F.transitionOfLE_surjective h _)]⟩

/-- **Towers of modules with finitely many elements are Mittag-Leffler**: the images in each
term form a decreasing family of finite sets, which stabilises. -/
theorem isMittagLeffler_of_finite [∀ n, Finite (F.obj (op n))] : F.IsMittagLeffler :=
  Functor.isMittagLeffler_of_exists_finite_range _ fun ⟨n⟩ ↦
    ⟨op n, 𝟙 _, by rw [range_forget_map, LinearMap.coe_range]; exact Set.finite_range _⟩

/-- Let `Bₙ ⊆ Aₙ` be submodules such that, for every `n`, some composite transition `Aₘ → Aₙ` has
image in `Bₙ`. Then every family `(bₙ)` agrees with the image of some family under the shift
map modulo the `Bₙ`. -/
private theorem exists_sub_shift_mem (B : ∀ n, Submodule R (F.obj (op n)))
    (hB : ∀ n, ∃ m, ∃ hnm : n ≤ m, LinearMap.range (F.transitionOfLE hnm) ≤ B n)
    (b : F.Product) : ∃ y : F.Product, ∀ n, b n - F.shift y n ∈ B n := by
  choose m hnm hm using hB
  -- `g n k = φₙₖ(bₖ)` for `n ≤ k`, and `s n N = ∑_{n ≤ k < N} φₙₖ(bₖ)`.
  let g (n k : ℕ) : F.obj (op n) := if h : n ≤ k then F.transitionOfLE h (b k) else 0
  let s (n N : ℕ) : F.obj (op n) := ∑ k ∈ Finset.Ico n N, g n k
  have hg_self (n : ℕ) : g n n = b n := by simp [g]
  have hg_succ {n k : ℕ} (hk : n + 1 ≤ k) : F.transition n (g (n + 1) k) = g n k := by
    simp [g, hk, (Nat.le_succ n).trans hk]
  have hg_mem {n k : ℕ} (hk : m n ≤ k) : g n k ∈ B n := by
    have hnk : n ≤ k := (hnm n).trans hk
    simp only [g, hnk, ↓reduceDIte]
    exact hm n (F.range_transitionOfLE_le (hnm n) hk ⟨b k, rfl⟩)
  -- Peeling off the first term of `s n N` gives `s n N = bₙ + φₙ(s (n + 1) N)`.
  have hs {n N : ℕ} (hN : n + 1 ≤ N) : s n N = b n + F.transition n (s (n + 1) N) := by
    simp only [s, Finset.sum_eq_sum_Ico_succ_bot hN, hg_self, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun k hk ↦ (hg_succ (Finset.mem_Ico.1 hk).1).symm
  -- An increasing sequence of truncation points `Mₙ ≥ n + 1` with `Mₙ ≥ mₙ`.
  let M (n : ℕ) : ℕ := n + 1 + (Finset.range (n + 1)).sup m
  have hM_succ (n : ℕ) : n + 1 ≤ M n := Nat.le_add_right _ _
  have hM_mono (n : ℕ) : M n ≤ M (n + 1) := by
    have : (Finset.range (n + 1)).sup m ≤ (Finset.range (n + 1 + 1)).sup m :=
      Finset.sup_mono (Finset.range_subset_range.2 (Nat.le_succ _))
    simp only [M]
    omega
  have hM_ge (n : ℕ) : m n ≤ M n :=
    (Finset.le_sup (Finset.self_mem_range_succ n)).trans (Nat.le_add_left _ _)
  refine ⟨fun n ↦ s n (M n), fun n ↦ ?_⟩
  -- `bₙ - δ(y)ₙ = s n Mₙ₊₁ - s n Mₙ` is a sum of terms `φₙₖ(bₖ)` with `k ≥ Mₙ ≥ mₙ`.
  have hsum : b n - F.shift (fun n ↦ s n (M n)) n =
      ∑ k ∈ Finset.Ico (M n) (M (n + 1)), g n k := by
    have hcons : s n (M n) + ∑ k ∈ Finset.Ico (M n) (M (n + 1)), g n k = s n (M (n + 1)) :=
      Finset.sum_Ico_consecutive _ ((Nat.le_succ n).trans (hM_succ n)) (hM_mono n)
    rw [shift_apply, ← add_right_inj (s n (M n)), hcons, hs ((hM_succ n).trans (hM_mono n))]
    abel
  rw [hsum]
  exact Submodule.sum_mem _ fun k hk ↦ hg_mem ((hM_ge n).trans (Finset.mem_Ico.1 hk).1)

/-- **The shift map of a Mittag-Leffler tower is surjective.** -/
theorem shift_surjective_of_isMittagLeffler (h : F.IsMittagLeffler) :
    Function.Surjective F.shift := by
  choose m hnm hm using (F.isMittagLeffler_iff_ranges).1 h
  -- `Bₙ` is the stable image of the composite transitions into `Aₙ`.
  let B (n : ℕ) : Submodule R (F.obj (op n)) := LinearMap.range (F.transitionOfLE (hnm n))
  have hB_eq (n k : ℕ) (hk : m n ≤ k) :
      B n = LinearMap.range (F.transitionOfLE ((hnm n).trans hk)) :=
    (hm n k hk).symm
  -- The transition `φₙ` maps `Bₙ₊₁` onto `Bₙ`: both are images of `A_K` for `K` large.
  have hB (n : ℕ) : B n ≤ (B (n + 1)).map (F.transition n) := by
    let K := max (m n) (m (n + 1))
    have h₁ : m (n + 1) ≤ K := le_max_right _ _
    have h₂ : n + 1 ≤ K := (hnm (n + 1)).trans h₁
    intro x hx
    rw [hB_eq n K (le_max_left _ _)] at hx
    obtain ⟨a, rfl⟩ := hx
    refine ⟨F.transitionOfLE h₂ a, ?_, by simp⟩
    rw [hB_eq (n + 1) K h₁]
    exact ⟨a, rfl⟩
  intro b
  obtain ⟨y, hy⟩ := F.exists_sub_shift_mem B (fun n ↦ ⟨m n, hnm n, le_rfl⟩) b
  obtain ⟨z, hz⟩ := F.mem_range_shift_of_le_map B hB hy
  exact ⟨y + z, funext fun n ↦ by rw [map_add, hz, Pi.add_apply, add_sub_cancel]⟩

/-- **Mittag-Leffler towers have vanishing `lim¹`** (Stacks, Tag 07KW). -/
theorem subsingleton_limOne_of_isMittagLeffler (h : F.IsMittagLeffler) :
    Subsingleton F.limOne :=
  F.subsingleton_limOne_iff.2 (F.shift_surjective_of_isMittagLeffler h)

end ModuleTower

end TauCeti
