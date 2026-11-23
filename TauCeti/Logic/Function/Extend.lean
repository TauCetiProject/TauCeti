/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Init
public import Mathlib.Data.Set.Inclusion
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Coe

/-!
# Extending functions along injections

A function `a` on `ℕ` extends to `ℤ` along the cast `ℕ → ℤ` by `Function.extend`, with a
fallback function `e` supplying the values off the range of the cast. This file records that the
negative integers lie off that range, so the extension agrees with the fallback there.
Translated extensions can be checked before the anchor and at natural-number offsets.
For a function constant before a natural anchor, extending its tail and translating gives
the same integer function as extending the original function.

A function `g` on a subset `t` extends to the whole type along `Subtype.val`, for instance by
zero. Restricting `g` to a smaller subset `s` before extending does not change the extension at
the points which lie in `s` as soon as they lie in `t`.

A dependent function on the range of an injection `f` extends to the whole index type, for
instance by a fallback function, so restriction `g ↦ fun i ↦ g (f i)` of dependent functions
along `f` is surjective.

## Main results

* `Function.extend_natCast_of_neg`: the extension of `a` along `ℕ → ℤ` with fallback `e` takes
  the value `e n` at every negative integer `n`.
* `Function.Injective.extend_comp_extend`: extension along a composite `f₂₃ ∘ f₁₂` is the iterated
  extension, provided only the outer map `f₂₃` is injective.
* `Function.extend_eq_of_forall`, `Function.extend_subtypeVal_eq`, and
  `Function.extend_prodMap_subtypeVal_eq`: `Function.extend` evaluates to the fallback at a point
  whenever the extended function agrees with the fallback on every preimage of that point (including
  vacuously off the range).
* `Function.extend_subtypeVal_comp_inclusion`: extending a function on `t` and extending its
  restriction to `s ⊆ t` agree at every point of `s` and every point outside `t`.
* `Function.Injective.surjective_pi_comp_right`: restriction of dependent functions along an
  injection is surjective.
-/

public section

namespace Function

/-- The extension of a function on `ℕ` along the cast to `ℤ` agrees with the fallback at
negative integers. -/
theorem extend_natCast_of_neg {α : Sort*} (a : ℕ → α) (e : ℤ → α) {n : ℤ} (hn : n < 0) :
    extend ((↑) : ℕ → ℤ) a e n = e n :=
  extend_apply' _ _ _ fun ⟨_, _⟩ => by omega

/-- To prove a property of a translated natural-number extension, it suffices to check
integers below the anchor and natural-number offsets from it. -/
@[elab_as_elim]
theorem extend_natCast_sub_induction {α : Sort*} (a : ℕ → α) (e : α) (s n : ℤ)
    {P : ℤ → α → Prop} (hlt : ∀ n, n < s → P n e)
    (hadd : ∀ k : ℕ, P (s + k) (a k)) :
    P n (extend ((↑) : ℕ → ℤ) a (fun _ => e) (n - s)) := by
  rcases lt_or_ge n s with hn | hn
  · rw [extend_natCast_of_neg _ _ (by omega)]
    exact hlt n hn
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = s + k := ⟨(n - s).toNat, by omega⟩
    have hoff : s + (k : ℤ) - s = (k : ℤ) := by omega
    rw [hoff, Injective.extend_apply (fun _ _ h => Int.natCast_inj.mp h)]
    exact hadd k

/-- If a natural-indexed function is constant before `s`, its integer extension is
obtained by extending its tail and translating the index by `s`. -/
theorem extend_natCast_sub_natCast {α : Sort*} (a : ℕ → α) (e : α) (s : ℕ)
    (ha : ∀ k < s, a k = e) (n : ℤ) :
    extend ((↑) : ℕ → ℤ) (fun k => a (s + k)) (fun _ => e) (n - (s : ℤ)) =
      extend ((↑) : ℕ → ℤ) a (fun _ => e) n := by
  refine extend_natCast_sub_induction _ e (s : ℤ) n
    (P := fun n y => y = extend ((↑) : ℕ → ℤ) a (fun _ => e) n) ?_ ?_
  · intro n hn
    by_cases hn0 : n < 0
    · rw [extend_natCast_of_neg _ _ hn0]
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
      rw [Injective.extend_apply (fun _ _ h => Int.natCast_inj.mp h)]
      exact (ha k (by omega)).symm
  · intro k
    have hcast : (s : ℤ) + (k : ℤ) = ((s + k : ℕ) : ℤ) := by omega
    rw [hcast, Injective.extend_apply (fun _ _ h => Int.natCast_inj.mp h)]

/-- If `g` agrees with the fallback `e` at every preimage of `b` under `f` (including vacuously
when `b` has no preimage), then `Function.extend f g e b = e b`. -/
theorem extend_eq_of_forall {α β γ : Sort*} {f : α → β} (g : α → γ) (e : β → γ) {b : β}
    (hb : ∀ a, f a = b → g a = e b) :
    extend f g e b = e b := by
  classical
  by_cases h : ∃ a, f a = b
  · rw [extend_def, dite_eq_left_of_eq_true (eq_true h)]
    exact hb _ (Classical.choose_spec h)
  · exact extend_apply' g e b h

/-- Extending `g : Subtype p → γ` along `Subtype.val` with fallback `e` gives `e x` whenever `g`
agrees with `e x` on every witness of `p x` (including vacuously when `¬ p x`). -/
theorem extend_subtypeVal_eq {α γ : Sort*} {p : α → Prop} (g : Subtype p → γ) (e : α → γ) {x : α}
    (hg : ∀ hx : p x, g ⟨x, hx⟩ = e x) :
    extend Subtype.val g e x = e x := by
  refine extend_eq_of_forall g e ?_
  rintro ⟨_, hx⟩ rfl
  exact hg hx

/-- Extending `g : Subtype p × β → γ` along `Prod.map Subtype.val id` with fallback `e` gives
`e (x, y)` whenever `g (⟨x, hx⟩, y) = e (x, y)` for every `hx : p x` (including vacuously when
`¬ p x`). -/
theorem extend_prodMap_subtypeVal_eq {α β : Type*} {γ : Sort*} {p : α → Prop}
    (g : Subtype p × β → γ) (e : α × β → γ) {x : α} (y : β)
    (hg : ∀ hx : p x, g (⟨x, hx⟩, y) = e (x, y)) :
    extend (Prod.map Subtype.val id) g e (x, y) = e (x, y) :=
  extend_eq_of_forall g e fun ⟨⟨_, hx⟩, _⟩ h ↦ by
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h
    exact hg hx

/-- Extending a function on `t` along `Subtype.val`, or first restricting it to a subset `s ⊆ t`,
gives the same value at a point `a` that lies in `s` whenever it lies in `t`: both are `g a` if
`a ∈ s`, and both are the fallback `e a` if `a ∉ t`. -/
theorem extend_subtypeVal_comp_inclusion {α β : Type*} {s t : Set α} (h : s ⊆ t) (g : t → β)
    (e : α → β) {a : α} (ha : a ∈ t → a ∈ s) :
    extend Subtype.val (g ∘ Set.inclusion h) e a = extend Subtype.val g e a := by
  by_cases hat : a ∈ t
  · exact (Subtype.val_injective.extend_apply _ e ⟨a, ha hat⟩).trans
      (Subtype.val_injective.extend_apply g e ⟨a, hat⟩).symm
  · have has : a ∉ s := fun has ↦ hat (h has)
    rw [extend_apply' _ _ _ fun ⟨b, hb⟩ ↦ has (hb ▸ b.property),
      extend_apply' _ _ _ fun ⟨b, hb⟩ ↦ hat (hb ▸ b.property)]

/-- `Function.extend` along a composite `f₂₃ ∘ f₁₂` is the iterated extension, provided only the
outer map `f₂₃` is injective. The inner extension of `g` along `f₁₂` uses the fallback `e' ∘ f₂₃`,
and the outer extension uses the fallback `e'`. This generalizes Mathlib's
`Function.Injective.extend_comp`, dropping injectivity of the inner map `f₁₂`. -/
theorem Injective.extend_comp_extend {α β γ δ : Type*} {f₁₂ : α → β} {f₂₃ : β → γ}
    (h : Function.Injective f₂₃) (g : α → δ) (e' : γ → δ) :
    extend (f₂₃ ∘ f₁₂) g e' = extend f₂₃ (extend f₁₂ g (e' ∘ f₂₃)) e' := by
  classical
  funext x
  simp only [Function.comp_def]
  by_cases hk : ∃ k, f₂₃ k = x
  · obtain ⟨k, rfl⟩ := hk
    rw [h.extend_apply]
    by_cases hx : ∃ a, f₁₂ a = k
    · have hpred : (fun a => f₂₃ (f₁₂ a) = f₂₃ k) = fun a => f₁₂ a = k :=
        funext fun a => propext h.eq_iff
      rw [extend_def, extend_def]
      simp only [hx, dite_true, hpred]
    · rw [extend_apply' _ _ _ hx,
        extend_apply' _ _ _ (fun ⟨a, ha⟩ => hx ⟨a, h.eq_iff.1 ha⟩)]
  · rw [extend_apply' _ _ _ hk, extend_apply' _ _ _ (fun ⟨a, ha⟩ => hk ⟨_, ha⟩)]

/-- Restriction `g ↦ fun i ↦ g (f i)` of dependent functions along an injective map `f` is
surjective: extend by a fallback `g₀` off the range of `f`. This is the dependent version of
Mathlib's `Function.Injective.surjective_comp_right'`; Mathlib's `Subtype.surjective_restrict` is
the case of `Subtype.val`. -/
theorem Injective.surjective_pi_comp_right {σ τ : Type*} {G : τ → Sort*} {f : σ → τ}
    (hf : Injective f) (g₀ : ∀ j, G j) : Surjective fun (g : ∀ j, G j) i ↦ g (f i) := fun k ↦ by
  classical
  let e := Equiv.ofInjective f hf
  refine ⟨fun j ↦ if hj : j ∈ Set.range f then
    Equiv.piCongrLeft (fun j : Set.range f ↦ G j) e k ⟨j, hj⟩ else g₀ j, funext fun i ↦ ?_⟩
  simp only [Set.mem_range_self, ↓reduceDIte]
  exact Equiv.piCongrLeft_apply_apply (fun j : Set.range f ↦ G j) e k i

end Function
