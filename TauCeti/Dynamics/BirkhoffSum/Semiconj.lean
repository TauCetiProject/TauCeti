/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Basic

/-!
# Birkhoff sums along a semiconjugacy

If `h : α → β` semiconjugates `f : α → α` to `g : β → β`, that is `h ∘ f = g ∘ h`, then the
Birkhoff sums of `φ ∘ h` along `f` are the Birkhoff sums of `φ` along `g` composed with `h`. This
generalizes Mathlib's `birkhoffSum_comp_apply`, the case `h = f = g`.

## Main results

* `Function.Semiconj.birkhoffSum_comp_apply`: `birkhoffSum f (φ ∘ h) n x = birkhoffSum g φ n (h x)`.
* `Function.Semiconj.birkhoffSum_comp`: `birkhoffSum f (φ ∘ h) n = birkhoffSum g φ n ∘ h`.
-/

public section

namespace Function.Semiconj

variable {α β M : Type*} [AddCommMonoid M] {f : α → α} {g : β → β} {h : α → β}

/-- If `h` semiconjugates `f` to `g`, the Birkhoff sums of `φ ∘ h` along `f` are the Birkhoff sums
of `φ` along `g` at the image point. -/
theorem birkhoffSum_comp_apply (hsc : Semiconj h f g) (φ : β → M) (n : ℕ) (x : α) :
    birkhoffSum f (φ ∘ h) n x = birkhoffSum g φ n (h x) :=
  Finset.sum_congr rfl fun k _ ↦ by rw [comp_apply, hsc.iterate_right k x]

/-- If `h` semiconjugates `f` to `g`, the Birkhoff sums of `φ ∘ h` along `f` are the Birkhoff sums
of `φ` along `g` composed with `h`. -/
theorem birkhoffSum_comp (hsc : Semiconj h f g) (φ : β → M) (n : ℕ) :
    birkhoffSum f (φ ∘ h) n = birkhoffSum g φ n ∘ h :=
  funext <| hsc.birkhoffSum_comp_apply φ n

end Function.Semiconj
