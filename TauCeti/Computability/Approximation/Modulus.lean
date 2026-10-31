/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Partrec
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.PartialSups
import Mathlib.Order.Filter.Finite

/-!
# Limit approximations and their moduli

A sequence of total functions `f : ℕ → α → β`, read as the stages `f s`, **converges** to
`g : α → β` when it agrees with `g` at every point from some stage on:
`∀ x, ∀ᶠ s in atTop, f s x = g x`. The stage after which the value at `x` is correct depends on
`x` and is not part of the data. A **modulus** of convergence is a function `m : α → ℕ` supplying
such stages: `f s x = g x` whenever `m x ≤ s`.

These are the notions of the Limit Lemma, by which the functions computable relative to the
halting problem are exactly the limits of uniformly computable sequences, and of the Modulus
Lemma, by which a function computable in a c.e. set has a computable approximation with a modulus
computable in that set. Neither lemma is proved here. What is proved is the elementary calculus of
limits and moduli, and the unrelativized fact that a uniformly computable sequence with a
computable modulus has a computable limit. Convergence alone does not suffice: the halting problem
is the limit of its increasing approximation by step-bounded evaluation, which therefore has no
computable modulus.

## Main definitions

* `TauCeti.Approximation.Converges f g`: the stages `f s` agree with `g` at every point from some
  stage on.
* `TauCeti.Approximation.IsModulus f g m`: `m x` is a stage after which `f s x = g x`.

## Main results

* `TauCeti.Approximation.converges_iff_exists_isModulus`: a sequence converges exactly when it has
  a modulus.
* `TauCeti.Approximation.Converges.unique`: limits are unique.
* `TauCeti.Approximation.Converges.eventually_forall_mem`,
  `TauCeti.Approximation.IsModulus.forall_mem_of_sup_le`: finite-coordinate aggregation. Finitely
  many coordinates are simultaneously correct from some stage on, and from the largest of their
  moduli on.
* `TauCeti.Approximation.Converges.exists_monotone_isModulus`: a convergent sequence on `ℕ`, or on
  any locally finite order with a bottom, has a monotone modulus.
* `TauCeti.Approximation.converges_shift_iff`, `TauCeti.Approximation.IsModulus.shift`,
  `TauCeti.Approximation.IsModulus.of_shift`: shifting the stages preserves the limit, and moves
  the modulus by the shift.
* `TauCeti.Approximation.Converges.comp_tendsto`, `TauCeti.Approximation.IsModulus.comp`:
  reindexing the stages by a clock tending to infinity preserves the limit; a modulus for the
  clock turns a modulus of the sequence into one of the reindexed sequence.
* `TauCeti.Approximation.IsModulus.computable`: a uniformly computable sequence with a computable
  modulus has a computable limit.
* `TauCeti.Approximation.computable_iff_exists_isModulus`: a function is computable exactly when
  it is the limit of a uniformly computable sequence with a computable modulus.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.3.
-/

public section

open Filter

namespace TauCeti

namespace Approximation

variable {α β : Type*} {f : ℕ → α → β} {g g' : α → β} {m m' : α → ℕ}

/-! ### Convergence -/

/-- The stages `f s` **converge** to `g`: at every point `x`, the value `f s x` equals `g x` from
some stage on. The stage may depend on `x`. -/
def Converges (f : ℕ → α → β) (g : α → β) : Prop :=
  ∀ x, ∀ᶠ s in atTop, f s x = g x

/-- Unfolding `TauCeti.Approximation.Converges`. -/
theorem converges_iff_eventually : Converges f g ↔ ∀ x, ∀ᶠ s in atTop, f s x = g x :=
  Iff.rfl

/-- Convergence with an explicit stage at every point. -/
theorem converges_iff_forall_exists :
    Converges f g ↔ ∀ x, ∃ s₀, ∀ s, s₀ ≤ s → f s x = g x := by
  simp [converges_iff_eventually, eventually_atTop]

/-- Convergence is pointwise convergence to `g` in the discrete sense: each sequence of values
tends to the principal filter of its limit. -/
theorem converges_iff_tendsto :
    Converges f g ↔ ∀ x, Tendsto (fun s => f s x) atTop (pure (g x)) := by
  simp [converges_iff_eventually]

/-- **Uniqueness of limits.** -/
theorem Converges.unique (h : Converges f g) (h' : Converges f g') : g = g' :=
  funext fun x => ((h x).and (h' x)).exists.elim fun _ hs => hs.1.symm.trans hs.2

/-- A constant sequence converges to its value. -/
@[simp]
theorem converges_const (g : α → β) : Converges (fun _ => g) g :=
  fun _ => Eventually.of_forall fun _ => rfl

/-- **Finite-coordinate aggregation.** Finitely many coordinates of a convergent sequence are
simultaneously correct from some stage on. -/
theorem Converges.eventually_forall_mem (h : Converges f g) (F : Finset α) :
    ∀ᶠ s in atTop, ∀ x ∈ F, f s x = g x :=
  (eventually_all_finset F).2 fun x _ => h x

/-! ### Moduli -/

/-- `m` is a **modulus** of the convergence of `f` to `g`: from stage `m x` on, the value at `x`
is `g x`. -/
def IsModulus (f : ℕ → α → β) (g : α → β) (m : α → ℕ) : Prop :=
  ∀ x s, m x ≤ s → f s x = g x

/-- Unfolding `TauCeti.Approximation.IsModulus`. -/
theorem isModulus_iff : IsModulus f g m ↔ ∀ x s, m x ≤ s → f s x = g x :=
  Iff.rfl

/-- The value at the stage given by a modulus is the limit. -/
theorem IsModulus.apply_eq (hm : IsModulus f g m) (x : α) : f (m x) x = g x :=
  hm x _ le_rfl

/-- A sequence with a modulus converges. -/
theorem IsModulus.converges (hm : IsModulus f g m) : Converges f g :=
  fun x => eventually_atTop.2 ⟨m x, hm x⟩

/-- A sequence converges exactly when it has a modulus. -/
theorem converges_iff_exists_isModulus : Converges f g ↔ ∃ m, IsModulus f g m :=
  ⟨fun h => ⟨fun x => (converges_iff_forall_exists.1 h x).choose,
    fun x => (converges_iff_forall_exists.1 h x).choose_spec⟩, fun ⟨_, hm⟩ => hm.converges⟩

/-- A convergent sequence has a modulus. -/
theorem Converges.exists_isModulus (h : Converges f g) : ∃ m, IsModulus f g m :=
  converges_iff_exists_isModulus.1 h

/-- Every larger function is a modulus too. -/
theorem IsModulus.mono (hm : IsModulus f g m) (h : m ≤ m') : IsModulus f g m' :=
  fun x s hs => hm x s ((h x).trans hs)

/-- Every function is a modulus of a constant sequence. -/
@[simp]
theorem isModulus_const (g : α → β) (m : α → ℕ) : IsModulus (fun _ => g) g m :=
  fun _ _ _ => rfl

/-- **Finite-coordinate aggregation for a modulus.** From the largest modulus of finitely many
coordinates on, all of them are correct. -/
theorem IsModulus.forall_mem_of_sup_le (hm : IsModulus f g m) {F : Finset α} {s : ℕ}
    (hs : F.sup m ≤ s) : ∀ x ∈ F, f s x = g x :=
  fun x hx => hm x s ((Finset.le_sup hx).trans hs)

/-- A modulus can be replaced by its partial suprema `x ↦ max_{y ≤ x} m y`, which are monotone
(`partialSups_monotone`). From that stage on, every coordinate up to `x` is correct. -/
theorem IsModulus.partialSups [Preorder α] [LocallyFiniteOrderBot α] (hm : IsModulus f g m) :
    IsModulus f g (partialSups m) :=
  hm.mono (le_partialSups m)

/-- A convergent sequence on a locally finite order with a bottom, such as `ℕ`, has a monotone
modulus. -/
theorem Converges.exists_monotone_isModulus [Preorder α] [LocallyFiniteOrderBot α]
    (h : Converges f g) : ∃ m : α → ℕ, Monotone m ∧ IsModulus f g m := by
  obtain ⟨m, hm⟩ := h.exists_isModulus
  exact ⟨_, partialSups_monotone m, hm.partialSups⟩

/-! ### Shifts and reindexing -/

/-- **Stage shifts.** Dropping the first `k` stages does not change convergence or the limit. -/
@[simp]
theorem converges_shift_iff (k : ℕ) : Converges (fun s => f (s + k)) g ↔ Converges f g := by
  simp only [converges_iff_tendsto]
  exact forall_congr' fun x => tendsto_add_atTop_iff_nat (f := fun s => f s x) k

/-- After dropping the first `k` stages, a modulus decreases by `k`. -/
theorem IsModulus.shift (hm : IsModulus f g m) (k : ℕ) :
    IsModulus (fun s => f (s + k)) g fun x => m x - k :=
  fun x s (hs : m x - k ≤ s) => hm x (s + k) (by omega)

/-- A modulus of the sequence with the first `k` stages dropped, increased by `k`, is a modulus of
the original sequence. -/
theorem IsModulus.of_shift {k : ℕ} (hm : IsModulus (fun s => f (s + k)) g m) :
    IsModulus f g fun x => m x + k :=
  fun x s (hs : m x + k ≤ s) => by
    simpa [Nat.sub_add_cancel (le_of_add_le_right hs)] using hm x (s - k) (by omega)

/-- **Reindexing by a clock.** Reading the stages along a clock `t` tending to infinity preserves
the limit. The clock need not be monotone. -/
theorem Converges.comp_tendsto (h : Converges f g) {t : ℕ → ℕ} (ht : Tendsto t atTop atTop) :
    Converges (fun s => f (t s)) g :=
  fun x => ht.eventually (h x)

/-- **Effective reindexing.** If `n k` is a stage after which the clock `t` stays at least `k`,
then `n ∘ m` is a modulus of the reindexed sequence. For a computable clock modulus `n` and a
computable modulus `m`, this modulus is computable. -/
theorem IsModulus.comp (hm : IsModulus f g m) {t n : ℕ → ℕ} (ht : ∀ k s, n k ≤ s → k ≤ t s) :
    IsModulus (fun s => f (t s)) g fun x => n (m x) :=
  fun x s hs => hm x (t s) (ht _ s hs)

/-! ### Computability of limits -/

variable [Primcodable α] [Primcodable β]

/-- **Computable modulus, computable limit.** A uniformly computable sequence with a computable
modulus has a computable limit: evaluate the sequence at the stage given by the modulus. -/
theorem IsModulus.computable (hm : IsModulus f g m) (hf : Computable₂ f) (hmc : Computable m) :
    Computable g :=
  (hf.comp hmc Computable.id).of_eq hm.apply_eq

/-- A function is computable exactly when it is the limit of a uniformly computable sequence with
a computable modulus. -/
theorem computable_iff_exists_isModulus :
    Computable g ↔ ∃ (f : ℕ → α → β) (m : α → ℕ), Computable₂ f ∧ Computable m ∧ IsModulus f g m :=
  ⟨fun hg => ⟨fun _ => g, fun _ => 0, hg.comp Computable.snd, Computable.const 0,
    isModulus_const g _⟩, fun ⟨_, _, hf, hm, h⟩ => h.computable hf hm⟩

end Approximation

end TauCeti
