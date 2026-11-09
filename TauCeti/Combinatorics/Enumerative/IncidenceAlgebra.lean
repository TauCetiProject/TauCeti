/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# Order invariance, converse Möbius inversion and Weisner's theorem

The Möbius function is invariant under order isomorphisms (`OrderIso.mu_map`).

Mathlib's `IncidenceAlgebra.moebius_inversion_bot` recovers `f` from its lower sums
`g x = ∑_{y ≤ x} f y` as `f x = ∑_{y ≤ x} μ(y, x) g y`. This file proves the converse direction:
summing the Möbius transform `x ↦ ∑_{z ≤ x} μ(z, x) g z` over the lower set of `x` gives back
`g x`.

It also proves Weisner's theorem: in a finite lattice, the values `μ(⊥, x)` summed over the
elements `x` whose join with a fixed `a ≠ ⊥` is `⊤` cancel. Choosing `a` to be an atom turns this
into a recurrence for `μ(⊥, ⊤)` in terms of the Möbius function on smaller intervals; this is how
the Möbius function of the lattice of noncrossing partitions is computed.

## Main results

* `IncidenceAlgebra.sum_Iic_sum_Iic_mu_mul` — `∑_{y ≤ x} ∑_{z ≤ y} μ(z, y) g z = g x`.
* `IncidenceAlgebra.sum_filter_sup_eq_top_mu_bot_eq_zero` — *Weisner's theorem*: for `a ≠ ⊥`,
  `∑_{x ⊔ a = ⊤} μ(⊥, x) = 0`.

## References

* L. Weisner, *Abstract theory of inversion of finite series*, Trans. Amer. Math. Soc. 38 (1935),
  474–484.
* R. P. Stanley, *Enumerative Combinatorics, Volume 1*, 2nd ed., Corollary 3.9.3.
-/

public section

open Finset IncidenceAlgebra

namespace OrderIso

variable {𝕜 α β : Type*} [AddCommGroup 𝕜] [One 𝕜]
  [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]
  [PartialOrder β] [LocallyFiniteOrder β] [DecidableEq β]

/-- The Möbius function is invariant under order isomorphisms. -/
@[simp]
theorem mu_map (e : α ≃o β) (a b : α) : mu 𝕜 (e a) (e b) = mu 𝕜 a b := by
  induction hn : #(Icc a b) using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    by_cases hab : a = b
    · subst b
      simp
    rw [mu_eq_neg_sum_Ico_of_ne (e.injective.ne hab), mu_eq_neg_sum_Ico_of_ne hab]
    congr 1
    refine sum_bij (fun x _ => e.symm x) (fun x hx => ?_) ?_ ?_ ?_
    · exact mem_Ico.2 ⟨by simpa using e.symm.monotone (mem_Ico.1 hx).1,
        by simpa using e.symm.strictMono (mem_Ico.1 hx).2⟩
    · intro x hx y hy hxy
      exact e.symm.injective hxy
    · intro x hx
      exact ⟨e x, by simpa using hx, e.symm_apply_apply x⟩
    · intro x hx
      have h := mem_Ico.1 hx
      have hlt : #(Icc a (e.symm x)) < #(Icc a b) := card_lt_card
        (Icc_ssubset_Icc_right (by simpa using e.symm.monotone (h.1.trans h.2.le)) le_rfl
          (by simpa using e.symm.strictMono h.2))
      simpa using ih _ (hn ▸ hlt) (e.symm x) rfl

end OrderIso

namespace IncidenceAlgebra

section Converse

variable {𝕜 α : Type*} [NonAssocRing 𝕜] [PartialOrder α] [LocallyFiniteOrder α]
  [LocallyFiniteOrderBot α] [DecidableEq α]

/-- *Converse Möbius inversion*: the lower sums of the Möbius transform
`y ↦ ∑_{z ≤ y} μ(z, y) g z` of `g` recover `g`, `∑_{y ≤ x} ∑_{z ≤ y} μ(z, y) g z = g x`. -/
theorem sum_Iic_sum_Iic_mu_mul (g : α → 𝕜) (x : α) :
    ∑ y ∈ Iic x, ∑ z ∈ Iic y, mu 𝕜 z y * g z = g x := by
  rw [sum_comm' (t' := Iic x) (s' := fun z => Icc z x) fun y z => by
    simp only [mem_Iic, mem_Icc]
    exact ⟨fun h => ⟨⟨h.2, h.1⟩, h.2.trans h.1⟩, fun h => ⟨h.1.2, h.1.1⟩⟩]
  simp [← sum_mul, sum_Icc_mu_right]

end Converse

section Weisner

variable {𝕜 α : Type*} [Ring 𝕜] [Lattice α] [BoundedOrder α] [LocallyFiniteOrder α]
  [DecidableEq α]

/-- *Weisner's theorem*: in a finite lattice, for every `a ≠ ⊥` the Möbius function `μ(⊥, x)`
sums to zero over the elements `x` with `x ⊔ a = ⊤`. -/
theorem sum_filter_sup_eq_top_mu_bot_eq_zero {a : α} (ha : a ≠ ⊥) :
    ∑ x ∈ Icc ⊥ ⊤ with x ⊔ a = ⊤, mu 𝕜 ⊥ x = 0 := by
  classical
  -- Detect `x ⊔ a = ⊤` by `∑_{x ⊔ a ≤ y} μ(y, ⊤)`, then exchange the two sums: the inner sum
  -- `∑_{x ≤ y} μ(⊥, x)` vanishes for every `y ≥ a`, since such `y` is not `⊥`.
  have hdetect (x : α) : (if x ⊔ a = ⊤ then mu 𝕜 ⊥ x else 0) =
      ∑ y ∈ Icc ⊥ ⊤, if x ⊔ a ≤ y then mu 𝕜 ⊥ x * mu 𝕜 y ⊤ else 0 := by
    rw [← sum_filter, ← mul_sum,
      show {y ∈ Icc (⊥ : α) ⊤ | x ⊔ a ≤ y} = Icc (x ⊔ a) ⊤ by ext; simp, sum_Icc_mu_left]
    split_ifs <;> simp
  have hinner (y : α) : ∑ x ∈ Icc ⊥ ⊤, (if x ⊔ a ≤ y then mu 𝕜 ⊥ x * mu 𝕜 y ⊤ else 0) = 0 := by
    by_cases hay : a ≤ y
    · simp_rw [sup_le_iff, and_iff_left hay]
      rw [← sum_filter, show {x ∈ Icc (⊥ : α) ⊤ | x ≤ y} = Icc ⊥ y by ext; simp, ← sum_mul,
        sum_Icc_mu_right, ite_eq_right fun h : ⊥ = y => ha (le_bot_iff.1 (h ▸ hay)), zero_mul]
    · exact sum_eq_zero fun x _ => ite_eq_right fun h => hay (le_sup_right.trans h)
  rw [sum_filter, sum_congr rfl fun x _ => hdetect x, sum_comm]
  exact sum_eq_zero fun y _ => hinner y

end Weisner

end IncidenceAlgebra
