/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Enumerating the cycles of a permutation

Let `σ` be a permutation of a finite type `α`. Every point lies on exactly one cycle of `σ`, a class
of the relation `Equiv.Perm.SameCycle σ`, and the cycle through `x` consists of the points
`σ^[i] x` for `i < Function.minimalPeriod σ x`, each listed once. Choosing the point `c.out` on
each cycle `c` gives the equivalence `Equiv.Perm.sigmaCycleEquiv σ` from
`Σ c, Fin (Function.minimalPeriod σ c.out)` to `α`, under which `σ` acts on each summand by the
rotation `finRotate`. This is the shape of input taken by results about maps acting cyclically on
the members of a family, such as the classification of the fixed vectors of a linear map that
permutes a basis up to scalars.

## Main definitions

* `Equiv.Perm.sigmaCycleEquiv`: the enumeration `⟨c, i⟩ ↦ σ^[i] c.out` of the points of `α`.

## Main results

* `Equiv.Perm.sameCycle_iterate_right`: iterating `σ` stays on the same cycle.
* `Equiv.Perm.sameCycle_mk_out_left`: the chosen point of the cycle through `x` shares a cycle with
  exactly the points that `x` does.
* `Equiv.Perm.apply_sigmaCycleEquiv`: `σ` acts on the enumeration by `finRotate` on each cycle.
* `Equiv.Perm.mk_sigmaCycleEquiv`: the point at position `⟨c, i⟩` lies on the cycle `c`.
* `Equiv.Perm.prod_sigmaCycleEquiv`: a product over the positions of a cycle is the product over
  its points.
-/

public section

open Function

namespace Equiv.Perm

section SameCycle

variable {α : Type*} {f : Perm α} {x y : α}

/-- Iterating a permutation on the right stays on the same cycle; the iterate form of
`Equiv.Perm.sameCycle_pow_right`. -/
@[simp]
theorem sameCycle_iterate_right {n : ℕ} : f.SameCycle x (f^[n] y) ↔ f.SameCycle x y := by
  rw [← coe_pow, sameCycle_pow_right]

/-- The chosen point of the cycle through `x` shares a cycle with exactly the points that `x`
does. -/
theorem sameCycle_mk_out_left :
    f.SameCycle (Quotient.mk (SameCycle.setoid f) x).out y ↔ f.SameCycle x y :=
  have hx := Quotient.mk_out (s := SameCycle.setoid f) x
  ⟨hx.symm.trans, hx.trans⟩

end SameCycle

variable {α : Type*} [Finite α] (σ : Perm α)

/-- **Enumeration of the cycles of a permutation.** For a permutation `σ` of a finite type, the
equivalence sending the position `⟨c, i⟩`, where `c` is a cycle of `σ` and
`i < Function.minimalPeriod σ c.out`, to the point `σ^[i] c.out`. -/
noncomputable def sigmaCycleEquiv :
    (Σ c : Quotient (SameCycle.setoid σ), Fin (minimalPeriod σ c.out)) ≃ α :=
  Equiv.ofBijective (fun p ↦ σ^[p.2] p.1.out) <| by
    constructor
    · rintro ⟨c, i⟩ ⟨d, j⟩ h
      simp only at h
      have hcd : c = d := by
        rw [← Quotient.out_eq c, ← Quotient.out_eq d]
        refine Quotient.sound ?_
        exact ((sameCycle_iterate_right.2 (SameCycle.refl σ c.out)).trans
          (h ▸ (sameCycle_iterate_right.2 (SameCycle.refl σ d.out)).symm))
      subst hcd
      exact Sigma.ext rfl (heq_of_eq (Fin.ext (iterate_injOn_Iio_minimalPeriod i.2 j.2 h)))
    · intro y
      have hy : σ.SameCycle (Quotient.mk (SameCycle.setoid σ) y).out y :=
        Quotient.mk_out (s := SameCycle.setoid σ) y
      obtain ⟨k, hk⟩ := hy.exists_nat_pow_eq
      refine ⟨⟨Quotient.mk _ y, ⟨k % minimalPeriod σ _, Nat.mod_lt _
        (minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts _))⟩⟩,
        ?_⟩
      simp only
      rw [iterate_mod_minimalPeriod_eq, ← coe_pow, hk]

@[simp]
theorem sigmaCycleEquiv_apply (c : Quotient (SameCycle.setoid σ))
    (i : Fin (minimalPeriod σ c.out)) : σ.sigmaCycleEquiv ⟨c, i⟩ = σ^[i] c.out :=
  (rfl)

/-- The point at position `⟨c, i⟩` lies on the cycle `c`. -/
@[simp]
theorem mk_sigmaCycleEquiv (p : Σ c : Quotient (SameCycle.setoid σ), Fin (minimalPeriod σ c.out)) :
    Quotient.mk (SameCycle.setoid σ) (σ.sigmaCycleEquiv p) = p.1 := by
  obtain ⟨c, i⟩ := p
  exact Quotient.mk_eq_iff_out.2 (sameCycle_iterate_right.2 (SameCycle.refl σ c.out)).symm

/-- The point at position `⟨c, i⟩` lies on the same cycle as the chosen point `c.out`. -/
theorem sameCycle_out_sigmaCycleEquiv (c : Quotient (SameCycle.setoid σ))
    (i : Fin (minimalPeriod σ c.out)) : σ.SameCycle c.out (σ.sigmaCycleEquiv ⟨c, i⟩) :=
  sameCycle_iterate_right.2 (SameCycle.refl σ c.out)

/-- **`σ` rotates each enumerated cycle.** Applying `σ` to the point at position `⟨c, i⟩` gives the
point at position `⟨c, finRotate _ i⟩`. -/
theorem apply_sigmaCycleEquiv (c : Quotient (SameCycle.setoid σ))
    (i : Fin (minimalPeriod σ c.out)) :
    σ (σ.sigmaCycleEquiv ⟨c, i⟩) = σ.sigmaCycleEquiv ⟨c, finRotate _ i⟩ := by
  have : NeZero (minimalPeriod σ c.out) :=
    ⟨(minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts c.out)).ne'⟩
  rw [sigmaCycleEquiv_apply, sigmaCycleEquiv_apply, finRotate_apply, Fin.val_add, Fin.val_one',
    Nat.add_mod_mod, iterate_mod_minimalPeriod_eq, iterate_succ_apply']

/-- **Products over an enumerated cycle.** The product over the positions of the cycle `c` is the
product over the points of `α` on that cycle. -/
@[to_additive /-- **Sums over an enumerated cycle.** The sum over the positions of the cycle `c` is
the sum over the points of `α` on that cycle. -/]
theorem prod_sigmaCycleEquiv {M : Type*} [CommMonoid M] [Fintype α] [DecidableRel σ.SameCycle]
    (c : Quotient (SameCycle.setoid σ)) (f : α → M) :
    ∏ i, f (σ.sigmaCycleEquiv ⟨c, i⟩) = ∏ x with σ.SameCycle c.out x, f x := by
  refine Finset.prod_bij (fun i _ ↦ σ.sigmaCycleEquiv ⟨c, i⟩) (fun i _ ↦ ?_)
    (fun i _ j _ h ↦ ?_) (fun x hx ↦ ?_) fun _ _ ↦ rfl
  · simpa using σ.sameCycle_out_sigmaCycleEquiv c i
  · simpa using σ.sigmaCycleEquiv.injective h
  · have hx : Quotient.mk (SameCycle.setoid σ) x = c :=
      Quotient.mk_eq_iff_out.2 (Finset.mem_filter.1 hx).2.symm
    obtain ⟨⟨d, i⟩, rfl⟩ := σ.sigmaCycleEquiv.surjective x
    rw [mk_sigmaCycleEquiv] at hx
    subst hx
    exact ⟨i, Finset.mem_univ _, rfl⟩

end Equiv.Perm
