/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.OrderOfElement

/-!
# Elements coprime to an ideal with finite quotient

Let `C` be an ideal of a commutative ring `R` with finite quotient `R ⧸ C`. An element `x` with
`(x) + C = R` is a unit modulo `C`, and the unit group of the finite ring `R ⧸ C` is finite, so
some positive power of `x` is congruent to `1` modulo `C`.

Consequently coprimality to `C` descends along any ring homomorphism `f : S →+* R`: if `f x` is
coprime to `C`, then `x` is coprime to the contraction `C.comap f`, since the inverse of `x` modulo
`C.comap f` can be taken to be a power of `x` itself. For an order `O` in a number field and its
conductor `𝔣`, this says that an element of `O` coprime to `𝔣` in the maximal order is already
coprime to `𝔣` in `O`.

## Main results

* `Ideal.exists_pow_sub_one_mem_of_sup_eq_top`: an element coprime to an ideal with finite
  quotient has a positive power congruent to `1`.
* `Ideal.span_singleton_sup_comap_eq_top`: coprimality to an ideal with finite quotient descends
  along a ring homomorphism.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] {C : Ideal R}

/-- An element coprime to an ideal `C` with finite quotient ring has a positive power congruent
to `1` modulo `C`. -/
theorem exists_pow_sub_one_mem_of_sup_eq_top [Finite (R ⧸ C)] {x : R} (hx : span {x} ⊔ C = ⊤) :
    ∃ n, 0 < n ∧ x ^ n - 1 ∈ C := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ((eq_top_iff_one _).mp hx)
  obtain ⟨s, rfl⟩ := mem_span_singleton'.mp ha
  -- The class of `x` is a unit of the finite ring `R ⧸ C`, so it has finite order.
  have hs : Quotient.mk C s * Quotient.mk C x = 1 := by
    rw [← map_mul, ← map_one (Quotient.mk C), ← hab, map_add,
      Quotient.eq_zero_iff_mem.mpr hb, add_zero]
  set u : (R ⧸ C)ˣ := (IsUnit.of_mul_eq_one_right _ hs).unit
  refine ⟨orderOf u, (isOfFinOrder_of_finite u).orderOf_pos, Quotient.eq.mp ?_⟩
  have h := congrArg Units.val (pow_orderOf_eq_one u)
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h
  rw [map_pow, map_one, h]

/-- **Coprimality descends along a ring homomorphism to an ideal with finite quotient.** If `f x`
is coprime to an ideal `C` with finite quotient ring, then `x` is coprime to `C.comap f`. -/
theorem span_singleton_sup_comap_eq_top [Finite (R ⧸ C)] (f : S →+* R) {x : S}
    (hx : span {f x} ⊔ C = ⊤) :
    span {x} ⊔ C.comap f = ⊤ := by
  obtain ⟨n, hn, hxn⟩ := exists_pow_sub_one_mem_of_sup_eq_top hx
  -- `1 = x * x ^ (n - 1) - (x ^ n - 1)`, where `x ^ n - 1` lies in the contraction of `C`.
  refine (eq_top_iff_one _).mpr (Submodule.mem_sup.mpr
    ⟨x * x ^ (n - 1), mul_mem_right _ _ (mem_span_singleton_self x), -(x ^ n - 1),
      neg_mem (by simpa [mem_comap] using hxn), ?_⟩)
  rw [← pow_succ', Nat.sub_add_cancel hn]
  ring

end Ideal
