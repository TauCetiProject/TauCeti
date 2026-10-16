/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Elementary facts about the abelianization

Conjugate elements have the same image in the abelianization (`Abelianization.of_inv_mul_mul`),
and written additively, the abelianization map sends products to sums in either order
(`Abelianization.ofMul_of_add_ofMul_of`). An element has trivial image exactly when it lies in
the commutator subgroup (`Abelianization.of_eq_one_iff`), and isomorphisms out of an
abelianization are determined by their values on classes (`Abelianization.mulEquiv_ext`).
-/

public section

namespace Abelianization

variable {G : Type*} [Group G]

/-- Conjugate elements have the same image in the abelianization. -/
@[simp]
lemma of_inv_mul_mul (p q : G) : of (p⁻¹ * q * p) = of q := by
  simp only [map_mul, map_inv, inv_mul_cancel_comm]

/-- Written additively, the abelianization map sends the product `q * p` to the sum of the images
of `p` and `q`. -/
lemma ofMul_of_add_ofMul_of (p q : G) :
    Additive.ofMul (of p) + Additive.ofMul (of q) = Additive.ofMul (of (q * p)) := by
  rw [← ofMul_mul]
  simp [mul_comm]

/-- An element has trivial image in the abelianization exactly when it is in the commutator
subgroup. -/
@[simp]
theorem of_eq_one_iff {g : G} : of g = 1 ↔ g ∈ commutator G := by
  rw [← MonoidHom.mem_ker, ker_of]

/-- Two isomorphisms out of an abelianization agree if they agree on the classes of elements. -/
theorem mulEquiv_ext {M : Type*} [Monoid M] {e e' : Abelianization G ≃* M}
    (h : ∀ x : G, e (of x) = e' (of x)) : e = e' :=
  MulEquiv.toMonoidHom_injective (hom_ext _ _ (MonoidHom.ext h))

end Abelianization
