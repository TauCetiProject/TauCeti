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
the commutator subgroup (`Abelianization.of_eq_one_iff`), so the abelianization map of a
commutative group is injective (`Abelianization.of_injective`), and isomorphisms out of an
abelianization are determined by their values on classes (`Abelianization.mulEquiv_ext`).
Every element of the additive abelianization is the class of a group element
(`Abelianization.exists_eq_ofMul_of`). The abelianization of a product of two groups is the
product of their abelianizations (`Abelianization.prodMulEquiv`).
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

/-- Written additively, every element of the abelianization is the class of a group element. -/
theorem exists_eq_ofMul_of (x : Additive (Abelianization G)) : ∃ g : G, x = .ofMul (of g) := by
  obtain ⟨g, hg⟩ : ∃ g, of g = x.toMul := QuotientGroup.mk_surjective x.toMul
  exact ⟨g, by rw [hg, ofMul_toMul]⟩

/-- The abelianization map of a commutative group is injective. -/
theorem of_injective [IsMulCommutative G] : Function.Injective (of (G := G)) :=
  (MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_of, commutator_eq_bot])

/-- Two isomorphisms out of an abelianization agree if they agree on the classes of elements. -/
theorem mulEquiv_ext {M : Type*} [Monoid M] {e e' : Abelianization G ≃* M}
    (h : ∀ x : G, e (of x) = e' (of x)) : e = e' :=
  MulEquiv.toMonoidHom_injective (hom_ext _ _ (MonoidHom.ext h))

/-- **The abelianization of a product** of two groups is the product of their abelianizations:
the class of `(g, h)` corresponds to the pair of the classes of `g` and `h`. -/
def prodMulEquiv (H : Type*) [Group H] :
    Abelianization (G × H) ≃* Abelianization G × Abelianization H where
  __ := lift (MonoidHom.prodMap of of)
  invFun := MonoidHom.coprod (map (MonoidHom.inl G H)) (map (MonoidHom.inr G H))
  left_inv w := QuotientGroup.induction_on w fun gh ↦ by
    -- The inverse sends the pair of classes of `gh.1` and `gh.2` to the product of the classes of
    -- `(gh.1, 1)` and `(1, gh.2)`; the classes are `QuotientGroup.mk`, which is `of`.
    change of ((gh.1, 1) : G × H) * of ((1, gh.2) : G × H) = of gh
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  right_inv := by
    rintro ⟨a, b⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
    -- The classes `QuotientGroup.mk g` are `of g`, and `map` sends `of x` to `of` of its image.
    change (of g, of 1) * (of 1, of h) = (of g, of h)
    simp [Prod.mk_mul_mk]

@[simp]
theorem prodMulEquiv_of (H : Type*) [Group H] (gh : G × H) :
    prodMulEquiv H (of gh) = (of gh.1, of gh.2) :=
  (rfl)

end Abelianization
