/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Ring

/-!
# Dependent products over finite sets in graded commutative monoids

For a graded monoid `A : ι → Type*`, Mathlib's `List.dProd` multiplies a list of homogeneous
elements `fA a : A (fι a)` in the given order, landing in degree `l.dProdIndex fι`. When the
multiplication is commutative (`GradedMonoid.GCommMonoid A`), the order no longer matters, and
the product can be taken over a finite set: `Finset.dProd s fι fA : A (∑ a ∈ s, fι a)`. This is
the form in which a product over an unordered finite index type is stated, for instance the cup
product of a family of cohomology classes indexed by the double cosets `V \ G / U`.

The degree `∑ a ∈ s, fι a` is not definitionally the degree of the product computed in the
commutative monoid `GradedMonoid A`, so `Finset.dProd` is defined through a cast. It is
characterized by `GradedMonoid.mk_finset_dProd`, which identifies it with the product
`∏ a ∈ s, GradedMonoid.mk (fι a) (fA a)` in `GradedMonoid A`, and `Finset.eq_dProd_iff` lets an
element of `A (∑ a ∈ s, fι a)` be recognized as the product by that equation, so the cast never has
to be unfolded.

## Main definitions

* `Finset.dProd`: the dependent product over a finite set of homogeneous elements of a graded
  commutative monoid.

## Main results

* `GradedMonoid.fst_prod`: the degree of a finite product is the sum of the degrees.
* `GradedMonoid.mk_finset_dProd`: the characteristic equation of `Finset.dProd`.
* `Finset.eq_dProd_iff`: an element is the dependent product exactly when it satisfies that
  equation.
* `Finset.map_dProd`: degree-preserving maps respecting the unit and the multiplication commute
  with dependent products.
* `DirectSum.of_finset_dProd`: in the direct sum, the dependent product is the ordinary product.
-/

public section

variable {ι α : Type*} {A : ι → Type*}

namespace GradedMonoid

variable [AddCommMonoid ι] [GCommMonoid A]

/-- The degree of a finite product of homogeneous elements is the sum of their degrees. -/
@[simp]
theorem fst_prod (s : Finset α) (f : α → GradedMonoid A) :
    (∏ a ∈ s, f a).fst = ∑ a ∈ s, (f a).fst := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, fst_mul, ih]

end GradedMonoid

namespace Finset

variable [AddCommMonoid ι] [GradedMonoid.GCommMonoid A]

/-- The **dependent product** over a finite set `s` of homogeneous elements `fA a : A (fι a)` of a
graded commutative monoid, an element of degree `∑ a ∈ s, fι a`. This is the unordered counterpart
of `List.dProd`; it is characterized by `GradedMonoid.mk_finset_dProd`. -/
def dProd (s : Finset α) (fι : α → ι) (fA : ∀ a, A (fι a)) : A (∑ a ∈ s, fι a) :=
  cast (congrArg A (GradedMonoid.fst_prod s fun a ↦ GradedMonoid.mk (fι a) (fA a)))
    (∏ a ∈ s, GradedMonoid.mk (fι a) (fA a)).snd

end Finset

/-- **The characteristic equation of `Finset.dProd`**: as an element of `GradedMonoid A`, the
dependent product is the product of the homogeneous factors. -/
theorem GradedMonoid.mk_finset_dProd [AddCommMonoid ι] [GCommMonoid A] (s : Finset α)
    (fι : α → ι) (fA : ∀ a, A (fι a)) :
    mk _ (s.dProd fι fA) = ∏ a ∈ s, mk (fι a) (fA a) :=
  -- the one place the cast in the definition is unfolded
  Sigma.ext (fst_prod s fun a ↦ mk (fι a) (fA a)).symm
    (by unfold Finset.dProd; exact cast_heq _ _)

namespace Finset

variable [AddCommMonoid ι] [GradedMonoid.GCommMonoid A]

/-- An element of degree `∑ a ∈ s, fι a` is the dependent product exactly when, as an element of
`GradedMonoid A`, it is the product of the homogeneous factors. -/
theorem eq_dProd_iff {s : Finset α} {fι : α → ι} {fA : ∀ a, A (fι a)}
    {x : A (∑ a ∈ s, fι a)} :
    x = s.dProd fι fA ↔ GradedMonoid.mk _ x = ∏ a ∈ s, GradedMonoid.mk (fι a) (fA a) := by
  rw [← GradedMonoid.mk_finset_dProd]
  exact ⟨congrArg _, fun h ↦ sigma_mk_injective h⟩

/-- A degree-preserving map between graded commutative monoids that respects the unit and the
multiplication commutes with dependent products over finite sets. -/
theorem map_dProd {B : ι → Type*} [GradedMonoid.GCommMonoid B] (F : ∀ {i}, A i → B i)
    (hone : F GradedMonoid.GOne.one = GradedMonoid.GOne.one)
    (hmul : ∀ {i j} (a : A i) (b : A j),
      F (GradedMonoid.GMul.mul a b) = GradedMonoid.GMul.mul (F a) (F b))
    (s : Finset α) (fι : α → ι) (fA : ∀ a, A (fι a)) :
    F (s.dProd fι fA) = s.dProd fι fun a ↦ F (fA a) := by
  -- `F` applied in every degree is a monoid homomorphism of the total graded monoids
  let Φ : GradedMonoid A →* GradedMonoid B :=
    { toFun := fun x ↦ ⟨x.fst, F x.snd⟩
      map_one' := congrArg (GradedMonoid.mk 0) hone
      map_mul' := fun x y ↦ congrArg (GradedMonoid.mk _) (hmul x.snd y.snd) }
  rw [eq_dProd_iff]
  exact (congrArg Φ (GradedMonoid.mk_finset_dProd s fι fA)).trans (map_prod Φ _ s)

end Finset

/-- In the direct sum of a graded commutative semiring, the dependent product over a finite set is
the ordinary product of the homogeneous components. -/
theorem DirectSum.of_finset_dProd [DecidableEq ι] [AddCommMonoid ι] [∀ i, AddCommMonoid (A i)]
    [GCommSemiring A] (s : Finset α) (fι : α → ι) (fA : ∀ a, A (fι a)) :
    of A _ (s.dProd fι fA) = ∏ a ∈ s, of A (fι a) (fA a) := by
  -- `of` read on the total graded monoid is a monoid homomorphism into the direct sum
  let Φ : GradedMonoid A →* DirectSum ι A :=
    { toFun := fun x ↦ of A x.fst x.snd
      map_one' := rfl
      map_mul' := fun x y ↦ (of_mul_of x.snd y.snd).symm }
  exact (congrArg Φ (GradedMonoid.mk_finset_dProd s fι fA)).trans (map_prod Φ _ s)
