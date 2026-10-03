/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product

/-!
# Graded commutativity of the Tate cup product with a degree-zero class

For a finite group `G`, the tensor braiding identifies the two orders of the Tate cup product when
one class has degree zero. Since the Koszul sign is `(-1)^(p * 0) = 1`, this is the degree-zero
edge of graded commutativity:

`β (x ∪ y) = y ∪ x` if either `x` or `y` has degree zero.

The result is built into the construction of the all-degree product. The product in bidegree
`(p, 0)` is `cupH0`, while the product in bidegree `(0, p)` is its opposite transported through
the tensor braiding (`cup0H`). The symmetry identity for the braiding then gives both edge forms.
These are the base cases for extending graded commutativity through the dimension shifts defining
the product in arbitrary integer bidegrees.

## Main statements

* `TauCeti.TateCohomology.cupH0_eq_flip_cup0H`: graded commutativity in bidegree `(p, 0)`.
* `TauCeti.TateCohomology.cup0H_eq_flip_cupH0`: graded commutativity in bidegree `(0, q)`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Preliminaries §2.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- **Graded commutativity in bidegree `(p, 0)`**: after braiding the coefficients, cupping a
degree-`p` class with a degree-zero class agrees with cupping in the opposite order. The Koszul
sign is trivial because the second degree is zero. -/
@[simp]
theorem cupH0_eq_flip_cup0H (M N : Rep k G) (p : ℤ)
    (x : tateCohomology M p) (y : tateCohomology N 0) :
    (tateCohomologyFunctor p).map (β_ M N).hom
        (cupH0 M N p x y) =
      cup0H N M p y x := by
  rw [cup0H_apply]

/-- **Graded commutativity in bidegree `(0, q)`**: after braiding the coefficients, cupping a
degree-zero class with a degree-`q` class agrees with cupping in the opposite order. The Koszul
sign is trivial because the first degree is zero. -/
@[simp]
theorem cup0H_eq_flip_cupH0 (M N : Rep k G) (q : ℤ)
    (x : tateCohomology M 0) (y : tateCohomology N q) :
    (tateCohomologyFunctor q).map (β_ M N).hom
        (cup0H M N q x y) =
      cupH0 N M q y x := by
  rw [cup0H_apply]
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, SymmetricCategory.symmetry]
  simp

end TauCeti.TateCohomology
