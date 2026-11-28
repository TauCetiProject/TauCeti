/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

/-!
# The pairing of a line bundle class on a group scheme

Let `G` be a monoid object of `Over S`, for instance a group scheme over `S`. Its `T`-points
`x y : T ⟶ G`, for `T` over `S`, form a monoid (Mathlib's scoped instance
`CategoryTheory.Hom.monoid`), written multiplicatively like the Picard group
`LineBundleClass`. A class `c` of line bundles on `G` pulls back along a `T`-point `x` to the
class `x^*c = LineBundleClass.pullback x.left c` on `T`. This file defines

* `LineBundleClass.pairing c x y = (x y)^*c · (x^*c)⁻¹ · (y^*c)⁻¹ · 1^*c`, a class on `T`, which
  measures how far `x ↦ x^*c` is from being multiplicative; written additively it is
  `⟨x, y⟩_c = (x + y)^*c − x^*c − y^*c + 0^*c`;
* `LineBundleClass.ParallelogramLaw c`, for a group object `G`: for every `T` over `S` and all
  `T`-points `x`, `y`, `(x y)^*c · (x / y)^*c · (1^*c)² = (x^*c · y^*c)²`; additively,
  `(x + y)^*c + (x − y)^*c + 2·0^*c = 2(x^*c + y^*c)`.

The pairing is natural in `T` (`LineBundleClass.pullback_pairing`), trivial when one point is the
unit (`LineBundleClass.pairing_one_left`, `LineBundleClass.pairing_one_right`), and a group
homomorphism in the class (`LineBundleClass.pairing_mul`, `LineBundleClass.pairing_inv`). The
classes satisfying the parallelogram law form a subgroup (`LineBundleClass.ParallelogramLaw.one`,
`LineBundleClass.ParallelogramLaw.mul`, `LineBundleClass.ParallelogramLaw.inv`).

## References

* The definitions follow the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207 (`New.Pic.atPoint`, `New.Pic.pairing`,
  `New.Pic.ParallelogramLaw`).
-/

public section

open CategoryTheory Limits CartesianMonoidalCategory MonObj

open scoped CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

namespace LineBundleClass

universe u

variable {S : AlgebraicGeometry.Scheme.{u}} {G : Over S}

section Monoid

variable [MonObj G]

/-- The **pairing** `⟨x, y⟩_c` of a line bundle class `c` on a monoid object `G` of `Over S`
(for instance a group scheme), evaluated at two `T`-points `x` and `y`: the class
`(x y)^*c · (x^*c)⁻¹ · (y^*c)⁻¹ · 1^*c` on `T`. Additively,
`⟨x, y⟩_c = (x + y)^*c − x^*c − y^*c + 0^*c`. -/
noncomputable def pairing (c : LineBundleClass G.left) {T : Over S} (x y : T ⟶ G) :
    LineBundleClass T.left :=
  pullback (x * y).left c * (pullback x.left c)⁻¹ * (pullback y.left c)⁻¹ *
    pullback (1 : T ⟶ G).left c

/-- Unfolding lemma for `LineBundleClass.pairing`. -/
lemma pairing_def (c : LineBundleClass G.left) {T : Over S} (x y : T ⟶ G) :
    pairing c x y = pullback (x * y).left c * (pullback x.left c)⁻¹ * (pullback y.left c)⁻¹ *
      pullback (1 : T ⟶ G).left c :=
  (rfl)

/-- The pairing is natural in the test object: pulling `⟨x, y⟩_c` back along `g : T' ⟶ T` gives
the pairing of the composites `g ≫ x` and `g ≫ y`. -/
@[simp]
lemma pullback_pairing (c : LineBundleClass G.left) {T T' : Over S} (g : T' ⟶ T)
    (x y : T ⟶ G) : pullback g.left (pairing c x y) = pairing c (g ≫ x) (g ≫ y) := by
  simp only [pairing_def, pullback_mul, pullback_inv, pullback_comp, ← Over.comp_left,
    MonObj.comp_mul, MonObj.comp_one]

/-- The pairing with the unit point on the left is trivial. -/
@[simp]
lemma pairing_one_left (c : LineBundleClass G.left) {T : Over S} (y : T ⟶ G) :
    pairing c 1 y = 1 := by
  rw [pairing_def, _root_.one_mul, mul_right_comm _ (pullback y.left c)⁻¹, inv_mul_cancel_right,
    mul_inv_cancel]

/-- The pairing with the unit point on the right is trivial. -/
@[simp]
lemma pairing_one_right (c : LineBundleClass G.left) {T : Over S} (x : T ⟶ G) :
    pairing c x 1 = 1 := by
  rw [pairing_def, _root_.mul_one, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

/-- The pairing of the trivial class is trivial. -/
@[simp]
lemma pairing_one {T : Over S} (x y : T ⟶ G) : pairing (1 : LineBundleClass G.left) x y = 1 := by
  simp only [pairing_def, pullback_one, inv_one, _root_.mul_one]

/-- The pairing is multiplicative in the class: `⟨x, y⟩_{c d} = ⟨x, y⟩_c · ⟨x, y⟩_d`. -/
@[simp]
lemma pairing_mul (c d : LineBundleClass G.left) {T : Over S} (x y : T ⟶ G) :
    pairing (c * d) x y = pairing c x y * pairing d x y := by
  simp only [pairing_def, pullback_mul, mul_inv]
  ac_rfl

/-- The pairing of the inverse class is the inverse of the pairing. -/
@[simp]
lemma pairing_inv (c : LineBundleClass G.left) {T : Over S} (x y : T ⟶ G) :
    pairing c⁻¹ x y = (pairing c x y)⁻¹ := by
  simp only [pairing_def, pullback_inv, mul_inv, inv_inv]

end Monoid

section Group

variable [GrpObj G]

/-- A line bundle class `c` on a group object `G` of `Over S` satisfies the **parallelogram law**
if `(x y)^*c · (x / y)^*c · (1^*c)² = (x^*c · y^*c)²` for every `T` over `S` and all `T`-points
`x` and `y`; additively, `(x + y)^*c + (x − y)^*c + 2·0^*c = 2(x^*c + y^*c)`. -/
def ParallelogramLaw (c : LineBundleClass G.left) : Prop :=
  ∀ (T : Over S) (x y : T ⟶ G), pullback (x * y).left c * pullback (x / y).left c *
    pullback (1 : T ⟶ G).left c ^ 2 = (pullback x.left c * pullback y.left c) ^ 2

/-- Unfolding lemma for `LineBundleClass.ParallelogramLaw`. -/
lemma parallelogramLaw_iff (c : LineBundleClass G.left) :
    ParallelogramLaw c ↔ ∀ (T : Over S) (x y : T ⟶ G), pullback (x * y).left c *
      pullback (x / y).left c * pullback (1 : T ⟶ G).left c ^ 2 =
        (pullback x.left c * pullback y.left c) ^ 2 :=
  Iff.rfl

namespace ParallelogramLaw

/-- The trivial class satisfies the parallelogram law. -/
lemma one : ParallelogramLaw (1 : LineBundleClass G.left) := fun T x y ↦ by
  simp only [pullback_one, one_pow, _root_.mul_one]

/-- The product of two classes satisfying the parallelogram law satisfies it. -/
lemma mul {c d : LineBundleClass G.left} (hc : ParallelogramLaw c) (hd : ParallelogramLaw d) :
    ParallelogramLaw (c * d) := fun T x y ↦ by
  -- Multiply the two laws; both sides then agree up to reordering the factors.
  have h := congrArg₂ (· * ·) (hc T x y) (hd T x y)
  simp only [pullback_mul, mul_pow] at h ⊢
  exact (by ac_rfl : _ = _).trans (h.trans (by ac_rfl))

/-- The inverse of a class satisfying the parallelogram law satisfies it. -/
lemma inv {c : LineBundleClass G.left} (hc : ParallelogramLaw c) : ParallelogramLaw c⁻¹ :=
  fun T x y ↦ by
    simp only [pullback_inv, ← mul_inv, inv_pow, hc T x y]

end ParallelogramLaw

end Group

end LineBundleClass

end AlgebraicGeometry

end TauCeti
