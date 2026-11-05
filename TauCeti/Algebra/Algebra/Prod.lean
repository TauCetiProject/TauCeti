/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Prod

/-!
# Algebra maps out of a product that factor through a coordinate

An algebra map `φ : A × C →ₐ[F] B` does not restrict to the first factor on the nose, because
`a ↦ (a, 0)` is not unital and so is not an algebra map.  It does restrict once `φ (1, 0) = 1`:
that hypothesis supplies exactly the missing unitality, and `a ↦ φ (a, 0)` is then an algebra map
`A →ₐ[F] B`.

This is why there is no `AlgHom.inl` upstream to compose with, and what
`AlgHom.prodFirst` provides instead.

## Main declarations

* `AlgHom.map_eq_map_fst`: a `φ` with `φ (1, 0) = 1` ignores its second argument.
* `AlgHom.map_zero_one_eq_zero`: such a `φ` kills the second coordinate unit.
* `AlgHom.prodFirst`: the first-coordinate algebra map attached to such a `φ`.
* `AlgHom.prodFirst_comp_fst`: the coordinate map is a factorisation -- precomposing with the first
  projection returns `φ`.
* `AlgHom.prodFirst_surjective_iff`: it is surjective exactly when `φ` is.
-/

public section

namespace AlgHom

section Semiring

variable {F A C B : Type*} [CommSemiring F] [Semiring A] [Algebra F A] [Semiring C] [Algebra F C]
  [Semiring B] [Algebra F B]

/-- **`φ` ignores its second argument**, once `φ (1, 0) = 1`: right multiplication by `(1, 0)`
zeroes the second coordinate, and `φ` sends it to `1`. -/
theorem map_eq_map_fst (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) (p : A × C) :
    φ p = φ (p.1, 0) := by
  rw [← mul_one (φ p), ← hu, ← map_mul]
  simp [Prod.mul_def]

/-- **The second coordinate unit is killed**, once `φ (1, 0) = 1`. The two coordinate units
annihilate each other in the product, so this holds over an arbitrary semiring and needs no
additive cancellation. -/
@[simp]
theorem map_zero_one_eq_zero (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) : φ (0, 1) = 0 := by
  rw [map_eq_map_fst φ hu, Prod.mk_zero_zero, map_zero]

/-- The coordinate map `a ↦ φ (a, 0)` attached to an algebra map out of a product, packaged as an
algebra map once the image of `(1, 0)` is known to be the unit. It is multiplicative and linear for
every `φ`; unitality is exactly the hypothesis.

Note that `a ↦ (a, 0)` is not itself an algebra map -- it does not preserve `1` -- so this cannot
be obtained by composing `φ` with an inclusion. -/
def prodFirst (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) : A →ₐ[F] B where
  __ := φ.toNonUnitalAlgHom.comp (NonUnitalAlgHom.inl F A C)
  map_one' := hu
  commutes' r := by
    -- The inherited non-unital hom is `a ↦ φ (a, 0)` by definition; state it so that the
    -- rewrites below can act on `φ`.
    change φ (algebraMap F A r, 0) = algebraMap F B r
    rw [← φ.commutes, map_eq_map_fst φ hu (algebraMap F (A × C) r), Prod.algebraMap_apply]

/-- The first coordinate map is what its name says: `a ↦ φ (a, 0)`. -/
@[simp]
theorem prodFirst_apply (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) (a : A) :
    prodFirst φ hu a = φ (a, 0) := (rfl)

/-- **The first coordinate map really is a factorisation of `φ`**: precomposing it with the first
projection returns `φ`. -/
@[simp]
theorem prodFirst_comp_fst (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) :
    (prodFirst φ hu).comp (AlgHom.fst F A C) = φ :=
  AlgHom.ext fun p => (map_eq_map_fst φ hu p).symm

/-- **The first coordinate map is surjective exactly when `φ` is**, since `φ` factors through it
along the surjective first projection. -/
theorem prodFirst_surjective_iff (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) :
    Function.Surjective (prodFirst φ hu) ↔ Function.Surjective φ := by
  conv_rhs => rw [← prodFirst_comp_fst φ hu, AlgHom.coe_comp]
  exact (Function.Surjective.of_comp_iff _ Prod.fst_surjective).symm

end Semiring

end AlgHom
