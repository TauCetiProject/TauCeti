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

* `AlgHom.prodFirst`: the first-coordinate algebra map attached to `φ` with `φ (1, 0) = 1`.
* `AlgHom.map_eq_map_fst`: such a `φ` ignores its second argument.
* `AlgHom.prodFirst_comp_fst`: the coordinate map is a factorisation -- precomposing with the first
  projection returns `φ`.
* `AlgHom.prodFirst_surjective`: it inherits surjectivity from `φ`.
-/

public section

namespace AlgHom

section Semiring

variable {F A C B : Type*} [CommSemiring F] [Semiring A] [Algebra F A] [Semiring C] [Algebra F C]
  [Semiring B] [Algebra F B]

/-- The coordinate map `a ↦ φ (a, 0)` attached to an algebra map out of a product, packaged as an
algebra map once the image of `(1, 0)` is known to be the unit. It is multiplicative and linear for
every `φ`; unitality is exactly the hypothesis.

Note that `a ↦ (a, 0)` is not itself an algebra map -- it does not preserve `1` -- so this cannot
be obtained by composing `φ` with an inclusion. -/
def prodFirst (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) : A →ₐ[F] B where
  __ := φ.toNonUnitalAlgHom.comp (NonUnitalAlgHom.inl F A C)
  map_one' := hu
  commutes' r := by
    have hr : ((algebraMap F A r : A), (0 : C)) = algebraMap F (A × C) r * (1, 0) := by
      simp [Prod.algebraMap_apply]
    change φ (algebraMap F A r, 0) = _
    rw [hr, map_mul, AlgHom.commutes, hu, mul_one]

/-- The first coordinate map is what its name says: `a ↦ φ (a, 0)`. -/
@[simp]
theorem prodFirst_apply (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) (a : A) :
    prodFirst φ hu a = φ (a, 0) := (rfl)

end Semiring

section CancelAdd

variable {F A C B : Type*} [CommSemiring F] [Semiring A] [Algebra F A] [Semiring C] [Algebra F C]
  [Semiring B] [IsLeftCancelAdd B] [Algebra F B]

/-- If the image of `(1, 0)` is the unit then the first coordinate map is surjective as soon as `φ`
is: the image of `(0, 1)` is then complementary to `1`, so it vanishes, and with it the whole
second coordinate.

Unlike the construction itself this needs `B` additively left-cancellative, to pass from
`1 + φ (0, 1) = 1 + 0` to `φ (0, 1) = 0`. That is all it needs -- a cancellative semiring will do,
without subtraction. -/
theorem map_snd_eq_zero (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) : φ (0, 1) = 0 := by
  have hsum : φ (1, 0) + φ (0, 1) = 1 := by
    rw [← map_add, show ((1, 0) + (0, 1) : A × C) = 1 by simp [Prod.ext_iff], map_one]
  rw [hu] at hsum
  exact add_left_cancel (b := φ (0, 1)) (c := 0) (by rw [hsum, add_zero])

/-- **`φ` ignores its second argument**, once `φ (1, 0) = 1`: the second coordinate is a multiple
of `(0, 1)`, which `φ` kills. -/
theorem map_eq_map_fst (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) (p : A × C) :
    φ p = φ (p.1, 0) := by
  conv_lhs => rw [show p = (p.1, 0) + (0, p.2) * (0, 1) by simp]
  rw [map_add, map_mul, map_snd_eq_zero φ hu, mul_zero, add_zero]

/-- **The first coordinate map really is a factorisation of `φ`**: precomposing it with the first
projection returns `φ`. -/
@[simp]
theorem prodFirst_comp_fst (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1) :
    (prodFirst φ hu).comp (AlgHom.fst F A C) = φ :=
  AlgHom.ext fun p => (map_eq_map_fst φ hu p).symm

theorem prodFirst_surjective (φ : (A × C) →ₐ[F] B) (hu : φ (1, 0) = 1)
    (hφ : Function.Surjective φ) : Function.Surjective (prodFirst φ hu) := by
  intro b
  obtain ⟨p, rfl⟩ := hφ b
  exact ⟨p.1, (map_eq_map_fst φ hu p).symm⟩

end CancelAdd

end AlgHom
