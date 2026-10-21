/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The Kulkarni–Nomizu product of bilinear forms

The Kulkarni–Nomizu product of two bilinear forms `h` and `k` on a module `M` is the
quadrilinear form

`(h ⊙ k)(x, y, z, w) = h(x, w) k(y, z) + h(y, z) k(x, w) - h(x, z) k(y, w) - h(y, w) k(x, z)`.

It is the basic way to build curvature-type tensors out of symmetric bilinear forms: with the
convention `Rm(x, y, z, w) = ⟨R(x, y)z, w⟩`, the curvature tensor of a space of constant
sectional curvature `κ` is `(κ / 2) (g ⊙ g)`, and the Weyl tensor of a Riemannian metric is the
part of `Rm` left after removing the Kulkarni–Nomizu product of the Schouten tensor with `g`.

The product is bilinear and commutative, and is always antisymmetric in its first and in its last
pair of arguments. For symmetric `h` and `k` it is moreover symmetric under interchanging the two
pairs and satisfies the first Bianchi identity, so it has all the algebraic symmetries of a
Riemann curvature tensor.

## Main declarations

* `LinearMap.BilinForm.kulkarniNomizu`: the Kulkarni–Nomizu product, as a bilinear map.
* `LinearMap.BilinForm.kulkarniNomizu_comm`: the product is commutative.
* `LinearMap.BilinForm.IsSymm.kulkarniNomizu_swap_pairs` and
  `LinearMap.BilinForm.IsSymm.kulkarniNomizu_cyclic_eq_zero`: pair interchange and the first
  Bianchi identity for symmetric factors.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7.
-/

public section

open LinearMap (BilinForm)

noncomputable section

namespace LinearMap.BilinForm

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The Kulkarni–Nomizu product of two bilinear forms, bundled as a bilinear map:
`(h ⊙ k)(x, y, z, w) = h(x, w) k(y, z) + h(y, z) k(x, w) - h(x, z) k(y, w) - h(y, w) k(x, z)`. -/
def kulkarniNomizu :
    BilinForm R M →ₗ[R] BilinForm R M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] M →ₗ[R] R :=
  LinearMap.mk₂ R
    (fun h k ↦ LinearMap.mk₂ R
      (fun x y ↦ LinearMap.mk₂ R
        (fun z w ↦ h x w * k y z + h y z * k x w - h x z * k y w - h y w * k x z)
        (fun _ _ _ ↦ by simp only [map_add]; ring)
        (fun _ _ _ ↦ by simp only [map_smul, smul_eq_mul]; ring)
        (fun _ _ _ ↦ by simp only [map_add]; ring)
        (fun _ _ _ ↦ by simp only [map_smul, smul_eq_mul]; ring))
      (fun _ _ _ ↦ by ext; simp only [map_add, LinearMap.add_apply, LinearMap.mk₂_apply]; ring)
      (fun _ _ _ ↦ by
        ext; simp only [map_smul, LinearMap.smul_apply, LinearMap.mk₂_apply, smul_eq_mul]; ring)
      (fun _ _ _ ↦ by ext; simp only [map_add, LinearMap.add_apply, LinearMap.mk₂_apply]; ring)
      (fun _ _ _ ↦ by
        ext; simp only [map_smul, LinearMap.smul_apply, LinearMap.mk₂_apply, smul_eq_mul]; ring))
    (fun _ _ _ ↦ by ext; simp only [LinearMap.add_apply, LinearMap.mk₂_apply]; ring)
    (fun _ _ _ ↦ by ext; simp only [LinearMap.smul_apply, LinearMap.mk₂_apply, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by ext; simp only [LinearMap.add_apply, LinearMap.mk₂_apply]; ring)
    (fun _ _ _ ↦ by ext; simp only [LinearMap.smul_apply, LinearMap.mk₂_apply, smul_eq_mul]; ring)

/-- Evaluation of the Kulkarni–Nomizu product. -/
@[simp]
theorem kulkarniNomizu_apply (h k : BilinForm R M) (x y z w : M) :
    kulkarniNomizu h k x y z w =
      h x w * k y z + h y z * k x w - h x z * k y w - h y w * k x z :=
  (rfl)

/-- The Kulkarni–Nomizu product is commutative. -/
theorem kulkarniNomizu_comm (h k : BilinForm R M) :
    kulkarniNomizu h k = kulkarniNomizu k h := by
  ext x y z w
  simp only [kulkarniNomizu_apply]
  ring

/-- The Kulkarni–Nomizu product is antisymmetric in its first pair of arguments. -/
theorem kulkarniNomizu_antisymm_first (h k : BilinForm R M) (x y z w : M) :
    kulkarniNomizu h k x y z w = -kulkarniNomizu h k y x z w := by
  simp only [kulkarniNomizu_apply]
  ring

/-- The Kulkarni–Nomizu product is antisymmetric in its last pair of arguments. -/
theorem kulkarniNomizu_antisymm_last (h k : BilinForm R M) (x y z w : M) :
    kulkarniNomizu h k x y z w = -kulkarniNomizu h k x y w z := by
  simp only [kulkarniNomizu_apply]
  ring

/-- The Kulkarni–Nomizu product of symmetric bilinear forms is unchanged when its two pairs of
arguments are interchanged. -/
theorem IsSymm.kulkarniNomizu_swap_pairs {h k : BilinForm R M} (hh : h.IsSymm)
    (hk : k.IsSymm) (x y z w : M) :
    kulkarniNomizu h k x y z w = kulkarniNomizu h k z w x y := by
  simp only [kulkarniNomizu_apply, hh.eq z, hh.eq w, hk.eq z, hk.eq w]
  ring

/-- The first Bianchi identity for the Kulkarni–Nomizu product of symmetric bilinear forms: the
cyclic sum over the first three arguments vanishes. -/
theorem IsSymm.kulkarniNomizu_cyclic_eq_zero {h k : BilinForm R M} (hh : h.IsSymm)
    (hk : k.IsSymm) (x y z w : M) :
    kulkarniNomizu h k x y z w + kulkarniNomizu h k y z x w +
      kulkarniNomizu h k z x y w = 0 := by
  simp only [kulkarniNomizu_apply, hh.eq y x, hh.eq z y, hh.eq z x, hk.eq y x, hk.eq z y,
    hk.eq z x]
  ring

end LinearMap.BilinForm
