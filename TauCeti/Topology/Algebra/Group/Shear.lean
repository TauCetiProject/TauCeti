/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Shear automorphisms of a product

Let `A` be a monoid with a topology and `B` a commutative topological group. A continuous
homomorphism `φ : A →* B` shears the product `A × B`: the map `(a, b) ↦ (a, φ a * b)` is a
continuous multiplicative automorphism (a `ContinuousMulEquiv`), with inverse
`(a, b) ↦ (a, (φ a)⁻¹ * b)`; this is a continuous multiplicative version of Mathlib's
`Equiv.prodShear`. Shears are the automorphisms of `A × B` that fix the first coordinate and act on
each fiber over `A` by a translation of `B`, so they describe how two splittings `G ≃ₜ* A × B`
differ when their transition has this fiberwise-translation form; for instance, the splittings of
the multiplicative group of a local field attached to two uniformizers differ by a shear.

## Main definitions

* `MonoidHom.prodShear`: the shear `A × B ≃ₜ* A × B` attached to a continuous `φ : A →* B`.

## Main results

* `MonoidHom.prodShear_apply` and `MonoidHom.prodShear_symm_apply`: the
  shear and its inverse on elements.
* `MonoidHom.prodShear_one`: the shear by the trivial homomorphism is the identity.
* `MonoidHom.prodShear_trans_prodShear`: shears compose by multiplying the
  homomorphisms.
-/

public section

namespace MonoidHom

variable {A B : Type*} [Monoid A] [TopologicalSpace A] [CommGroup B] [TopologicalSpace B]
  [IsTopologicalGroup B]

/-- The **shear** of `A × B` by a continuous homomorphism `φ : A →* B` into a commutative
topological group: the continuous multiplicative automorphism `(a, b) ↦ (a, φ a * b)`, with
inverse `(a, b) ↦ (a, (φ a)⁻¹ * b)`. Its underlying function is that of `Equiv.prodShear`. -/
def prodShear (φ : A →* B) (hφ : Continuous φ) : A × B ≃ₜ* A × B where
  toFun p := (p.1, φ p.1 * p.2)
  invFun p := (p.1, (φ p.1)⁻¹ * p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_mul' p q := Prod.ext rfl <| by
    simp only [Prod.snd_mul, Prod.fst_mul, map_mul]
    exact mul_mul_mul_comm _ _ _ _
  continuous_toFun := continuous_fst.prodMk <| (hφ.comp continuous_fst).mul continuous_snd
  continuous_invFun := continuous_fst.prodMk <| (hφ.comp continuous_fst).inv.mul continuous_snd

/-- The shear by `φ` sends `(a, b)` to `(a, φ a * b)`. -/
@[simp]
theorem prodShear_apply (φ : A →* B) (hφ : Continuous φ) (p : A × B) :
    prodShear φ hφ p = (p.1, φ p.1 * p.2) :=
  (rfl)

/-- The inverse of the shear by `φ` sends `(a, b)` to `(a, (φ a)⁻¹ * b)`. -/
@[simp]
theorem prodShear_symm_apply (φ : A →* B) (hφ : Continuous φ) (p : A × B) :
    (prodShear φ hφ).symm p = (p.1, (φ p.1)⁻¹ * p.2) :=
  (rfl)

/-- The shear by the trivial homomorphism is the identity. -/
@[simp]
theorem prodShear_one :
    prodShear 1 (continuous_const.congr fun a ↦ (one_apply a).symm) =
      ContinuousMulEquiv.refl (A × B) :=
  ContinuousMulEquiv.ext fun p ↦ by simp

/-- Shears compose by multiplying the homomorphisms: shearing by `φ` and then by `ψ` is shearing
by `ψ * φ`. -/
@[simp]
theorem prodShear_trans_prodShear (φ ψ : A →* B) (hφ : Continuous φ) (hψ : Continuous ψ) :
    (prodShear φ hφ).trans (prodShear ψ hψ) =
      prodShear (ψ * φ) ((hψ.mul hφ).congr fun a ↦ (mul_apply ψ φ a).symm) :=
  ContinuousMulEquiv.ext fun p ↦ by simp [mul_assoc]

end MonoidHom
