/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Shear automorphisms and homeomorphisms of a product

Let `A` be a monoid with a topology and `B` a commutative topological group. A continuous
homomorphism `φ : A →* B` shears the product `A × B`: the map `(a, b) ↦ (a, φ a * b)` is a
continuous multiplicative automorphism (a `ContinuousMulEquiv`), with inverse
`(a, b) ↦ (a, (φ a)⁻¹ * b)`; this is a continuous multiplicative version of Mathlib's
`Equiv.prodShear`. Shears are the automorphisms of `A × B` that fix the first coordinate and act on
each fiber over `A` by a translation of `B`, so they describe how two splittings `G ≃ₜ* A × B`
differ when their transition has this fiberwise-translation form; for instance, the splittings of
the multiplicative group of a local field attached to two uniformizers differ by a shear.

More generally, for any topological space `X`, group `G` with continuous multiplication and
inversion, and continuous map `c : X → G`, the map `(x, g) ↦ (x, c x * g)` is a self-homeomorphism
of `X × G` (`TauCeti.prodMulLeftHomeomorph`, with additive counterpart
`TauCeti.prodAddLeftHomeomorph`), requiring neither algebraic structure on `X` nor commutativity
of `G`.

## Main definitions

* `MonoidHom.prodShear`: the shear `A × B ≃ₜ* A × B` attached to a continuous `φ : A →* B`.
* `TauCeti.prodMulLeftHomeomorph`: the left-translation shear homeomorphism `X × G ≃ₜ X × G`
  attached to a continuous map `c : X → G` (with additive counterpart
  `TauCeti.prodAddLeftHomeomorph`).

## Main results

* `MonoidHom.prodShear_apply` and `MonoidHom.prodShear_symm_apply`: the
  shear and its inverse on elements.
* `MonoidHom.prodShear_one`: the shear by the trivial homomorphism is the identity.
* `MonoidHom.prodShear_trans_prodShear`: shears compose by multiplying the
  homomorphisms.
* `TauCeti.prodMulLeftHomeomorph_apply` and `TauCeti.prodMulLeftHomeomorph_symm_apply`:
  evaluation of the left-translation shear homeomorphism and its inverse on elements.
* `TauCeti.prodMulLeftHomeomorph_symm`, `TauCeti.prodMulLeftHomeomorph_const_one`, and
  `TauCeti.prodMulLeftHomeomorph_trans`: inversion, identity, and composition of
  left-translation shear homeomorphisms.
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

namespace TauCeti

variable {X G : Type*} [TopologicalSpace X] [Group G] [TopologicalSpace G]
  [ContinuousMul G] [ContinuousInv G]

/-- The **left-translation shear homeomorphism** `(x, g) ↦ (x, c x * g)` of `X × G` attached to a
continuous map `c : X → G` into a group with continuous multiplication and inversion, with inverse
`(x, g) ↦ (x, (c x)⁻¹ * g)`. Its underlying equivalence is
`Equiv.prodShear (Equiv.refl X) (fun x ↦ Equiv.mulLeft (c x))`. -/
@[to_additive prodAddLeftHomeomorph /-- The **left-translation shear homeomorphism**
`(x, g) ↦ (x, c x + g)` of `X × G` attached to a continuous map `c : X → G` into an additive group
with continuous addition and negation, with inverse `(x, g) ↦ (x, -c x + g)`. Its underlying
equivalence is `Equiv.prodShear (Equiv.refl X) (fun x ↦ Equiv.addLeft (c x))`. -/]
def prodMulLeftHomeomorph (c : X → G) (hc : Continuous c) : X × G ≃ₜ X × G where
  toEquiv := Equiv.prodShear (Equiv.refl X) fun x ↦ Equiv.mulLeft (c x)
  continuous_toFun := continuous_fst.prodMk <| (hc.comp continuous_fst).mul continuous_snd
  continuous_invFun := continuous_fst.prodMk <| (hc.comp continuous_fst).inv.mul continuous_snd

/-- The left-translation shear by `c` sends `(x, g)` to `(x, c x * g)`. -/
@[to_additive (attr := simp) prodAddLeftHomeomorph_apply /-- The left-translation shear by `c`
sends `(x, g)` to `(x, c x + g)`. -/]
theorem prodMulLeftHomeomorph_apply (c : X → G) (hc : Continuous c) (p : X × G) :
    prodMulLeftHomeomorph c hc p = (p.1, c p.1 * p.2) :=
  (rfl)

/-- The inverse of the left-translation shear by `c` sends `(x, g)` to `(x, (c x)⁻¹ * g)`. -/
@[to_additive (attr := simp) prodAddLeftHomeomorph_symm_apply /-- The inverse of the
left-translation shear by `c` sends `(x, g)` to `(x, -c x + g)`. -/]
theorem prodMulLeftHomeomorph_symm_apply (c : X → G) (hc : Continuous c) (p : X × G) :
    (prodMulLeftHomeomorph c hc).symm p = (p.1, (c p.1)⁻¹ * p.2) :=
  (rfl)

/-- The inverse of the left-translation shear by `c` is the left-translation shear by
`fun x ↦ (c x)⁻¹`. -/
@[to_additive prodAddLeftHomeomorph_symm /-- The inverse of the left-translation shear by `c` is
the left-translation shear by `fun x ↦ -c x`. -/]
theorem prodMulLeftHomeomorph_symm (c : X → G) (hc : Continuous c) :
    (prodMulLeftHomeomorph c hc).symm = prodMulLeftHomeomorph (fun x ↦ (c x)⁻¹) hc.inv :=
  Homeomorph.ext fun p ↦ by simp

/-- The left-translation shear by the constant map `1` is the identity homeomorphism. -/
@[to_additive (attr := simp) prodAddLeftHomeomorph_const_zero /-- The left-translation shear by
the constant map `0` is the identity homeomorphism. -/]
theorem prodMulLeftHomeomorph_const_one :
    prodMulLeftHomeomorph (fun _ : X ↦ (1 : G)) continuous_const = Homeomorph.refl (X × G) :=
  Homeomorph.ext fun p ↦ by simp

/-- Left-translation shears compose by pointwise multiplication: shearing by `c` and then by `d`
is shearing by `fun x ↦ d x * c x`. -/
@[to_additive (attr := simp) prodAddLeftHomeomorph_trans /-- Left-translation shears compose by
pointwise addition: shearing by `c` and then by `d` is shearing by `fun x ↦ d x + c x`. -/]
theorem prodMulLeftHomeomorph_trans (c d : X → G) (hc : Continuous c) (hd : Continuous d) :
    (prodMulLeftHomeomorph c hc).trans (prodMulLeftHomeomorph d hd) =
      prodMulLeftHomeomorph (fun x ↦ d x * c x) (hd.mul hc) :=
  Homeomorph.ext fun p ↦ by simp [mul_assoc]

end TauCeti
