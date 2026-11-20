/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Monoid

/-!
# Shear automorphisms and homeomorphisms of a product

Let `X` be a topological space and `G` a group with continuous inversion acting continuously on a
space `Y`. A continuous map `c : X → G` shears the product `X × Y`: the map
`(x, y) ↦ (x, c x • y)` is a self-homeomorphism of `X × Y` (`TauCeti.prodSMulHomeomorph`, with
additive counterpart `TauCeti.prodVAddHomeomorph`), with inverse `(x, y) ↦ (x, (c x)⁻¹ • y)`.
It requires no algebraic structure on `X`. Its underlying equivalence is Mathlib's
`Equiv.prodShear` of the permutations `MulAction.toPerm (c x)`. For `G` acting on itself by left
multiplication it is the left-translation shear `(x, g) ↦ (x, c x * g)`; for a structure group
acting on the fiber of a trivial bundle it is the change of trivialization given by the transition
map `c`.

When `A` is a topological space with a multiplication and a one (`MulOne`), `B` a commutative
topological group and `c = φ` a continuous homomorphism `φ : A →* B`, the shear
`(a, b) ↦ (a, φ a * b)` of `A × B` is moreover multiplicative, hence a continuous multiplicative
automorphism (a `ContinuousMulEquiv`), `MonoidHom.prodShear`. When the multiplication of `A` is
unital (`MulOneClass`), shears of this form are exactly the continuous multiplicative
automorphisms of `A × B` that fix the first coordinate and act on each fiber over `A` by a
translation of `B`, so they describe how two splittings `G ≃ₜ* A × B` differ when their transition
has this fiberwise-translation form; for instance, the splittings of the multiplicative group of a
local field attached to two uniformizers differ by a shear.

## Main definitions

* `TauCeti.prodSMulHomeomorph`: the shear homeomorphism `X × Y ≃ₜ X × Y` attached to a continuous
  map `c : X → G` (with additive counterpart `TauCeti.prodVAddHomeomorph`).
* `MonoidHom.prodShear`: the shear `A × B ≃ₜ* A × B` attached to a continuous `φ : A →* B`.

## Main results

* `TauCeti.prodSMulHomeomorph_apply` and `TauCeti.prodSMulHomeomorph_symm_apply`: evaluation of
  the shear homeomorphism and its inverse on elements.
* `TauCeti.prodSMulHomeomorph_symm`, `TauCeti.prodSMulHomeomorph_const_one`, and
  `TauCeti.prodSMulHomeomorph_trans`: inversion, identity, and composition of shear
  homeomorphisms.
* `MonoidHom.prodShear_apply` and `MonoidHom.prodShear_symm_apply`: the
  shear and its inverse on elements.
* `MonoidHom.prodShear_one`: the shear by the trivial homomorphism is the identity.
* `MonoidHom.prodShear_trans_prodShear`: shears compose by multiplying the
  homomorphisms.
-/

public section

namespace TauCeti

variable {X G Y : Type*} [TopologicalSpace X] [Group G] [TopologicalSpace G] [ContinuousInv G]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]

/-- The **shear homeomorphism** `(x, y) ↦ (x, c x • y)` of `X × Y` attached to a continuous map
`c : X → G` into a group with continuous inversion acting continuously on `Y`, with inverse
`(x, y) ↦ (x, (c x)⁻¹ • y)`. Its underlying equivalence is
`Equiv.prodShear (Equiv.refl X) (fun x ↦ MulAction.toPerm (c x))`. For `G` acting on itself it is
the left-translation shear `(x, g) ↦ (x, c x * g)`. -/
@[to_additive prodVAddHomeomorph /-- The **shear homeomorphism** `(x, y) ↦ (x, c x +ᵥ y)` of
`X × Y` attached to a continuous map `c : X → G` into an additive group with continuous negation
acting continuously on `Y`, with inverse `(x, y) ↦ (x, -c x +ᵥ y)`. Its underlying equivalence is
`Equiv.prodShear (Equiv.refl X) (fun x ↦ AddAction.toPerm (c x))`. For `G` acting on itself it is
the left-translation shear `(x, g) ↦ (x, c x + g)`. -/]
def prodSMulHomeomorph (c : X → G) (hc : Continuous c) : X × Y ≃ₜ X × Y where
  toEquiv := Equiv.prodShear (Equiv.refl X) fun x ↦ MulAction.toPerm (c x)
  continuous_toFun := continuous_fst.prodMk <| (hc.comp continuous_fst).smul continuous_snd
  continuous_invFun := continuous_fst.prodMk <| (hc.comp continuous_fst).inv.smul continuous_snd

/-- The shear by `c` sends `(x, y)` to `(x, c x • y)`. -/
@[to_additive (attr := simp) prodVAddHomeomorph_apply /-- The shear by `c` sends `(x, y)` to
`(x, c x +ᵥ y)`. -/]
theorem prodSMulHomeomorph_apply (c : X → G) (hc : Continuous c) (p : X × Y) :
    prodSMulHomeomorph c hc p = (p.1, c p.1 • p.2) :=
  (rfl)

/-- The inverse of the shear by `c` sends `(x, y)` to `(x, (c x)⁻¹ • y)`. -/
@[to_additive (attr := simp) prodVAddHomeomorph_symm_apply /-- The inverse of the shear by `c`
sends `(x, y)` to `(x, -c x +ᵥ y)`. -/]
theorem prodSMulHomeomorph_symm_apply (c : X → G) (hc : Continuous c) (p : X × Y) :
    (prodSMulHomeomorph c hc).symm p = (p.1, (c p.1)⁻¹ • p.2) :=
  (rfl)

/-- The inverse of the shear by `c` is the shear by `fun x ↦ (c x)⁻¹`. -/
@[to_additive prodVAddHomeomorph_symm /-- The inverse of the shear by `c` is the shear by
`fun x ↦ -c x`. -/]
theorem prodSMulHomeomorph_symm (c : X → G) (hc : Continuous c) :
    (prodSMulHomeomorph (Y := Y) c hc).symm = prodSMulHomeomorph (fun x ↦ (c x)⁻¹) hc.inv :=
  Homeomorph.ext fun p ↦ by simp

/-- The shear by the constant map `1` is the identity homeomorphism. -/
@[to_additive (attr := simp) prodVAddHomeomorph_const_zero /-- The shear by the constant map `0`
is the identity homeomorphism. -/]
theorem prodSMulHomeomorph_const_one :
    prodSMulHomeomorph (fun _ : X ↦ (1 : G)) continuous_const = Homeomorph.refl (X × Y) :=
  Homeomorph.ext fun p ↦ by simp

/-- Shears compose by pointwise multiplication: shearing by `c` and then by `d` is shearing by
`fun x ↦ d x * c x`. -/
@[to_additive (attr := simp) prodVAddHomeomorph_trans /-- Shears compose by pointwise addition:
shearing by `c` and then by `d` is shearing by `fun x ↦ d x + c x`. -/]
theorem prodSMulHomeomorph_trans [ContinuousMul G] (c d : X → G) (hc : Continuous c)
    (hd : Continuous d) :
    (prodSMulHomeomorph (Y := Y) c hc).trans (prodSMulHomeomorph d hd) =
      prodSMulHomeomorph (fun x ↦ d x * c x) (hd.mul hc) :=
  Homeomorph.ext fun p ↦ by simp [mul_smul]

end TauCeti

namespace MonoidHom

variable {A B : Type*} [TopologicalSpace A] [CommGroup B] [TopologicalSpace B]
  [IsTopologicalGroup B]

section MulOne

variable [MulOne A]

/-- The **shear** of `A × B` by a continuous homomorphism `φ : A →* B` into a commutative
topological group: the continuous multiplicative automorphism `(a, b) ↦ (a, φ a * b)`, with
inverse `(a, b) ↦ (a, (φ a)⁻¹ * b)`. Its underlying homeomorphism is the shear homeomorphism
`TauCeti.prodSMulHomeomorph φ hφ` of `B` acting on itself. -/
def prodShear (φ : A →* B) (hφ : Continuous φ) : A × B ≃ₜ* A × B :=
  .mk' (TauCeti.prodSMulHomeomorph φ hφ) fun p q ↦ by
    simp [mul_mul_mul_comm]

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

end MulOne

/-- Shears compose by multiplying the homomorphisms: shearing by `φ` and then by `ψ` is shearing
by `ψ * φ`. -/
@[simp]
theorem prodShear_trans_prodShear [MulOneClass A] (φ ψ : A →* B) (hφ : Continuous φ)
    (hψ : Continuous ψ) :
    (prodShear φ hφ).trans (prodShear ψ hψ) =
      prodShear (ψ * φ) ((hψ.mul hφ).congr fun a ↦ (mul_apply ψ φ a).symm) :=
  ContinuousMulEquiv.ext fun p ↦ by simp [mul_assoc]

end MonoidHom
