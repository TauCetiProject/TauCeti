/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Affine equivalences

This file records computations with affine equivalences. In particular, identifying the
commutator of two homotheties as a translation supports affine representations that detect
infinite-order elements, such as those used for Euclidean triangle groups.

An affine equivalence between modules is also recorded here as its linear part followed by the
translation by its value at the zero vector. This is Mathlib's `AffineMap.map_vadd` read at the
zero base point; Mathlib's `AffineMap.decomp` is the same fact as an equality of functions, which
does not directly give the factorisation as a product of affine equivalences.

## Main results

* `TauCeti.AffineEquiv.commutatorElement_homothetyUnitsMulHom_zero_one`: the commutator of
  homotheties about `0` and `1` is a translation.
* `AffineEquiv.apply_eq_linear_add`: an affine equivalence between modules is its linear part
  plus its value at the zero vector.
* `AffineEquiv.eq_constVAdd_mul_linear`: the resulting factorisation of an affine automorphism of
  a module into a translation after a linear automorphism.
* `LinearEquiv.toAffineEquiv_one`, `LinearEquiv.toAffineEquiv_mul`,
  `LinearEquiv.toAffineEquiv_inv`: reading a linear automorphism of a module as an affine one
  respects the group structure.
* `AffineEquiv.linear_toAffineEquiv`, `AffineEquiv.linear_mul` and `AffineEquiv.linear_inv`: the
  linear part of such a reading, and of a composite or an inverse. Mathlib's
  `AffineEquiv.linear_constVAdd` is the same for a translation.
-/

public section

open scoped commutatorElement

namespace TauCeti

namespace AffineEquiv

variable {K : Type*} [Field K]

/-- The commutator of homotheties with ratios `ω` and `η` about `0` and `1`, respectively, is
translation by `(ω - 1) * (1 - η)`. -/
@[simp]
theorem commutatorElement_homothetyUnitsMulHom_zero_one (ω η : Kˣ) :
    ⁅_root_.AffineEquiv.homothetyUnitsMulHom (0 : K) ω,
        _root_.AffineEquiv.homothetyUnitsMulHom (1 : K) η⁆ =
      _root_.AffineEquiv.constVAdd K K (((ω : K) - 1) * (1 - η)) := by
  rw [commutatorElement_def, ← map_inv, ← map_inv]
  ext z
  simp only [_root_.AffineEquiv.coe_mul, Function.comp_apply,
    _root_.AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply, vsub_eq_sub,
    vadd_eq_add, smul_eq_mul, Units.val_inv_eq_inv_val, _root_.AffineEquiv.constVAdd_apply]
  field_simp
  ring

end AffineEquiv

section Module

variable {k V W : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- **An affine equivalence between modules is its linear part plus its value at the zero
vector.** -/
theorem _root_.AffineEquiv.apply_eq_linear_add (f : V ≃ᵃ[k] W) (x : V) :
    f x = f.linear x + f 0 := by
  simpa using (f : V →ᵃ[k] W).map_vadd 0 x

/-- Reading the identity linear automorphism as an affine one gives the identity. -/
@[simp]
theorem _root_.LinearEquiv.toAffineEquiv_one :
    (1 : V ≃ₗ[k] V).toAffineEquiv = 1 :=
  rfl

/-- Reading linear automorphisms as affine ones respects composition. -/
@[simp]
theorem _root_.LinearEquiv.toAffineEquiv_mul (e f : V ≃ₗ[k] V) :
    (e * f).toAffineEquiv = e.toAffineEquiv * f.toAffineEquiv :=
  rfl

/-- Reading linear automorphisms as affine ones respects inverses. -/
@[simp]
theorem _root_.LinearEquiv.toAffineEquiv_inv (e : V ≃ₗ[k] V) :
    (e⁻¹).toAffineEquiv = (e.toAffineEquiv)⁻¹ :=
  rfl

/-- The linear part of a linear equivalence read as an affine one is itself. -/
@[simp]
theorem _root_.AffineEquiv.linear_toAffineEquiv (e : V ≃ₗ[k] W) :
    e.toAffineEquiv.linear = e :=
  rfl

/-- The linear part of a composite of affine automorphisms is the composite of the linear
parts. -/
@[simp]
theorem _root_.AffineEquiv.linear_mul (f g : V ≃ᵃ[k] V) :
    (f * g).linear = f.linear * g.linear :=
  rfl

/-- The linear part of the inverse of an affine automorphism is the inverse of its linear part. -/
@[simp]
theorem _root_.AffineEquiv.linear_inv (f : V ≃ᵃ[k] V) :
    (f⁻¹).linear = (f.linear)⁻¹ :=
  rfl

/-- **An affine automorphism of a module factors as a translation after a linear automorphism**,
the translation being by its value at the zero vector. -/
theorem _root_.AffineEquiv.eq_constVAdd_mul_linear (f : V ≃ᵃ[k] V) :
    f = _root_.AffineEquiv.constVAdd k V (f 0) * f.linear.toAffineEquiv := by
  ext x
  rw [_root_.AffineEquiv.coe_mul, Function.comp_apply, _root_.AffineEquiv.constVAdd_apply,
    LinearEquiv.coe_toAffineEquiv, vadd_eq_add, AffineEquiv.apply_eq_linear_add f x, add_comm]

end Module

end TauCeti
