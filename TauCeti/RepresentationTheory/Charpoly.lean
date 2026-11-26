/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.AsModule
import TauCeti.LinearAlgebra.Charpoly.Comp
import TauCeti.LinearAlgebra.Charpoly.Dual
import TauCeti.LinearAlgebra.Charpoly.Inverse
import TauCeti.LinearAlgebra.Charpoly.Quotient

/-!
# Characteristic polynomials of representations

For a representation `ρ` of a monoid on a finite free module and an element `g`, the
characteristic polynomial of `ρ g` is invariant under isomorphism of representations and cyclic
permutation `g * h ↔ h * g`, multiplicative on products, and equal to `(X - 1) ^ dim V` for the
trivial representation. The determinant of `ρ g` is invariant under isomorphism too, on any module.

For a representation of a group, `(ρ g).charpoly` is invariant under conjugation; `g⁻¹` acts with
the reverse of the characteristic polynomial of `g`, up to a unit, and so does `g` in the
contragredient representation `ρ.dual`. Hence in any
field over the coefficients, the characteristic roots of `g` in `ρ.dual` are the inverses of those
of `g` in `ρ`, counted with multiplicity. Applied to a Frobenius element, this compares the
eigenvalues of arithmetic and geometric Frobenius.

## Main results

* `Representation.Equiv.charpoly_apply_eq`, `Representation.Equiv.det_apply_eq`: invariance of
  the characteristic polynomial and of the determinant under isomorphism.
* `Representation.charpoly_apply_mul_comm` and `Representation.charpoly_apply_conj`: cyclic and
  conjugation invariance.
* `Representation.charpoly_prod_apply`: multiplicativity on products.
* `Representation.charpoly_trivial_apply`: the characteristic polynomial of the trivial
  representation.
* `Representation.eq_one_of_mem_roots_map_charpoly_trivial`: its roots in any domain are `1`.
* `Representation.charpoly_apply_eq_subrepresentation_mul_quotient`: multiplicativity on an
  invariant submodule and its quotient.
* `Representation.charpoly_lsmul_asModule_of`: `g` acts on the `R[G]`-module `ρ.asModule` with the
  characteristic polynomial of `ρ g`.
* `Representation.charpoly_apply_inv`, `Representation.aroots_charpoly_apply_inv`: the
  characteristic polynomial and the characteristic roots of `g⁻¹`.
* `Representation.charpoly_dual_apply`, `Representation.aroots_charpoly_dual_apply`: the
  characteristic polynomial and the characteristic roots of `g` in the contragredient
  representation.
-/

public section

open Module Polynomial

namespace Representation

/-- Isomorphic representations have the same determinants. -/
theorem Equiv.det_apply_eq {R G V W : Type*} [CommRing R] [Monoid G] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] {ρ : Representation R G V} {σ : Representation R G W}
    (φ : ρ.Equiv σ) (g : G) : (ρ g).det = (σ g).det := by
  rw [← φ.conj_apply_self g, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj]

variable {R G V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Module.Free R V]
  [Module.Finite R V] [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]

section Monoid

variable [Monoid G] {ρ : Representation R G V} {σ : Representation R G W}

/-- Isomorphic representations have the same characteristic polynomials. -/
theorem Equiv.charpoly_apply_eq (φ : ρ.Equiv σ) (g : G) : (ρ g).charpoly = (σ g).charpoly := by
  rw [← φ.conj_apply_self g, LinearEquiv.charpoly_conj]

variable (ρ) in
/-- Cyclic invariance of the characteristic polynomial:
`(ρ (g * h)).charpoly = (ρ (h * g)).charpoly` for any elements `g, h` of the acting monoid `G`. -/
theorem charpoly_apply_mul_comm (g h : G) : (ρ (g * h)).charpoly = (ρ (h * g)).charpoly := by
  rw [map_mul, map_mul]
  exact LinearMap.charpoly_comp_comm (ρ h) (ρ g) rfl

variable (ρ σ) in
/-- The characteristic polynomial is multiplicative on products of representations. -/
@[simp]
theorem charpoly_prod_apply (g : G) :
    (ρ.prod σ g).charpoly = (ρ g).charpoly * (σ g).charpoly :=
  LinearMap.charpoly_prodMap (ρ g) (σ g)

variable (R G V) in
/-- Every element acts with characteristic polynomial `(X - 1) ^ dim V` in the trivial
representation. -/
@[simp]
theorem charpoly_trivial_apply (g : G) : (trivial R G V g).charpoly = (X - 1) ^ finrank R V := by
  nontriviality R
  rw [isTrivial_def, ← Module.End.one_eq_id, LinearMap.charpoly_one]

/-- Every root of the characteristic polynomial of an element of the trivial representation, mapped
to a domain `S`, is `1`. -/
theorem eq_one_of_mem_roots_map_charpoly_trivial {S : Type*} [CommRing S] [IsDomain S]
    {φ : R →+* S} {g : G} {z : S} (hz : z ∈ ((trivial R G V g).charpoly.map φ).roots) :
    z = 1 := by
  have h := (mem_roots'.mp hz).2
  simp only [charpoly_trivial_apply, IsRoot.def, eval_map, eval₂_pow, eval₂_sub, eval₂_X,
    eval₂_one] at h
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h)

/-- **The characteristic polynomial on an invariant submodule and its quotient.** If `U` and
`V ⧸ U` are free of finite rank, `g` acts on `V` with characteristic polynomial the product of
those of its actions on `U` and on `V ⧸ U`. No complement of `U` is needed. -/
theorem charpoly_apply_eq_subrepresentation_mul_quotient (ρ : Representation R G V)
    (U : Submodule R V) (le_comap : ∀ g, U ≤ U.comap (ρ g)) [Module.Free R U] [Module.Finite R U]
    [Module.Free R (V ⧸ U)] [Module.Finite R (V ⧸ U)] (g : G) :
    (ρ g).charpoly =
      (ρ.subrepresentation U le_comap g).charpoly * (ρ.quotient U le_comap g).charpoly :=
  LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ U (ρ g) (le_comap g)

variable (ρ) in
/-- The action of `g` on the `R[G]`-module `ρ.asModule` has the characteristic polynomial of
`ρ g`. -/
theorem charpoly_lsmul_asModule_of (g : G) :
    (Algebra.lsmul R R ρ.asModule (MonoidAlgebra.of R G g)).charpoly = (ρ g).charpoly := by
  rw [← ρ.asModuleEquiv.charpoly_conj]
  congr 1
  ext x
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Algebra.lsmul_coe,
    ← asModuleEquiv_symm_map_rho, LinearEquiv.apply_symm_apply]

end Monoid

section Group

variable [Group G] (ρ : Representation R G V)

/-- Conjugation invariance of the characteristic polynomial in a group representation. -/
theorem charpoly_apply_conj (g h : G) : (ρ (g * h * g⁻¹)).charpoly = (ρ h).charpoly := by
  rw [ρ.charpoly_apply_mul_comm, inv_mul_cancel_left]

/-- In a representation of a group on a finite free module of rank `d`, the characteristic
polynomial of `g⁻¹` is `(-1) ^ d * det (ρ g⁻¹)` times the reverse `det (1 - X ρ(g))` of that of
`g`. -/
theorem charpoly_apply_inv (g : G) :
    (ρ g⁻¹).charpoly = (-1) ^ finrank R V * C (LinearMap.det (ρ g⁻¹)) * (ρ g).charpoly.reverse :=
  LinearMap.charpoly_of_mul_eq_one (by rw [← map_mul, inv_mul_cancel, map_one])

/-- In a representation of a group on a finite free module, the characteristic roots of `g⁻¹` in
a field `S` are the inverses of those of `g`, counted with multiplicity. -/
theorem aroots_charpoly_apply_inv {S : Type*} [Field S] [Algebra R S] (g : G) :
    (ρ g⁻¹).charpoly.aroots S = ((ρ g).charpoly.aroots S).map (·⁻¹) :=
  LinearMap.aroots_charpoly_of_mul_eq_one (by rw [← map_mul, inv_mul_cancel, map_one])

/-- In the contragredient representation, `g` acts with the characteristic polynomial of `g⁻¹`
in the original representation. -/
theorem charpoly_dual_apply (g : G) : (ρ.dual g).charpoly = (ρ g⁻¹).charpoly := by
  rw [dual_apply, ← LinearMap.dualMap_def, LinearMap.charpoly_dualMap]

/-- The characteristic roots of `g` in the contragredient representation, in a field `S`, are the
inverses of those of `g` in the original representation, counted with multiplicity. -/
theorem aroots_charpoly_dual_apply {S : Type*} [Field S] [Algebra R S] (g : G) :
    (ρ.dual g).charpoly.aroots S = ((ρ g).charpoly.aroots S).map (·⁻¹) := by
  rw [charpoly_dual_apply, aroots_charpoly_apply_inv]

end Group

end Representation
