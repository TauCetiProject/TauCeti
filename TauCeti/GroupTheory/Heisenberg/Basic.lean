/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.Algebra.GroupAction.Trivial
public import TauCeti.GroupTheory.GroupExtension.Of.FactorSet

/-!
# The Heisenberg group of a bilinear form

The Heisenberg group of a symplectic space is the central extension of the additive group of that
space, by its centre, whose factor set is the symplectic form. This file builds the extension of an
arbitrary bilinear map in the library's factor-set coordinates, and computes the group law, the
inverse, the commutator and the centre in those coordinates. The development is deliberately
coordinate-level: no alternating, nondegeneracy or invertibility hypothesis is used unless a
theorem states it, so one API serves both the integral bilinear extensions and the
half-alternating convention `ω / 2` of the metaplectic cover.

The extension of `B : W × W → C` is the `TauCeti.FactorSet.Extension` of
`TauCeti.Heisenberg.bilinearFactorSet B`: its elements are pairs `(t, w)` with the coefficient
written first, its identity is `(0, 0)`, and its multiplication is

`(t, w) * (s, v) = (t + s + B w v, w + v)`.

Because the action of the space on the coefficients is trivial, the copy of the coefficient group
supplied by `TauCeti.FactorSet.inl` is central (`TauCeti.FactorSet.inl_range_le_center`), and the
commutator of two elements measures the failure of `B` to be symmetric
(`TauCeti.Heisenberg.bilinearExtension_commutator`). Halving an alternating form is therefore what
makes the commutator recover the form itself
(`TauCeti.Heisenberg.halfForm_commutator`), and for a nondegenerate alternating `ω` the centre of
the extension of `ω / 2` is exactly the copy of the coefficient group
(`TauCeti.Heisenberg.halfForm_center`).

## Main definitions

* `TauCeti.Heisenberg.bilinearFactorSet`: the factor set `(w, v) ↦ B w v` of a bilinear map, for
  the trivial action, written multiplicatively on the space and on the coefficients.

## Main results

* `TauCeti.Heisenberg.bilinearFactorSet_apply`: the value of the factor set is `B`.
* `TauCeti.Heisenberg.bilinearExtension_mul_left`,
  `TauCeti.Heisenberg.bilinearExtension_mul_right`: the two coordinates of a product.
* `TauCeti.Heisenberg.bilinearExtension_inv`: the inverse of `(t, w)` is `(B w w - t, -w)`.
* `TauCeti.Heisenberg.bilinearExtension_commutator`: the commutator of `(t, w)` and `(s, v)` is
  `inl (B w v - B v w)`.
* `TauCeti.Heisenberg.bilinearExtension_mem_center_iff`: `(t, w)` is central exactly when `B w ·`
  and `B · w` agree.
* `TauCeti.Heisenberg.halfForm_commutator`, `TauCeti.Heisenberg.halfForm_center`: the two forms
  the half-alternating convention needs.
* `TauCeti.Heisenberg.polarization_cocycle`: the quadratic correction `q x = B x x / 2` converts
  the cocycle of `B` into the cocycle of `ω / 2` for `ω = B - Bᵀ`.

## References

* S. Kudla, Notes on local theta correspondence and local Langlands correspondence (1996), I.1.
* H. Weil, Sur certains groupes d'opérateurs unitaires, Acta Math. 111 (1964), I.§3.
-/

public section

open Multiplicative
open scoped commutatorElement

attribute [local instance] TauCeti.trivialMulDistribMulAction

namespace TauCeti.Heisenberg

variable {R : Type*} [CommRing R] {W C : Type*} [AddCommGroup W] [Module R W]
  [AddCommGroup C] [Module R C]

/-- **The factor set of a bilinear map.** The map `(w, v) ↦ B w v`, written multiplicatively on
both the bilinear space and the coefficient group, is a normalized factor set for the trivial
action of the space on the coefficients: the cocycle identity is the biadditivity of `B`, and the
normalization is `B 0 0 = 0`. The associated extension
`TauCeti.FactorSet.Extension (TauCeti.Heisenberg.bilinearFactorSet B)` is the **Heisenberg group of
`B`**; its law is `(t, w) * (s, v) = (t + s + B w v, w + v)`. -/
def bilinearFactorSet (B : LinearMap.BilinMap R W C) :
    FactorSet (Multiplicative W) (Multiplicative C) where
  toFun p := ofAdd (B p.1.toAdd p.2.toAdd)
  isMulCocycle₂' g h j := by
    refine toAdd.injective ?_
    simp only [TauCeti.trivialMulDistribMulAction_smul, toAdd_mul, toAdd_ofAdd, map_add,
      LinearMap.add_apply]
    abel
  map_one_one' := by
    simp only [toAdd_one, map_zero, ofAdd_zero]

/-- The value of the factor set of `B` at two multiplicatively written space coordinates is the
image under `ofAdd` of the value of `B` at the corresponding additive coordinates: the additive
value of the factor set is `B` itself. -/
@[simp]
theorem bilinearFactorSet_apply (B : LinearMap.BilinMap R W C) (w v : Multiplicative W) :
    bilinearFactorSet B (w, v) = ofAdd (B w.toAdd v.toAdd) :=
  (rfl)

section

variable {B : LinearMap.BilinMap R W C} {p q : (bilinearFactorSet B).Extension}

/-- **The coefficient coordinate of a product** in the Heisenberg group of `B`: the coefficient
accumulates the value of `B` at the two space coordinates. Not `@[simp]`: the global simplifier
already rewrites `(p * q).left` to this normal form through
`TauCeti.FactorSet.Extension.mul_left`, `TauCeti.trivialMulDistribMulAction_smul` and
`TauCeti.Heisenberg.bilinearFactorSet_apply`, so tagging it would shadow those lemmas
(the `simpNF` linter rejects the tag). -/
theorem bilinearExtension_mul_left :
    (p * q).left = ofAdd (p.left.toAdd + q.left.toAdd + B p.right.toAdd q.right.toAdd) := by
  simp only [FactorSet.Extension.mul_left, TauCeti.trivialMulDistribMulAction_smul,
    bilinearFactorSet_apply, ofAdd_add, ofAdd_toAdd]

/-- **The space coordinate of a product** in the Heisenberg group of `B` is the sum of the two
space coordinates: the projection `(t, w) ↦ w` is a homomorphism
(`TauCeti.FactorSet.rightHom`). -/
@[simp]
theorem bilinearExtension_mul_right :
    (p * q).right = ofAdd (p.right.toAdd + q.right.toAdd) := by
  rw [FactorSet.Extension.mul_right]
  conv_lhs => rw [← ofAdd_toAdd p.right, ← ofAdd_toAdd q.right, ← ofAdd_add]

/-- **The inverse in the Heisenberg group of `B`** is `(t, w)⁻¹ = (B w w - t, -w)`. The diagonal
value of `B` appears because `B w (-w) = -B w w`, so the inverse of `(0, w)` is not `(0, -w)`
unless `B` is alternating. -/
theorem bilinearExtension_inv :
    p⁻¹ = ⟨ofAdd (-p.left.toAdd + B p.right.toAdd p.right.toAdd), ofAdd (-p.right.toAdd)⟩ := by
  refine FactorSet.Extension.ext ?_ ?_
  · rw [FactorSet.Extension.inv_left, TauCeti.trivialMulDistribMulAction_smul,
      bilinearFactorSet_apply, toAdd_inv, map_neg]
    conv_lhs => rw [← ofAdd_toAdd p.left, ← ofAdd_add, ← ofAdd_neg, neg_add, neg_neg]
  · rw [FactorSet.Extension.inv_right]
    conv_lhs => rw [← ofAdd_toAdd p.right, ← ofAdd_neg]

/-- **The commutator in the Heisenberg group of `B`**, with the convention
`⁅p, q⁆ = p * q * p⁻¹ * q⁻¹`, is a central element determined by the two space coordinates: it
records the failure of `B` to be symmetric. This is the additive form, for the factor set of a
bilinear map, of `TauCeti.FactorSet.commutatorElement_eq_inl`. -/
theorem bilinearExtension_commutator :
    ⁅p, q⁆ = FactorSet.inl (bilinearFactorSet B)
      (ofAdd (B p.right.toAdd q.right.toAdd - B q.right.toAdd p.right.toAdd)) := by
  rw [FactorSet.commutatorElement_eq_inl (bilinearFactorSet B)
      TauCeti.trivialMulDistribMulAction_smul, bilinearFactorSet_apply, bilinearFactorSet_apply,
    ← ofAdd_sub]

/-- **The centre criterion for the Heisenberg group of `B`**: `(t, w)` is central exactly when the
two maps `B w ·` and `B · w` agree. No nondegeneracy is assumed, so a degenerate `B` can have a
larger centre than the copy of the coefficient group. -/
theorem bilinearExtension_mem_center_iff :
    p ∈ Subgroup.center _ ↔ ∀ v : W, B p.right.toAdd v = B v p.right.toAdd := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hp v
    have hl := congrArg FactorSet.Extension.left (hp ⟨1, ofAdd v⟩)
    simp only [bilinearExtension_mul_left, toAdd_one, toAdd_ofAdd, zero_add, add_zero] at hl
    have h2 := congrArg toAdd hl
    rw [toAdd_ofAdd, toAdd_ofAdd, add_left_cancel_iff] at h2
    exact h2.symm
  · intro hv q
    refine FactorSet.Extension.ext ?_ ?_
    · rw [bilinearExtension_mul_left, bilinearExtension_mul_left, hv q.right.toAdd]
      congr 1
      abel
    · rw [bilinearExtension_mul_right, bilinearExtension_mul_right]
      congr 1
      abel

end

section HalfForm

variable [Invertible (2 : R)] {ω : LinearMap.BilinForm R W}

/-- **The quadratic correction between the two Heisenberg cocycles.** For a scalar form `B` with
`2` invertible, put `q x = B x x / 2` and `ω = B - Bᵀ`. Then the difference of the cocycle of `B`
and the cocycle of `ω / 2` is the coboundary of `q`: concretely
`ω x y / 2 + q (x + y) = B x y + q x + q y`. This is Weil's identity comparing the two ways of
writing the same central extension, and it is what lets the integral extension of `B` be replaced
by the half-alternating one. -/
theorem polarization_cocycle (B : LinearMap.BilinForm R W) (x y : W) :
    (⅟(2 : R) • (B - B.flip)) x y + ⅟(2 : R) • B (x + y) (x + y)
      = B x y + ⅟(2 : R) • B x x + ⅟(2 : R) • B y y := by
  have hstep : (⅟(2 : R) • (B - B.flip)) x y = ⅟(2 : R) • (B x y - B y x) := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.sub_apply,
      show (B.flip x) y = B y x from rfl]
  have hdiag : B (x + y) (x + y) = B x x + B x y + B y x + B y y := by
    simp only [map_add, LinearMap.add_apply]
    abel
  have hinner : B x y - B y x + (B x x + B x y + B y x + B y y)
      = (2 : R) • B x y + B x x + B y y := by
    rw [two_smul]
    abel
  rw [hstep, hdiag, ← smul_add, hinner, smul_add, smul_add, smul_smul, invOf_mul_self, one_smul]

/-- **The commutator in the half-alternating Heisenberg group**: for an alternating `ω` with `2`
invertible, the commutator of two elements of the extension of `ω / 2` is the central element
`inl (ω w v)`. The halving is what makes the commutator recover `ω` itself, rather than twice `ω`.
-/
theorem halfForm_commutator (hω : ω.IsAlt) (p q : (bilinearFactorSet (⅟(2 : R) • ω)).Extension) :
    ⁅p, q⁆ = FactorSet.inl (bilinearFactorSet (⅟(2 : R) • ω))
      (ofAdd (ω p.right.toAdd q.right.toAdd)) := by
  rw [bilinearExtension_commutator]
  congr 1
  have key : (⅟(2 : R) • ω) p.right.toAdd q.right.toAdd
      - (⅟(2 : R) • ω) q.right.toAdd p.right.toAdd = ω p.right.toAdd q.right.toAdd := by
    simp only [LinearMap.smul_apply]
    rw [show ω q.right.toAdd p.right.toAdd = -(ω p.right.toAdd q.right.toAdd) from
      (hω.neg_eq p.right.toAdd q.right.toAdd).symm, smul_neg, sub_eq_add_neg, neg_neg,
      ← add_smul, ← two_mul, mul_invOf_self, one_smul]
  rw [key]

/-- **The centre of the Heisenberg group**: for a nondegenerate alternating `ω` with `2`
invertible, the centre of the extension of `ω / 2` is exactly the range of
`TauCeti.FactorSet.inl`, the copy of the coefficient group. This is the group-theoretic shadow of
nondegeneracy: a central element has trivial space coordinate. -/
theorem halfForm_center (hω : ω.IsAlt) (hωn : ω.Nondegenerate) :
    Subgroup.center ((bilinearFactorSet (⅟(2 : R) • ω)).Extension) =
      (FactorSet.inl (bilinearFactorSet (⅟(2 : R) • ω))).range := by
  refine le_antisymm ?_ ?_
  · intro p hp
    rw [bilinearExtension_mem_center_iff] at hp
    simp only [LinearMap.smul_apply] at hp
    have hsym : ∀ y : W, ω p.right.toAdd y = ω y p.right.toAdd := by
      intro y
      have h2 := congrArg ((2 : R) • ·) (hp y)
      rw [smul_smul, mul_invOf_self, one_smul, smul_smul, mul_invOf_self, one_smul] at h2
      exact h2
    have hzero : ∀ v : W, ω p.right.toAdd v = 0 := by
      intro v
      have hn : ω p.right.toAdd v = -(ω p.right.toAdd v) :=
        (hsym v).trans (hω.neg_eq p.right.toAdd v).symm
      have ht : (2 : R) • ω p.right.toAdd v = 0 := by
        rw [two_smul]
        nth_rw 2 [hn]
        abel
      have hc : ω p.right.toAdd v = ⅟(2 : R) • (2 : R) • ω p.right.toAdd v := by
        rw [smul_smul, invOf_mul_self, one_smul]
      rw [hc, ht, smul_zero]
    have hz : ω p.right.toAdd = 0 := by
      ext v
      rw [LinearMap.zero_apply]
      exact hzero v
    have hw : p.right.toAdd = 0 := by
      have hmem : p.right.toAdd ∈ LinearMap.ker (ω : LinearMap.BilinForm R W) :=
        LinearMap.mem_ker.mpr hz
      rw [hωn.ker_eq_bot] at hmem
      exact hmem
    refine MonoidHom.mem_range.mpr ⟨p.left, FactorSet.Extension.ext
      (FactorSet.inl_left _ _) ?_⟩
    rw [FactorSet.inl_right, ← ofAdd_toAdd p.right, hw, ofAdd_zero]
  · exact FactorSet.inl_range_le_center (bilinearFactorSet (⅟(2 : R) • ω))
      TauCeti.trivialMulDistribMulAction_smul

end HalfForm

end TauCeti.Heisenberg
