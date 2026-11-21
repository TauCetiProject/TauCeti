/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Algebra.GroupAction.Trivial
public import TauCeti.GroupTheory.GroupExtension.Of.FactorSet

/-!
# The Heisenberg group of a bilinear form

The Heisenberg group of a symplectic space is the central extension of the additive group of that
space by its coefficient group, with factor set the half-form `ω / 2` when `2` is invertible. This
file builds the extension of an arbitrary bilinear map in the library's factor-set coordinates, and
computes the group law, the inverse, the commutator and the centre in those coordinates. The
development is deliberately coordinate-level: no alternating, nondegeneracy or invertibility
hypothesis is used unless a theorem states it, so one API serves both the integral bilinear
extensions and the half-alternating convention of the metaplectic cover. In general the copy of the
coefficient group supplied by `TauCeti.FactorSet.inl` is only a subgroup of the centre; it is the
whole centre exactly when the form is nondegenerate alternating.

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
    FactorSet (Multiplicative W) (Multiplicative C) :=
  FactorSet.ofBimultiplicative
    { toFun w := AddMonoidHom.toMultiplicative (LinearMap.toAddMonoidHom (B w.toAdd))
      map_one' := by ext; simp
      map_mul' _ _ := by ext; simp [ofAdd_add] }
    TauCeti.trivialMulDistribMulAction_smul

/-- The value of the factor set of `B` at two multiplicatively written space coordinates is the
image under `ofAdd` of the value of `B` at the corresponding additive coordinates: the additive
value of the factor set is `B` itself. -/
@[simp]
theorem bilinearFactorSet_apply (B : LinearMap.BilinMap R W C) (w v : Multiplicative W) :
    bilinearFactorSet B (w, v) = ofAdd (B w.toAdd v.toAdd) := by
  rw [bilinearFactorSet, FactorSet.ofBimultiplicative_apply]
  simp [LinearMap.toAddMonoidHom_coe]

section

variable {B : LinearMap.BilinMap R W C} {p q : (bilinearFactorSet B).Extension}

/-- **The inverse in the Heisenberg group of `B`** is `(t, w)⁻¹ = (B w w - t, -w)`. In particular,
the inverse of `(0, w)` is `(0, -w)` exactly when `B w w = 0`; this holds for every `w` when `B` is
alternating. -/
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
    have hcomm := commutatorElement_eq_one_iff_mul_comm.mpr (hp ⟨1, ofAdd v⟩)
    rw [bilinearExtension_commutator, map_eq_one_iff _ (FactorSet.inl_injective _),
      ofAdd_eq_one, sub_eq_zero] at hcomm
    exact hcomm.symm
  · intro hv q
    refine commutatorElement_eq_one_iff_mul_comm.mp ?_
    rw [bilinearExtension_commutator]
    have h0 : B q.right.toAdd p.right.toAdd - B p.right.toAdd q.right.toAdd = 0 := by
      rw [hv q.right.toAdd]; abel
    simp [h0, map_one]

end

section HalfForm

variable [Invertible (2 : R)] {ω : LinearMap.BilinForm R W}

/-- **The quadratic correction between the two Heisenberg cocycles.** For a scalar form `B` with
`2` invertible, put `q x = B x x / 2` and `ω = B - Bᵀ`. Then the difference of the cocycle of
`ω / 2` and the cocycle of `B` is the coboundary of `q`; explicitly `ω / 2 - B = δq`, where
`δq (x, y) = q x + q y - q (x + y)`, or concretely
`(ω x y) / 2 + q (x + y) = B x y + q x + q y`. This is Weil's identity comparing the two ways of
writing the same central extension, and it is what lets the integral extension of `B` be replaced
by the half-alternating one. -/
theorem polarization_cocycle (B : LinearMap.BilinForm R W) (x y : W) :
    (⅟(2 : R) • (B - B.flip)) x y + ⅟(2 : R) • B (x + y) (x + y)
      = B x y + ⅟(2 : R) • B x x + ⅟(2 : R) • B y y := by
  have hstep : (⅟(2 : R) • (B - B.flip)) x y = ⅟(2 : R) • (B x y - B y x) := by
    simp [LinearMap.sub_apply, LinearMap.smul_apply, mul_sub]
  have hdiag : B (x + y) (x + y) = B x x + B x y + B y x + B y y := by
    have h := LinearMap.BilinMap.polar_toQuadraticMap (B := B) x y
    simp only [QuadraticMap.polar, LinearMap.BilinMap.toQuadraticMap_apply] at h
    calc B (x + y) (x + y) = (B (x + y) (x + y) - B x x - B y y) + B x x + B y y := by abel
      _ = (B x y + B y x) + B x x + B y y := by rw [h]
      _ = B x x + B x y + B y x + B y y := by abel
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
  refine le_antisymm ?_ (FactorSet.inl_range_le_center _ TauCeti.trivialMulDistribMulAction_smul)
  · intro p hp
    rw [FactorSet.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, FactorSet.rightHom_apply]
    rw [← ofAdd_toAdd p.right]
    congr
    apply hωn.2 p.right.toAdd
    intro y
    have hcomm := commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hp ⟨1, ofAdd y⟩)
    rw [halfForm_commutator hω] at hcomm
    have hcomm' : (bilinearFactorSet (⅟(2 : R) • ω)).inl (ofAdd (ω y p.right.toAdd)) = 1 := by
      simpa using hcomm
    have hzero : ω y p.right.toAdd = 0 := by
      have h' : (bilinearFactorSet (⅟(2 : R) • ω)).inl (ofAdd (ω y p.right.toAdd))
          = (bilinearFactorSet (⅟(2 : R) • ω)).inl 1 := by
        rw [hcomm']
        exact (FactorSet.inl (bilinearFactorSet (⅟(2 : R) • ω))).map_one.symm
      have h'' := FactorSet.inl_injective (bilinearFactorSet (⅟(2 : R) • ω)) h'
      simpa [ofAdd_eq_one] using h''
    exact hzero

end HalfForm

end TauCeti.Heisenberg
