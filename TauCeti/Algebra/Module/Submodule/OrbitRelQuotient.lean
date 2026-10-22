/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# The group structure on the translation orbit space of a submodule

A submodule `p` of a module `M` over a ring acts on `M` by translation, and the orbit space of this
action is the standard carrier `AddAction.orbitRel.Quotient p M` for quotients of `M` by
translations, for instance for a complex torus `E ⧸ Λ` built from a lattice `Λ` in a complex
vector space `E`. Two points lie in one orbit exactly when their difference lies in `p`, which is
also the relation defining the quotient module `M ⧸ p`.

This file transfers the additive group structure of `M ⧸ p` to the orbit space, so that the orbit
projection is additive, and records the resulting additive equivalence between the two quotients.

## Main declarations

* `Submodule.orbitRelQuotientAddEquiv`: the orbit space of translation by `p` is additively
  equivalent to the quotient module `M ⧸ p`, by an equivalence sending the orbit of `x` to the
  class of `x`.
* `Submodule.orbitRelQuotient_mk_add`, `Submodule.orbitRelQuotient_mk_zero`,
  `Submodule.orbitRelQuotient_mk_neg`, `Submodule.orbitRelQuotient_mk_sub`: the orbit projection
  is additive.
* `Submodule.orbitRelQuotient_mk_eq_zero_iff`: its kernel is `p`.
-/

public section

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M)

/-- Two points lie in one orbit of translation by a submodule `p` exactly when their difference
lies in `p`. -/
theorem Submodule.orbitRel_apply_iff_sub_mem {x y : M} :
    AddAction.orbitRel p M x y ↔ x - y ∈ p :=
  (QuotientAddGroup.rightRel_apply (s := p.toAddSubgroup)).trans <| by
    rw [← sub_eq_add_neg]; exact sub_mem_comm_iff

/-- The additive group structure on the orbit space of translation by `p`, transferred from the
quotient module `M ⧸ p`, which is the same quotient of `M`. -/
instance Submodule.instAddCommGroupOrbitRelQuotient :
    AddCommGroup (AddAction.orbitRel.Quotient p M) :=
  Equiv.addCommGroup (β := M ⧸ p) <|
    Quotient.congrRight fun _ _ ↦ p.orbitRel_apply_iff_sub_mem.trans p.quotientRel_def.symm

/-- The orbit space of translation by `p` is additively equivalent to the quotient module
`M ⧸ p`, by an equivalence sending the orbit of `x` to the class of `x`. -/
def Submodule.orbitRelQuotientAddEquiv : AddAction.orbitRel.Quotient p M ≃+ M ⧸ p :=
  Equiv.addEquiv (β := M ⧸ p) <|
    Quotient.congrRight fun _ _ ↦ p.orbitRel_apply_iff_sub_mem.trans p.quotientRel_def.symm

/-- `Submodule.orbitRelQuotientAddEquiv` sends the orbit of `x` to the class of `x`. -/
@[simp]
theorem Submodule.orbitRelQuotientAddEquiv_mk (x : M) :
    p.orbitRelQuotientAddEquiv (_root_.Quotient.mk (AddAction.orbitRel p M) x) =
      Submodule.Quotient.mk x :=
  (rfl)

/-- The inverse of `Submodule.orbitRelQuotientAddEquiv` sends the class of `x` to the orbit of
`x`. -/
@[simp]
theorem Submodule.orbitRelQuotientAddEquiv_symm_mk (x : M) :
    p.orbitRelQuotientAddEquiv.symm (Submodule.Quotient.mk x) =
      _root_.Quotient.mk (AddAction.orbitRel p M) x :=
  (rfl)

/-- The orbit projection for translation by `p` is additive. -/
@[simp]
theorem Submodule.orbitRelQuotient_mk_add (x y : M) :
    _root_.Quotient.mk (AddAction.orbitRel p M) (x + y) =
      _root_.Quotient.mk (AddAction.orbitRel p M) x +
        _root_.Quotient.mk (AddAction.orbitRel p M) y :=
  p.orbitRelQuotientAddEquiv.injective <| by simp

/-- The orbit projection for translation by `p` sends `0` to `0`. -/
@[simp]
theorem Submodule.orbitRelQuotient_mk_zero :
    _root_.Quotient.mk (AddAction.orbitRel p M) 0 = 0 :=
  p.orbitRelQuotientAddEquiv.injective <| by simp

/-- A point of `M` projects to `0` in the orbit space of translation by `p` exactly when it lies
in `p`. -/
@[simp]
theorem Submodule.orbitRelQuotient_mk_eq_zero_iff {x : M} :
    _root_.Quotient.mk (AddAction.orbitRel p M) x = 0 ↔ x ∈ p := by
  rw [← orbitRelQuotient_mk_zero, _root_.Quotient.eq, orbitRel_apply_iff_sub_mem, sub_zero]

/-- The orbit projection for translation by `p` commutes with negation. -/
@[simp]
theorem Submodule.orbitRelQuotient_mk_neg (x : M) :
    _root_.Quotient.mk (AddAction.orbitRel p M) (-x) =
      -_root_.Quotient.mk (AddAction.orbitRel p M) x :=
  p.orbitRelQuotientAddEquiv.injective <| by simp

/-- The orbit projection for translation by `p` commutes with subtraction. -/
@[simp]
theorem Submodule.orbitRelQuotient_mk_sub (x y : M) :
    _root_.Quotient.mk (AddAction.orbitRel p M) (x - y) =
      _root_.Quotient.mk (AddAction.orbitRel p M) x -
        _root_.Quotient.mk (AddAction.orbitRel p M) y :=
  p.orbitRelQuotientAddEquiv.injective <| by simp
