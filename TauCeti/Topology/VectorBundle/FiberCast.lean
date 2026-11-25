/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Bundle
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Identifying the fibres over equal points

For a family `E : X → Type*` of topological modules over a semiring `R`, for instance the fibres of
a vector bundle, an equality `a = b` of points of `X` identifies the fibres `E a` and `E b` as
topological modules (`TauCeti.fiberCast`). This identification does not move points of the total
space (`TauCeti.mk_fiberCast`), so a frame along one map can be read as a frame along another map
with the same values. It is the identity for `rfl` and is compatible with inverses and composition
(`TauCeti.fiberCast_rfl`, `TauCeti.fiberCast_symm`, `TauCeti.fiberCast_trans`).

## Main definitions

* `TauCeti.fiberCast`: the identification `E a ≃L[R] E b` of the fibres over two equal points.

## Main results

* `TauCeti.mk_fiberCast`: `TauCeti.fiberCast` does not move points of the total space.
-/

public section

noncomputable section

open Bundle

namespace TauCeti

variable {R X : Type*} [Semiring R] {E : X → Type*} [∀ x, AddCommMonoid (E x)]
  [∀ x, Module R (E x)] [∀ x, TopologicalSpace (E x)]

/-- The identification of the fibres of `E` over two equal points, which lets a frame along one
map be read as a frame along another map with the same values. -/
def fiberCast {a b : X} (h : a = b) : E a ≃L[R] E b :=
  h ▸ ContinuousLinearEquiv.refl R (E a)

/-- `TauCeti.fiberCast` does not move points of the total space. -/
@[simp]
theorem mk_fiberCast {F : Type*} {a b : X} (h : a = b) (w : E a) :
    TotalSpace.mk' F b (fiberCast (R := R) h w) = TotalSpace.mk' F a w := by
  subst h
  rfl

/-- The identification of the fibres over a point with themselves is the identity. -/
@[simp]
theorem fiberCast_rfl {a : X} :
    fiberCast (E := E) (rfl : a = a) = ContinuousLinearEquiv.refl R (E a) := by
  ext
  rfl

/-- The inverse of the identification of the fibres along `h` is the identification along
`h.symm`. -/
@[simp]
theorem fiberCast_symm {a b : X} (h : a = b) :
    (fiberCast (R := R) (E := E) h).symm = fiberCast h.symm := by
  subst h
  rfl

/-- Identifications of fibres compose along the composite equality. -/
@[simp]
theorem fiberCast_trans {a b c : X} (h : a = b) (h' : b = c) :
    (fiberCast (R := R) (E := E) h).trans (fiberCast h') = fiberCast (h.trans h') := by
  subst h h'
  rfl

end TauCeti
