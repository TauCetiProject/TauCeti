/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# Reduced products and reduced matrix rings

A product of monoids with zero is reduced exactly when every factor is (`TauCeti.isReduced_pi_iff`;
Mathlib supplies the instance for the converse direction).  A matrix ring over a nonzero reduced
semiring is reduced exactly when it has at most one index (`Matrix.isReduced_iff_subsingleton`):
for `i ≠ j` the matrix unit `Eᵢⱼ` is nonzero and squares to zero.

Together these read off the shape of a reduced ring from an Artin--Wedderburn decomposition: every
matrix block has size one.

## Main results

* `TauCeti.isReduced_pi_iff`: a product of monoids with zero is reduced if and only if every factor
  is.
* `Matrix.subsingleton_of_isReduced`: a reduced matrix ring over a nonzero semiring has at most one
  index.
* `Matrix.isReduced_iff_subsingleton`: a matrix ring over a nonzero reduced semiring is reduced
  if and only if it has at most one index.

## Implementation notes

Mathlib's `Matrix.uniqueRingEquiv` fixes the `Fintype` structure on the one-element index type to
the one manufactured from `Unique`, so its type does not match a matrix ring formed with a given
`Fintype` instance -- the two are equal but not definitionally so, and the multiplication of a
matrix ring depends on which one is used.  The proof of `Matrix.isReduced_iff_subsingleton`
therefore rewrites along `Subsingleton.elim` first.
-/

public section

/-- **A product of monoids with zero is reduced exactly when every factor is.**  A nilpotent element
of one factor extends by zero, via `Pi.single`, to a nilpotent element of the product. -/
@[simp]
theorem TauCeti.isReduced_pi_iff {ι : Type*} {R : ι → Type*} [∀ i, MonoidWithZero (R i)] :
    IsReduced (∀ i, R i) ↔ ∀ i, IsReduced (R i) := by
  classical
  refine ⟨fun _ i => ⟨fun y ⟨n, hn⟩ => ?_⟩, fun _ => inferInstance⟩
  -- The `(n + 1)`-st power of `Pi.single i y` vanishes in every coordinate.
  have hx : (Pi.single i y : ∀ j, R j) ^ (n + 1) = 0 := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp [pow_succ, hn]
    · simp [hj, zero_pow]
  simpa using congrFun (IsReduced.eq_zero _ ⟨n + 1, hx⟩) i

namespace Matrix

variable {m A : Type*} [DecidableEq m] [Fintype m] [Semiring A] [Nontrivial A]

/-- **A matrix ring of size at least two is never reduced.**  For `i ≠ j` the matrix unit `Eᵢⱼ` is
nonzero and squares to zero, so a reduced matrix ring over a nonzero semiring has at most one
index. -/
theorem subsingleton_of_isReduced [IsReduced (Matrix m m A)] : Subsingleton m := by
  refine ⟨fun i j => by_contra fun hij => ?_⟩
  have h0 : (single i j 1 : Matrix m m A) = 0 :=
    IsReduced.eq_zero _ ⟨2, by simp [sq, Ne.symm hij]⟩
  simpa using congrFun (congrFun h0 i) j

/-- **A matrix ring over a nonzero reduced semiring is reduced exactly in size at most one.**  In
one direction this is `Matrix.subsingleton_of_isReduced`; in the other, a matrix ring on an empty
index is the zero ring, and on a one-element index it is the base semiring. -/
@[simp]
theorem isReduced_iff_subsingleton [IsReduced A] : IsReduced (Matrix m m A) ↔ Subsingleton m := by
  refine ⟨fun _ => subsingleton_of_isReduced (A := A), fun hm => ?_⟩
  rcases isEmpty_or_nonempty m with hempty | ⟨⟨i⟩⟩
  · infer_instance
  · have : Unique m := uniqueOfSubsingleton i
    -- Replace the given `Fintype` instance by the one `Matrix.uniqueRingEquiv` is stated for.
    obtain rfl : ‹Fintype m› = Unique.fintype := Subsingleton.elim _ _
    exact isReduced_of_injective _ uniqueRingEquiv.injective

end Matrix
