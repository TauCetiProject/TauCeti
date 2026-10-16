/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Natural numbers invertible in residue fields

This file records how the condition `(N : κ(x)) ≠ 0`, that a natural number `N` is invertible in
the residue field at a point `x`, carries over between schemes. It is the form in which "`N` is
invertible on the base" enters the theory of level structures on elliptic curves.

## Main results

* `AlgebraicGeometry.Scheme.Hom.natCast_residueField_ne_zero`: if `N` is invertible in the residue
  field at `f x`, then it is invertible in the residue field at `x`, for any morphism `f`.
* `AlgebraicGeometry.Spec.natCast_residueField_ne_zero`: if `N` is invertible in a field `K`, then
  it is invertible in the residue field of `Spec K`.

The proofs only use that a ring homomorphism between fields, such as Mathlib's
`Scheme.Hom.residueFieldMap`, preserves natural number casts and is injective.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- If `N` is invertible in the residue field at `f x`, it is invertible in the residue field
at `x`. -/
theorem Scheme.Hom.natCast_residueField_ne_zero {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {N : ℕ}
    (hN : (N : Y.residueField (f x)) ≠ 0) : (N : X.residueField x) ≠ 0 := by
  rw [← map_natCast (f.residueFieldMap x).hom]
  exact (map_ne_zero _).mpr hN

/-- If `N` is invertible in a field `K`, it is invertible in the residue field of `Spec K`. -/
theorem Spec.natCast_residueField_ne_zero {K : Type u} [Field K] {N : ℕ} (hN : (N : K) ≠ 0)
    (s : Spec (.of K)) : (N : (Spec (.of K)).residueField s) ≠ 0 := by
  rw [← map_natCast ((Scheme.ΓSpecIso (.of K)).inv ≫
    (Spec (.of K)).presheaf.germ ⊤ s trivial ≫ (Spec (.of K)).residue s).hom]
  exact (map_ne_zero _).mpr hN

end AlgebraicGeometry
