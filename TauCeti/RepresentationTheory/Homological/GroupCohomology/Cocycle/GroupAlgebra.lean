/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import TauCeti.Algebra.MonoidAlgebra.Augmentation.Basic

/-!
# Scalar cocycles on a group algebra

The linear extension of a crossed homomorphism for a scalar character satisfies a product rule
with two different scalar factors. On the right it uses augmentation, and on the left it uses
the character. In particular, its restriction to the augmentation ideal is equivariant for
the character action. This is useful for translating group algebra relations into equations
on cocycle values.
-/

public section

open scoped MonoidAlgebra

namespace MonoidAlgebra

variable {R G V : Type*} [CommSemiring R] [Monoid G] [AddCommMonoid V] [Module R V]

/-- Extend the scalar cocycle identity from group elements to products in the group algebra. -/
theorem constr_mul_of_cocycle (χ : G →* R) {c : G → V}
    (hc : ∀ g h, c (g * h) = c g + χ g • c h) (x y : R[G]) :
    (basis G R).constr R c (x * y) =
      augmentation R G y • (basis G R).constr R c x +
        lift R R G χ x • (basis G R).constr R c y := by
  have hF (g : G) : (basis G R).constr R c (of R G g) = c g := by
    rw [of_apply, ← basis_apply, Module.Basis.constr_basis]
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    induction y using MonoidAlgebra.induction_on with
    | of h =>
      rw [← map_mul]
      rw [hF, hF, hF, lift_of]
      simpa only [of_apply, augmentation_single, one_smul] using hc g h
    | add x y hx hy =>
      simp only [mul_add, map_add, add_smul, smul_add, hx, hy]
      ac_rfl
    | smul r y hy =>
      simp only [mul_smul_comm, map_smul, augmentation_smul, hy,
        smul_add, mul_smul, smul_comm (lift R R G χ (of R G g)) r]
  | add x y hx hy =>
    simp only [add_mul, map_add, add_smul, smul_add, hx, hy]
    abel
  | smul r x hx =>
    simp only [smul_mul_assoc, map_smul, hx, smul_add, mul_smul,
      smul_comm (augmentation R G y) r, smul_eq_mul]

end MonoidAlgebra
