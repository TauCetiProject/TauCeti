/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Noncommutative.Basic
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Group.Units.Opposite

/-!
# Opposite coefficients and inverse factors

For a crossed system `(σ, a)` on `D`, the automorphisms `σ_g.op` and units
`op (a(g,h)⁻¹)` form a crossed system on `Dᵐᵒᵖ`, with the same index monoid.
This is the system for left algebra actions on right-`D` multiplicity spaces:
semilinear operators satisfying `A_g A_h(m) = A_(gh)(m) a(g,h)⁻¹` act through its
crossed-product algebra. In particular it retains the noncommutative commutant
in Clifford theory, instead of replacing it with scalars.

The crossed-product algebra, its basis and universal property are supplied by
`CrossedSystem.Algebra`; only the coefficient system is changed here.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace TauCeti.CrossedSystem

open MulOpposite

universe u v w

variable {k : Type u} {D : Type v} {G : Type w}
  [CommSemiring k] [Semiring D] [_root_.Algebra k D] [Monoid G]

/-- The crossed system on the opposite coefficient algebra, with inverse unit factors.
The index monoid is unchanged. -/
def op (c : CrossedSystem k D G) : CrossedSystem k Dᵐᵒᵖ G where
  action g := (c.action g).op
  factor g h := Units.opEquiv.symm (MulOpposite.op (c.factor g h)⁻¹)
  action_one := by
    ext d
    simp [AlgEquiv.op_apply_apply]
  factor_one_left g := by simp
  factor_one_right g := by simp
  action_mul g h d := by
    apply MulOpposite.unop_injective
    simp only [AlgEquiv.op_apply_apply, Units.coe_opEquiv_symm, unop_op, unop_mul]
    have hmul := c.action_mul g h d.unop
    calc
      (↑(c.factor g h)⁻¹ : D) * c.action g (c.action h d.unop) =
          (↑(c.factor g h)⁻¹ : D) *
            (c.action g (c.action h d.unop) * c.factor g h) *
              (↑(c.factor g h)⁻¹ : D) := by simp [mul_assoc]
      _ = c.action (g * h) d.unop * (↑(c.factor g h)⁻¹ : D) := by
        rw [hmul]
        simp
  factor_assoc g h j := by
    apply MulOpposite.unop_injective
    simp only [Units.coe_opEquiv_symm, unop_op, unop_mul, AlgEquiv.op_apply_apply]
    have h : c.factor g h * c.factor (g * h) j =
        Units.map (c.action g).toMonoidHom (c.factor h j) * c.factor g (h * j) :=
      Units.ext (c.factor_assoc g h j)
    have hi := congrArg (fun a : Dˣ => (↑a⁻¹ : D)) h
    simpa using hi

/-- The opposite system applies the original automorphism to the underlying coefficient. -/
@[simp]
theorem op_action (c : CrossedSystem k D G) (g : G) (d : Dᵐᵒᵖ) :
    c.op.action g d = MulOpposite.op (c.action g d.unop) := (rfl)

/-- The opposite system's factor is the opposite of the original inverse factor. -/
@[simp]
theorem op_factor (c : CrossedSystem k D G) (g h : G) :
    (c.op.factor g h : Dᵐᵒᵖ) = MulOpposite.op (↑(c.factor g h)⁻¹ : D) := (rfl)

end TauCeti.CrossedSystem
