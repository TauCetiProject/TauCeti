/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Noncommutative.Basic

/-!
# Changing the coefficient algebra of a noncommutative crossed product

An algebra equivalence transports a crossed system by conjugating its coefficient
automorphisms and mapping its unit factors. The corresponding crossed-product equivalence
sends `d[g]` to `e(d)[g]`, retaining the index monoid and the order of all factors.
More generally, `TauCeti.CrossedSystem.Algebra.congr` compares any two crossed systems
whose automorphisms and factors correspond under the specified coefficient equivalence.

These comparisons allow crossed-product modules to be transported when an equivariant
endomorphism algebra is replaced by an isomorphic algebra. Both forward and inverse
coefficient formulas are available without unfolding the constructions.

The construction follows `TauCeti.CrossedProduct.congr`, using the noncommutative
crossed-product universal property and Mathlib's `Finsupp.mapRange.linearEquiv`.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace TauCeti.CrossedSystem

universe u v w x y

variable {k : Type u} [CommSemiring k] {D : Type v} [Semiring D] [_root_.Algebra k D]
  {E : Type w} [Semiring E] [_root_.Algebra k E] {G : Type x} [Monoid G]

/-- Transport a crossed system along an equivalence of coefficient algebras, conjugating
the automorphisms and mapping the unit factors. -/
def map (c : CrossedSystem k D G) (e : D ≃ₐ[k] E) : CrossedSystem k E G where
  action g := e.autCongr (c.action g)
  factor g h := Units.map e.toMonoidHom (c.factor g h)
  action_one := by
    rw [c.action_one]
    exact e.autCongr.map_one
  factor_one_left g := by simp
  factor_one_right g := by simp
  action_mul g h d := by
    simpa using congrArg e (c.action_mul g h (e.symm d))
  factor_assoc g h j := by
    simpa using congrArg e (c.factor_assoc g h j)

/-- The transported automorphism is conjugation by the coefficient equivalence. -/
@[simp]
theorem map_action_apply (c : CrossedSystem k D G) (e : D ≃ₐ[k] E) (g : G) (d : E) :
    (c.map e).action g d = e (c.action g (e.symm d)) := (rfl)

/-- The transported factors are the images of the original unit factors. -/
@[simp]
theorem map_factor (c : CrossedSystem k D G) (e : D ≃ₐ[k] E) (g h : G) :
    (c.map e).factor g h = Units.map e.toMonoidHom (c.factor g h) := (rfl)

/-- Transport by the identity coefficient equivalence leaves the crossed system unchanged. -/
@[simp]
theorem map_refl (c : CrossedSystem k D G) : c.map (AlgEquiv.refl : D ≃ₐ[k] D) = c := by
  ext <;> rfl

/-- Successive coefficient transports agree with transport along the composite equivalence. -/
theorem map_trans (c : CrossedSystem k D G) (e : D ≃ₐ[k] E)
    {F : Type y} [Semiring F] [_root_.Algebra k F] (f : E ≃ₐ[k] F) :
    (c.map e).map f = c.map (e.trans f) := by
  ext <;> rfl

namespace Algebra

variable (c : CrossedSystem k D G) (d : CrossedSystem k E G) (e : D ≃ₐ[k] E)

private noncomputable def congrLinearEquiv : Algebra c ≃ₗ[k] Algebra d :=
  ((basis c).repr.restrictScalars k).trans
    ((Finsupp.mapRange.linearEquiv e.toLinearEquiv).trans
      ((basis d).repr.symm.restrictScalars k))

private theorem congrLinearEquiv_smul_basis (g : G) (a : D) :
    congrLinearEquiv c d e (a • basis c g) = e a • basis d g := by
  simp [congrLinearEquiv, Finsupp.smul_single, smul_eq_mul]

variable (hact : ∀ g a, e (c.action g a) = d.action g (e a))
  (hfactor : ∀ g h, Units.map e.toMonoidHom (c.factor g h) = d.factor g h)

private noncomputable def congrHom : Algebra c →ₐ[k] Algebra d :=
  lift ((inc d).comp e.toAlgHom) (basis d)
    (fun g a ↦ by simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, basis_mul_inc, hact])
    (fun g h ↦ by
      have hf : e (c.factor g h : D) = (d.factor g h : E) :=
        congrArg Units.val (hfactor g h)
      simp only [basis_mul_basis, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hf])
    (basis_one)

private theorem coe_congrHom : ⇑(congrHom c d e hact hfactor) = congrLinearEquiv c d e := by
  funext a
  induction a using induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | smul_basis g a =>
    rw [congrHom, lift_smul_basis, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      congrLinearEquiv_smul_basis, smul_def]

/-- An equivalence of coefficient algebras identifying the automorphisms and unit factors
induces an equivalence of crossed products, sending `a[g]` to `e(a)[g]`. -/
noncomputable def congr : Algebra c ≃ₐ[k] Algebra d :=
  AlgEquiv.ofBijective (congrHom c d e hact hfactor) (by
    rw [coe_congrHom]
    exact (congrLinearEquiv c d e).bijective)

/-- Coefficient transport preserves each index basis element. -/
@[simp]
theorem congr_basis (g : G) : congr c d e hact hfactor (basis c g) = basis d g := by
  simp only [congr, AlgEquiv.ofBijective_apply, congrHom, lift_basis]

/-- Coefficient transport restricts to the specified algebra equivalence. -/
@[simp]
theorem congr_inc (a : D) : congr c d e hact hfactor (inc c a) = inc d (e a) := by
  simp only [congr, AlgEquiv.ofBijective_apply, congrHom, lift_inc, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom]

/-- The crossed-product equivalence is semilinear for the left coefficient actions. -/
@[simp]
theorem congr_smul (a : D) (b : Algebra c) :
    congr c d e hact hfactor (a • b) = e a • congr c d e hact hfactor b := by
  rw [smul_def, map_mul, congr_inc, smul_def]

/-- Every coefficient is mapped by the specified equivalence. -/
@[simp]
theorem repr_congr (a : Algebra c) (g : G) :
    (basis d).repr (congr c d e hact hfactor a) g = e ((basis c).repr a g) := by
  rw [congr, AlgEquiv.ofBijective_apply, coe_congrHom]
  simp [congrLinearEquiv]

/-- Inverse transport preserves each index basis element. -/
@[simp]
theorem congr_symm_basis (g : G) : (congr c d e hact hfactor).symm (basis d g) = basis c g :=
  (congr c d e hact hfactor).symm_apply_eq.mpr (congr_basis c d e hact hfactor g).symm

/-- Inverse transport restricts to the inverse coefficient equivalence. -/
@[simp]
theorem congr_symm_inc (a : E) :
    (congr c d e hact hfactor).symm (inc d a) = inc c (e.symm a) := by
  apply (congr c d e hact hfactor).injective
  simp

/-- Inverse transport is semilinear for the inverse coefficient equivalence. -/
@[simp]
theorem congr_symm_smul (a : E) (b : Algebra d) :
    (congr c d e hact hfactor).symm (a • b) =
      e.symm a • (congr c d e hact hfactor).symm b := by
  apply (congr c d e hact hfactor).injective
  simp

/-- The inverse equivalence maps coefficients by the inverse coefficient equivalence. -/
@[simp]
theorem repr_congr_symm (a : Algebra d) (g : G) :
    (basis c).repr ((congr c d e hact hfactor).symm a) g = e.symm ((basis d).repr a g) := by
  apply e.injective
  rw [← repr_congr c d e hact hfactor, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

end Algebra
end TauCeti.CrossedSystem
