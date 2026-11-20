/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Basic

/-!
# Algebraic laws of the coefficient action on C⋆-modules

The inner-product axioms force the given coefficient action to be additive, associative,
and compatible with complex scalars. For a right Hilbert `B`-module, take `A = Bᵐᵒᵖ`:
then associativity of the left `A`-action gives the usual right-action law.

The structures here are reducible non-instances, preserving the caller's existing `SMul A E`.
Install them locally, for example with `letI := CStarModule.module A E` when `A` is unital,
to use the ordinary module laws. For nonunital coefficients, use `distribSMul`,
`smulWithZero`, and `semigroupAction`, together with `add_smul`, `neg_smul`, `sub_smul`,
and `sum_smul`. Keeping these structures explicit avoids a typeclass-search cycle through
the action required by `CStarModule` itself.
Neither completeness nor the analytic C⋆-algebra axioms are needed for these algebraic laws.

## References

* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
-/

public section

namespace CStarModule

section NonUnital

variable (A E : Type*) [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E]
  [CStarModule A E]

/-- The given coefficient action preserves vector addition and zero. -/
abbrev distribSMul : DistribSMul A E where
  smul := (· • ·)
  smul_zero a := by
    apply ext_inner_left (A := A)
    intro y
    simp
  smul_add a x y := by
    apply ext_inner_left (A := A)
    intro z
    simp [mul_add]

/-- Zero coefficients act by zero, also for nonunital coefficient rings. -/
abbrev smulWithZero : SMulWithZero A E where
  toSMulZeroClass := (distribSMul A E).toSMulZeroClass
  zero_smul x := by
    apply ext_inner_left (A := A)
    intro y
    simp

/-- The given coefficient action is associative, also for nonunital coefficient rings. -/
abbrev semigroupAction : SemigroupAction A E where
  smul := (· • ·)
  mul_smul a b x := by
    apply ext_inner_left (A := A)
    intro y
    simp [mul_assoc]

variable {A E}

/-- The action is additive in the coefficient, without requiring a unit. -/
protected theorem add_smul (a b : A) (x : E) : (a + b) • x = a • x + b • x := by
  apply ext_inner_left (A := A)
  intro y
  simp [add_mul]

/-- Negating a coefficient negates its action, without requiring a unit. -/
protected theorem neg_smul (a : A) (x : E) : (-a) • x = -(a • x) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← CStarModule.add_smul, neg_add_cancel]
  exact (smulWithZero A E).zero_smul x

/-- The action preserves coefficient subtraction, without requiring a unit. -/
protected theorem sub_smul (a b : A) (x : E) : (a - b) • x = a • x - b • x := by
  rw [sub_eq_add_neg, CStarModule.add_smul, CStarModule.neg_smul, sub_eq_add_neg]

/-- Finite sums of coefficients act by the sum of their actions, without requiring a unit. -/
protected theorem sum_smul {ι : Type*} (s : Finset ι) (a : ι → A) (x : E) :
    (∑ i ∈ s, a i) • x = ∑ i ∈ s, a i • x := by
  let f : A →+ E :=
    { toFun := (· • x)
      map_zero' := (smulWithZero A E).zero_smul x
      map_add' := fun a b => CStarModule.add_smul a b x }
  exact map_sum f a s

variable (A E)

/-- Complex scaling of a coefficient agrees with successive actions on the module. -/
theorem isScalarTower [IsScalarTower ℂ A A] : IsScalarTower ℂ A E where
  smul_assoc c a x := by
    apply ext_inner_left (A := A)
    intro y
    simp [smul_mul_assoc]

/-- The coefficient action commutes with complex scaling of vectors.
After installing this class locally, `letI := SMulCommClass.symm ℂ A E` supplies the
reverse class for consumers such as linear action maps and pointwise submodule actions. -/
theorem smulCommClass [SMulCommClass ℂ A A] : SMulCommClass ℂ A E where
  smul_comm c a x := by
    apply ext_inner_left (A := A)
    intro y
    simp [mul_smul_comm]

end NonUnital

/-- Over a unital coefficient ring, the given action is an ordinary module structure.
This reducible non-instance retains the caller's scalar multiplication. -/
abbrev module (A E : Type*) [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
    [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E]
    [CStarModule A E] : Module A E where
  toSMul := inferInstance
  mul_smul := (semigroupAction A E).mul_smul
  one_smul x := by
    apply ext_inner_left (A := A)
    intro y
    simp
  smul_zero := (distribSMul A E).smul_zero
  smul_add := (distribSMul A E).smul_add
  add_smul := CStarModule.add_smul
  zero_smul := (smulWithZero A E).zero_smul

end CStarModule
