/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Bilinear
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Algebra.Algebra

/-!
# The algebra of bounded Hölder functions

Bounded Hölder functions with values in a normed real algebra form a normed real algebra under
pointwise multiplication. The existing supremum-plus-Hölder norm is submultiplicative with constant
one. Completeness is inherited from `HolderSpace`, so Banach algebra valued functions
give a Banach algebra. Commutativity and the normalization `‖1‖ = 1` are inherited when available;
the latter requires a nonempty domain.

Constants, inclusion into bounded continuous functions, and evaluation are continuous algebra
homomorphisms of operator norm at most one, with equality on nontrivial values and nonempty domains.
This makes coefficient multiplication available within the Hölder spaces used in elliptic estimates.
-/

public section

noncomputable section

open scoped NNReal BoundedContinuousFunction

namespace TauCeti.HolderSpace

variable {X A : Type*} [MetricSpace X] {α : ℝ≥0}

section NonUnital

variable [NonUnitalNormedRing A] [NormedSpace ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

instance : Mul (HolderSpace α X A) := ⟨fun f g ↦ (ContinuousLinearMap.mul ℝ A).compHolder₂ f g⟩

@[simp]
theorem mul_apply (f g : HolderSpace α X A) (x : X) : (f * g) x = f x * g x :=
  (ContinuousLinearMap.mul ℝ A).compHolder₂_apply f g x

@[simp]
theorem toBoundedContinuousFunction_mul (f g : HolderSpace α X A) :
    (f * g).toBoundedContinuousFunction =
      f.toBoundedContinuousFunction * g.toBoundedContinuousFunction := by
  ext x
  simp

instance : NonUnitalRing (HolderSpace α X A) where
  __ := (inferInstance : AddCommGroup (HolderSpace α X A))
  mul_assoc f g h := ext fun x ↦ by simp [mul_assoc]
  left_distrib f g h := toBoundedContinuousFunction_injective (by simp [mul_add])
  right_distrib f g h := toBoundedContinuousFunction_injective (by simp [add_mul])
  zero_mul f := toBoundedContinuousFunction_injective (by simp)
  mul_zero f := toBoundedContinuousFunction_injective (by simp)

/-- The supremum-plus-Hölder norm is submultiplicative, with no loss in the constant. -/
instance : NonUnitalNormedRing (HolderSpace α X A) where
  __ := (inferInstance : NonUnitalRing (HolderSpace α X A))
  __ := (inferInstance : NormedAddCommGroup (HolderSpace α X A))
  norm_mul_le f g := by
    have h := ((ContinuousLinearMap.mul ℝ A).compHolder₂ (α := α) (X := X)).le_opNorm₂ f g
    have hnorm := ((ContinuousLinearMap.mul ℝ A).norm_compHolder₂_le
      (α := α) (X := X)).trans (ContinuousLinearMap.opNorm_mul_le ℝ A)
    exact h.trans (by nlinarith [mul_nonneg (norm_nonneg f) (norm_nonneg g)])

instance : IsScalarTower ℝ (HolderSpace α X A) (HolderSpace α X A) where
  smul_assoc c f g := toBoundedContinuousFunction_injective (by simp [smul_mul_assoc])

instance : SMulCommClass ℝ (HolderSpace α X A) (HolderSpace α X A) where
  smul_comm c f g := toBoundedContinuousFunction_injective (by simp [mul_smul_comm])

@[simp]
theorem const_mul (a b : A) : const (α := α) (X := X) (a * b) = const a * const b := by
  ext x
  simp

end NonUnital

section Unital

variable [NormedRing A] [NormedAlgebra ℝ A]

instance : One (HolderSpace α X A) := ⟨const 1⟩

@[simp]
theorem one_apply (x : X) : (1 : HolderSpace α X A) x = 1 := const_apply 1 x

@[simp]
theorem toBoundedContinuousFunction_one :
    (1 : HolderSpace α X A).toBoundedContinuousFunction = 1 := by
  ext x
  simp

instance : NatCast (HolderSpace α X A) := ⟨fun n ↦ const (n : A)⟩

instance : IntCast (HolderSpace α X A) := ⟨fun n ↦ const (n : A)⟩

instance : Pow (HolderSpace α X A) ℕ := ⟨fun f n ↦ npowRec n f⟩

@[simp]
theorem natCast_apply (n : ℕ) (x : X) : (n : HolderSpace α X A) x = n := const_apply (n : A) x

@[simp]
theorem intCast_apply (n : ℤ) (x : X) : (n : HolderSpace α X A) x = n := const_apply (n : A) x

@[simp]
theorem pow_apply (f : HolderSpace α X A) (n : ℕ) (x : X) : (f ^ n) x = f x ^ n := by
  induction n with
  | zero =>
    have h : f ^ 0 = (1 : HolderSpace α X A) := rfl
    rw [h, one_apply, pow_zero]
  | succ n ih =>
    calc
      (f ^ (n + 1)) x = (f ^ n) x * f x := mul_apply (f ^ n) f x
      _ = f x ^ (n + 1) := by rw [ih, pow_succ]

instance : Ring (HolderSpace α X A) :=
  Function.Injective.ring toBoundedContinuousFunction toBoundedContinuousFunction_injective
    toBoundedContinuousFunction_zero toBoundedContinuousFunction_one
    toBoundedContinuousFunction_add toBoundedContinuousFunction_mul
    toBoundedContinuousFunction_neg toBoundedContinuousFunction_sub
    toBoundedContinuousFunction_nsmul toBoundedContinuousFunction_zsmul
    (fun f n ↦ by ext x; simp) (fun n ↦ by ext x; simp) (fun n ↦ by ext x; simp)

/-- Bounded Hölder functions inherit the normed-ring structure from their values. -/
instance : NormedRing (HolderSpace α X A) where
  __ := (inferInstance : Ring (HolderSpace α X A))
  __ := (inferInstance : NonUnitalNormedRing (HolderSpace α X A))

instance : Algebra ℝ (HolderSpace α X A) where
  algebraMap := RingHom.comp
    { toFun := const
      map_zero' := const_zero
      map_one' := rfl
      map_add' := const_add
      map_mul' := const_mul }
    (algebraMap ℝ A)
  commutes' c f := ext fun x ↦ by
    simpa using Algebra.commutes (R := ℝ) (A := A) c (f x)
  smul_def' c f := toBoundedContinuousFunction_injective (by
    ext x
    simp [Algebra.smul_def])

@[simp]
theorem algebraMap_apply (c : ℝ) (x : X) :
    algebraMap ℝ (HolderSpace α X A) c x = algebraMap ℝ A c := const_apply _ x

/-- With the inherited scalar action and Hölder norm, pointwise operations give a normed algebra. -/
instance : NormedAlgebra ℝ (HolderSpace α X A) where
  norm_smul_le c f := by simp [norm_smul]

instance [Nonempty X] [NormOneClass A] : NormOneClass (HolderSpace α X A) where
  norm_one := by
    have h : (1 : HolderSpace α X A) = const 1 := rfl
    rw [h, norm_const, norm_one]

/-- The continuous algebra homomorphism assigning a constant Hölder function to each value. -/
def constA : A →A[ℝ] HolderSpace α X A where
  toFun := const
  map_zero' := const_zero
  map_one' := rfl
  map_add' := const_add
  map_mul' := const_mul
  commutes' c := by ext x; simp
  cont := constL.continuous.congr constL_apply

@[simp]
theorem constA_apply (a : A) : constA (α := α) (X := X) a = const a := (rfl)

@[simp]
theorem toContinuousLinearMap_constA :
    (constA (α := α) (X := X) (A := A)).toContinuousLinearMap = constL := by
  ext a x
  simp

/-- The constant map has operator norm at most one. -/
theorem norm_constA_le_one :
    ‖(constA (α := α) (X := X) (A := A)).toContinuousLinearMap‖ ≤ 1 := by
  simpa only [toContinuousLinearMap_constA] using
    norm_constL_le_one (α := α) (X := X) (Y := A)

/-- On a nonempty domain with nontrivial values, the constant map has operator norm one. -/
theorem norm_constA [Nonempty X] [Nontrivial A] :
    ‖(constA (α := α) (X := X) (A := A)).toContinuousLinearMap‖ = 1 := by
  simp

/-- The continuous algebra homomorphism forgetting the Hölder seminorm. -/
def toBoundedContinuousFunctionA : HolderSpace α X A →A[ℝ] (X →ᵇ A) where
  toFun := toBoundedContinuousFunction
  map_zero' := toBoundedContinuousFunction_zero
  map_one' := toBoundedContinuousFunction_one
  map_add' := toBoundedContinuousFunction_add
  map_mul' := toBoundedContinuousFunction_mul
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]
  cont := toBoundedContinuousFunctionCLM.continuous.congr toBoundedContinuousFunctionCLM_apply

@[simp]
theorem toBoundedContinuousFunctionA_apply (f : HolderSpace α X A) :
    toBoundedContinuousFunctionA f = f.toBoundedContinuousFunction := (rfl)

@[simp]
theorem toContinuousLinearMap_toBoundedContinuousFunctionA :
    (toBoundedContinuousFunctionA (α := α) (X := X) (A := A)).toContinuousLinearMap =
      toBoundedContinuousFunctionCLM := by
  ext f x
  simp

/-- The inclusion into bounded continuous functions has operator norm at most one. -/
theorem norm_toBoundedContinuousFunctionA_le_one :
    ‖(toBoundedContinuousFunctionA (α := α) (X := X) (A := A)).toContinuousLinearMap‖ ≤ 1 := by
  simpa only [toContinuousLinearMap_toBoundedContinuousFunctionA] using
    norm_toBoundedContinuousFunctionCLM_le_one (α := α) (X := X) (Y := A)

/-- On a nonempty domain with nontrivial values, the inclusion has operator norm one. -/
theorem norm_toBoundedContinuousFunctionA [Nonempty X] [Nontrivial A] :
    ‖(toBoundedContinuousFunctionA (α := α) (X := X) (A := A)).toContinuousLinearMap‖ = 1 := by
  simp

/-- Evaluation at a point as a continuous algebra homomorphism. -/
def evalA (x : X) : HolderSpace α X A →A[ℝ] A where
  toFun f := f x
  map_zero' := zero_apply x
  map_one' := one_apply x
  map_add' f g := add_apply f g x
  map_mul' f g := mul_apply f g x
  commutes' c := algebraMap_apply c x
  cont := (evalCLM x).continuous.congr (evalCLM_apply x)

@[simp]
theorem evalA_apply (x : X) (f : HolderSpace α X A) : evalA x f = f x := (rfl)

@[simp]
theorem toContinuousLinearMap_evalA (x : X) :
    (evalA (α := α) (A := A) x).toContinuousLinearMap = evalCLM x := by
  ext f
  simp

/-- Evaluation has operator norm at most one. -/
theorem norm_evalA_le_one (x : X) :
    ‖(evalA (α := α) (A := A) x).toContinuousLinearMap‖ ≤ 1 := by
  simpa only [toContinuousLinearMap_evalA] using norm_evalCLM_le_one (α := α) (Y := A) x

/-- With nontrivial values, evaluation has operator norm one. -/
theorem norm_evalA [Nontrivial A] (x : X) :
    ‖(evalA (α := α) (A := A) x).toContinuousLinearMap‖ = 1 := by
  simp

@[simp]
theorem evalA_comp_constA (x : X) :
    (evalA (α := α) (A := A) x).comp constA = ContinuousAlgHom.id ℝ A := by
  ext a
  simp

end Unital

section Commutative

variable [NormedCommRing A] [NormedAlgebra ℝ A]

instance : NormedCommRing (HolderSpace α X A) where
  __ := (inferInstance : NormedRing (HolderSpace α X A))
  mul_comm f g := ext fun x ↦ by simp [mul_comm]

end Commutative

end TauCeti.HolderSpace
