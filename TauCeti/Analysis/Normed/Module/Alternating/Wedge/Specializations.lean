/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Wedge
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Scalar and algebra-valued wedge products

The ordinary wedge of real-valued forms and the wedge of forms valued in a normed real algebra
are the multiplication specializations of the paired wedge. They use its determinant
normalization: the wedge of two one-forms evaluates as a two-term determinant. The scalar
product is graded commutative, while the algebra-valued product is graded commutative when
the algebra is commutative.

The convention follows John M. Lee, *Introduction to Smooth Manifolds*, second edition,
Chapter 14. The underlying paired construction is `ContinuousAlternatingMap.pairedWedge`.
-/

public section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {k l m : ℕ}

namespace ContinuousAlternatingMap

/-- The real-valued wedge product, normalized so that the wedge of two covectors is their
two-term determinant. -/
noncomputable def wedge (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : E [⋀^Fin l]→L[ℝ] ℝ) :
    E [⋀^Fin (k + l)]→L[ℝ] ℝ :=
  pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ φ ψ

/-- The real wedge is the paired wedge for multiplication. -/
theorem wedge_def (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : E [⋀^Fin l]→L[ℝ] ℝ) :
    wedge φ ψ =
      pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ φ ψ :=
  wedge.eq_def φ ψ

/-- The wedge of two real one-forms evaluates as a determinant. -/
@[simp]
theorem wedge_apply_one_one (φ ψ : E [⋀^Fin 1]→L[ℝ] ℝ) (v w : E) :
    wedge φ ψ ![v, w] = φ ![v] * ψ ![w] - φ ![w] * ψ ![v] := by
  simpa only [wedge, ContinuousLinearMap.mul_apply'] using
    (pairedWedge_apply_one_one (ContinuousLinearMap.mul ℝ ℝ).continuous₂ φ ψ v w)

/-- The real wedge is additive in its first argument. -/
@[simp]
theorem wedge_add_left (φ φ' : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : E [⋀^Fin l]→L[ℝ] ℝ) :
    wedge (φ + φ') ψ = wedge φ ψ + wedge φ' ψ :=
  pairedWedge_add_left _ _ _ _ _

/-- The real wedge is additive in its second argument. -/
@[simp]
theorem wedge_add_right (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ ψ' : E [⋀^Fin l]→L[ℝ] ℝ) :
    wedge φ (ψ + ψ') = wedge φ ψ + wedge φ ψ' :=
  pairedWedge_add_right _ _ _ _ _

/-- The real wedge respects scalar multiplication in its first argument. -/
@[simp]
theorem wedge_smul_left (c : ℝ) (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : E [⋀^Fin l]→L[ℝ] ℝ) : wedge (c • φ) ψ = c • wedge φ ψ :=
  pairedWedge_smul_left _ _ _ _ _

/-- The real wedge respects scalar multiplication in its second argument. -/
@[simp]
theorem wedge_smul_right (c : ℝ) (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : E [⋀^Fin l]→L[ℝ] ℝ) : wedge φ (c • ψ) = c • wedge φ ψ :=
  pairedWedge_smul_right _ _ _ _ _

/-- The real wedge obeys the binomial operator-norm bound. -/
theorem norm_wedge_le (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : E [⋀^Fin l]→L[ℝ] ℝ) :
    ‖wedge φ ψ‖ ≤ (k + l).choose k * ‖φ‖ * ‖ψ‖ := by
  simpa only [wedge, ContinuousLinearMap.opNorm_mul, mul_one] using
    norm_pairedWedge_le (ContinuousLinearMap.mul ℝ ℝ) φ ψ

/-- Pulling both real forms back along a continuous linear map commutes with wedge. -/
@[simp]
theorem wedge_compContinuousLinearMap {E' : Type*} [SeminormedAddCommGroup E']
    [NormedSpace ℝ E'] (f : E' →L[ℝ] E) (φ : E [⋀^Fin k]→L[ℝ] ℝ)
    (ψ : E [⋀^Fin l]→L[ℝ] ℝ) :
    wedge (φ.compContinuousLinearMap f) (ψ.compContinuousLinearMap f) =
      (wedge φ ψ).compContinuousLinearMap f :=
  (pairedWedge_compContinuousLinearMap _ _ _ _ _).symm

/-- The real wedge is graded commutative. -/
theorem wedge_comm (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : E [⋀^Fin l]→L[ℝ] ℝ)
    (v : Fin (k + l) → E) :
    wedge φ ψ v = (-1 : ℝ) ^ (k * l) •
      wedge ψ φ (v ∘ Fin.cast (Nat.add_comm l k)) := by
  exact pairedWedge_comm (fun a b : ℝ => mul_comm a b) φ ψ v

/-- The real wedge is associative, up to the canonical reassociation of its degree. -/
theorem wedge_assoc (φ : E [⋀^Fin k]→L[ℝ] ℝ) (ψ : E [⋀^Fin l]→L[ℝ] ℝ)
    (χ : E [⋀^Fin m]→L[ℝ] ℝ) (v : Fin (k + l + m) → E) :
    wedge (wedge φ ψ) χ v =
      wedge φ (wedge ψ χ) (v ∘ Fin.cast (Nat.add_assoc k l m).symm) := by
  exact pairedWedge_assoc _ _ _ _ (fun a b c : ℝ => mul_assoc a b c) φ ψ χ v

/-- The wedge of forms valued in a normed real algebra, using multiplication in the algebra. -/
noncomputable def wedgeMul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (φ : E [⋀^Fin k]→L[ℝ] A) (ψ : E [⋀^Fin l]→L[ℝ] A) :
    E [⋀^Fin (k + l)]→L[ℝ] A :=
  pairedWedge (ContinuousLinearMap.mul ℝ A) (ContinuousLinearMap.mul ℝ A).continuous₂ φ ψ

/-- The algebra-valued wedge is the paired wedge for multiplication. -/
theorem wedgeMul_def {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (φ : E [⋀^Fin k]→L[ℝ] A) (ψ : E [⋀^Fin l]→L[ℝ] A) :
    wedgeMul φ ψ =
      pairedWedge (ContinuousLinearMap.mul ℝ A) (ContinuousLinearMap.mul ℝ A).continuous₂ φ ψ :=
  wedgeMul.eq_def φ ψ

/-- The algebra-valued wedge of two one-forms is the antisymmetrized product. -/
@[simp]
theorem wedgeMul_apply_one_one {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (φ ψ : E [⋀^Fin 1]→L[ℝ] A) (v w : E) :
    wedgeMul φ ψ ![v, w] = φ ![v] * ψ ![w] - φ ![w] * ψ ![v] := by
  simpa only [wedgeMul, ContinuousLinearMap.mul_apply'] using
    (pairedWedge_apply_one_one (ContinuousLinearMap.mul ℝ A).continuous₂ φ ψ v w)

/-- The algebra-valued wedge is additive in its first argument. -/
@[simp]
theorem wedgeMul_add_left {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (φ φ' : E [⋀^Fin k]→L[ℝ] A) (ψ : E [⋀^Fin l]→L[ℝ] A) :
    wedgeMul (φ + φ') ψ = wedgeMul φ ψ + wedgeMul φ' ψ :=
  pairedWedge_add_left _ _ _ _ _

/-- The algebra-valued wedge is additive in its second argument. -/
@[simp]
theorem wedgeMul_add_right {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (φ : E [⋀^Fin k]→L[ℝ] A) (ψ ψ' : E [⋀^Fin l]→L[ℝ] A) :
    wedgeMul φ (ψ + ψ') = wedgeMul φ ψ + wedgeMul φ ψ' :=
  pairedWedge_add_right _ _ _ _ _

/-- The algebra-valued wedge respects real scalar multiplication in its first argument. -/
@[simp]
theorem wedgeMul_smul_left {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] (c : ℝ)
    (φ : E [⋀^Fin k]→L[ℝ] A) (ψ : E [⋀^Fin l]→L[ℝ] A) :
    wedgeMul (c • φ) ψ = c • wedgeMul φ ψ :=
  pairedWedge_smul_left _ _ _ _ _

/-- The algebra-valued wedge respects real scalar multiplication in its second argument. -/
@[simp]
theorem wedgeMul_smul_right {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] (c : ℝ)
    (φ : E [⋀^Fin k]→L[ℝ] A) (ψ : E [⋀^Fin l]→L[ℝ] A) :
    wedgeMul φ (c • ψ) = c • wedgeMul φ ψ :=
  pairedWedge_smul_right _ _ _ _ _

/-- The algebra-valued wedge obeys the binomial operator-norm bound. -/
theorem norm_wedgeMul_le {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (φ : E [⋀^Fin k]→L[ℝ] A) (ψ : E [⋀^Fin l]→L[ℝ] A) :
    ‖wedgeMul φ ψ‖ ≤ (k + l).choose k * ‖φ‖ * ‖ψ‖ := by
  calc
    ‖wedgeMul φ ψ‖ ≤ (k + l).choose k * ‖ContinuousLinearMap.mul ℝ A‖ * ‖φ‖ * ‖ψ‖ :=
      norm_pairedWedge_le (ContinuousLinearMap.mul ℝ A) φ ψ
    _ ≤ (k + l).choose k * ‖φ‖ * ‖ψ‖ := by
      gcongr
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_mul_le ℝ A)
          (show 0 ≤ ((k + l).choose k : ℝ) by positivity)

/-- Pulling both algebra-valued forms back along a continuous linear map commutes with wedge. -/
@[simp]
theorem wedgeMul_compContinuousLinearMap {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {E' : Type*} [SeminormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : E' →L[ℝ] E) (φ : E [⋀^Fin k]→L[ℝ] A) (ψ : E [⋀^Fin l]→L[ℝ] A) :
    wedgeMul (φ.compContinuousLinearMap f) (ψ.compContinuousLinearMap f) =
      (wedgeMul φ ψ).compContinuousLinearMap f :=
  (pairedWedge_compContinuousLinearMap _ _ _ _ _).symm

/-- The algebra-valued wedge is associative, up to reassociation of its degree. -/
theorem wedgeMul_assoc {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (φ : E [⋀^Fin k]→L[ℝ] A) (ψ : E [⋀^Fin l]→L[ℝ] A)
    (χ : E [⋀^Fin m]→L[ℝ] A) (v : Fin (k + l + m) → E) :
    wedgeMul (wedgeMul φ ψ) χ v =
      wedgeMul φ (wedgeMul ψ χ) (v ∘ Fin.cast (Nat.add_assoc k l m).symm) := by
  exact pairedWedge_assoc _ _ _ _ (fun a b c : A => mul_assoc a b c) φ ψ χ v

/-- For a commutative normed algebra, the algebra-valued wedge is graded commutative. -/
theorem wedgeMul_comm {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A]
    (φ : E [⋀^Fin k]→L[ℝ] A) (ψ : E [⋀^Fin l]→L[ℝ] A)
    (v : Fin (k + l) → E) :
    wedgeMul φ ψ v = (-1 : ℝ) ^ (k * l) •
      wedgeMul ψ φ (v ∘ Fin.cast (Nat.add_comm l k)) := by
  exact pairedWedge_comm (fun a b : A => mul_comm a b) φ ψ v

end ContinuousAlternatingMap
