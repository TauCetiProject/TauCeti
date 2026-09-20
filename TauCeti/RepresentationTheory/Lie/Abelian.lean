/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# A faithful square-zero representation of an abelian Lie algebra

For an abelian Lie algebra `L` over a commutative ring `R`, let `L` act on `R × L` by

`x • (a, y) = (0, a • x)`.

Every two operators in this representation have zero composite, while evaluation at `(1, 0)`
recovers the acting element. The representation is therefore faithful and square-zero.

Over a field, this gives an explicit faithful representation of an `n`-dimensional abelian Lie
algebra by square-zero endomorphisms of an `(n + 1)`-dimensional vector space. It is the basic
abelian model for faithful nilrepresentations.

## Main definition

* `TauCeti.abelianSquareZeroRepresentation`: the resulting faithful Lie representation.
-/

public section

universe u v

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

local instance : Module Rᵐᵒᵖ L :=
  Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)

local instance : IsCentralScalar R L := ⟨fun _ _ ↦ rfl⟩

private def abelianSquareZeroOperatorLinearMap : L →ₗ[R] Module.End R (R × L) :=
  (Algebra.lmul R (TrivSqZeroExt R L)).toLinearMap.comp (TrivSqZeroExt.inrHom R L)

private def abelianSquareZeroOperator (x : L) : Module.End R (R × L) :=
  abelianSquareZeroOperatorLinearMap R L x

@[simp, grind =]
private theorem abelianSquareZeroOperator_apply (x : L) (z : R × L) :
    abelianSquareZeroOperator R L x z = (0, z.1 • x) := by
  change @Mul.mul (TrivSqZeroExt R L) _ (TrivSqZeroExt.inr x) z = _
  ext
  · change 0 * z.1 = 0
    simp
  · change (0 : R) • z.2 + (MulOpposite.op z.1) • x = z.1 • x
    simp

@[simp]
private theorem abelianSquareZeroOperator_zero : abelianSquareZeroOperator R L 0 = 0 := by
  simp [abelianSquareZeroOperator]

@[simp]
private theorem abelianSquareZeroOperatorLinearMap_apply (x : L) :
    abelianSquareZeroOperatorLinearMap R L x = abelianSquareZeroOperator R L x :=
  (rfl)

private theorem abelianSquareZeroOperator_mul_eq_zero (x y : L) :
    abelianSquareZeroOperator R L x * abelianSquareZeroOperator R L y = 0 := by
  change Algebra.lmul R (TrivSqZeroExt R L) (TrivSqZeroExt.inr x) *
      Algebra.lmul R (TrivSqZeroExt R L) (TrivSqZeroExt.inr y) = 0
  rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]

/-- The canonical representation of an abelian Lie algebra by square-zero operators on `R × L`.
The first coordinate records the scalar that the acting element transfers to the second
coordinate. -/
def abelianSquareZeroRepresentation [IsLieAbelian L] :
    L →ₗ⁅R⁆ Module.End R (R × L) :=
  { abelianSquareZeroOperatorLinearMap R L with
    map_lie' := by
      intro x y
      simp [trivial_lie_zero, LieRing.of_associative_ring_bracket,
        abelianSquareZeroOperator_mul_eq_zero] }

private theorem abelianSquareZeroRepresentation_apply [IsLieAbelian L] (x : L) :
    abelianSquareZeroRepresentation R L x = abelianSquareZeroOperator R L x :=
  (rfl)

/-- The canonical representation acts by the square-zero operator construction. -/
@[simp]
theorem abelianSquareZeroRepresentation_apply_apply [IsLieAbelian L] (x : L) (z : R × L) :
    abelianSquareZeroRepresentation R L x z = (0, z.1 • x) := by
  rw [abelianSquareZeroRepresentation_apply, abelianSquareZeroOperator_apply]

/-- Any two operators in the canonical abelian representation have zero product. -/
@[simp]
theorem abelianSquareZeroRepresentation_mul_eq_zero [IsLieAbelian L] (x y : L) :
    abelianSquareZeroRepresentation R L x * abelianSquareZeroRepresentation R L y = 0 := by
  rw [abelianSquareZeroRepresentation_apply, abelianSquareZeroRepresentation_apply]
  exact abelianSquareZeroOperator_mul_eq_zero R L x y

/-- Every operator in the canonical abelian representation is square-zero. -/
@[simp]
theorem abelianSquareZeroRepresentation_sq_eq_zero [IsLieAbelian L] (x : L) :
    abelianSquareZeroRepresentation R L x ^ 2 = 0 := by
  simp [pow_two]

/-- Every operator in the canonical abelian representation is nilpotent, uniformly with exponent
two. -/
theorem isNilpotent_abelianSquareZeroRepresentation [IsLieAbelian L] (x : L) :
    IsNilpotent (abelianSquareZeroRepresentation R L x) :=
  ⟨2, abelianSquareZeroRepresentation_sq_eq_zero R L x⟩

/-- The canonical square-zero representation of an abelian Lie algebra is faithful. -/
theorem abelianSquareZeroRepresentation_injective [IsLieAbelian L] :
    Function.Injective (abelianSquareZeroRepresentation R L) := by
  intro x y hxy
  have h := LinearMap.congr_fun hxy (1, 0)
  simpa using congrArg Prod.snd h

/-- The carrier of the canonical square-zero representation has dimension one more than the
abelian Lie algebra. -/
theorem finrank_abelianSquareZeroRepresentation (K : Type u) [DivisionRing K]
    (A : Type v) [AddCommGroup A] [Module K A] [FiniteDimensional K A] :
    Module.finrank K (K × A) = Module.finrank K A + 1 := by
  simp [add_comm]

/-- Every finite-dimensional abelian Lie algebra has an explicit faithful finite-dimensional
representation whose operators have pairwise-zero products. -/
theorem exists_faithful_squareZeroRepresentation (K : Type u) [Field K]
    (A : Type v) [LieRing A] [LieAlgebra K A] [IsLieAbelian A] [FiniteDimensional K A] :
    ∃ (V : Type max u v) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (ρ : A →ₗ⁅K⁆ Module.End K V),
      Function.Injective ρ ∧ ∀ x y : A, ρ x * ρ y = 0 :=
  ⟨K × A, inferInstance, inferInstance, inferInstance,
    abelianSquareZeroRepresentation K A,
    abelianSquareZeroRepresentation_injective K A,
    abelianSquareZeroRepresentation_mul_eq_zero K A⟩

end TauCeti
