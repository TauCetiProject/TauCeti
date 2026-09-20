/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import TauCeti.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Finiteness.Prod

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

/-- The right scalar action on `L` induced by commutativity of `R`. -/
private local instance moduleMulOpposite : Module Rᵐᵒᵖ L :=
  Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)

private local instance isCentralScalar : IsCentralScalar R L := ⟨fun _ _ ↦ rfl⟩

private def abelianSquareZeroLieHom [IsLieAbelian L] :
    LieHom R L (TrivSqZeroExt R L) :=
  { TrivSqZeroExt.inrHom R L with
    map_lie' := by
      intro x y
      simp [trivial_lie_zero, LieRing.of_associative_ring_bracket] }

@[simp]
private theorem abelianSquareZeroLieHom_apply [IsLieAbelian L] (x : L) :
    abelianSquareZeroLieHom R L x = TrivSqZeroExt.inr x :=
  (rfl)

private theorem abelianSquareZeroLeftRegular_apply_apply [IsLieAbelian L] (x : L)
    (z : TrivSqZeroExt R L) :
    LieHom.leftRegularRep (abelianSquareZeroLieHom R L) x z =
      TrivSqZeroExt.inr (z.fst • x) := by
  rw [LieHom.leftRegularRep_apply, abelianSquareZeroLieHom_apply]
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp

private theorem abelianSquareZeroLeftRegular_mul_eq_zero [IsLieAbelian L] (x y : L) :
    LieHom.leftRegularRep (abelianSquareZeroLieHom R L) x *
      LieHom.leftRegularRep (abelianSquareZeroLieHom R L) y = 0 := by
  refine LinearMap.ext fun z ↦ ?_
  rw [Module.End.mul_apply, abelianSquareZeroLeftRegular_apply_apply,
    abelianSquareZeroLeftRegular_apply_apply]
  simp

/-- The canonical representation of an abelian Lie algebra by square-zero operators on `R × L`.
The first coordinate records the scalar that the acting element transfers to the second
coordinate. -/
def abelianSquareZeroRepresentation [IsLieAbelian L] :
    L →ₗ⁅R⁆ Module.End R (R × L) :=
  LieHom.leftRegularRep (abelianSquareZeroLieHom R L)

/-- The canonical representation acts by the square-zero operator construction. -/
@[simp, grind =]
theorem abelianSquareZeroRepresentation_apply_apply [IsLieAbelian L] (x : L) (z : R × L) :
    abelianSquareZeroRepresentation R L x z = (0, z.1 • x) :=
  abelianSquareZeroLeftRegular_apply_apply R L x z

/-- Any two operators in the canonical abelian representation have zero product. -/
@[simp]
theorem abelianSquareZeroRepresentation_mul_eq_zero [IsLieAbelian L] (x y : L) :
    abelianSquareZeroRepresentation R L x * abelianSquareZeroRepresentation R L y = 0 :=
  abelianSquareZeroLeftRegular_mul_eq_zero R L x y

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

/-- The canonical square-zero representation of an abelian Lie algebra is injective (faithful). -/
theorem abelianSquareZeroRepresentation_injective [IsLieAbelian L] :
    Function.Injective (abelianSquareZeroRepresentation R L) :=
  (LieHom.leftRegularRep_injective_iff (abelianSquareZeroLieHom R L)).2 fun _ _ h ↦
    TrivSqZeroExt.inr_injective (R := R) (by simpa using h)

/-- Every finite-dimensional abelian Lie algebra `A` has an explicit faithful representation
whose operators have pairwise-zero products, on a carrier of dimension `finrank K A + 1`. -/
theorem exists_faithful_squareZeroRepresentation (K : Type u) [Field K]
    (A : Type v) [LieRing A] [LieAlgebra K A] [IsLieAbelian A] [FiniteDimensional K A] :
    ∃ (V : Type max u v) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (ρ : A →ₗ⁅K⁆ Module.End K V),
      Function.Injective ρ ∧ (∀ x y : A, ρ x * ρ y = 0) ∧
        Module.finrank K V = Module.finrank K A + 1 :=
  ⟨K × A, inferInstance, inferInstance, inferInstance,
    abelianSquareZeroRepresentation K A,
    abelianSquareZeroRepresentation_injective K A,
    abelianSquareZeroRepresentation_mul_eq_zero K A,
    by rw [Module.finrank_prod, Module.finrank_self, add_comm]⟩

end TauCeti
