/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Dimension.Constructions
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

The construction is the left-regular representation (`LieHom.leftRegularRep`) of the inclusion
of `L` into the trivial square-zero extension `TrivSqZeroExt R L`.

## Main definition

* `TauCeti.abelianSquareZeroRepresentation`: the resulting faithful Lie representation.

## Main result

* `TauCeti.exists_faithful_squareZeroRepresentation`: a faithful square-zero representation
  on a vector space of dimension `Module.finrank K L + 1`.
-/

public section

universe u v

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The right scalar action on `L` induced by commutativity of `R`. -/
private local instance moduleMulOpposite {R : Type u} [CommSemiring R]
    {L : Type v} [AddCommMonoid L] [Module R L] : Module Rᵐᵒᵖ L :=
  Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)

private local instance isCentralScalar {R : Type u} [CommSemiring R]
    {L : Type v} [AddCommMonoid L] [Module R L] : IsCentralScalar R L := ⟨fun _ _ ↦ rfl⟩

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

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

/-- The canonical representation of an abelian Lie algebra by square-zero operators on `R × L`.
The first coordinate records the scalar that the acting element transfers to the second
coordinate. -/
def abelianSquareZeroRepresentation [IsLieAbelian L] :
    L →ₗ⁅R⁆ Module.End R (R × L) :=
  -- Mathlib exposes `TrivSqZeroExt R L` as `R × L`, with the same additive and scalar
  -- structures. This lets the left-regular construction act directly on the product.
  LieHom.leftRegularRep (abelianSquareZeroLieHom R L)

/-- The acting element sends the first coordinate, as a scalar multiple of itself, to the
second coordinate and kills the second coordinate. -/
@[simp, grind =]
theorem abelianSquareZeroRepresentation_apply_apply [IsLieAbelian L] (x : L) (z : R × L) :
    abelianSquareZeroRepresentation R L x z = (0, z.1 • x) := by
  -- Keep the intermediate equality on the square-zero extension so rewriting does not cross
  -- the definitional identification of its bundled maps with maps on the product.
  have h (z : TrivSqZeroExt R L) :
      LieHom.leftRegularRep (abelianSquareZeroLieHom R L) x z =
      TrivSqZeroExt.inr (z.fst • x) := by
    rw [LieHom.leftRegularRep_apply, abelianSquareZeroLieHom_apply]
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  exact h z

/-- Any two operators in the canonical abelian representation have zero product. -/
@[simp]
theorem abelianSquareZeroRepresentation_mul_eq_zero [IsLieAbelian L] (x y : L) :
    abelianSquareZeroRepresentation R L x * abelianSquareZeroRepresentation R L y = 0 := by
  apply LinearMap.ext
  intro z
  simp [Module.End.mul_apply]

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
