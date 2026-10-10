/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Abelian
public import TauCeti.Algebra.Lie.UniversalEnveloping.Augmentation.Basic
import Mathlib.RingTheory.Finiteness.Prod

/-!
# The first augmentation quotient of an abelian enveloping algebra

For an abelian Lie algebra `L` over a commutative ring `R`, the quotient of `U(L)` by the
square of its augmentation ideal is canonically the trivial square-zero extension `R ⊕ L`.
The comparison sends scalars to the first summand and Lie generators to the second.
In particular this quotient retains every Lie generator, without freeness or characteristic
assumptions. Its left-multiplication action is the faithful square-zero action on `R × L`.

The construction uses the existing identification of an abelian enveloping algebra with its
symmetric algebra, and Mathlib's `TrivSqZeroExt.liftEquivOfComm` for the inverse map.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §17.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, §E.2,
  for faithful nilpotent representations from augmentation quotients.
-/

public section

open scoped Pointwise

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]
  [IsLieAbelian L] [Module Rᵐᵒᵖ L] [IsCentralScalar R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "I" => HopfIdeal.toIdeal (HopfIdeal.augmentation R U)
local notation "Q" => U ⧸ I ^ 2

attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def toSquareZero : U →ₐ[R] TrivSqZeroExt R L :=
  (SymmetricAlgebra.lift (TrivSqZeroExt.inrHom R L)).comp
    (symmetricAlgebraEquiv R L).symm.toAlgHom

private theorem toSquareZero_ι (x : L) :
    toSquareZero R L (_root_.UniversalEnvelopingAlgebra.ι R x) = TrivSqZeroExt.inr x := by
  simp [toSquareZero]

private theorem augmentation_sq_le_ker_toSquareZero : I ^ 2 ≤ RingHom.ker (toSquareZero R L) := by
  rw [augmentation_toIdeal_pow_eq_span_range_ι_pow, pow_two, Ideal.span_le]
  rintro _ ⟨a, ⟨x, rfl⟩, b, ⟨y, rfl⟩, rfl⟩
  apply RingHom.mem_ker.mpr
  rw [map_mul, toSquareZero_ι, toSquareZero_ι, TrivSqZeroExt.inr_mul_inr]

private noncomputable def quotientToSquareZero : Q →ₐ[R] TrivSqZeroExt R L :=
  Ideal.Quotient.liftₐ (I ^ 2) (toSquareZero R L)
    (fun _ hz ↦ augmentation_sq_le_ker_toSquareZero R L hz)

private theorem quotientToSquareZero_mk (z : U) :
    quotientToSquareZero R L (Ideal.Quotient.mk (I ^ 2) z) = toSquareZero R L z := by
  exact Ideal.Quotient.lift_mk _ _ _

private noncomputable def squareZeroToQuotient : TrivSqZeroExt R L →ₐ[R] Q :=
  TrivSqZeroExt.liftEquivOfComm
    ⟨(Ideal.Quotient.mkₐ R (I ^ 2)).toLinearMap.comp
      (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap, quotient_ι_mul_ι R L⟩

private theorem squareZeroToQuotient_inr (x : L) :
    squareZeroToQuotient R L (TrivSqZeroExt.inr x) =
      Ideal.Quotient.mk (I ^ 2) (_root_.UniversalEnvelopingAlgebra.ι R x) := by
  simp [squareZeroToQuotient, TrivSqZeroExt.liftEquivOfComm_apply]

private theorem squareZeroToQuotient_inl (r : R) :
    squareZeroToQuotient R L (TrivSqZeroExt.inl r) = algebraMap R Q r := by
  exact (squareZeroToQuotient R L).commutes r

private theorem squareZeroToQuotient_comp_quotientToSquareZero :
    (squareZeroToQuotient R L).comp (quotientToSquareZero R L) = AlgHom.id R Q := by
  apply Ideal.Quotient.algHom_ext R
  apply _root_.UniversalEnvelopingAlgebra.hom_ext R
  ext x
  simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
    Ideal.Quotient.mkₐ_eq_mk, quotientToSquareZero_mk, toSquareZero_ι,
    squareZeroToQuotient_inr, AlgHom.id_apply]

private theorem quotientToSquareZero_comp_squareZeroToQuotient :
    (quotientToSquareZero R L).comp (squareZeroToQuotient R L) =
      AlgHom.id R (TrivSqZeroExt R L) := by
  apply AlgHom.ext
  intro z
  rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z]
  simp only [AlgHom.comp_apply, AlgHom.id_apply, map_add, squareZeroToQuotient_inl,
    squareZeroToQuotient_inr, quotientToSquareZero_mk, toSquareZero_ι, AlgHom.commutes,
    TrivSqZeroExt.algebraMap_eq_inl]

/-- For an abelian Lie algebra, the quotient of its enveloping algebra by the augmentation
square is the trivial square-zero extension of the coefficient ring by the Lie algebra. -/
noncomputable def augmentationSqEquiv : Q ≃ₐ[R] TrivSqZeroExt R L :=
  AlgEquiv.ofAlgHom (quotientToSquareZero R L) (squareZeroToQuotient R L)
    (quotientToSquareZero_comp_squareZeroToQuotient R L)
    (squareZeroToQuotient_comp_quotientToSquareZero R L)

/-- The comparison sends a canonical Lie generator to the square-zero summand. -/
theorem augmentationSqEquiv_mk_ι (x : L) :
    augmentationSqEquiv R L (Ideal.Quotient.mk (I ^ 2)
      (_root_.UniversalEnvelopingAlgebra.ι R x)) = TrivSqZeroExt.inr x := by
  simp only [augmentationSqEquiv, AlgEquiv.ofAlgHom_apply, quotientToSquareZero_mk,
    toSquareZero_ι]

/-- The generator computation in the normal form used by `simp`. -/
@[simp]
theorem augmentationSqEquiv_mk_ι' (x : L) :
    augmentationSqEquiv R L (Ideal.Quotient.mk (I ^ 2)
      (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x))) =
        TrivSqZeroExt.inr x := by
  simpa using augmentationSqEquiv_mk_ι R L x

/-- The inverse comparison reads the two coordinates as a scalar plus a Lie generator. -/
theorem augmentationSqEquiv_symm_apply (z : TrivSqZeroExt R L) :
    (augmentationSqEquiv R L).symm z =
      algebraMap R Q z.fst +
        Ideal.Quotient.mk (I ^ 2) (_root_.UniversalEnvelopingAlgebra.ι R z.snd) := by
  have h := congrArg (squareZeroToQuotient R L)
    (TrivSqZeroExt.inl_fst_add_inr_snd_eq z).symm
  simpa only [augmentationSqEquiv, AlgEquiv.ofAlgHom_symm_apply, map_add,
    squareZeroToQuotient_inl, squareZeroToQuotient_inr] using h

/-- The inverse comparison sends the square-zero summand to the canonical Lie generator. -/
@[simp]
theorem augmentationSqEquiv_symm_inr (x : L) :
    (augmentationSqEquiv R L).symm (TrivSqZeroExt.inr x) =
      Ideal.Quotient.mk (I ^ 2) (_root_.UniversalEnvelopingAlgebra.ι R x) := by
  rw [augmentationSqEquiv_symm_apply]
  simp

omit [Module Rᵐᵒᵖ L] [IsCentralScalar R L] in
/-- The augmentation-square quotient loses no element of an abelian Lie algebra. -/
theorem quotient_ι_injective_of_isLieAbelian :
    Function.Injective fun x : L ↦
      Ideal.Quotient.mk (I ^ 2) (_root_.UniversalEnvelopingAlgebra.ι R x) := by
  let : Module Rᵐᵒᵖ L := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  let : IsCentralScalar R L := ⟨fun _ _ ↦ rfl⟩
  intro x y h
  have he := congrArg (augmentationSqEquiv R L) h
  rw [augmentationSqEquiv_mk_ι, augmentationSqEquiv_mk_ι] at he
  exact TrivSqZeroExt.inr_injective (R := R) he

/-- Under the comparison, multiplication by a Lie generator transfers the scalar coordinate
to the Lie-algebra coordinate and annihilates that second coordinate. -/
theorem augmentationSqEquiv_mk_ι_mul (x : L) (z : Q) :
    augmentationSqEquiv R L
      (Ideal.Quotient.mk (I ^ 2) (_root_.UniversalEnvelopingAlgebra.ι R x) * z) =
        TrivSqZeroExt.inr ((augmentationSqEquiv R L z).fst • x) := by
  rw [map_mul, augmentationSqEquiv_mk_ι]
  apply TrivSqZeroExt.ext <;> simp

omit [Module Rᵐᵒᵖ L] [IsCentralScalar R L] in
/-- The augmentation-square quotient of an abelian Lie algebra is finite as a module whenever
the Lie algebra is, over any commutative coefficient ring. -/
instance instModuleFiniteQuotientAugmentationSq [Module.Finite R L] : Module.Finite R Q := by
  let : Module Rᵐᵒᵖ L := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  let : IsCentralScalar R L := ⟨fun _ _ ↦ rfl⟩
  -- `TrivSqZeroExt R L` has the additive and scalar structures of the product `R × L`.
  have : Module.Finite R (TrivSqZeroExt R L) :=
    inferInstanceAs (Module.Finite R (R × L))
  exact Module.Finite.equiv (augmentationSqEquiv R L).symm.toLinearEquiv

variable (K : Type u) [Field K] (A : Type v) [LieRing A] [LieAlgebra K A]
  [IsLieAbelian A] [FiniteDimensional K A]

/-- The first augmentation quotient of an `n`-dimensional abelian Lie algebra has dimension
`n + 1`: its coordinates are one scalar and one Lie-algebra element. -/
theorem finrank_quotient_augmentation_sq :
    Module.finrank K (_root_.UniversalEnvelopingAlgebra K A ⧸
      (HopfIdeal.augmentation K (_root_.UniversalEnvelopingAlgebra K A)).toIdeal ^ 2) =
        Module.finrank K A + 1 := by
  let : Module Kᵐᵒᵖ A := Module.compHom _ ((RingHom.id K).fromOpposite mul_comm)
  let : IsCentralScalar K A := ⟨fun _ _ ↦ rfl⟩
  rw [(augmentationSqEquiv K A).toLinearEquiv.finrank_eq]
  -- The square-zero extension uses the product's module structure, so its dimension is
  -- Mathlib's product dimension formula.
  exact (Module.finrank_prod (R := K) (M := K) (M' := A)).trans
    (by rw [Module.finrank_self, add_comm])

end TauCeti.UniversalEnvelopingAlgebra
