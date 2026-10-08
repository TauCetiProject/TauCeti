/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Heisenberg
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Cofinite
public import TauCeti.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# A faithful truncated enveloping representation of the Heisenberg algebra

For the three-dimensional Heisenberg Lie algebra `𝔥`, the quotient
`U(𝔥) / (U⁺(𝔥))³` is a finite module over the coefficient ring. Left multiplication by the
canonical Lie generators gives a faithful representation, and every operator has cube zero.
In particular the action detects the central generator `z = [x,y]`, which the adjoint action
kills: `ι z` belongs to the square of the augmentation ideal but not to its cube.

The defining strictly upper triangular matrices certify that the quotient retains `𝔥`:
any product of three such matrices is zero, so their enveloping map factors through the
quotient. No assumption on characteristic is needed. Module-finiteness uses
`TauCeti.UniversalEnvelopingAlgebra.moduleFinite_quotient_pow_of_isIntegral`, with the standard
Heisenberg basis and the zero images of its generators in `U(𝔥) / U⁺(𝔥)`.

## References

* N. Jacobson, *Lie Algebras*, Chapter V, the truncated enveloping construction of faithful
  representations of nilpotent Lie algebras.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§1.2 and 17.
-/

public section

namespace TauCeti

open scoped Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

local notation "U" => _root_.UniversalEnvelopingAlgebra R (heisenberg R)
local notation "I" => (HopfIdeal.toIdeal (HopfIdeal.augmentation R U))

/-- The truncated enveloping algebra of the Heisenberg algebra, killing products of three
augmented elements while retaining the central bracket. -/
noncomputable abbrev heisenbergAugmentationQuotient := U ⧸ I ^ 3

/-- The defining matrix representation kills the cube of the augmentation ideal. -/
theorem heisenberg_augmentation_cube_le_ker_lift_incl :
    I ^ 3 ≤ RingHom.ker (_root_.UniversalEnvelopingAlgebra.lift R (heisenberg R).incl) := by
  rw [UniversalEnvelopingAlgebra.augmentation_toIdeal_pow_eq_span_range_ι_pow, Ideal.span_le]
  intro u hu
  rw [pow_succ, pow_two, Set.mem_mul] at hu
  obtain ⟨v, hv, w, ⟨c, rfl⟩, rfl⟩ := hu
  obtain ⟨s, ⟨a, rfl⟩, t, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp hv
  simp only [SetLike.mem_coe, RingHom.mem_ker, map_mul]
  simp only [_root_.UniversalEnvelopingAlgebra.lift_ι_apply]
  exact mul_mul_heisenberg_eq_zero R a b c

/-- The canonical Heisenberg generators remain injective modulo the cube of the augmentation
ideal. This includes the central direction. -/
theorem heisenberg_quotient_ι_injective :
    Function.Injective (fun x : heisenberg R ↦
      Ideal.Quotient.mk (I ^ 3) (_root_.UniversalEnvelopingAlgebra.ι R x)) := by
  intro x y h
  have hmem := Ideal.Quotient.eq.mp h
  have hzero := heisenberg_augmentation_cube_le_ker_lift_incl R hmem
  rw [RingHom.mem_ker, map_sub] at hzero
  simp only [_root_.UniversalEnvelopingAlgebra.lift_ι_apply] at hzero
  exact Subtype.ext (sub_eq_zero.mp hzero)

/-- The truncated enveloping algebra is module-finite, over any commutative coefficient ring. -/
instance instModuleFiniteHeisenbergAugmentationQuotient :
    Module.Finite R (heisenbergAugmentationQuotient R) := by
  apply UniversalEnvelopingAlgebra.moduleFinite_quotient_pow_of_isIntegral R (heisenberg R)
    (heisenbergBasis R) (heisenbergBasis R).span_eq I _ 3
  intro i
  have hz : Ideal.Quotient.mk I (_root_.UniversalEnvelopingAlgebra.ι R
      (heisenbergBasis R i)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (UniversalEnvelopingAlgebra.ι_mem_augmentation R (heisenberg R) _)
  rw [hz]
  exact isIntegral_zero

/-- Left multiplication on the augmentation-cube quotient of the Heisenberg enveloping
algebra. It is faithful and every acting operator has cube zero. -/
noncomputable def heisenbergTruncatedRepresentation :
    heisenberg R →ₗ⁅R⁆ Module.End R (heisenbergAugmentationQuotient R) :=
  LieHom.leftRegularRep
    (((Ideal.Quotient.mkₐ R (I ^ 3)).toLieHom).comp
      (_root_.UniversalEnvelopingAlgebra.ι R))

/-- The action is left multiplication by the image of the canonical generator. -/
@[simp]
theorem heisenbergTruncatedRepresentation_apply (x : heisenberg R)
    (u : heisenbergAugmentationQuotient R) :
    heisenbergTruncatedRepresentation R x u =
      Ideal.Quotient.mk (I ^ 3) (_root_.UniversalEnvelopingAlgebra.ι R x) * u := by
  simp [heisenbergTruncatedRepresentation]

/-- The action on a representative multiplies by the canonical generator before taking its
quotient class. -/
theorem heisenbergTruncatedRepresentation_apply_mk (x : heisenberg R) (u : U) :
    heisenbergTruncatedRepresentation R x (Ideal.Quotient.mk (I ^ 3) u) =
      Ideal.Quotient.mk (I ^ 3) (_root_.UniversalEnvelopingAlgebra.ι R x * u) := by
  rw [heisenbergTruncatedRepresentation_apply, ← map_mul]

/-- The truncated enveloping action is faithful, including on the centre. -/
theorem heisenbergTruncatedRepresentation_injective :
    Function.Injective (heisenbergTruncatedRepresentation R) :=
  (LieHom.leftRegularRep_injective_iff _).mpr (heisenberg_quotient_ι_injective R)

/-- Every operator in the truncated enveloping action has cube zero. -/
@[simp]
theorem heisenbergTruncatedRepresentation_cube (x : heisenberg R) :
    heisenbergTruncatedRepresentation R x ^ 3 = 0 := by
  rw [heisenbergTruncatedRepresentation, LieHom.leftRegularRep_eq_mulLeft,
    LinearMap.pow_mulLeft, LinearMap.mulLeft_eq_zero_iff]
  simp only [LieHom.comp_apply, AlgHom.coe_toLieHom, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow
    (UniversalEnvelopingAlgebra.ι_mem_augmentation R (heisenberg R) x) 3)

/-- The central generator acts by a square-zero operator: its enveloping image already lies
in the square of the augmentation ideal. -/
@[simp]
theorem heisenbergTruncatedRepresentation_heisenbergZ_sq :
    heisenbergTruncatedRepresentation R (heisenbergZ R) ^ 2 = 0 := by
  rw [heisenbergTruncatedRepresentation, LieHom.leftRegularRep_eq_mulLeft,
    LinearMap.pow_mulLeft, LinearMap.mulLeft_eq_zero_iff]
  simp only [LieHom.comp_apply, AlgHom.coe_toLieHom, ← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [pow_two, Submodule.pow_succ]
  exact Ideal.mul_mem_mul (ι_heisenbergZ_mem_augmentation_toIdeal_sq R)
    (UniversalEnvelopingAlgebra.ι_mem_augmentation R (heisenberg R) _)

/-- The central generator survives the truncated enveloping action over a nontrivial ring. -/
theorem heisenbergTruncatedRepresentation_heisenbergZ_ne_zero [Nontrivial R] :
    heisenbergTruncatedRepresentation R (heisenbergZ R) ≠ 0 := by
  intro h
  apply heisenbergZ_ne_zero (R := R)
  exact heisenbergTruncatedRepresentation_injective R (h.trans (map_zero _).symm)

/-- The central generator does not lie in the cube of the augmentation ideal, although
`ι_heisenbergZ_mem_augmentation_toIdeal_sq` puts it in the square. -/
theorem ι_heisenbergZ_not_mem_augmentation_toIdeal_cube [Nontrivial R] :
    _root_.UniversalEnvelopingAlgebra.ι R (heisenbergZ R) ∉ I ^ 3 := by
  intro h
  have heq := Ideal.Quotient.eq_zero_iff_mem.mpr h
  exact heisenbergZ_ne_zero (R := R)
    (heisenberg_quotient_ι_injective R (heq.trans (by simp)))

end TauCeti
