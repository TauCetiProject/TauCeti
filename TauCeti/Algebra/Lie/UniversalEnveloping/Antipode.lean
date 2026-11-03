/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.Ring.Subring.MulOpposite
public import Mathlib.RingTheory.Binomial
public import TauCeti.Algebra.Module.Rat
public import TauCeti.Algebra.Polynomial.Smeval
public import TauCeti.RingTheory.DividedPowers.Associative

/-!
# The antipode of a universal enveloping algebra

The universal enveloping algebra of a Lie algebra has a canonical algebra homomorphism to its
opposite algebra, determined by sending every Lie generator `x` to `-x`. After identifying the
underlying modules of an algebra and its opposite, this is the usual antipode. It fixes scalars,
reverses products, and is an involution.

The opposite-algebra formulation records antimultiplicativity in the type. It also makes the
construction available before a coalgebra structure has been chosen: only Mathlib's universal
property of the enveloping algebra is used here.

## Main definitions

* `UniversalEnvelopingAlgebra.antipodeOp`: the algebra homomorphism from an enveloping
  algebra to its opposite.
* `UniversalEnvelopingAlgebra.antipode`: the same map as a linear endomorphism.
* `UniversalEnvelopingAlgebra.antipodeComap`: the preimage of a subring under the
  antipode, again a subring.
* `UniversalEnvelopingAlgebra.antipodeEquiv`: the resulting algebra equivalence with the
  opposite algebra.

## Main results

* `UniversalEnvelopingAlgebra.antipode_ι`: the antipode negates each canonical Lie
  generator.
* `UniversalEnvelopingAlgebra.antipode_mul_antidistrib`: the antipode reverses
  multiplication.
* `UniversalEnvelopingAlgebra.antipode_antipode`: the antipode is involutive.
* `UniversalEnvelopingAlgebra.antipode_dividedPower` and
  `UniversalEnvelopingAlgebra.antipode_ringChoose`: over `ℚ`, the antipode passes through a
  divided power and through a generalized binomial coefficient.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

universe u v

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) [CommRing R]
variable {L : Type v} [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The canonical Lie homomorphism from `L` to the opposite of its universal enveloping algebra,
sending `x` to the opposite of `-ι R x`.

The minus sign compensates for the fact that the commutator bracket changes sign in the opposite
algebra. -/
private noncomputable def opNegι :
    L →ₗ⁅R⁆ (_root_.UniversalEnvelopingAlgebra R L)ᵐᵒᵖ where
  toLinearMap :=
    { toFun := fun x => MulOpposite.op (-_root_.UniversalEnvelopingAlgebra.ι R x)
      map_add' := fun x y => by simp [add_comm]
      map_smul' := fun r x => by simp }
  map_lie' := by
    intro x y
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, LieRing.of_associative_ring_bracket,
      MulOpposite.unop_sub, MulOpposite.unop_mul]
    rw [LieHom.map_lie]
    simp only [LieRing.of_associative_ring_bracket, neg_sub, neg_mul_neg]

end TauCeti.UniversalEnvelopingAlgebra

namespace UniversalEnvelopingAlgebra

variable (R : Type u) [CommRing R]
variable {L : Type v} [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The canonical algebra homomorphism from a universal enveloping algebra to its opposite.

It is uniquely determined by sending `ι R x` to `op (-ι R x)`. Viewing the codomain as the
opposite algebra makes the usual antimultiplicativity of the antipode ordinary multiplicativity. -/
noncomputable def antipodeOp :
    UniversalEnvelopingAlgebra R L →ₐ[R]
      (UniversalEnvelopingAlgebra R L)ᵐᵒᵖ :=
  UniversalEnvelopingAlgebra.lift R (TauCeti.UniversalEnvelopingAlgebra.opNegι R)

/-- The opposite-valued antipode negates every canonical Lie generator. -/
theorem antipodeOp_ι (x : L) :
    antipodeOp R (UniversalEnvelopingAlgebra.ι R x) =
      MulOpposite.op (-UniversalEnvelopingAlgebra.ι R x) := by
  rw [antipodeOp, UniversalEnvelopingAlgebra.lift_ι_apply]
  simp [TauCeti.UniversalEnvelopingAlgebra.opNegι]

/-- The `simp`-normal form of `antipodeOp_ι`, stated for the canonical generators as `simp`
writes them. -/
@[simp]
theorem antipodeOp_mkAlgHom_ι (x : L) :
    antipodeOp R
        (UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      MulOpposite.op
        (-UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) := by
  simpa using antipodeOp_ι R x

/-- An algebra homomorphism to the opposite enveloping algebra is the antipode exactly when it
negates every canonical Lie generator. -/
theorem antipodeOp_unique
    (f : UniversalEnvelopingAlgebra R L →ₐ[R]
      (UniversalEnvelopingAlgebra R L)ᵐᵒᵖ) :
    (∀ x, f (UniversalEnvelopingAlgebra.ι R x) =
      MulOpposite.op (-UniversalEnvelopingAlgebra.ι R x)) ↔ f = antipodeOp R := by
  rw [antipodeOp]
  refine Iff.trans ?_ (UniversalEnvelopingAlgebra.lift_unique R
      (TauCeti.UniversalEnvelopingAlgebra.opNegι R) f)
  constructor
  · intro h
    funext x
    simpa [TauCeti.UniversalEnvelopingAlgebra.opNegι] using h x
  · intro h x
    simpa [TauCeti.UniversalEnvelopingAlgebra.opNegι] using congrFun h x

/-- The antipode of a universal enveloping algebra, as a linear endomorphism of its underlying
module. -/
noncomputable def antipode :
    UniversalEnvelopingAlgebra R L →ₗ[R]
      UniversalEnvelopingAlgebra R L :=
  (MulOpposite.opLinearEquiv R).symm.toLinearMap.comp (antipodeOp R).toLinearMap

/-- The linear antipode is the unopposite of the opposite-valued algebra homomorphism. -/
theorem antipode_apply (a : UniversalEnvelopingAlgebra R L) :
    antipode R a = (antipodeOp R a).unop := (rfl)

/-- The antipode negates every canonical Lie generator. -/
theorem antipode_ι (x : L) :
    antipode R (UniversalEnvelopingAlgebra.ι R x) =
      -UniversalEnvelopingAlgebra.ι R x := by
  rw [antipode_apply, antipodeOp_ι]
  exact MulOpposite.unop_op _

/-- The `simp`-normal form of `antipode_ι`, stated for the canonical generators as `simp` writes
them. -/
@[simp]
theorem antipode_mkAlgHom_ι (x : L) :
    antipode R
        (UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x)) =
      -UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R x) := by
  simpa using antipode_ι R x

/-- The antipode fixes the multiplicative identity. -/
@[simp]
theorem antipode_one :
    antipode R (1 : UniversalEnvelopingAlgebra R L) = 1 := by
  rw [antipode_apply, map_one, MulOpposite.unop_one]

/-- The antipode fixes the image of every scalar. -/
@[simp]
theorem antipode_algebraMap (r : R) :
    antipode R (algebraMap R (UniversalEnvelopingAlgebra R L) r) =
      algebraMap R (UniversalEnvelopingAlgebra R L) r := by
  rw [antipode_apply, (antipodeOp R).commutes, MulOpposite.algebraMap_apply,
    MulOpposite.unop_op]

/-- The antipode reverses multiplication. -/
@[simp]
theorem antipode_mul_antidistrib (a b : UniversalEnvelopingAlgebra R L) :
    antipode R (a * b) = antipode R b * antipode R a := by
  rw [antipode_apply, map_mul, MulOpposite.unop_mul, antipode_apply, antipode_apply]

/-- The antipode commutes with powers of one element. -/
@[simp]
theorem antipode_pow (a : UniversalEnvelopingAlgebra R L) (n : ℕ) :
    antipode R (a ^ n) = antipode R a ^ n := by
  rw [antipode_apply, map_pow, MulOpposite.unop_pow, antipode_apply]

/-- Applying the opposite-valued antipode and then its opposite transform is the identity. -/
private theorem opComm_antipodeOp_comp_antipodeOp :
    (AlgHom.opComm (antipodeOp R)).comp (antipodeOp R) =
      AlgHom.id R (UniversalEnvelopingAlgebra R L) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  simp only [AlgHom.coe_toLieHom, LieHom.comp_apply, AlgHom.comp_apply, antipodeOp_ι,
    AlgHom.id_apply, AlgHom.opComm_apply_apply, MulOpposite.unop_op]
  rw [map_neg, antipodeOp_ι]
  simp

/-- The opposite transform of the opposite-valued antipode is also a right inverse. -/
private theorem antipodeOp_comp_opComm_antipodeOp :
    (antipodeOp R).comp (AlgHom.opComm (antipodeOp R)) =
      AlgHom.id R ((UniversalEnvelopingAlgebra R L)ᵐᵒᵖ) := by
  apply AlgHom.ext
  intro a
  induction a using MulOpposite.rec' with
  | _ a =>
      simp only [AlgHom.comp_apply, AlgHom.opComm_apply_apply, MulOpposite.unop_op,
        AlgHom.id_apply]
      exact congrArg MulOpposite.op
        (AlgHom.congr_fun (opComm_antipodeOp_comp_antipodeOp R) a)

/-- A universal enveloping algebra is canonically equivalent to its opposite algebra by negating
the Lie generators. -/
noncomputable def antipodeEquiv :
    UniversalEnvelopingAlgebra R L ≃ₐ[R]
      (UniversalEnvelopingAlgebra R L)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (antipodeOp R) (AlgHom.opComm (antipodeOp R))
    (antipodeOp_comp_opComm_antipodeOp R) (opComm_antipodeOp_comp_antipodeOp R)

/-- The algebra homomorphism underlying `antipodeEquiv` is `antipodeOp`. -/
@[simp]
theorem antipodeEquiv_toAlgHom :
    (antipodeEquiv (L := L) R).toAlgHom = antipodeOp (L := L) R := by
  rw [antipodeEquiv, AlgEquiv.toAlgHom_ofAlgHom]

/-- The opposite-algebra equivalence agrees with `antipodeOp` on every element. -/
@[simp]
theorem antipodeEquiv_apply (a : UniversalEnvelopingAlgebra R L) :
    antipodeEquiv (L := L) R a = antipodeOp R a := by
  rw [← AlgEquiv.toAlgHom_apply, antipodeEquiv_toAlgHom]

/-- The opposite-algebra equivalence negates every canonical Lie generator. -/
theorem antipodeEquiv_ι (x : L) :
    antipodeEquiv (L := L) R (UniversalEnvelopingAlgebra.ι R x) =
      MulOpposite.op (-UniversalEnvelopingAlgebra.ι R x) := by
  rw [antipodeEquiv_apply, antipodeOp_ι]

/-- The inverse of `antipodeEquiv` is the opposite transform of `antipodeOp`. -/
@[simp]
theorem antipodeEquiv_symm_toAlgHom :
    (antipodeEquiv (L := L) R).symm.toAlgHom = AlgHom.opComm (antipodeOp R) := by
  rw [antipodeEquiv, AlgEquiv.ofAlgHom_symm, AlgEquiv.toAlgHom_ofAlgHom]

/-- The inverse opposite-algebra equivalence acts by the same underlying antipode. -/
@[simp]
theorem antipodeEquiv_symm_apply
    (a : (UniversalEnvelopingAlgebra R L)ᵐᵒᵖ) :
    (antipodeEquiv (L := L) R).symm a = antipode R a.unop := by
  rw [← AlgEquiv.toAlgHom_apply, antipodeEquiv_symm_toAlgHom, antipode_apply,
    AlgHom.opComm_apply_apply]

/-- The antipode is involutive. -/
@[simp]
theorem antipode_antipode (a : UniversalEnvelopingAlgebra R L) :
    antipode R (antipode R a) = a := by
  rw [antipode_apply, antipode_apply]
  exact AlgHom.congr_fun (opComm_antipodeOp_comp_antipodeOp R) a

/-- The preimage of a subring under the antipode.

Antimultiplicativity is no obstruction: it is the preimage of the opposite subring `Subring.op S`
under the genuine ring homomorphism `antipodeOp`. -/
noncomputable def antipodeComap (S : Subring (UniversalEnvelopingAlgebra R L)) :
    Subring (UniversalEnvelopingAlgebra R L) :=
  (Subring.op S).comap (antipodeOp R).toRingHom

@[simp]
theorem mem_antipodeComap {S : Subring (UniversalEnvelopingAlgebra R L)}
    {a : UniversalEnvelopingAlgebra R L} :
    a ∈ antipodeComap R S ↔ antipode R a ∈ S := Iff.rfl

/-- The antipode is bijective. -/
theorem antipode_bijective : Function.Bijective (antipode (L := L) R) :=
  Function.Involutive.bijective (fun a => antipode_antipode R a)

section DividedPowers

variable {L : Type v} [LieRing L] [LieAlgebra ℚ L]

attribute [local instance] TauCeti.moduleNNRat

variable (a : UniversalEnvelopingAlgebra ℚ L)

/-- The antipode passes through a divided power. Antimultiplicativity is invisible here because a
divided power is a rational multiple of a power of a single element. -/
@[simp]
theorem antipode_dividedPower (n : ℕ) :
    antipode ℚ (TauCeti.Associative.dividedPower n a) =
      TauCeti.Associative.dividedPower n (antipode ℚ a) := by
  rw [antipode_apply, TauCeti.Associative.map_dividedPower, antipode_apply]
  simp [TauCeti.Associative.dividedPower_def]

/-- The antipode passes through a generalized binomial coefficient. -/
@[simp]
theorem antipode_ringChoose (n : ℕ) :
    antipode ℚ (Ring.choose a n) = Ring.choose (antipode ℚ a) n := by
  rw [antipode_apply, Ring.map_choose, antipode_apply]
  have hfac : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  refine smul_right_injective _ hfac ?_
  simp only [Nat.cast_smul_eq_nsmul]
  rw [← MulOpposite.unop_smul, ← Ring.descPochhammer_eq_factorial_smul_choose,
    ← Ring.descPochhammer_eq_factorial_smul_choose]
  exact Polynomial.unop_smeval _ _

end DividedPowers

end UniversalEnvelopingAlgebra
