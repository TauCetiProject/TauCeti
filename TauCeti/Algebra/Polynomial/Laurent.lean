/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Evaluating a Laurent polynomial at a unit of a not necessarily commutative algebra

Mathlib's `LaurentPolynomial.eval₂` substitutes a unit of a *commutative* semiring into a Laurent
polynomial.  The Laurent coefficient ring of graded `K`-theory has to act on abelian groups, so it
has to be substituted into endomorphism rings, which are not commutative.  This file supplies that
evaluation.

For a unit `u` of an `R`-algebra `A`, `TauCeti.laurentEval u : R[T;T⁻¹] →ₐ[R] A` is the algebra map
sending `T` to `u` and `T⁻¹` to `u⁻¹`.  It is the algebra map attached by
`AddMonoidAlgebra.lift` to the monoid homomorphism `n ↦ uⁿ` out of `Multiplicative ℤ`, so it exists
for an arbitrary semiring `A` and is the unique algebra map with the prescribed value at `T`.
Consequently `TauCeti.laurentEvalEquiv` identifies the units of `A` with the `R`-algebra maps out of
`R[T;T⁻¹]`: the Laurent polynomial ring is the free `R`-algebra on one invertible generator.

The module-theoretic use is `TauCeti.laurentTAut`: on any `R[T;T⁻¹]`-module, multiplication by `T`
-- written `q` in the graded `K`-theory literature -- is an automorphism of the underlying additive
monoid, and that automorphism is what a shift-compatible invariant is compared against.

Evaluation also lets a module of the target algebra be read as an `R[T;T⁻¹]`-module, by
`TauCeti.laurentEvalModule`.  Over `ℤ` this is the coefficient module along which
`TauCeti.LaurentSpecialization` extends scalars: `ℤ ⊗[ℤ[q,q⁻¹]] M` is the specialization of a
`ℤ[q,q⁻¹]`-module `M` at `q = a`, and its universal property turns an additive map on `M` that
evaluates Laurent scalars into a map on the specialization.

## Main definitions

* `TauCeti.laurentEval`: evaluation of a Laurent polynomial at a unit of an `R`-algebra.
* `TauCeti.laurentEvalEquiv`: the units of `A` are the `R`-algebra maps `R[T;T⁻¹] →ₐ[R] A`.
* `TauCeti.laurentTAut`: multiplication by `T` on an `R[T;T⁻¹]`-module, as an additive
  automorphism.
* `TauCeti.laurentEvalModule`: the `R[T;T⁻¹]`-module structure induced on an `A`-module by
  evaluating the variable at a unit of `A`.
* `TauCeti.LaurentSpecialization`: extension of scalars of a `ℤ[q,q⁻¹]`-module along evaluation
  at an integer unit, together with `TauCeti.LaurentSpecialization.mk` and its universal property
  `TauCeti.LaurentSpecialization.desc`.

## Main results

* `TauCeti.laurentEval_unique`: an algebra map out of `R[T;T⁻¹]` is determined by its value at `T`.
* `TauCeti.laurentEval_eq_eval₂`: over a commutative target, this evaluation is Mathlib's
  `LaurentPolynomial.eval₂`.
* `TauCeti.laurentPolynomialC_smul`: a constant Laurent polynomial acts by integer scalar
  multiplication.
* `TauCeti.LaurentSpecialization.mk_smul`: Laurent scalars evaluate under specialization.
* `TauCeti.LaurentSpecialization.hom_ext_mk`: additive maps out of a specialization are determined
  on the canonical image.

## References

* `TauCetiRoadmap/GrothendieckEulerForms/README.md`, Layer 6, which fixes `ℤ[q,q⁻¹]`,
  represented by `LaurentPolynomial ℤ`, as the coefficient ring of the graded theory.
-/

public section

namespace TauCeti

open LaurentPolynomial

section Eval

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

/-- **Evaluation of a Laurent polynomial at a unit** `u` of an `R`-algebra `A`: the `R`-algebra
map `R[T;T⁻¹] →ₐ[R] A` sending `T` to `u`, hence `T⁻¹` to `u⁻¹`.

Unlike `LaurentPolynomial.eval₂` this does not ask `A` to be commutative, because the intended
targets are endomorphism rings.  The construction is the universal property of the group algebra
`R[ℤ]`: an integer power of a unit is a monoid homomorphism out of `Multiplicative ℤ`. -/
noncomputable def laurentEval (u : Aˣ) : R[T;T⁻¹] →ₐ[R] A :=
  AddMonoidAlgebra.lift R A ℤ ((Units.coeHom A).comp (zpowersHom Aˣ u))

@[simp]
lemma laurentEval_T (u : Aˣ) (n : ℤ) : laurentEval (R := R) u (T n) = ((u ^ n : Aˣ) : A) := by
  rw [laurentEval]
  simp only [LaurentPolynomial.T, AddMonoidAlgebra.lift_single, one_smul]
  rfl

@[simp]
lemma laurentEval_C (u : Aˣ) (r : R) : laurentEval u (C r) = algebraMap R A r := by
  rw [C_eq_algebraMap]
  exact (laurentEval u).commutes r

/-- The generator `T` evaluates to the chosen unit. -/
lemma laurentEval_T_one (u : Aˣ) : laurentEval (R := R) u (T 1) = (u : A) := by
  simp

/-- **An `R`-algebra map out of `R[T;T⁻¹]` is determined by its value at `T`.** -/
theorem laurentEval_unique (u : Aˣ) (f : R[T;T⁻¹] →ₐ[R] A) (hf : f (T 1) = (u : A)) :
    f = laurentEval u :=
  (AddMonoidAlgebra.lift R A ℤ).symm.injective <|
    MonoidHom.ext_mint <| by
      rw [AddMonoidAlgebra.lift_symm_apply, AddMonoidAlgebra.lift_symm_apply]
      exact hf.trans (laurentEval_T_one u).symm

/-- **The Laurent polynomial ring is the free `R`-algebra on one invertible generator**: its
`R`-algebra maps to `A` are exactly the units of `A`, through evaluation at `T`. -/
noncomputable def laurentEvalEquiv : Aˣ ≃ (R[T;T⁻¹] →ₐ[R] A) where
  toFun := laurentEval
  invFun f :=
    { val := f (T 1)
      inv := f (T (-1))
      val_inv := by rw [← map_mul, ← T_add]; simp
      inv_val := by rw [← map_mul, ← T_add]; simp }
  left_inv u := Units.ext <| by simp
  right_inv f := (laurentEval_unique _ f rfl).symm

@[simp]
lemma laurentEvalEquiv_apply (u : Aˣ) : laurentEvalEquiv (R := R) u = laurentEval u :=
  (rfl)

@[simp]
lemma laurentEvalEquiv_symm_apply (f : R[T;T⁻¹] →ₐ[R] A) :
    ((laurentEvalEquiv.symm f : Aˣ) : A) = f (T 1) :=
  (rfl)

/-- Evaluation at a unit is natural in the target algebra. -/
@[simp]
theorem comp_laurentEval {B : Type*} [Semiring B] [Algebra R B] (g : A →ₐ[R] B) (u : Aˣ) :
    g.comp (laurentEval u) = laurentEval (Units.map (g : A →* B) u) :=
  laurentEval_unique _ _ <| by simp

/-- **Over a commutative target this is Mathlib's `LaurentPolynomial.eval₂`.**  The two
constructions are separate only because `LaurentPolynomial.eval₂` is built by localization and so
needs a commutative codomain. -/
theorem laurentEval_eq_eval₂ {S : Type*} [CommSemiring S] [Algebra R S] (u : Sˣ)
    (p : R[T;T⁻¹]) : laurentEval u p = eval₂ (algebraMap R S) u p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | C_mul_T n a => simp

end Eval

section EvalModule

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

/-- **The module structure obtained by evaluating the variable at a unit**: an `A`-module is an
`R[T;T⁻¹]`-module once `T` is made to act through the unit `u`.

It is kept as a named class-valued definition because tensor products over the Laurent coefficient
ring must remember this particular module structure. -/
@[expose, instance_reducible]
noncomputable def laurentEvalModule (u : Aˣ) (N : Type*) [AddCommMonoid N] [Module A N] :
    Module R[T;T⁻¹] N :=
  Module.compHom N (laurentEval u).toRingHom

/-- **The computation rule of `TauCeti.laurentEvalModule`**: a Laurent scalar acts through its
value at the unit. -/
theorem laurentEvalModule_smul (u : Aˣ) {N : Type*} [AddCommMonoid N] [Module A N]
    (p : R[T;T⁻¹]) (x : N) :
    letI := laurentEvalModule (R := R) u N
    p • x = laurentEval u p • x :=
  (rfl)

end EvalModule

section TAut

variable (R : Type*) [Semiring R] (N : Type*) [AddCommMonoid N]
  [Module (LaurentPolynomial R) N]

/-- **Multiplication by the variable on an `R[T;T⁻¹]`-module**, as an automorphism of the
underlying additive monoid.  In the graded `K`-theory notation the variable is `q`, so this is the
operator `x ↦ q • x` against which a shift-compatible invariant is compared. -/
noncomputable def laurentTAut : AddAut N where
  toFun x := (T 1 : LaurentPolynomial R) • x
  invFun x := (T (-1) : LaurentPolynomial R) • x
  left_inv x := by
    simp only [smul_smul, ← T_add, neg_add_cancel, T_zero, one_smul]
  right_inv x := by
    simp only [smul_smul, ← T_add, add_neg_cancel, T_zero, one_smul]
  map_add' _ _ := smul_add _ _ _

@[simp]
lemma laurentTAut_apply (x : N) : laurentTAut R N x = (T 1 : LaurentPolynomial R) • x :=
  (rfl)

@[simp]
lemma laurentTAut_symm_apply (x : N) :
    (laurentTAut R N).symm x = (T (-1) : LaurentPolynomial R) • x :=
  (rfl)

end TAut

section Constants

variable {N : Type*} [AddCommGroup N] [Module (LaurentPolynomial ℤ) N]

/-- **A constant Laurent polynomial acts by the integer scalar multiplication** of the underlying
abelian group of a `ℤ[T;T⁻¹]`-module.

Not `@[simp]`: `LaurentPolynomial.C a` is not in simp-normal form, because `eq_intCast` rewrites
the ring homomorphism `C : ℤ →+* ℤ[T;T⁻¹]` to the integer cast; the normal form of the statement
is Mathlib's own `Int.cast_smul_eq_zsmul`. -/
lemma laurentPolynomialC_smul (a : ℤ) (x : N) :
    (C a : LaurentPolynomial ℤ) • x = a • x := by
  rw [C_eq_algebraMap, ← Int.cast_smul_eq_zsmul (LaurentPolynomial ℤ) a x]
  congr 1

end Constants

section Specialization

variable (M : Type*) [AddCommGroup M] [Module (LaurentPolynomial ℤ) M] (a : ℤˣ)

/-- **A `ℤ[q,q⁻¹]`-module specialized at the integer unit `a`.**  This is extension of scalars
from `ℤ[q,q⁻¹]` to `ℤ` along evaluation at `q = a`. -/
noncomputable abbrev LaurentSpecialization : Type _ :=
  @TensorProduct (LaurentPolynomial ℤ) inferInstance ℤ M inferInstance inferInstance
    (laurentEvalModule (R := ℤ) a ℤ) inferInstance

namespace LaurentSpecialization

noncomputable instance : AddCommGroup (LaurentSpecialization M a) := inferInstanceAs
  (AddCommGroup
    (@TensorProduct (LaurentPolynomial ℤ) inferInstance ℤ M inferInstance inferInstance
      (laurentEvalModule (R := ℤ) a ℤ) inferInstance))

/-- The canonical additive map from a `ℤ[q,q⁻¹]`-module to its specialization. -/
noncomputable def mk : M →+ LaurentSpecialization M a := by
  let _ : Module (LaurentPolynomial ℤ) ℤ := laurentEvalModule (R := ℤ) a ℤ
  exact (TensorProduct.mk (LaurentPolynomial ℤ) ℤ M 1).toAddMonoidHom

private theorem mk_apply (x : M) :
    mk M a x =
      @TensorProduct.tmul (LaurentPolynomial ℤ) inferInstance ℤ M inferInstance inferInstance
        (laurentEvalModule (R := ℤ) a ℤ) inferInstance 1 x :=
  (rfl)

/-- **Laurent scalars evaluate under specialization.** -/
@[simp]
theorem mk_smul (p : LaurentPolynomial ℤ) (x : M) :
    mk M a (p • x) = (laurentEval a p : ℤ) • mk M a x := by
  let _ : Module (LaurentPolynomial ℤ) ℤ := laurentEvalModule (R := ℤ) a ℤ
  have hsmul : ∀ n : ℤ, p • n = (laurentEval a p : ℤ) • n := fun n =>
    laurentEvalModule_smul (R := ℤ) a p n
  calc
    mk M a (p • x) = (p • (1 : ℤ)) ⊗ₜ[LaurentPolynomial ℤ] x :=
      TensorProduct.tmul_smul p 1 x
    _ = ((laurentEval a p : ℤ) • (1 : ℤ)) ⊗ₜ[LaurentPolynomial ℤ] x := by
      rw [hsmul]
    _ = (laurentEval a p : ℤ) •
        @TensorProduct.tmul (LaurentPolynomial ℤ) inferInstance ℤ M inferInstance inferInstance
          (laurentEvalModule (R := ℤ) a ℤ) inferInstance 1 x :=
      (TensorProduct.smul_tmul' _ _ _).symm
    _ = (laurentEval a p : ℤ) • mk M a x := by
      rw [mk_apply]

section UniversalProperty

variable {G : Type*} [AddCommGroup G]

/-- **The universal map out of a specialization.**  An additive map out of `M` factors through
evaluation at `a` when it sends Laurent scalar multiplication to multiplication by the evaluated
integer. -/
noncomputable def desc (f : M →+ G)
    (hf : ∀ (p : LaurentPolynomial ℤ) (x : M), f (p • x) = (laurentEval a p : ℤ) • f x) :
    LaurentSpecialization M a →+ G := by
  let _ : Module (LaurentPolynomial ℤ) ℤ := laurentEvalModule (R := ℤ) a ℤ
  refine TensorProduct.liftAddHom ((smulAddHom ℤ (M →+ G)).flip f) ?_
  intro p n x
  have hsmul : ∀ m : ℤ, p • m = (laurentEval a p : ℤ) • m := fun m =>
    laurentEvalModule_smul (R := ℤ) a p m
  simp only [AddMonoidHom.flip_apply, smulAddHom_apply, AddMonoidHom.smul_apply]
  rw [hf, hsmul]
  simp [mul_smul, Int.mul_comm]

/-- **`desc` restricts to `f` on the canonical image**: the universal map out of the
specialization agrees with `f` on every class of the form `mk M a x`. -/
@[simp]
theorem desc_mk (f : M →+ G)
    (hf : ∀ (p : LaurentPolynomial ℤ) (x : M), f (p • x) = (laurentEval a p : ℤ) • f x) (x : M) :
    desc M a f hf (mk M a x) = f x := by
  let _ : Module (LaurentPolynomial ℤ) ℤ := laurentEvalModule (R := ℤ) a ℤ
  rw [desc, mk_apply, TensorProduct.liftAddHom_tmul]
  simp

/-- **Additive maps out of a specialization are determined by their values on the canonical
image.** -/
theorem hom_ext_mk {f g : LaurentSpecialization M a →+ G}
    (h : ∀ x : M, f (mk M a x) = g (mk M a x)) : f = g := by
  let _ : Module (LaurentPolynomial ℤ) ℤ := laurentEvalModule (R := ℤ) a ℤ
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul n x =>
      have hn : n ⊗ₜ[LaurentPolynomial ℤ] x =
          n • (1 ⊗ₜ[LaurentPolynomial ℤ] x) := by
        calc
          n ⊗ₜ[LaurentPolynomial ℤ] x = (n • (1 : ℤ)) ⊗ₜ[LaurentPolynomial ℤ] x := by
            simp
          _ = n • (1 ⊗ₜ[LaurentPolynomial ℤ] x) :=
            (TensorProduct.smul_tmul' _ _ _).symm
      rw [hn, map_zsmul, map_zsmul]
      exact congrArg (n • ·) (h x)
  | add x y hx hy => simp [hx, hy]

end UniversalProperty

end LaurentSpecialization

end Specialization

end TauCeti
