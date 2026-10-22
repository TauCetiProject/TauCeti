/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Exponential
public import TauCeti.RingTheory.Derivation.Flow
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Roots

/-!
# One-parameter subgroups from locally nilpotent invariant vector fields

A tangent vector whose invariant derivation is locally nilpotent integrates to a
polynomial family of points. Its coordinate map is the counit applied coefficientwise
to the Taylor expansion of the invariant derivation. The coefficient of degree one is
the original tangent vector.

Over a rational integral domain this family satisfies the additive parameter law in
every commutative value algebra, including nonreduced algebras. Thus it defines an
algebraic one-parameter subgroup, rather than just a homomorphism on field-valued points.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 14.
* G. Freudenburg, *Algebraic Theory of Locally Nilpotent Derivations*, Chapter 1.

The construction uses `TauCeti.Bialgebra.expPoint` and
`Derivation.taylorExpPolynomial`.
-/

public section

open Polynomial LinearMap TensorProduct
open scoped TensorProduct

namespace TauCeti.Bialgebra

variable {R H : Type*} [CommRing R] [Algebra ℚ R] [CommRing H]
  [_root_.Bialgebra R H] [Algebra ℚ H]
variable (d : Derivation R H (CounitAlgebra R H R))
  (hd : ∀ h, ∃ n, (leftInvariantDerivation d)^[n] h = 0)

/-- The polynomial-valued exponential point associated to a locally nilpotent invariant
vector field. -/
noncomputable def expPointPolynomial : H →ₐ[R] R[X] :=
  (Polynomial.mapAlgHom (_root_.Bialgebra.counitAlgHom R H)).comp
    ((leftInvariantDerivation d).taylorExpPolynomial hd)

omit [Algebra ℚ R] in
/-- The coefficients of the exponential curve are the counits of the divided iterates
of its invariant derivation. -/
theorem coeff_expPointPolynomial (h : H) (n : ℕ) :
    (expPointPolynomial d hd h).coeff n =
      Coalgebra.counit (R := R)
        ((n.factorial : ℚ)⁻¹ • (leftInvariantDerivation d)^[n] h) := by
  simp [expPointPolynomial, Polynomial.coeff_map]

omit [Algebra ℚ R] in
/-- The velocity of the exponential curve at zero is its specified tangent vector. -/
@[simp]
theorem coeff_one_expPointPolynomial (h : H) :
    (expPointPolynomial d hd h).coeff 1 = CounitAlgebra.algEquivSelf R H R (d h) := by
  simpa only [coeff_expPointPolynomial, Nat.factorial_one, Nat.cast_one, inv_one,
    one_smul, Function.iterate_one] using counit_leftInvariantDerivation d h

/-- Evaluate the exponential curve in any commutative value algebra. -/
noncomputable def expPointAt {B : Type*} [CommRing B] [Algebra R B] (t : B) :
    WithConv (H →ₐ[R] B) :=
  WithConv.toConv ((aeval t).comp (expPointPolynomial d hd))

omit [Algebra ℚ R] in
/-- Evaluation of the polynomial-valued point gives the exponential curve. -/
@[simp]
theorem expPointAt_apply {B : Type*} [CommRing B] [Algebra R B] (t : B) (h : H) :
    expPointAt d hd t h = aeval t (expPointPolynomial d hd h) := (rfl)

omit [Algebra ℚ R] in
/-- The exponential curve is natural under homomorphisms of value algebras. -/
theorem mapValue_expPointAt {B C : Type*} [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (f : B →ₐ[R] C) (t : B) :
    AlgHom.mapValue f (expPointAt d hd t) = expPointAt d hd (f t) := by
  apply WithConv.ext
  ext h
  simp only [AlgHom.mapValue_apply, expPointAt, WithConv.ofConv_toConv,
    AlgHom.comp_apply]
  exact (AlgHom.congr_fun (Polynomial.aeval_algHom f t) (expPointPolynomial d hd h)).symm

omit [Algebra ℚ R] in
/-- Over the base ring the exponential curve is the counit of the polynomial flow. -/
theorem expPointAt_apply_self (t : R) (h : H) :
    expPointAt d hd t h =
      Coalgebra.counit (R := R) ((leftInvariantDerivation d).taylorExpAt hd t h) := by
  simp only [expPointAt_apply, expPointPolynomial, AlgHom.comp_apply,
    Polynomial.coe_mapAlgHom, Polynomial.aeval_def, Polynomial.eval₂_map,
    Derivation.taylorExpAt_apply, Algebra.algebraMap_self, RingHom.id_comp,
    Polynomial.eval₂_id]
  have he : (_root_.Bialgebra.counitAlgHom R H) (algebraMap R H t) = t := by simp
  have hv := Polynomial.eval₂_at_apply (_root_.Bialgebra.counitAlgHom R H).toRingHom
    (p := (leftInvariantDerivation d).taylorExpPolynomial hd h) (algebraMap R H t)
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, he,
    _root_.Bialgebra.counitAlgHom_apply] using hv

omit [Algebra ℚ R] in
/-- The exponential curve starts at the identity in every value algebra. -/
@[simp]
theorem expPointAt_zero {B : Type*} [CommRing B] [Algebra R B] :
    expPointAt d hd (0 : B) = 1 := by
  apply WithConv.ext
  ext h
  simp [expPointAt_apply, ← Polynomial.coeff_zero_eq_aeval_zero',
    coeff_expPointPolynomial]

omit [Algebra ℚ R] in
/-- At parameter one, the curve recovers the invariant-vector-field exponential. -/
theorem expPointAt_one : expPointAt d hd (1 : R) = WithConv.toConv (expPoint d hd) := by
  apply WithConv.ext
  ext h
  rw [expPointAt_apply_self, expPoint_apply, Derivation.taylorExpAt_one]

omit [Algebra ℚ R] in
/-- The polynomial flow of an invariant vector field is translation by its
exponential curve. -/
theorem taylorExpAt_leftInvariantDerivation_apply (t : R) (h : H) :
    (leftInvariantDerivation d).taylorExpAt hd t h =
      tensorComponent (expPointAt d hd t).ofConv.toLinearMap (Coalgebra.comul (R := R) h) := by
  have hsmul : leftInvariantDerivation (t • d) = t • leftInvariantDerivation d :=
    (leftInvariantDerivation (R := R) (H := H)).toLinearMap.map_smul t d
  have ht : ∀ h, ∃ n, (leftInvariantDerivation (t • d))^[n] h = 0 := by
    simpa only [hsmul] using
      (leftInvariantDerivation d).exists_iterate_smul_eq_zero hd t
  have he : expPointAt d hd t = WithConv.toConv (expPoint (t • d) ht) := by
    apply WithConv.ext
    ext x
    rw [expPointAt_apply_self, expPoint_apply]
    simp only [hsmul]
    rw [Derivation.taylorExpAt_eq_taylorExp_smul]
  rw [he, Derivation.taylorExpAt_eq_taylorExp_smul]
  simpa only [hsmul] using taylorExp_leftInvariantDerivation_apply (t • d) ht h

private theorem expPointAt_add_self (r s : R) :
    expPointAt d hd (r + s) = expPointAt d hd r * expPointAt d hd s := by
  apply WithConv.ext
  ext h
  rw [expPointAt_apply_self, Derivation.taylorExpAt_add, AlgHom.comp_apply,
    ← expPointAt_apply_self, taylorExpAt_leftInvariantDerivation_apply, AlgHom.convMul_apply]
  induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.TensorProduct.lift_tmul, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Substitute the sum of two independent parameters in the exponential curve. -/
private noncomputable def expPointAddPolynomial : H →ₐ[R] R[X][X] :=
  (aeval (C X + X : R[X][X])).comp (expPointPolynomial d hd)

/-- Multiply the exponential points at two independent parameters. -/
private noncomputable def expPointMulPolynomial : H →ₐ[R] R[X][X] :=
  (Algebra.TensorProduct.lift
    (Polynomial.CAlgHom.comp (expPointPolynomial d hd))
    ((Polynomial.mapAlgHom (Algebra.ofId R R[X])).comp (expPointPolynomial d hd))
    (fun _ _ => Commute.all ..)).comp (_root_.Bialgebra.comulAlgHom R H)

omit [Algebra ℚ R] in
private theorem eval_expPointAddPolynomial {B : Type*} [CommRing B] [Algebra R B]
    (r s : B) (h : H) :
    aevalAeval r s (expPointAddPolynomial d hd h) = expPointAt d hd (r + s) h := by
  have he : (aevalAeval r s).comp (aeval (C X + X : R[X][X])) = aeval (r + s) := by
    ext
    simp
  exact AlgHom.congr_fun
    (congrArg (fun f => f.comp (expPointPolynomial d hd)) he) h

omit [Algebra ℚ R] in
private theorem eval_expPointMulPolynomial {B : Type*} [CommRing B] [Algebra R B]
    (r s : B) (h : H) :
    aevalAeval r s (expPointMulPolynomial d hd h) =
      (expPointAt d hd r * expPointAt d hd s) h := by
  have he : (aevalAeval r s).comp
      (Polynomial.mapAlgHom (Algebra.ofId R R[X])) = aeval s := by
    ext
    simp
  simp only [expPointMulPolynomial, AlgHom.comp_apply, _root_.Bialgebra.comulAlgHom_apply,
    AlgHom.convMul_apply]
  induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.comp_apply,
      Polynomial.CAlgHom_apply, aevalAeval_C, expPointAt_apply]
    exact congrArg (fun z => aeval r (expPointPolynomial d hd x) * z)
      (AlgHom.congr_fun he (expPointPolynomial d hd y))
  | add x y hx hy => simp only [map_add, hx, hy]

section ParameterLaw

variable [IsDomain R]

/-- The exponential curve respects addition in every commutative value algebra. -/
theorem expPointAt_add {B : Type*} [CommRing B] [Algebra R B] (r s : B) :
    expPointAt d hd (r + s) = expPointAt d hd r * expPointAt d hd s := by
  let : Infinite R := Infinite.of_injective (algebraMap ℚ R) (algebraMap ℚ R).injective
  -- Detect the bivariate polynomial identity on base-ring points, then evaluate it
  -- in the arbitrary value algebra. In particular, nilpotent parameters are retained.
  have hpq (h : H) : expPointAddPolynomial d hd h = expPointMulPolynomial d hd h := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Polynomial.C_injective (R := R))).mono
    rintro _ ⟨b, rfl⟩
    apply Polynomial.funext
    intro a
    have he := congrArg (fun f : WithConv (H →ₐ[R] R) => f h)
      (expPointAt_add_self d hd a b)
    have hev := (eval_expPointAddPolynomial d hd a b h).trans
      (he.trans (eval_expPointMulPolynomial d hd a b h).symm)
    simpa only [Polynomial.coe_aevalAeval_eq_evalEval] using hev
  apply WithConv.ext
  ext h
  rw [← eval_expPointAddPolynomial, hpq, eval_expPointMulPolynomial]

/-- The exponential curve as a one-parameter homomorphism on any value algebra. -/
noncomputable def expPointHom (B : Type*) [CommRing B] [Algebra R B] :
    Multiplicative B →* WithConv (H →ₐ[R] B) where
  toFun t := expPointAt d hd t.toAdd
  map_one' := expPointAt_zero d hd
  map_mul' t u := expPointAt_add d hd t.toAdd u.toAdd

/-- The one-parameter homomorphism evaluates the polynomial exponential curve. -/
@[simp]
theorem expPointHom_apply {B : Type*} [CommRing B] [Algebra R B] (t : Multiplicative B) :
    expPointHom d hd B t = expPointAt d hd t.toAdd := (rfl)

end ParameterLaw

end TauCeti.Bialgebra
