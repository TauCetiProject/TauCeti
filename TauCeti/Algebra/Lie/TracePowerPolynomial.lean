/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.LinearAlgebra.SymmetricAlgebra.LieModule
import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
import TauCeti.RingTheory.Derivation.Matrix

/-!
# Trace-power polynomials of a Lie module

Let `L` be a Lie algebra over a commutative ring `R` and `M` a Lie module which is free of finite
rank over `R`. The symmetric algebra `S(L*)` of the dual of `L` is the algebra of polynomial
functions on `L`: a point `x : L` evaluates `p : S(L*)` through
`SymmetricAlgebra.lift (Module.Dual.eval R L x)`. For each natural number `m`, the function
`x ↦ tr (ρ_M(x) ^ m)` is such a polynomial function, the **trace-power polynomial**
`TauCeti.tracePowerPolynomial R L M m`, homogeneous of degree `m`.

It is built from the **generic action matrix** of a basis `c` of `M`
(`TauCeti.genericActionMatrix`): the matrix over `S(L*)` whose `(p, q)` entry is the linear
function `x ↦ (matrix of ρ_M(x) in c) p q`. Evaluating it at `x` gives the matrix of `ρ_M(x)`, so
the trace of its `m`-th power evaluates to `tr (ρ_M(x) ^ m)`. Changing the basis conjugates the
generic action matrix by constant matrices, so this trace does not depend on the basis.

The trace-power polynomials are **invariant** under the coadjoint action of `L` on `S(L*)`: they
lie in `S(L*)^L` (`TauCeti.tracePowerPolynomial_mem_lieInvariants`). This is the polynomial form of
`tr (ρ(x) ^ m) = tr (ρ(g x) ^ m)` for inner automorphisms `g`, and it holds over every commutative
ring: the coadjoint derivation of `y : L`, applied entrywise, sends the generic action matrix `A`
to the commutator `A ρ(y) - ρ(y) A`, hence each power `A ^ m` to `A ^ m ρ(y) - ρ(y) A ^ m`, whose
trace vanishes.

For a semisimple Lie algebra over an algebraically closed field of characteristic zero, these
invariant polynomials restrict on a Cartan subalgebra to the power sums of the weights of `M`, and
they are the invariant polynomial functions used in the surjectivity half of Chevalley's
restriction theorem and of the Harish-Chandra isomorphism.

## Main definitions

* `TauCeti.genericActionMatrix R L c`: the generic action matrix of `L` on `M` in the basis `c`.
* `TauCeti.tracePowerPolynomial R L M m`: the polynomial function `x ↦ tr (ρ_M(x) ^ m)` on `L`, as
  an element of `S(L*)`.

## Main results

* `TauCeti.map_lift_eval_genericActionMatrix`: evaluating the generic action matrix at `x` gives
  the matrix of `ρ_M(x)`.
* `TauCeti.genericActionMatrix_eq_map_toMatrix_mul_mul`: change of basis conjugates the generic
  action matrix.
* `TauCeti.tracePowerPolynomial_eq_trace_pow_genericActionMatrix`: the trace-power polynomial is
  the trace of the `m`-th power of the generic action matrix in any basis.
* `TauCeti.lift_eval_tracePowerPolynomial`: the value of the trace-power polynomial at `x` is
  `tr (ρ_M(x) ^ m)`.
* `TauCeti.tracePowerPolynomial_mem_homogeneousSubmodule`: it is homogeneous of degree `m`.
* `TauCeti.tracePowerPolynomial_mem_lieInvariants`: it is invariant under the coadjoint action.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1, where
  the functions `x ↦ tr (ρ(x) ^ m)` are the invariant polynomial functions used to prove the
  surjectivity of the restriction to a Cartan subalgebra.
-/

public section

namespace TauCeti

open Module _root_.SymmetricAlgebra TauCeti.SymmetricAlgebra

variable (R L : Type*) {M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M]
  [Module R M] [LieRingModule L M] [LieModule R L M]

local notation "S" => SymmetricAlgebra R (Dual R L)
attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### The generic action matrix -/

section GenericActionMatrix

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The generic action matrix** of `L` on `M` in a basis `c` of `M`: the matrix over the algebra
`S(L*)` of polynomial functions on `L` whose `(p, q)` entry is the linear function
`x ↦ (matrix of ρ_M(x) in c) p q`. Evaluating it at `x : L` gives the matrix of `ρ_M(x)`
(`TauCeti.map_lift_eval_genericActionMatrix`). -/
noncomputable def genericActionMatrix (c : Basis κ R M) : Matrix κ κ S :=
  Matrix.of fun p q ↦ ι R (Dual R L) (Matrix.entryLinearMap R R p q ∘ₗ
    (LinearMap.toMatrix c c).toLinearMap ∘ₗ (LieModule.toEnd R L M).toLinearMap)

/-- The `(p, q)` entry of the generic action matrix is the generator of `S(L*)` given by the linear
function `x ↦ (matrix of ρ_M(x) in c) p q`. -/
theorem genericActionMatrix_apply (c : Basis κ R M) (p q : κ) :
    genericActionMatrix R L c p q = ι R (Dual R L) (Matrix.entryLinearMap R R p q ∘ₗ
      (LinearMap.toMatrix c c).toLinearMap ∘ₗ (LieModule.toEnd R L M).toLinearMap) :=
  (rfl)

/-- **Evaluating the generic action matrix** at `x : L` gives the matrix of `ρ_M(x)`. -/
@[simp]
theorem map_lift_eval_genericActionMatrix (c : Basis κ R M) (x : L) :
    (genericActionMatrix R L c).map (lift (Dual.eval R L x)) =
      LinearMap.toMatrix c c (LieModule.toEnd R L M x) := by
  ext p q
  simp [genericActionMatrix_apply]

/-- **Change of basis conjugates the generic action matrix** by the constant change-of-basis
matrices. -/
theorem genericActionMatrix_eq_map_toMatrix_mul_mul {κ' : Type*} [Fintype κ'] [DecidableEq κ']
    (c : Basis κ R M) (c' : Basis κ' R M) :
    genericActionMatrix R L c' = (c'.toMatrix c).map (algebraMap R S) * genericActionMatrix R L c *
      (c.toMatrix c').map (algebraMap R S) := by
  have hgen (a b : R) (f : Dual R L) : algebraMap R S a * ι R (Dual R L) f * algebraMap R S b =
      ι R (Dual R L) ((a * b) • f) := by
    rw [map_smul, Algebra.smul_def, map_mul]
    ring
  ext p q
  simp only [Matrix.mul_apply, Matrix.map_apply, genericActionMatrix_apply, Finset.sum_mul, hgen,
    ← map_sum]
  congr 1
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LieHom.coe_toLinearMap, LinearEquiv.coe_coe,
    Matrix.entryLinearMap_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := c') (c := c') (b' := c)
    (c' := c)]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun s _ ↦ by ring

/-- The trace of a power of the generic action matrix does not depend on the basis. -/
theorem trace_pow_genericActionMatrix {κ' : Type*} [Fintype κ'] [DecidableEq κ']
    (c : Basis κ R M) (c' : Basis κ' R M) (m : ℕ) :
    (genericActionMatrix R L c' ^ m).trace = (genericActionMatrix R L c ^ m).trace := by
  set P := (c'.toMatrix c).map (algebraMap R S)
  set Q := (c.toMatrix c').map (algebraMap R S)
  set A := genericActionMatrix R L c
  have hPQ : P * Q = 1 := by
    rw [← Matrix.map_mul, c'.toMatrix_mul_toMatrix_flip c,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP : Q * P = 1 := by
    rw [← Matrix.map_mul, c.toMatrix_mul_toMatrix_flip c',
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hpow (n : ℕ) : (P * A * Q) ^ n = P * A ^ n * Q := by
    induction n with
    | zero => simp [hPQ]
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
  rw [genericActionMatrix_eq_map_toMatrix_mul_mul R L c c', hpow, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, hQP, Matrix.one_mul]

/-- **The coadjoint action on the generic action matrix.** The derivation of `S(L*)` by which
`y : L` acts, applied entrywise, sends the generic action matrix `A` to the commutator
`A ρ_M(y) - ρ_M(y) A` with the constant matrix of `ρ_M(y)`. -/
theorem map_lieModuleDerivation_genericActionMatrix (c : Basis κ R M) (y : L) :
    (genericActionMatrix R L c).map (lieModuleDerivation R L (Dual R L) y) =
      genericActionMatrix R L c *
          (LinearMap.toMatrix c c (LieModule.toEnd R L M y)).map (algebraMap R S) -
        (LinearMap.toMatrix c c (LieModule.toEnd R L M y)).map (algebraMap R S) *
          genericActionMatrix R L c := by
  have hgen (a : R) (f : Dual R L) :
      ι R (Dual R L) f * algebraMap R S a = ι R (Dual R L) (a • f) := by
    rw [map_smul, Algebra.smul_def, mul_comm]
  have hgen' (a : R) (f : Dual R L) :
      algebraMap R S a * ι R (Dual R L) f = ι R (Dual R L) (a • f) := by
    rw [map_smul, Algebra.smul_def]
  ext p q
  simp only [Matrix.map_apply, genericActionMatrix_apply, lieModuleDerivation_ι, Matrix.sub_apply,
    Matrix.mul_apply, hgen, hgen', ← map_sum, ← map_sub]
  congr 1
  ext x
  simp only [Module.Dual.lie_apply, LinearMap.coe_comp, Function.comp_apply,
    LieHom.coe_toLinearMap, LieHom.map_lie, LinearEquiv.coe_coe, Matrix.entryLinearMap_apply,
    LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Ring.lie_def, LinearMap.toMatrix_mul, map_sub, Matrix.mul_apply]
  rw [neg_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun r _ ↦ by ring

end GenericActionMatrix

/-! ### The trace-power polynomials -/

section TracePowerPolynomial

variable (M) [Module.Free R M] [Module.Finite R M]

/-- **The trace-power polynomial** of the Lie module `M`: the polynomial function
`x ↦ tr (ρ_M(x) ^ m)` on `L`, as an element of the symmetric algebra `S(L*)`
(`TauCeti.lift_eval_tracePowerPolynomial`). It is the trace of the `m`-th power of the generic
action matrix of any basis of `M` (`TauCeti.tracePowerPolynomial_eq_trace_pow_genericActionMatrix`),
and it is invariant under the coadjoint action of `L`
(`TauCeti.tracePowerPolynomial_mem_lieInvariants`). -/
noncomputable def tracePowerPolynomial (m : ℕ) : S :=
  letI := Classical.decEq (Free.ChooseBasisIndex R M)
  (genericActionMatrix R L (Free.chooseBasis R M) ^ m).trace

variable {R L M}

/-- The trace-power polynomial is the trace of the `m`-th power of the generic action matrix in any
basis of `M`. -/
theorem tracePowerPolynomial_eq_trace_pow_genericActionMatrix {κ : Type*} [Fintype κ]
    [DecidableEq κ] (c : Basis κ R M) (m : ℕ) :
    tracePowerPolynomial R L M m = (genericActionMatrix R L c ^ m).trace := by
  let := Classical.decEq (Free.ChooseBasisIndex R M)
  exact trace_pow_genericActionMatrix R L c (Free.chooseBasis R M) m

/-- **The value of the trace-power polynomial** at `x : L` is `tr (ρ_M(x) ^ m)`. -/
@[simp]
theorem lift_eval_tracePowerPolynomial (x : L) (m : ℕ) :
    lift (Dual.eval R L x) (tracePowerPolynomial R L M m) =
      LinearMap.trace R M (LieModule.toEnd R L M x ^ m) := by
  classical
  let c := Free.chooseBasis R M
  rw [tracePowerPolynomial_eq_trace_pow_genericActionMatrix c, AddMonoidHom.map_trace,
    LinearMap.trace_eq_matrix_trace R c, ← LinearMap.toMatrix_pow,
    ← map_lift_eval_genericActionMatrix,
    ← AlgHom.mapMatrix_apply, map_pow, AlgHom.mapMatrix_apply]

/-- **The trace-power polynomial of degree `m` is homogeneous of degree `m`.** -/
theorem tracePowerPolynomial_mem_homogeneousSubmodule (m : ℕ) :
    tracePowerPolynomial R L M m ∈ homogeneousSubmodule R (Dual R L) m := by
  classical
  let c := Free.chooseBasis R M
  rw [tracePowerPolynomial_eq_trace_pow_genericActionMatrix c]
  -- every entry of the `n`-th power of the generic action matrix has degree `n`
  have hentry (n : ℕ) (p q : Free.ChooseBasisIndex R M) :
      (genericActionMatrix R L c ^ n) p q ∈ homogeneousSubmodule R (Dual R L) n := by
    induction n generalizing q with
    | zero =>
      rw [pow_zero, Matrix.one_apply]
      split_ifs
      · exact SetLike.GradedOne.one_mem
      · exact Submodule.zero_mem _
    | succ n ih =>
      rw [pow_succ, Matrix.mul_apply]
      exact Submodule.sum_mem _ fun r _ ↦ SetLike.mul_mem_graded (ih r)
        (ι_mem_homogeneousSubmodule R (Dual R L) _)
  exact Submodule.sum_mem _ fun p _ ↦ hentry m p p

/-- **The trace-power polynomials are invariant** under the coadjoint action of `L` on `S(L*)`. -/
theorem tracePowerPolynomial_mem_lieInvariants (m : ℕ) :
    tracePowerPolynomial R L M m ∈ lieInvariants R L (Dual R L) := by
  classical
  let c := Free.chooseBasis R M
  refine mem_lieInvariants.mpr fun y ↦ ?_
  rw [tracePowerPolynomial_eq_trace_pow_genericActionMatrix c]
  refine Derivation.trace_pow_eq_zero_of_map_eq_mul_sub_mul _
    (B := -(LinearMap.toMatrix c c (LieModule.toEnd R L M y)).map (algebraMap R S)) ?_ m
  rw [map_lieModuleDerivation_genericActionMatrix, neg_mul, mul_neg, sub_neg_eq_add,
    neg_add_eq_sub]

end TracePowerPolynomial

end TauCeti
