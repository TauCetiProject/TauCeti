/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic

/-!
# Bases of constants in a constant field extension

Let `F' = F · k'` be the compositum of a field `F` with a separable extension `k'` of a field `k`
that is relatively algebraically closed in `F`; the case of interest is a constant field extension
of an algebraic function field `F / k` with exact constant field `k`.  Linear disjointness of `F`
and `k'` over `k` makes `F'` behave like `F ⊗[k] k'`: the image in `F'` of a `k`-basis of `k'` is
an `F`-basis of `F'`, the coordinates of a constant in this basis are the images of its
coordinates over `k`, the trace from `F'` to `F` of a constant is the image of its trace from `k'`
to `k`, and the trace dual of a basis of constants is the basis of constants attached to the trace
dual over `k`.

These are the linear-algebraic inputs to the local theory of constant field extensions: at every
place `P` of `F / k` a basis of constants is an integral basis, which is what identifies the
functions of `F' = F · k'` with bounded poles in terms of those of `F`.

## Main definitions and results

* `TauCeti.constantBasis`: the `F`-basis of `F' = F · k'` given by a `k`-basis of `k'`.
* `TauCeti.constantBasis_repr_algebraMap`: the coordinates of a constant in a basis of constants
  are the images of its coordinates over `k`.
* `TauCeti.trace_algebraMap_of_constantCompositum_eq_top`: the trace of a constant is the image
  of its trace over `k`.  This is Mathlib's `Subalgebra.LinearDisjoint.trace_algebraMap` for the
  linearly disjoint pair `F`, `k'`, stated for the trace over the field `F` itself rather than
  over its image in `F'`.
* `TauCeti.traceDual_constantBasis`: the trace dual of a basis of constants.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
Proposition 3.6.1.
-/

public section

open Module

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- The constants generate the compositum `F · k'` as an `F`-algebra: for an algebraic extension
of constants, the intermediate field they generate is already the subalgebra they generate. -/
theorem adjoin_range_algebraMap_of_constantCompositum_eq_top [Algebra.IsIntegral k k']
    (h : constantCompositum F k' F' = ⊤) :
    Algebra.adjoin F (Set.range (algebraMap k' F')) = ⊤ := by
  have halg : ∀ x ∈ Set.range (algebraMap k' F'), IsAlgebraic F x := by
    rintro _ ⟨c, rfl⟩
    exact ((Algebra.IsIntegral.isIntegral (R := k) c).map
      (IsScalarTower.toAlgHom k k' F')).tower_top.isAlgebraic
  have := congrArg IntermediateField.toSubalgebra h
  rwa [constantCompositum_def, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg,
    IntermediateField.top_toSubalgebra] at this

/-- The image of a `k`-basis of `k'` spans the compositum `F' = F · k'` over `F`, for an algebraic
extension of constants. -/
theorem span_range_algebraMap_comp_of_constantCompositum_eq_top [Algebra.IsIntegral k k']
    (h : constantCompositum F k' F' = ⊤) {ι : Type*} (b : Basis ι k k') :
    Submodule.span F (Set.range (algebraMap k' F' ∘ b)) = ⊤ := by
  let L : Subalgebra k F' := (IsScalarTower.toAlgHom k k' F').range
  let e : k' ≃ₐ[k] L := AlgEquiv.ofInjective _ (algebraMap k' F').injective
  have hspan := Subalgebra.adjoin_eq_span_basis F L (b.map e.toLinearEquiv)
  have hfun : (fun i ↦ ((b.map e.toLinearEquiv) i).1) = algebraMap k' F' ∘ b := by
    ext i
    exact AlgEquiv.ofInjective_apply _ (algebraMap k' F').injective (b i)
  rw [AlgHom.coe_range, IsScalarTower.coe_toAlgHom',
    adjoin_range_algebraMap_of_constantCompositum_eq_top (k := k) h, Algebra.top_toSubmodule, hfun]
    at hspan
  exact hspan.symm

variable [Algebra.IsSeparable k k']
variable (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)

/-- **A basis of constants**: the `F`-basis of the compositum `F' = F · k'` given by the image of
a `k`-basis of `k'`.  Linear independence is the linear disjointness of `F` and `k'` over `k`
(Stichtenoth, Proposition 3.6.1(b)), which needs `k` exact in `F` and `k' / k` separable; spanning
is the definition of the compositum. -/
noncomputable def constantBasis {ι : Type*} (b : Basis ι k k') : Basis ι F F' :=
  Basis.mk (linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn hex
    (fun i ↦ Algebra.IsSeparable.isSeparable k (b i)) b.linearIndependent)
    (span_range_algebraMap_comp_of_constantCompositum_eq_top h b).ge

@[simp]
theorem constantBasis_apply {ι : Type*} (b : Basis ι k k') (i : ι) :
    constantBasis hex h b i = algebraMap k' F' (b i) :=
  Basis.mk_apply _ _ i

theorem coe_constantBasis {ι : Type*} (b : Basis ι k k') :
    ⇑(constantBasis hex h b) = algebraMap k' F' ∘ b :=
  Basis.coe_mk _ _

/-- The coordinates of a constant in a basis of constants are the images of its coordinates
over `k`. -/
@[simp]
theorem constantBasis_repr_algebraMap {ι : Type*} (b : Basis ι k k') (c : k') (i : ι) :
    (constantBasis hex h b).repr (algebraMap k' F' c) i = algebraMap k F (b.repr c i) := by
  have hc : algebraMap k' F' c = Finsupp.linearCombination F (constantBasis hex h b)
      ((b.repr c).mapRange (algebraMap k F) (map_zero _)) := by
    conv_lhs => rw [← b.linearCombination_repr c]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, map_finsuppSum,
      Finsupp.sum_mapRange_index]
    · refine Finsupp.sum_congr fun j _ ↦ ?_
      simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, constantBasis_apply]
    · intro
      simp
  rw [hc, Basis.repr_linearCombination, Finsupp.mapRange_apply]

include hex h in
/-- **The trace of a constant is a constant**: for a finite separable extension of constants, the
trace from `F' = F · k'` to `F` of a constant is the image of its trace from `k'` to `k`.

This is not a `simp` lemma: the base field `k` does not occur in the left-hand side, so `simp`
cannot infer it (the `simpNF` linter rejects the lemma); use `rw`. -/
theorem trace_algebraMap_of_constantCompositum_eq_top [FiniteDimensional k k'] (c : k') :
    Algebra.trace F F' (algebraMap k' F' c) = algebraMap k F (Algebra.trace k k' c) := by
  classical
  let b := Module.finBasis k k'
  rw [Algebra.trace_eq_matrix_trace (constantBasis hex h b), Algebra.trace_eq_matrix_trace b,
    Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, constantBasis_apply, ← map_mul,
    constantBasis_repr_algebraMap]

/-- The trace dual of a basis of constants is the basis of constants attached to the trace dual
over `k`: the trace form of `F' / F` restricts on constants to the trace form of `k' / k`. -/
@[simp]
theorem traceDual_constantBasis [FiniteDimensional k k'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι k k') :
    (constantBasis hex h b).traceDual = constantBasis hex h b.traceDual := by
  refine Basis.eq_of_apply_eq (congrFun (Basis.traceDual_eq_iff.2 fun i j ↦ ?_))
  rw [constantBasis_apply, constantBasis_apply, Algebra.traceForm_apply, ← map_mul,
    trace_algebraMap_of_constantCompositum_eq_top hex h, Basis.trace_traceDual_mul]
  split_ifs <;> simp

end TauCeti
