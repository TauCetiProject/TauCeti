/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# Bases of constants in a constant field extension

Let `F' = F · k'` be the compositum of a field `F` with a separable extension `k'` of a field `k`
that is relatively algebraically closed in `F`; the case of interest is a constant field extension
of an algebraic function field `F / k` with exact constant field `k`.  Linear disjointness of `F`
and `k'` over `k` makes `F'` behave like `F ⊗[k] k'`: the image in `F'` of a `k`-basis of `k'` is
an `F`-basis of `F'`, the coordinates of a constant in this basis are the images of its
coordinates over `k`, the trace from `F'` to `F` of a constant is the image of its trace from `k'`
to `k`, and the trace dual of a basis of constants is the basis of constants attached to the trace
dual over `k`.  Comparing coordinates before and after raising to a power of the characteristic
also shows that `k'` is the exact constant field of `F'`.

These are the linear-algebraic inputs to the local theory of constant field extensions: at every
place `P` of `F / k` a basis of constants is an integral basis, which is what identifies the
functions of `F' = F · k'` with bounded poles in terms of those of `F`.

## Main definitions and results

* `TauCeti.finrank_le_finrank_of_constantCompositum_eq_top`: `[F · k' : F] ≤ [k' : k]` for any
  finite `k' / k`, with no exactness or separability hypothesis.
* `TauCeti.constantBasis`: the `F`-basis of `F' = F · k'` given by a `k`-basis of `k'`.
* `TauCeti.constantBasis_repr_algebraMap`: the coordinates of a constant in a basis of constants
  are the images of its coordinates over `k`.
* `TauCeti.isIntegrallyClosedIn_of_constantCompositum_eq_top`: `k'` is the exact constant field
  of `F · k'` (Stichtenoth, Proposition 3.6.1(a)), with no perfectness hypothesis.
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

/-- **Adjoining finitely many constants costs at most their degree**: if `F' = F · k'` for a finite
extension `k' / k`, then `[F' : F] ≤ [k' : k]`, because the image of a `k`-basis of `k'` spans `F'`
over `F`.  Equality is the degree form of linear disjointness of `F` and `k'` over `k`
(`TauCeti.finrank_constantCompositum_eq_finrank_of_isSeparable`); for an inseparable `k' / k` the
inequality can be strict. -/
theorem finrank_le_finrank_of_constantCompositum_eq_top [FiniteDimensional k k']
    (h : constantCompositum F k' F' = ⊤) : Module.finrank F F' ≤ Module.finrank k k' := by
  let b := Module.finBasis k k'
  have hle := finrank_range_le_card (R := F) (algebraMap k' F' ∘ b)
  rwa [Set.finrank, span_range_algebraMap_comp_of_constantCompositum_eq_top h b, finrank_top,
    Fintype.card_fin] at hle

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
/-- **The constant field of a separable constant field extension** (Stichtenoth,
Proposition 3.6.1(a)): if `k` is the exact constant field of `F` and `k' / k` is separable
algebraic, then the compositum `F' = F · k'` has exact constant field `k'`.  Stichtenoth assumes
`k` perfect; separability of `k' / k` is all that is needed.  For an inseparable `k' / k` the
conclusion can fail: `k = 𝔽_p(t, u)` is exact in `F = k(x, y)` with `y ^ p = t * x ^ p + u`, but
`y - t ^ (1/p) * x` is a `p`-th root of `u` in `F · k(t ^ (1/p))`.

Together with `TauCeti.IsFunctionField.of_constantCompositum_eq_top`, this makes `F · k' / k'` a
function field with exact constant field for a separable algebraic `k' / k`, so that its genus,
its places and their degrees are the ones the theory of constant field extensions compares with
those of `F / k`. -/
theorem isIntegrallyClosedIn_of_constantCompositum_eq_top : IsIntegrallyClosedIn k' F' := by
  -- An element `z` algebraic over `k'` has a power `z ^ q ^ n` that is a constant. Raising to the
  -- power `q ^ n` carries a `k`-basis of the separable extension `k'` to another one, so the
  -- coordinates of `z` in a basis of constants have `q ^ n`-th powers in `k`, hence lie in `k`.
  refine isIntegrallyClosedIn_iff_forall_isAlgebraic.2 fun z hz ↦ ?_
  let q := ringExpChar k
  have : ExpChar k' q := expChar_of_injective_algebraMap (algebraMap k k').injective q
  have : ExpChar F q := expChar_of_injective_algebraMap (algebraMap k F).injective q
  have : ExpChar F' q := expChar_of_injective_algebraMap (algebraMap k F').injective q
  -- Some power `z ^ q ^ n` is separable over `k'`, hence a constant.
  obtain ⟨g, hg, n, hgz⟩ := (minpoly.irreducible hz.isIntegral).hasSeparableContraction q
  have hsep : IsSeparable k' (z ^ q ^ n) := hg.of_dvd <| minpoly.dvd k' _ <| by
    simpa only [Polynomial.expand_aeval, minpoly.aeval] using congr(Polynomial.aeval z $hgz)
  obtain ⟨c, hc⟩ : ∃ c : k', algebraMap k' F' c = z ^ q ^ n := by
    refine IntermediateField.mem_bot.1 ?_
    rw [← separableClosure_eq_bot_of_constantCompositum_eq_top hex h]
    exact mem_separableClosure_iff.2 hsep
  -- Compare coordinates in the bases of constants given by `b` and by its `q ^ n`-th powers.
  let b := Basis.ofVectorSpace k k'
  let B := constantBasis hex h b
  let B' := constantBasis hex h (b.mapPowExpCharPowOfIsSeparable q n)
  have hpow : z ^ q ^ n = Finsupp.linearCombination F B'
      ((B.repr z).mapRange (iterateFrobenius F q n) (map_zero _)) := by
    conv_lhs => rw [← B.linearCombination_repr z]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (by simp), ← iterateFrobenius_def, map_finsuppSum]
    refine Finsupp.sum_congr fun i _ ↦ ?_
    simp [B, B', Module.Basis.mapPowExpCharPowOfIsSeparable, Algebra.smul_def,
      iterateFrobenius_def, mul_pow]
  have hcoord (i) : ∃ a : k, algebraMap k F a = B.repr z i := by
    have hi := congrArg (fun w ↦ B'.repr w i) hpow
    simp only [B'.repr_linearCombination, Finsupp.mapRange_apply, iterateFrobenius_def] at hi
    rw [← hc, constantBasis_repr_algebraMap] at hi
    let _ := hex
    exact IsIntegrallyClosedIn.isIntegral_iff.mp <| (IsAlgebraic.of_pow
      (pow_pos (expChar_pos k q) n) (hi ▸ isAlgebraic_algebraMap _)).isIntegral
  choose a ha using hcoord
  -- So `z` is the image of a constant.
  refine ⟨∑ i ∈ (B.repr z).support, a i • b i, ?_⟩
  conv_rhs => rw [← B.linearCombination_repr z]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← ha, constantBasis_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

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
